-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-13T12:54:13.925858+00:00
-- url     : https://prove2.me/submissions/091c2d71-8658-4bfb-bb8f-57286e7cf5a2

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

/- The requested target is false. These auxiliary declarations certify the
   obstruction; this file does not claim to prove the requested target.
   Take m = 0, K = 1, w0 = 0, v0 = theta = H = 1, and P = X 0.
   The weighted support bound permits P, but the column simplex contains
   only exponent zero because H / w0 = 0. Hence its coefficient vector
   is zero, while the packet's constant coefficient is one. -/

noncomputable def counterexamplePolynomial :
    WeightedPolynomial 0 (fun _ : Fin 0 => (0 : Real)) 1 :=
  ⟨MvPolynomial.X 0, by
    intro a ha
    simp [InterpolationMatrix.columnWeights]⟩

noncomputable def counterexampleRow :
    InterpolationMatrix.Row 1 1 1 (fun _ : Fin 0 => (0 : Real)) 1 :=
  (0, ⟨fun _ => 0, by
    simp [strictWeightedSimplex, realWeightedSimplex,
      InterpolationMatrix.rowWeights, Fintype.mem_piFinset]⟩)

theorem counterexampleColumn_zero
    (c : InterpolationMatrix.Column 0 (fun _ : Fin 0 => (0 : Real)) 1) :
    c.val = fun _ => 0 := by
  have hc := c.property
  simp only [realWeightedSimplex, Finset.mem_filter] at hc
  have h := hc.1
  simp [Fintype.mem_piFinset, InterpolationMatrix.columnWeights] at h
  funext i
  fin_cases i
  simpa using h

theorem counterexamplePacket_one :
    truncatedPolynomialPacket 1 1 1 (fun _ : Fin 0 => (0 : Real)) 1
      (fun _ => (0 : Complex)) (fun _ => 0) counterexamplePolynomial.val
      counterexampleRow = 1 := by
  have hz : InterpolationMatrix.exponentVector (fun _ : Fin 1 => 0) = 0 := by
    ext
    simp [InterpolationMatrix.exponentVector]
  simp [truncatedPolynomialPacket, truncatedPolynomialJet,
    counterexamplePolynomial, counterexampleRow, hz]

theorem counterexampleMatrix_zero :
    (InterpolationMatrix.truncatedLogMatrix 1 0 1 1
      (fun _ : Fin 0 => (0 : Real)) 1 (fun _ => (0 : Complex)) (fun _ => 0)).mulVecLin
      (fun c : InterpolationMatrix.Column 0 (fun _ : Fin 0 => (0 : Real)) 1 =>
        counterexamplePolynomial.val.coeff (InterpolationMatrix.exponentVector c.1)) = 0 := by
  have hz : (fun c : InterpolationMatrix.Column 0 (fun _ : Fin 0 => (0 : Real)) 1 =>
      counterexamplePolynomial.val.coeff (InterpolationMatrix.exponentVector c.1)) = 0 := by
    funext c
    rw [counterexampleColumn_zero c]
    have he : InterpolationMatrix.exponentVector (fun _ : Fin 1 => 0) = 0 := by
      ext
      simp [InterpolationMatrix.exponentVector]
    simp [counterexamplePolynomial, he]
  rw [hz, map_zero]

theorem solution :
    ¬ (∀ {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
      (r : Fin m → Complex) (T : Fin m → Nat) (P : WeightedPolynomial w0 w H),
      truncatedPolynomialPacket K v0 theta w H r T P.val =
        (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
          (fun c : InterpolationMatrix.Column w0 w H =>
            P.val.coeff (InterpolationMatrix.exponentVector c.1))) := by
  intro h
  have he := h 1 0 1 1 (fun _ : Fin 0 => (0 : Real)) 1
    (fun _ => (0 : Complex)) (fun _ => 0) counterexamplePolynomial
  rw [counterexampleMatrix_zero] at he
  have hr := congrFun he counterexampleRow
  rw [counterexamplePacket_one] at hr
  exact one_ne_zero hr
