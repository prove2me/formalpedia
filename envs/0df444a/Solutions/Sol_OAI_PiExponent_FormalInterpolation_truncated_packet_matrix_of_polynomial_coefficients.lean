-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_matrix_of_polynomial_coefficients
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-16T11:51:48.445979+00:00
-- url     : https://prove2.me/submissions/96b659c7-1f5f-47d6-bd56-5651384309f2

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

/- The exact requested statement is false without a support-containment hypothesis.
   For m = 0, K = 1, w0 = 0, v0 = theta = H = 1, and P = X 0,
   the column bound is the natural floor of H / w0, hence zero.
   The matrix image is zero, while the packet's zero-exponent row is one.
   The final theorem certifies the negation of the entire quantified target. -/

noncomputable def packetObstructionPolynomial :
    WeightedPolynomial 0 (fun _ : Fin 0 => (0 : Real)) 1 :=
  ⟨MvPolynomial.X 0, by
    intro a ha
    simp [InterpolationMatrix.columnWeights]⟩

noncomputable def packetObstructionRow :
    InterpolationMatrix.Row 1 1 1 (fun _ : Fin 0 => (0 : Real)) 1 :=
  (0, ⟨fun _ => 0, by
    simp [strictWeightedSimplex, realWeightedSimplex,
      InterpolationMatrix.rowWeights, Fintype.mem_piFinset]⟩)

theorem packetObstruction_column_zero
    (c : InterpolationMatrix.Column 0 (fun _ : Fin 0 => (0 : Real)) 1) :
    c.val = fun _ => 0 := by
  have hc := c.property
  simp only [realWeightedSimplex, Finset.mem_filter] at hc
  have h := hc.1
  simp [Fintype.mem_piFinset, InterpolationMatrix.columnWeights] at h
  funext i
  fin_cases i
  simpa using h

theorem packetObstruction_packet_one :
    truncatedPolynomialPacket 1 1 1 (fun _ : Fin 0 => (0 : Real)) 1
      (fun _ => (0 : Complex)) (fun _ => 0) packetObstructionPolynomial.val
      packetObstructionRow = 1 := by
  have hz : InterpolationMatrix.exponentVector (fun _ : Fin 1 => 0) = 0 := by
    ext
    simp [InterpolationMatrix.exponentVector]
  simp [truncatedPolynomialPacket, truncatedPolynomialJet,
    packetObstructionPolynomial, packetObstructionRow, hz]

theorem packetObstruction_matrix_zero :
    (InterpolationMatrix.truncatedLogMatrix 1 0 1 1
      (fun _ : Fin 0 => (0 : Real)) 1 (fun _ => (0 : Complex)) (fun _ => 0)).mulVecLin
      (fun c : InterpolationMatrix.Column 0 (fun _ : Fin 0 => (0 : Real)) 1 =>
        packetObstructionPolynomial.val.coeff (InterpolationMatrix.exponentVector c.1)) = 0 := by
  have hz : (fun c : InterpolationMatrix.Column 0 (fun _ : Fin 0 => (0 : Real)) 1 =>
      packetObstructionPolynomial.val.coeff (InterpolationMatrix.exponentVector c.1)) = 0 := by
    funext c
    rw [packetObstruction_column_zero c]
    have he : InterpolationMatrix.exponentVector (fun _ : Fin 1 => 0) = 0 := by
      ext
      simp [InterpolationMatrix.exponentVector]
    simp [packetObstructionPolynomial, he]
  rw [hz, map_zero]

theorem solution :
    ¬ (∀ {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
      (r : Fin m → Complex) (T : Fin m → Nat) (P : WeightedPolynomial w0 w H),
      truncatedPolynomialPacket K v0 theta w H r T P.val =
        (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
          (fun c : InterpolationMatrix.Column w0 w H =>
            P.val.coeff (InterpolationMatrix.exponentVector c.1))) := by
  intro h
  have he := h (m := 0) 1 0 1 1 (fun _ : Fin 0 => (0 : Real)) 1
    (fun _ => (0 : Complex)) (fun _ => 0) packetObstructionPolynomial
  rw [packetObstruction_matrix_zero] at he
  have hr := congrFun he packetObstructionRow
  rw [packetObstruction_packet_one] at hr
  exact one_ne_zero hr
