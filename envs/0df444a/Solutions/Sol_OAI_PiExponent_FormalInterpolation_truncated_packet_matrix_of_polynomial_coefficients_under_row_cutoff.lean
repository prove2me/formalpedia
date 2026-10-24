-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_matrix_of_polynomial_coefficients_under_row_cutoff
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:38:22.823689+00:00
-- url     : https://prove2.me/submissions/24c690ec-f47e-44ee-857e-1145fcdcfc53

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution : ¬ (∀ {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (hT : ∀ i, InterpolationMatrix.rowWeights v0 theta w i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights v0 theta w 0)
    (P : WeightedPolynomial w0 w H),
    truncatedPolynomialPacket K v0 theta w H r T P.val =
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : InterpolationMatrix.Column w0 w H =>
          P.val.coeff (InterpolationMatrix.exponentVector c.1))) := by
  intro h
  have hP : ∀ a ∈ (MvPolynomial.X 0 : MvPolynomial (Fin (0 + 1)) ℂ).support,
      ∑ i, InterpolationMatrix.columnWeights (0 : ℝ) (fun i : Fin 0 => Fin.elim0 i) i * (a i : ℝ)
        ≤ 1 := by
    intro a _
    simp [InterpolationMatrix.columnWeights]
  have h1 := h (m := 0) 1 0 1 1 (fun i => Fin.elim0 i) 1 (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) ⟨MvPolynomial.X 0, hP⟩
  have hrow : (fun _ : Fin (0 + 1) => (0 : ℕ)) ∈ strictWeightedSimplex
      (InterpolationMatrix.rowWeights (1 : ℝ) 1 (fun i : Fin 0 => Fin.elim0 i)) 1 := by
    simp [strictWeightedSimplex, realWeightedSimplex]
  have h2 := congrFun h1 ((0 : Fin 1), ⟨fun _ => 0, hrow⟩)
  have hL : truncatedPolynomialPacket 1 1 1 (fun i : Fin 0 => Fin.elim0 i) 1
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (MvPolynomial.X 0)
      ((0 : Fin 1), ⟨fun _ => 0, hrow⟩) = 1 := by
    have hz : Finsupp.equivFunOnFinite.symm (fun _ : Fin (0 + 1) => (0:ℕ)) = 0 := by ext; simp
    simp [truncatedPolynomialPacket, truncatedPolynomialJet, InterpolationMatrix.exponentVector,
      MvPolynomial.coeff_X', hz]
  have hR : (InterpolationMatrix.truncatedLogMatrix 1 0 1 1 (fun i : Fin 0 => Fin.elim0 i) 1
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)).mulVecLin
        (fun c : InterpolationMatrix.Column (0 : ℝ) (fun i : Fin 0 => Fin.elim0 i) 1 =>
          (MvPolynomial.X 0 : MvPolynomial (Fin (0 + 1)) ℂ).coeff
            (InterpolationMatrix.exponentVector c.1)) ((0 : Fin 1), ⟨fun _ => 0, hrow⟩) = 0 := by
    rw [Matrix.mulVecLin_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    have hc : c.1 = fun _ => 0 := by
      have := c.2
      simp only [realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset] at this
      funext i
      have h0 := this.1 i
      fin_cases i
      simpa [InterpolationMatrix.columnWeights] using h0
    have : (MvPolynomial.X 0 : MvPolynomial (Fin (0 + 1)) ℂ).coeff
        (InterpolationMatrix.exponentVector c.1) = 0 := by
      rw [hc, MvPolynomial.coeff_X']
      rw [if_neg]
      intro he
      have := congrArg (fun f => f 0) he
      simp [InterpolationMatrix.exponentVector] at this
    dsimp only
    rw [this, mul_zero]
  rw [hL, hR] at h2
  exact one_ne_zero h2
