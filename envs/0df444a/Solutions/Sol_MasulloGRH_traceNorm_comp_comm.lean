-- Prove2me | solution 1 for MasulloGRH.traceNorm_comp_comm
-- status  : ACCEPTED   (disprove)
-- author  : @marozols
-- created : 2026-11-21T00:56:06.638642+00:00
-- url     : https://prove2.me/submissions/dd950a02-4b9e-4551-9cb1-cfd61ca1b7da

import Definitions.Def_MasulloGRH_HilbertNuclear

set_option autoImplicit false
set_option linter.unusedVariables false

open MasulloGRH

theorem solution : ¬ (∀ (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (hT : IsNuclearOperator T)
    (A : H →L[ℂ] H),
    traceNorm (A ∘L T) = traceNorm (T ∘L A)) := by
  intro h
  -- the standard orthonormal basis of `ℂ²`
  obtain ⟨e, he⟩ : ∃ e : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)),
      ∀ i j, inner ℂ (e i) (e j) = if i = j then (1 : ℂ) else 0 :=
    ⟨EuclideanSpace.basisFun (Fin 2) ℂ,
      orthonormal_iff_ite.1 (EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal⟩
  have h00 : inner ℂ (e 0) (e 0) = (1 : ℂ) := by rw [he]; simp
  have h11 : inner ℂ (e 1) (e 1) = (1 : ℂ) := by rw [he]; simp
  have h01 : inner ℂ (e 0) (e 1) = (0 : ℂ) := by rw [he]; simp
  have h10 : inner ℂ (e 1) (e 0) = (0 : ℂ) := by rw [he]; simp
  -- rank-one operators `u ↦ ⟨u, x⟩ y`
  have R : ∀ x y : EuclideanSpace ℂ (Fin 2),
      ∃ S : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
        ∀ u, S u = inner ℂ x u • y :=
    fun x y => ⟨(innerSL ℂ x).smulRight y, fun u => rfl⟩
  obtain ⟨T, hTa⟩ := R (e 0) (e 0)
  obtain ⟨A, hAa⟩ := R (e 1) (e 0)
  obtain ⟨B, hBa⟩ := R (e 0) (e 1)
  obtain ⟨P, hPa⟩ := R (e 1) (e 1)
  have hT : IsNuclearOperator T := by
    refine ⟨fun m => if m = 0 then e 0 else 0, fun m => if m = 0 then e 0 else 0, ?_,
      fun u => ?_⟩
    · refine summable_of_ne_finset_zero (s := {0}) fun m hm => ?_
      have hm' : m ≠ 0 := by simpa using hm
      simp [hm']
    · rw [hTa]
      have h1 := hasSum_ite_eq (0 : ℕ) (inner ℂ (e 0) u • e 0)
      have e1 : (fun m : ℕ => inner ℂ (if m = 0 then e 0 else 0) u • (if m = 0 then e 0 else 0)) =
          fun m : ℕ => if m = 0 then inner ℂ (e 0) u • e 0 else 0 := by
        funext m
        split_ifs <;> simp
      rw [e1]
      exact h1
  -- `A T = 0` and `T A = A`
  have hAT : A ∘L T = 0 := by
    ext1 u
    rw [ContinuousLinearMap.comp_apply, hAa, hTa, inner_smul_right, h10]
    simp
  have hTA : T ∘L A = A := by
    ext1 u
    rw [ContinuousLinearMap.comp_apply, hTa, hAa, inner_smul_right, h00, mul_one]
  -- `|A| = P`
  have hstar : star A = B := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [hBa, hAa, inner_smul_left, inner_smul_right, inner_conj_symm]
    ring
  have hBA : star A * A = P := by
    rw [hstar]
    ext1 u
    change B (A u) = P u
    rw [hAa, hBa, hPa, inner_smul_right, h00, mul_one]
  have hPP : P * P = P := by
    ext1 u
    change P (P u) = P u
    rw [hPa (P u), hPa u, inner_smul_right, h11, mul_one]
  have hP0 : 0 ≤ P := by
    rw [← hBA]
    exact star_mul_self_nonneg A
  have habsA : operatorAbs A = P := by
    unfold operatorAbs
    rw [hBA]
    have h1 := CFC.sqrt_mul_self P hP0
    rw [hPP] at h1
    exact h1
  have htrP : operatorTrace P = 1 := by
    unfold operatorTrace
    have h1 : ∀ i, inner ℂ (chosenHilbertBasis (EuclideanSpace ℂ (Fin 2)) i)
        (P (chosenHilbertBasis (EuclideanSpace ℂ (Fin 2)) i)) =
        inner ℂ (e 1) (chosenHilbertBasis (EuclideanSpace ℂ (Fin 2)) i) *
          inner ℂ (chosenHilbertBasis (EuclideanSpace ℂ (Fin 2)) i) (e 1) := by
      intro i
      rw [hPa, inner_smul_right]
    rw [tsum_congr h1, (chosenHilbertBasis (EuclideanSpace ℂ (Fin 2))).tsum_inner_mul_inner, h11]
  have h1 : traceNorm (T ∘L A) = 1 := by
    unfold traceNorm
    rw [hTA, habsA, htrP]
    simp
  have h0 : traceNorm (A ∘L T) = 0 := by
    unfold traceNorm operatorAbs operatorTrace
    rw [hAT]
    simp [CFC.sqrt_zero]
  have hfinal := h (EuclideanSpace ℂ (Fin 2)) T hT A
  rw [h0, h1] at hfinal
  norm_num at hfinal
