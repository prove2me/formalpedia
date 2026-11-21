-- Prove2me | solution 1 for MasulloGRH.approxNumber_add_le_same_index
-- status  : ACCEPTED   (disprove)
-- author  : @marozols
-- created : 2026-11-21T01:04:20.126126+00:00
-- url     : https://prove2.me/submissions/6e61b77d-e308-43e0-9a7a-109906d88ae4

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

theorem solution : ¬ (∀ (E F : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (m : ℕ) (hm : 1 ≤ m) (A B : E →L[ℂ] F),
    sInf {r : ℝ | ∃ R : E →L[ℂ] F,
        FiniteDimensional ℂ (LinearMap.range (R : E →ₗ[ℂ] F)) ∧
        Module.finrank ℂ (LinearMap.range (R : E →ₗ[ℂ] F)) < m ∧ r = ‖(A + B) - R‖} ≤
      sInf {r : ℝ | ∃ R : E →L[ℂ] F,
        FiniteDimensional ℂ (LinearMap.range (R : E →ₗ[ℂ] F)) ∧
        Module.finrank ℂ (LinearMap.range (R : E →ₗ[ℂ] F)) < m ∧ r = ‖A - R‖} +
      sInf {r : ℝ | ∃ R : E →L[ℂ] F,
        FiniteDimensional ℂ (LinearMap.range (R : E →ₗ[ℂ] F)) ∧
        Module.finrank ℂ (LinearMap.range (R : E →ₗ[ℂ] F)) < m ∧ r = ‖B - R‖}) := by
  intro h
  -- the standard orthonormal basis of `ℂ²`
  obtain ⟨e, he⟩ : ∃ e : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)),
      ∀ i j, inner ℂ (e i) (e j) = if i = j then (1 : ℂ) else 0 :=
    ⟨EuclideanSpace.basisFun (Fin 2) ℂ,
      orthonormal_iff_ite.1 (EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal⟩
  -- the two coordinate projections
  have R1 : ∀ x : EuclideanSpace ℂ (Fin 2),
      ∃ S : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
        ∀ u, S u = inner ℂ x u • x :=
    fun x => ⟨(innerSL ℂ x).smulRight x, fun u => rfl⟩
  obtain ⟨A, hAa⟩ := R1 (e 0)
  obtain ⟨B, hBa⟩ := R1 (e 1)
  have hAB : A + B = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)) := by
    ext1 u
    rw [ContinuousLinearMap.add_apply, hAa, hBa, ContinuousLinearMap.id_apply]
    have h1 := e.sum_repr' u
    rw [Fin.sum_univ_two] at h1
    exact h1
  -- rank-one operators have range of dimension `< 2`
  have hrank : ∀ (x : EuclideanSpace ℂ (Fin 2))
      (S : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)),
      (∀ u, S u = inner ℂ x u • x) →
      Module.finrank ℂ (LinearMap.range
        (S : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))) < 2 := by
    intro x S hS
    have hle : LinearMap.range (S : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2)) ≤
        Submodule.span ℂ {x} := by
      rintro _ ⟨u, rfl⟩
      change S u ∈ Submodule.span ℂ {x}
      rw [hS]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
    have h1 := Submodule.finrank_mono hle
    have h2 : Module.finrank ℂ (Submodule.span ℂ ({x} : Set (EuclideanSpace ℂ (Fin 2)))) ≤ 1 :=
      (finrank_span_le_card ({x} : Set (EuclideanSpace ℂ (Fin 2)))).trans (by simp)
    omega
  -- lower bounds for the sets of approximation errors
  have hbdd : ∀ T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      BddBelow {r : ℝ | ∃ R : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
        FiniteDimensional ℂ (LinearMap.range
          (R : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))) ∧
        Module.finrank ℂ (LinearMap.range
          (R : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))) < 2 ∧
        r = ‖T - R‖} := by
    intro T
    refine ⟨0, ?_⟩
    rintro r ⟨R, -, -, rfl⟩
    exact norm_nonneg _
  -- `σ₂(A) ≤ 0` and `σ₂(B) ≤ 0`
  have hσA := csInf_le (hbdd A) (a := 0) ⟨A, inferInstance, hrank (e 0) A hAa, by simp⟩
  have hσB := csInf_le (hbdd B) (a := 0) ⟨B, inferInstance, hrank (e 1) B hBa, by simp⟩
  -- `σ₂(Id) ≥ 1`
  have hσI : (1 : ℝ) ≤ sInf {r : ℝ | ∃ R : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      FiniteDimensional ℂ (LinearMap.range
        (R : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))) ∧
      Module.finrank ℂ (LinearMap.range
        (R : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))) < 2 ∧
      r = ‖(A + B) - R‖} := by
    refine le_csInf ⟨_, 0, inferInstance, (by
      rw [ContinuousLinearMap.coe_zero, LinearMap.range_zero, finrank_bot]
      norm_num), rfl⟩ ?_
    rintro r ⟨R, -, hR, rfl⟩
    -- the kernel of `R` is nontrivial
    have h1 := LinearMap.finrank_range_add_finrank_ker
      (R : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))
    rw [finrank_euclideanSpace_fin] at h1
    have h2 : 0 < Module.finrank ℂ (LinearMap.ker
        (R : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))) := by omega
    obtain ⟨⟨u, hu⟩, hne⟩ := Module.finrank_pos_iff_exists_ne_zero.1 h2
    have hu0 : u ≠ 0 := fun h0 => hne (Subtype.ext h0)
    have hRu : R u = 0 := hu
    have h3 : ((A + B) - R) u = u := by
      rw [hAB, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, hRu, sub_zero]
    have h4 := ((A + B) - R).le_opNorm u
    rw [h3] at h4
    have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu0
    nlinarith
  have hfinal := h (EuclideanSpace ℂ (Fin 2)) (EuclideanSpace ℂ (Fin 2)) 2 (by norm_num) A B
  linarith
