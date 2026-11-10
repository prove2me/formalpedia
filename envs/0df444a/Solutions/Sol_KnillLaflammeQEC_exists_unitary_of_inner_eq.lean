-- Prove2me | solution 1 for KnillLaflammeQEC.exists_unitary_of_inner_eq
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T05:40:17.337729+00:00
-- url     : https://prove2.me/submissions/e700e93c-5f64-482d-916e-a546bb5b36ab

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

theorem solution {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (v w : β → EuclideanSpace ℂ ι) (h : ∀ a b, inner ℂ (v a) (v b) = inner ℂ (w a) (w b)) :
    ∃ U ∈ Matrix.unitaryGroup ι ℂ, ∀ a, QAlgorithms.act U (v a) = w a := by
  obtain ⟨lv, hlv⟩ : ∃ lv : (β →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι, lv = Finsupp.linearCombination ℂ v :=
    ⟨_, rfl⟩
  obtain ⟨lw, hlw⟩ : ∃ lw : (β →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι, lw = Finsupp.linearCombination ℂ w :=
    ⟨_, rfl⟩
  have hinner : ∀ f g : β →₀ ℂ, inner ℂ (lv f) (lv g) = inner ℂ (lw f) (lw g) := by
    intro f g
    rw [hlv, hlw]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, h]
  have hker : LinearMap.ker lv ≤ LinearMap.ker lw := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    have := hinner f f
    rw [hf, inner_zero_left] at this
    exact inner_self_eq_zero.mp this.symm
  let T : LinearMap.range lv →ₗ[ℂ] EuclideanSpace ℂ ι :=
    (LinearMap.ker lv).liftQ lw hker ∘ₗ lv.quotKerEquivRange.symm.toLinearMap
  have hT : ∀ f, T ⟨lv f, LinearMap.mem_range_self lv f⟩ = lw f := by
    intro f
    simp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hTnorm : ∀ x, ‖T x‖ = ‖x‖ := by
    rintro ⟨_, f, rfl⟩
    rw [hT, Submodule.coe_norm]
    have h1 := hinner f f
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
    have h2 : ‖lv f‖ ^ 2 = ‖lw f‖ ^ 2 := by exact_mod_cast h1
    exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2).symm
  let L : LinearMap.range lv →ₗᵢ[ℂ] EuclideanSpace ℂ ι := { toLinearMap := T, norm_map' := hTnorm }
  let Lx := L.extend
  let e := Lx.toLinearIsometryEquiv rfl
  let u := Unitary.linearIsometryEquiv.symm e
  refine ⟨(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).symm (u : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι), ?_,
    fun a => ?_⟩
  · exact Unitary.map_mem (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).symm u.2
  · have hact : QAlgorithms.act ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).symm
          (u : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) (v a)
        = Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).symm
          (u : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) (v a) := rfl
    rw [hact, StarAlgEquiv.apply_symm_apply]
    change Lx (v a) = w a
    have hsingle : lv (Finsupp.single a 1) = v a := by
      rw [hlv, Finsupp.linearCombination_single, one_smul]
    have hva : v a ∈ LinearMap.range lv := ⟨Finsupp.single a 1, hsingle⟩
    have hx : Lx (v a) = L ⟨v a, hva⟩ := L.extend_apply ⟨v a, hva⟩
    rw [hx]
    have hsub : (⟨v a, hva⟩ : LinearMap.range lv)
        = ⟨lv (Finsupp.single a 1), LinearMap.mem_range_self lv _⟩ := Subtype.ext hsingle.symm
    change T ⟨v a, hva⟩ = w a
    rw [hsub, hT, hlw, Finsupp.linearCombination_single, one_smul]
