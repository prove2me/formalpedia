-- Prove2me | solution 1 for GlobalTheory.TensorLat.exists_coe_eq_span_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:51.378848+00:00
-- url     : https://prove2.me/submissions/ef418c04-55d7-4d5e-bb8f-c9c81ab74951

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Theorems.Thm_GlobalTheory_TensorLat_exists_coe_eq_span_det_of_intVec_le
import Theorems.Thm_GlobalTheory_exists_smul_mem_of_mem_span_fraction
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_key
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_mem_intVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero



set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
open scoped nonZeroDivisors
open ReciprocityTheory.MultiplicativeHeights.SemiDegIdx ReciprocityTheory.PGsh
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
namespace GlobalTheory.TensorLat
theorem _root_.solution {Λ Λ' : Submodule (𝓞 K) (Fin n → K)} (hle : Λ ≤ Λ') (hfg : Λ'.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ J J' : FractionalIdeal (𝓞 K)⁰ K, J ≠ 0 ∧ J' ≠ 0 ∧
      (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ) ∧ d = (Matrix.of v).det} ∧
      (J' : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ') ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J =
        (Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup : ℚ) * FractionalIdeal.absNorm J' := by
  classical
  choose d hd0 hd using fun k : Fin n => exists_smul_mem_of_mem_span_fraction (K := K) Λ
    (Pi.single k (1 : K)) (hsp ▸ Submodule.mem_top)
  set δ : K := algebraMap (𝓞 K) K (∏ k, d k) with hδ
  have hδ0 : δ ≠ 0 := by simpa [hδ, Finset.prod_ne_zero_iff] using hd0
  let μ : (Fin n → K) →ₗ[𝓞 K] (Fin n → K) := (LinearMap.lsmul K _ δ).restrictScalars (𝓞 K)
  have hμ : ∀ x, μ x = δ • x := fun _ => rfl
  have hinj : Function.Injective μ := smul_right_injective _ hδ0
  have hsurj : Function.Surjective μ := fun x => ⟨δ⁻¹ • x, by rw [hμ, smul_inv_smul₀ hδ0]⟩
  have hstd : intVec K n ≤ Λ.comap μ := by
    intro x hx
    choose c hc using fun k => Submodule.mem_one.1 (mem_intVec.1 hx k)
    have : x = ∑ k, c k • (Pi.single k (1 : K) : Fin n → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hc]
    rw [this]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    rw [Submodule.mem_comap, hμ, hδ, algebraMap_smul,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ k), mul_smul]
    exact Λ.smul_mem _ (hd k)
  have key : ∀ Y : Submodule (𝓞 K) (Fin n → K), Λ ≤ Y → Y.FG →
      ∃ J : FractionalIdeal (𝓞 K)⁰ K, (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Y) ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J * ((intVec K n).toAddSubgroup.relIndex
        (Y.comap μ).toAddSubgroup : ℚ) = |Algebra.norm ℚ (δ ^ n)| := by
    intro Y hY hYfg
    obtain ⟨J, hJ, hN⟩ := exists_coe_eq_span_det_of_intVec_le (Y.comap μ)
      (Submodule.fg_of_fg_map_injective μ hinj
        (by rwa [Submodule.map_comap_eq_of_surjective hsurj]))
      (hstd.trans (Submodule.comap_mono hY))
    refine ⟨FractionalIdeal.spanSingleton _ (δ ^ n) * J, ?_, ?_⟩
    · rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton, hJ, Submodule.span_mul_span,
        Set.singleton_mul]
      congr 1
      ext x
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        refine ⟨δ • v, hv, ?_⟩
        change _ = (δ • Matrix.of v).det
        rw [Matrix.det_smul, Fintype.card_fin]
      · rintro ⟨v, hv, rfl⟩
        refine ⟨_, ⟨δ⁻¹ • v, fun i => ?_, rfl⟩, ?_⟩
        · rw [Submodule.mem_comap, hμ, Pi.smul_apply, smul_inv_smul₀ hδ0]
          exact hv i
        · change _ * (δ⁻¹ • Matrix.of v).det = _
          rw [Matrix.det_smul, Fintype.card_fin, inv_pow, mul_inv_cancel_left₀ (pow_ne_zero _ hδ0)]
    · rw [map_mul, mul_assoc, hN, mul_one, FractionalIdeal.absNorm_span_singleton]
  obtain ⟨J, hJ, hN⟩ := key Λ le_rfl (hfg.of_le hle)
  obtain ⟨J', hJ', hN'⟩ := key Λ' hle hfg
  have hn0 : |Algebra.norm ℚ (δ ^ n)| ≠ 0 :=
    abs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 (pow_ne_zero _ hδ0))
  have hidx : (Λ.comap μ).toAddSubgroup.relIndex (Λ'.comap μ).toAddSubgroup =
      Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup := by
    change (Λ.toAddSubgroup.comap μ.toAddMonoidHom).relIndex
      (Λ'.toAddSubgroup.comap μ.toAddMonoidHom) = _
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hsurj]
  have htower := AddSubgroup.relIndex_mul_relIndex (intVec K n).toAddSubgroup
    (Λ.comap μ).toAddSubgroup (Λ'.comap μ).toAddSubgroup hstd (Submodule.comap_mono hle)
  refine ⟨J, J', ?_, ?_, hJ, hJ', ?_⟩
  · rintro rfl
    rw [map_zero, zero_mul] at hN
    exact hn0 hN.symm
  · rintro rfl
    rw [map_zero, zero_mul] at hN'
    exact hn0 hN'.symm
  · rw [← htower, hidx, Nat.cast_mul, ← hN] at hN'
    refine mul_right_cancel₀ (right_ne_zero_of_mul (hN ▸ hn0)) ?_
    linear_combination -hN'
end GlobalTheory.TensorLat
