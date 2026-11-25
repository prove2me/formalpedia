-- Prove2me | solution 1 for GroundTheory.Global.norm_eq_absNorm_zpow_neg_ord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:46:47.596531+00:00
-- url     : https://prove2.me/submissions/c83a26ba-1035-4afd-a5b7-b213c7bba8fe

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Theorems.Thm_GroundTheory_Global_coe_integerEquivAdicCompletionIntegers
import Theorems.Thm_GroundTheory_Global_normalizedAbv_apply
import Theorems.Thm_GroundTheory_Global_normalizedAbv_eq_zpow
import Theorems.Thm_GroundTheory_Global_normalizedAbv_of_irreducible
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_unitsEquivIntProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivIntProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


attribute [local simp] GroundTheory.Global.coe_integerEquivAdicCompletionIntegers

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global
theorem _root_.solution {x : v.adicCompletion K} (hx : x ≠ 0) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-ord x) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K]
  set p := unitsEquivIntProd hϖ (Units.mk0 x hx)
  have hxp : x = ((ϖ : v.adicCompletion K)) ^ (Multiplicative.toAdd p.1) *
      ((p.2 : 𝒪[v.adicCompletion K]) : v.adicCompletion K) := by
    rw [← coe_unitsOfIntProd hϖ, ← unitsEquivIntProd_symm_apply hϖ, MulEquiv.symm_apply_apply]
    rfl
  have hord : Multiplicative.toAdd p.1 = ord x := by
    rw [unitsEquivIntProd_fst hϖ]
    rfl
  have hϖ' : Irreducible (integerEquivAdicCompletionIntegers v ϖ) :=
    hϖ.map (integerEquivAdicCompletionIntegers v)
  have hnϖ : ‖(ϖ : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
    have h := normalizedAbv_of_irreducible v hϖ'
    rw [normalizedAbv_apply, coe_integerEquivAdicCompletionIntegers] at h
    exact h
  have hu : ‖((p.2 : 𝒪[v.adicCompletion K]) : v.adicCompletion K)‖ = 1 := by
    have hunit : IsUnit (integerEquivAdicCompletionIntegers v p.2) :=
      p.2.isUnit.map (integerEquivAdicCompletionIntegers v)
    have h1 := (adicCompletionIntegers.isUnit_iff_valued_eq_one).1 hunit
    have h0 : ((p.2 : 𝒪[v.adicCompletion K]) : v.adicCompletion K) ≠ 0 := by
      exact_mod_cast p.2.ne_zero
    rw [← normalizedAbv_apply, normalizedAbv_eq_zpow v h0]
    rw [coe_integerEquivAdicCompletionIntegers] at h1
    rw [h1]
    simp
  conv_lhs => rw [hxp]
  rw [norm_mul, norm_zpow, hnϖ, hu, mul_one, hord, inv_zpow']
end GroundTheory.Global
