-- Prove2me | solution 1 for GroundTheory.Global.absNorm_eq_finprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:21:50.340001+00:00
-- url     : https://prove2.me/submissions/85ce0661-9e96-40bd-8ca4-7180e88ddc87

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleIdealMeasure
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_coe_finiteSingleUnits
import Theorems.Thm_GroundTheory_Global_finiteAdeleEval_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.coe_finiteSingleUnits
attribute [local simp] GroundTheory.Global.finiteAdeleEval_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Measure WithZero
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
namespace GroundTheory.Global
theorem _root_.solution :
    ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (Ideal.absNorm v.asIdeal : ℝ) ^ FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)).Finite := by
    refine (Filter.eventually_cofinite.1
      (FractionalIdeal.finite_factors (I : FractionalIdeal (𝓞 K)⁰ K))).subset fun v hv h ↦ hv ?_
    simp [h]
  have h := ((Rat.castHom ℝ : ℚ →* ℝ).comp
    (FractionalIdeal.absNorm : FractionalIdeal (𝓞 K)⁰ K →*₀ ℚ).toMonoidHom).map_finprod hfin
  rw [FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) I.ne_zero] at h
  refine h.trans (finprod_congr fun v ↦ ?_)
  simp [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
end GroundTheory.Global
