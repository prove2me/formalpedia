-- Prove2me | solution 1 for GlobalTheory.AbCoh.cupHyp_add_cupHyp_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:11:34.101886+00:00
-- url     : https://prove2.me/submissions/da308ce0-0d1f-441e-929a-9f9d52b07dd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechDeRhamHypercohomologyCupAnticomm
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_cupHyp_mk
import Theorems.Thm_GlobalTheory_CechDR_wedge_swap
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    ∀ a b : Hyp1 F, cupHyp F a b + cupHyp F b a = 0 := by
  intro R _ C _ F a b
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F a
  obtain ⟨b, rfl⟩ := Hyp1.mk_surjective F b
  rw [cupHyp_mk, cupHyp_mk, ← map_add]
  refine Hyp2.mk_eq_zero.2 ⟨(fun T T' φ ↦ -(a.1.1 T T' φ * b.1.1 T T' φ), 0), ?_⟩
  refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_
  · simp only [cechDeRhamTotalDifferentialOne_functionPart, Submodule.coe_add, Prod.fst_add, Pi.add_apply, coe_cupZZ, cupTot_apply,
      cechDeRhamTotalCocyclesOne.comp a, cechDeRhamTotalCocyclesOne.comp b, map_mul, map_neg]
    ring
  · simp only [dTot1_a, Submodule.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply, coe_cupZZ,
      cupTot_a, map_neg, Derivation.leibniz, Pi.zero_apply, map_zero]
    rw [cechDeRhamTotalCocyclesOne.conn a φ, cechDeRhamTotalCocyclesOne.conn b φ]
    module
  · simp only [dTot1_η, Submodule.coe_add, Prod.snd_add, Pi.add_apply, coe_cupZZ, cupTot_η,
      Pi.zero_apply, map_zero]
    rw [wedge_swap (a.1.2 T), neg_add_cancel]
end GlobalTheory.AbCoh
