-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSHighestOfKType.hwOfType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:19.286319+00:00
-- url     : https://prove2.me/submissions/c9a009f8-9f5a-4240-8706-7cab5bcd6895

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NotCdomAddRoot
import Theorems.Thm_GlobalTheory_CompanionTheory_DSHighestOfKType_not_cdom_add_root
import Theorems.Thm_GlobalTheory_CompanionTheory_DSHighestOfKType_isWeight_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSHighestOfKType
open Formalism.REAL (GlRel KHighest IsWeight)
open PI.UpqRep (CDom root)
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSHighestOfKType
theorem _root_.solution : CompanionTheory.D.DSIC.StabLink → CompanionTheory.D.DSIC.WtLink → CompanionTheory.D.DSIC.HWofType := by
  intro hS hW n ε H _ _ σ S E hσ hm μ T hT hTS
  obtain ⟨hfin, hst, -, ⟨v, hvT, hv0, hvw⟩, hdom⟩ := hT
  have hmap : (T.comap S.subtype).map S.subtype = T := by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hTS
  have hfinU : FiniteDimensional ℂ (T.comap S.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hTS).symm.finiteDimensional
  have hU := (hS n ε H σ S E hσ hm _ hfinU).2 (by rw [hmap]; exact hst)
  have hw : IsWeight E μ (⟨v, hTS hvT⟩ : S) := (hW n ε H σ S E hσ hm μ _).2 hvw
  refine ⟨⟨v, hTS hvT⟩, fun h => hv0 (congrArg Subtype.val h), hvT, hw, fun a b hab hε => ?_⟩
  by_contra hne
  have hmem := hU a b hε ⟨v, hTS hvT⟩ hvT
  have hw' := (hW n ε H σ S E hσ hm _ _).1 (isWeight_apply hm.gl hw a b)
  exact not_cdom_add_root ε μ hab (hdom _ _ hmem (fun h => hne (Subtype.ext h)) hw')
end GlobalTheory.CompanionTheory.DSHighestOfKType
