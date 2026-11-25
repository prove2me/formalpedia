-- Prove2me | solution 1 for GlobalTheory.CechDR.existsUnique_isPullO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:13:40.073839+00:00
-- url     : https://prove2.me/submissions/ccb8fd58-783a-46ec-9147-824a2c87074b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictPull1InjectiveOfSepGlue
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_Pull1RestrictSurjectiveOfComma
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompatFamilyExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocycleOneFormsCoboundaryOfRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictGlob1Bijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullHyp1RestrictInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullHyp1RestrictSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepOfFactoringCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueCommaOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleCoboundaryCommaLocalBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasLocOAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FormPowSmulEqZeroOfResBasicOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwoFormExistsPowSmulEqZeroOfIsLocalization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairCoverAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPairBelowTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open CatCoh
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ)
namespace GlobalTheory.CechDR
theorem _root_.solution (c : HO1 s) : ∃! c', IsPullO h c c' := by
  obtain ⟨c', hc, hu⟩ := (pairRes_bijective φ s').1.existsUnique ((pairPull h).pull1 c)
  exact ⟨c', hc.symm, fun y hy ↦ hu y hy.symm⟩
end GlobalTheory.CechDR
