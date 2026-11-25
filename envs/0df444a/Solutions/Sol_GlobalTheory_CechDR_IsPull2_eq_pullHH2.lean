-- Prove2me | solution 1 for GlobalTheory.CechDR.IsPull2.eq_pullHH2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:10:49.248879+00:00
-- url     : https://prove2.me/submissions/d705da70-871e-44dc-9805-1bd593f94bb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaDescentInjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaDescentRestrictionEquivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwoCocycleCoboundaryOfBasisFunctorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneFormsTwoCocycleCoboundaryOfRestrictStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOneFormsCocycleRestrictSubCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HigherFormsOneCocycleCoboundaryOfRestrictStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompatibleHigherFormsExtendAlongFunctorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasLocalisationAtElementsTrivSqZeroExtFormsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaFirstOrderCocycleLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaSecondOrderCocycleLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairResBijectiveTwo
import Theorems.Thm_GlobalTheory_CechDR_existsUnique_isPull2
import Theorems.Thm_GlobalTheory_CechDR_isPull2_pullHH2

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
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open FormExt FormExtJ
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ)
namespace GlobalTheory.CechDR
namespace IsPull2
theorem _root_.solution {c : HH2 s} {c' : HH2 s'} (e : IsPull2 h c c') : c' = pullHH2 h c :=
  (existsUnique_isPull2 h c).unique e (isPull2_pullHH2 h c)
end IsPull2
end GlobalTheory.CechDR
