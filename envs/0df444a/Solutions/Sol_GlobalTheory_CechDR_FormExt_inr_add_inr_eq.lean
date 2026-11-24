-- Prove2me | solution 1 for GlobalTheory.CechDR.FormExt.inr_add_inr_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:03:25.488587+00:00
-- url     : https://prove2.me/submissions/d4ffd05f-9aa7-495d-bb13-c91911fd8e2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneFormsTwoCocycleCoboundaryOfRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.FormExt
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
namespace GlobalTheory.CechDR.FormExt
theorem _root_.solution {A M : Type} [AddCommGroup A] [AddCommGroup M] {x y z w : M}
    (h : x + y = z + w) :
    (TrivSqZeroExt.inr x : TrivSqZeroExt A M) + TrivSqZeroExt.inr y =
      TrivSqZeroExt.inr z + TrivSqZeroExt.inr w := by
  rw [← TrivSqZeroExt.inr_add, ← TrivSqZeroExt.inr_add, h]
end GlobalTheory.CechDR.FormExt
