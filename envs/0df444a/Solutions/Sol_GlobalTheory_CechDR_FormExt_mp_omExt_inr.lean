-- Prove2me | solution 1 for GlobalTheory.CechDR.FormExt.mp_omExt_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:03:28.116383+00:00
-- url     : https://prove2.me/submissions/19a80598-bb37-43d5-bf9d-7447fe6c6d91

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
theorem _root_.solution {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    {T T' : C} (φ : T ⟶ T') (x : Ω[F.obj T⁄R]) :
    mp (omExt F) φ (TrivSqZeroExt.inr x : (omExt F).obj T) =
      (TrivSqZeroExt.inr (p1 F φ x) : (omExt F).obj T') :=
  TrivSqZeroExt.ext ((fst_extMap F φ _).trans (by rw [TrivSqZeroExt.fst_inr, map_zero]; rfl))
    ((snd_extMap F φ _).trans (by rw [TrivSqZeroExt.snd_inr]; rfl))
end GlobalTheory.CechDR.FormExt
