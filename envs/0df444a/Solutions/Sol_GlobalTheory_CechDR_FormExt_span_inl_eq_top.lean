-- Prove2me | solution 1 for GlobalTheory.CechDR.FormExt.span_inl_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:38:58.506271+00:00
-- url     : https://prove2.me/submissions/45ad16a3-eecc-4c9e-b447-f79cfe8cb233

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueCommaOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasLocOAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData

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
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.FormExt
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
namespace GlobalTheory.CechDR.FormExt
theorem _root_.solution {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    {S : C} {n : ℕ} {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ (TrivSqZeroExt.inl (b i) : (omExt F).obj S)) = ⊤ := by
  have := congrArg (Ideal.map (TrivSqZeroExt.inlHom (F.obj S) Ω[F.obj S⁄R])) hb
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  exact this
end GlobalTheory.CechDR.FormExt
