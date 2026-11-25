-- Prove2me | solution 1 for GlobalTheory.GlobalModelGuards.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:45:44.695887+00:00
-- url     : https://prove2.me/submissions/67ea99b2-fc9a-4879-a3a9-bf5ced793abf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_ExistsGoodLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GlobalModelGuards
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.GlobalModelGuards
theorem _root_.solution {l : Level H} {Xo : Moduli D l} {c : Coeff l} (W : ValuationSubring ℂ)
    (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (b : 𝓞 c.F →+* c.V W)
    (hb : ∀ x, ((b x : c.V W) : c.F) = (x : c.F)) :
    ∃ a : Xo.XF c ⟶ pullback Y.s (spMap b), a ≫ pullback.fst _ _ = Y.j := by
  have hc : (c.V W).subtype.comp b = algebraMap (𝓞 c.F) c.F := RingHom.ext hb
  refine ⟨pullback.lift Y.j (pullback.snd _ _ ≫ spMap (c.V W).subtype) ?_, pullback.lift_fst _ _ _⟩
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over, Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
end GlobalTheory.GlobalModelGuards
