-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.toFib_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:05:54.446039+00:00
-- url     : https://prove2.me/submissions/03e7c6ce-e9b2-482e-b786-e10d4d014452

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
import Theorems.Thm_GlobalTheory_HeckeFrCompare_gx_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeckeFrCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {Ω : Type} [CommRing Ω]
namespace GlobalTheory.HeckeFrCompare
theorem _root_.solution (x : Sp Ω ⟶ Xo.X) {T T' : Scheme.{0}} {t : T ⟶ Sp Ω} {t' : T' ⟶ Sp Ω} (q : T' ⟶ T)
    (hq : q ≫ t = t') (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    toFib x t' (res x q hq ≫ a) = q ≫ toFib x t a := by
  refine gx_ext ?_ ?_
  · rw [toFib_fst, Category.assoc, toFib_fst, hq]
  · rw [toFib_snd, Category.assoc, toFib_snd]; rfl
end GlobalTheory.HeckeFrCompare
