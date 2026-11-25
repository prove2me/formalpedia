-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.sends_conj_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:05:55.842885+00:00
-- url     : https://prove2.me/submissions/a5b5f861-7d36-4838-8b13-59493b687853

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
import Theorems.Thm_GlobalTheory_HeckeFrCompare_conj_apply
import Theorems.Thm_GlobalTheory_HeckeFrCompare_fibPt_swap

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
namespace GlobalTheory.HeckeFrCompare
theorem _root_.solution {Ω : Type} [Field Ω] {x x' : Sp Ω ⟶ Xo.X}
    (ψ : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x')
    (a : Over.mk x ⟶ Xo.univ.t.G) (b : Over.mk x' ⟶ Xo.univ.t.G) :
    Sends (conj x x' ψ) a b ↔ fibPt _ a ≫ ψ = fibPt _ b := by
  rw [Sends, conj_apply, ← fibPt_swap, ← fibPt_swap, ← Category.assoc, ← Category.assoc, Iso.comp_inv_eq]
end GlobalTheory.HeckeFrCompare
