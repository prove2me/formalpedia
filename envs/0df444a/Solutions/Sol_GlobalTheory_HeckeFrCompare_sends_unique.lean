-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.sends_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:48:15.404426+00:00
-- url     : https://prove2.me/submissions/9b37d554-8329-435f-9af3-f9be4c31aeb9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



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
theorem _root_.solution {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'} {a : Over.mk x ⟶ Xo.univ.t.G}
    {b b' : Over.mk x' ⟶ Xo.univ.t.G} (h : Sends ψ a b) (h' : Sends ψ a b') : b = b' := by
  have e := congrArg (· ≫ (snd (Over.mk x') Xo.univ.t.G).left) (h.symm.trans h')
  simp only [lift_l_snd] at e
  exact Over.OverMorphism.ext e
end GlobalTheory.HeckeFrCompare
