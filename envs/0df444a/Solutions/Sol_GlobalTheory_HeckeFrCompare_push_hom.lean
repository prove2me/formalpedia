-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.push_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:00:47.994009+00:00
-- url     : https://prove2.me/submissions/99532e4f-58d8-4f04-bba1-928763e41b87

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
theorem _root_.solution {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'}
    (hψ : ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    {T : Scheme.{0}} (t : T ⟶ Sp Ω) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    push ψ t a ≫ Xo.univ.t.G.hom = t ≫ x' := by
  simp only [push, Category.assoc]
  rw [snd_hom, reassoc_of% hψ, toFib_fst_assoc]
end GlobalTheory.HeckeFrCompare
