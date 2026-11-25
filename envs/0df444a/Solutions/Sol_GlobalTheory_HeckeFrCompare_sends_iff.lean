-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.sends_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:02:49.695877+00:00
-- url     : https://prove2.me/submissions/552695e7-0e0d-42f9-b4ce-01f4f813fe8b

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
theorem _root_.solution {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'}
    (hψ : ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (a : Over.mk x ⟶ Xo.univ.t.G) (b : Over.mk x' ⟶ Xo.univ.t.G) :
    Sends ψ a b ↔ (lift (𝟙 (Over.mk x)) a).left ≫ ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left = b.left := by
  refine ⟨fun h => ?_, fun h => gx_ext ?_ ?_⟩
  · rw [← Category.assoc, show _ ≫ ψ = _ from h, lift_l_snd]
  · rw [Category.assoc, hψ, lift_l_fst, lift_l_fst]; rfl
  · rw [Category.assoc, h, lift_l_snd]
end GlobalTheory.HeckeFrCompare
