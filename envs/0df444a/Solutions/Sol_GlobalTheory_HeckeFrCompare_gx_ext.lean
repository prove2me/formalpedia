-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.gx_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:48:08.118872+00:00
-- url     : https://prove2.me/submissions/39022f14-6e12-4b2e-a77b-3ce59561c52e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff

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
theorem _root_.solution {x : Sp Ω ⟶ Xo.X} {T : Scheme.{0}} {f g : T ⟶ Gx x}
    (h₁ : f ≫ (fst (Over.mk x) Xo.univ.t.G).left = g ≫ (fst (Over.mk x) Xo.univ.t.G).left)
    (h₂ : f ≫ (snd (Over.mk x) Xo.univ.t.G).left = g ≫ (snd (Over.mk x) Xo.univ.t.G).left) : f = g :=
  pullback.hom_ext h₁ h₂
end GlobalTheory.HeckeFrCompare
