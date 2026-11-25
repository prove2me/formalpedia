-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.idx_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:46:04.54975+00:00
-- url     : https://prove2.me/submissions/2a78688c-d80a-4ee8-9385-82007732b54f

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
variable {c : Coeff l} {𝔓 : Ideal (𝓞 E)} {p : ℕ}
namespace GlobalTheory.HeckeFrCompare
theorem _root_.solution (h : IsSplitOff l 𝔓 p) (i : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
    (y : FrPt Xo c Ω) : hkKer (Xo := Xo) 𝔓 p i Ω y = HeckeIdx Xo c h i Ω y := rfl
end GlobalTheory.HeckeFrCompare
