-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames.isEigenBasisAt_frPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:57:58.826875+00:00
-- url     : https://prove2.me/submissions/a8125d84-5d88-4b2a-bdf9-61d089628a6d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_EigenLatticeFrames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames
theorem _root_.solution {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (τ : E →+* ℂ) : IsEigenBasisAt Xo c y.x τ (y.u τ) :=
  ⟨y.tan τ, y.eig τ, y.basis τ⟩
end GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames
