-- Prove2me | solution 1 for GlobalTheory.ZH.WtPart.wt_partSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:17:49.316906+00:00
-- url     : https://prove2.me/submissions/6ce0eb87-a7ad-4549-ba61-c0c55de61a74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtPart
variable {k : Type} [Field k] (Φ : FibPre k) {d : ℕ}
open Classical
namespace GlobalTheory.ZH.WtPart
theorem _root_.solution (φ : (Φ.H d).Sec) (α β : Φ.E.X) (l : Φ.N₀.ι) :
    Φ.wt (partSec Φ φ α) β l = if α = β then Φ.wt φ α l else 0 :=
  cf_mono (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) β α _
end GlobalTheory.ZH.WtPart
