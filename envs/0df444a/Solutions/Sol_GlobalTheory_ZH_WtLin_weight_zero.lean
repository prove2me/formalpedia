-- Prove2me | solution 1 for GlobalTheory.ZH.WtLin.weight_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:17:57.151998+00:00
-- url     : https://prove2.me/submissions/9fdb653d-2981-4fc3-b38b-7964f92672a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffSymmSum
import Theorems.Thm_GlobalTheory_ZH_WtLin_coeff_symm_sum

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
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtLin
namespace GlobalTheory.ZH.WtLin
theorem _root_.solution {k : Type} [Field k] (Φ : FibPre k) (α : Φ.E.X) (l : Φ.N₀.ι) :
    Φ.D.weight (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α 0 = 0 := by
  have := coeff_symm_sum _ _ _ (Φ.D.coord (Φ.ch l) _ (Φ.aff l) (Φ.le l)) (J := Empty)
    Empty.elim Empty.elim α
  simpa [SplitExt.GtDatum.weight] using this
end GlobalTheory.ZH.WtLin
