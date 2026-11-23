-- Prove2me | solution 1 for GlobalTheory.ZH.WtPart.sec_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:38.699996+00:00
-- url     : https://prove2.me/submissions/69262587-2831-46a5-8a90-70c16de4176c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Theorems.Thm_GlobalTheory_ZH_WtPart_cf_ext

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
namespace GlobalTheory.ZH.WtPart
theorem _root_.solution (φ ψ : (Φ.H d).Sec) (h : ∀ α l, Φ.wt φ α l = Φ.wt ψ α l) : φ = ψ := by
  have : φ.f = ψ.f := funext fun l =>
    cf_ext (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) fun α => h α l
  cases φ
  cases ψ
  congr
end GlobalTheory.ZH.WtPart
