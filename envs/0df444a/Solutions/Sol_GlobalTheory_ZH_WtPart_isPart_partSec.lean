-- Prove2me | solution 1 for GlobalTheory.ZH.WtPart.isPart_partSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:28:17.219064+00:00
-- url     : https://prove2.me/submissions/c280f66f-aac0-4fb4-a737-1a72dde07183

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Theorems.Thm_GlobalTheory_ZH_WtPart_wt_partSec

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
theorem _root_.solution (φ : (Φ.H d).Sec) (α : Φ.E.X) : Φ.IsPart α φ (partSec Φ φ α) := by
  refine ⟨?_, fun l => by rw [wt_partSec, if_pos rfl]⟩
  rintro β ⟨l, hl⟩
  by_contra h
  exact hl (by rw [wt_partSec, if_neg (fun e => h e.symm)])
end GlobalTheory.ZH.WtPart
