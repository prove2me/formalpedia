-- Prove2me | solution 1 for GlobalTheory.UnipChange.continuous_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:49:48.33682+00:00
-- url     : https://prove2.me/submissions/20cb01bd-4752-47da-8c3c-93f90f8892ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitriangularMapInduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped Pointwise
open GlobalTheory GlobalTheory.UnipChange
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointRadical
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]
  {r : ℕ} {b : Fin r → ℕ}
namespace GlobalTheory.UnipChange
theorem _root_.solution {ι : Type} [Fintype ι] (L : (ι → k) →ₗ[k] ι → k) : Continuous L := by
  classical
  have : (L : (ι → k) → ι → k) = (LinearMap.toMatrix' L).mulVec := by
    funext x
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rw [this]
  exact continuous_const.matrix_mulVec continuous_id
end GlobalTheory.UnipChange
