-- Prove2me | solution 1 for GlobalTheory.SplitSpread.totalDegree_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:04.529385+00:00
-- url     : https://prove2.me/submissions/fdf0fba2-ba7d-4bd1-ae34-aab7fe36f7cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoCommonZeroSpreadsConstructibleNbhdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplittingAbsenceSpreads

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.SplitSpread
open MvPolynomial
variable {σ : Type} [Finite σ] (A : Type) [CommRing A] (D : ℕ)
variable {A D}
namespace GlobalTheory.SplitSpread
theorem _root_.solution {k : Type} [CommRing k] (c : Mon σ D → k) :
    (∑ m : Mon σ D, monomial m.1 (c m)).totalDegree ≤ D := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m _ => ?_)
  exact (totalDegree_monomial_le _ _).trans m.2
end GlobalTheory.SplitSpread
