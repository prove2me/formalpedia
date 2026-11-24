-- Prove2me | solution 1 for GlobalTheory.SplitSpread.sum_eq_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:03.809185+00:00
-- url     : https://prove2.me/submissions/1ad56acb-a1d6-454d-855c-2b4560ecedf3

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
namespace GlobalTheory.SplitSpread
theorem _root_.solution {σ : Type} (s : σ →₀ ℕ) : (s.sum fun _ e => e) = s.degree := rfl
end GlobalTheory.SplitSpread
