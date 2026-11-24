-- Prove2me | solution 1 for GlobalTheory.T.transpose_invariant_of_conj_invariant_distribution_GL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:04.908089+00:00
-- url     : https://prove2.me/submissions/7f235fa1-9776-4696-b297-ceb435ee69d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TransposeInvariantOfConjInvariantDistributionGL
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TransposeInvariantOfConjInvariantDistributionGLStatement
import Theorems.Thm_GlobalTheory_GelfandKazhdan_transpose_invariant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (T : SB (GL n k) →ₗ[ℂ] ℂ), (∀ (g : GL n k) (φ ψ : SB (GL n k)), (∀ x, ψ.1 x = φ.1 (g * x * g⁻¹)) → T ψ = T φ) → ∀ φ ψ : SB (GL n k), (∀ x y : GL n k, y.val = x.val.transpose → ψ.1 x = φ.1 y) → T ψ = T φ := by
  first | exact @GlobalTheory.GelfandKazhdan.transpose_invariant | exact GlobalTheory.GelfandKazhdan.transpose_invariant | (intros; apply GlobalTheory.GelfandKazhdan.transpose_invariant <;> assumption)
end _root_.GlobalTheory.T
