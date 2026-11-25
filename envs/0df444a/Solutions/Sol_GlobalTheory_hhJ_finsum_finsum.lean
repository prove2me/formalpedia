-- Prove2me | solution 1 for GlobalTheory.hhJ_finsum_finsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:34:20.844486+00:00
-- url     : https://prove2.me/submissions/3d3d3128-9712-487e-8ea7-3be5276d2eb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumNormHhJSelfLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
variable {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
namespace GlobalTheory
theorem _root_.solution {ι : Type} (ε : Fin n → Bool) (y : ι → Fin n → M) (In : Finset ι) :
    hhJ ε (∑ s ∈ In, y s) (∑ s ∈ In, y s) = ∑ s ∈ In, ∑ t ∈ In, hhJ ε (y s) (y t) := by
  unfold hhJ
  simp only [Finset.sum_apply, sum_inner, inner_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
end GlobalTheory
