-- Prove2me | solution 1 for GlobalTheory.T.gram_det_eq_sq_mul_gram_det_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:19:36.530006+00:00
-- url     : https://prove2.me/submissions/f4ac4988-9660-4444-91e2-64ce12b932cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GramDetIndexSublattice
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GramDetIndexSublatticeStatement
import Theorems.Thm_GlobalTheory_gram_det_index_sublattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (U V ι κ : Type) [AddCommGroup U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (φ : U →ₗ[ℤ] V) (u : ι → U) (v : κ → U), Fintype.card ι = Fintype.card κ → (∀ k, v k ∈ Submodule.span ℤ (Set.range u)) → ∃ m : ℕ, (Matrix.gram ℝ fun k => φ (v k)).det = (m : ℝ) ^ 2 * (Matrix.gram ℝ fun i => φ (u i)).det ∧ ∀ i, (m : ℤ) • u i ∈ Submodule.span ℤ (Set.range v) := by
  first | exact @GlobalTheory.gram_det_index_sublattice | exact GlobalTheory.gram_det_index_sublattice | (intros; apply GlobalTheory.gram_det_index_sublattice <;> assumption)
end _root_.GlobalTheory.T
