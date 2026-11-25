-- Prove2me | solution 1 for GlobalTheory.T.lattice_multiple_mem_sublattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:23:32.536877+00:00
-- url     : https://prove2.me/submissions/0db03741-d767-45f7-a374-72bdf71518ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeMultipleMemSublattice
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeMultipleMemSublatticeStatement
import Theorems.Thm_GlobalTheory_sublattice_of_full_rank_quotient_torsion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (Λ Λ₂ M : Submodule ℤ (Fin n → ℂ)), DiscreteTopology Λ → DiscreteTopology Λ₂ → Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ → Submodule.span ℝ (Λ₂ : Set (Fin n → ℂ)) = ⊤ → M ≤ Λ → Module.rank ℤ Λ₂ ≤ Module.rank ℤ M → ∀ w ∈ Λ, ∃ k : ℤ, k ≠ 0 ∧ k • w ∈ M := by
  first | exact @GlobalTheory.sublattice_of_full_rank_quotient_torsion | exact GlobalTheory.sublattice_of_full_rank_quotient_torsion | (intros; apply GlobalTheory.sublattice_of_full_rank_quotient_torsion <;> assumption)
end _root_.GlobalTheory.T
