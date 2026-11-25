-- Prove2me | solution 1 for GlobalTheory.T.lattice_shifted_cutoff_summable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:23:34.904746+00:00
-- url     : https://prove2.me/submissions/4cc579ab-29d0-416b-8e2f-a59a13a9063e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeShiftedCutoffSummable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeShiftedCutoffSummableStatement
import Theorems.Thm_GlobalTheory_LatticeSchwartz_summable_seminorm_mul_comp_sub


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
theorem _root_.solution : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h f : SchwartzMap V ℂ), HasCompactSupport h →
    ∀ u : Λ → SchwartzMap V ℂ, (∀ (l : Λ) (x : V), u l x = h x * f (x - l)) →
    ∀ k n : ℕ, Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  first | exact @GlobalTheory.LatticeSchwartz.summable_seminorm_mul_comp_sub | exact GlobalTheory.LatticeSchwartz.summable_seminorm_mul_comp_sub | (intros; apply GlobalTheory.LatticeSchwartz.summable_seminorm_mul_comp_sub <;> assumption)
end _root_.GlobalTheory.T
