-- Prove2me | solution 1 for GlobalTheory.T.lattice_translates_cutoff_summable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:22:46.749152+00:00
-- url     : https://prove2.me/submissions/316effa2-c4b4-47ea-9c7f-0d9527087459

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeTranslatesCutoffSummable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeTranslatesCutoffSummableStatement
import Theorems.Thm_GlobalTheory_SchwartzTranslateSum_summable_seminorm_mul_translate


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
    ∀ u : Λ → SchwartzMap V ℂ, (∀ (l : Λ) (x : V), u l x = h (x + l) * f x) →
    ∀ k n : ℕ, Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  first | exact @GlobalTheory.SchwartzTranslateSum.summable_seminorm_mul_translate | exact GlobalTheory.SchwartzTranslateSum.summable_seminorm_mul_translate | (intros; apply GlobalTheory.SchwartzTranslateSum.summable_seminorm_mul_translate <;> assumption)
end _root_.GlobalTheory.T
