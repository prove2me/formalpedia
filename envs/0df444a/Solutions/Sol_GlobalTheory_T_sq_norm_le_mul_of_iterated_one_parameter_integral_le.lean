-- Prove2me | solution 1 for GlobalTheory.T.sq_norm_le_mul_of_iterated_one_parameter_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:11.658809+00:00
-- url     : https://prove2.me/submissions/0e81665a-02f2-44b9-941c-4149c373ac05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SobolevIteratedOneParameterSubgroupsWords
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SobolevIteratedOneParameterSubgroups
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SobolevIteratedOneParameterSubgroupsWordsStatement
import Theorems.Thm_GlobalTheory_sobolev_iterated_one_parameter_subgroups_words


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : ℕ) (c : Fin N → ℝ → G) (s : ℝ), 0 < s → (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : List (Fin N) → G → ℂ), (∀ l, Continuous (F l)) → (∀ l i x, HasDerivAt (fun t => F l (x * c i t)) (F (i :: l) x) 0) → ∀ (y : G) (M : ℝ), (∀ l : List (Fin N), l.length ≤ N → ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖F l (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2 ≤ M) → ‖F [] y‖ ^ 2 ≤ C * M := by
  first | exact @GlobalTheory.sobolev_iterated_one_parameter_subgroups_words | exact GlobalTheory.sobolev_iterated_one_parameter_subgroups_words | (intros; apply GlobalTheory.sobolev_iterated_one_parameter_subgroups_words <;> assumption)
end _root_.GlobalTheory.T
