-- Prove2me | solution 1 for OAI.TwoWayComplementation.deterministic_rate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:09:30.758365+00:00
-- url     : https://prove2.me/submissions/52fa1f70-792c-4752-bdac-f322d2b4c1e9

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/DeterministicBound.lean:L28-L51
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.deterministic_rate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations
import Definitions.Def_OAI_Combinatorics_Automata_RankLoss
import Definitions.Def_OAI_Combinatorics_Automata_Recognition
import Definitions.Def_OAI_Combinatorics_Automata_PathNFA
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Network__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Chain__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Tape__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Main
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationBridge
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_TransitionBridge

-- ---- from OAI.Combinatorics.TwoWayAutomata.DeterministicBound ----
namespace OAI

namespace TwoWayComplementation

namespace CompanionBridge

end CompanionBridge

/-- Arithmetic specialization for the relation alphabet on n - 2 vertices. -/
theorem deterministic_rate (n s : ℕ) (hn : 131 ≤ n)
    (hb : 2 ^ ((n - 4) / 31) ≤ 4 * (s + 1) ^ 2) :
    (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) ≤ (s : ℝ) := by
  let k := (n - 4) / 127
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hrate : 4 * k ≤ (n - 4) / 31 := by dsimp [k]; omega
  have hbR : (2 : ℝ) ^ ((n - 4) / 31) ≤ 4 * ((s : ℝ) + 1) ^ 2 := by
    exact_mod_cast hb
  have hp : (2 : ℝ) ^ (4 * k) ≤ 4 * ((s : ℝ) + 1) ^ 2 :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hrate).trans hbR
  have he : (2 : ℝ) ^ (4 * k) = ((2 : ℝ) ^ k) ^ 4 := by
    rw [← pow_mul, Nat.mul_comm]
  rw [he] at hp
  have ht : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk)
  have hsq : (((2 : ℝ) ^ k) ^ 2) ^ 2 ≤ (2 * ((s : ℝ) + 1)) ^ 2 := by
    nlinarith only [hp]
  have hs : ((2 : ℝ) ^ k) ^ 2 ≤ 2 * ((s : ℝ) + 1) :=
    (sq_le_sq₀ (sq_nonneg _) (by positivity)).mp hsq
  change (1 / 2 : ℝ) * 2 ^ k ≤ (s : ℝ)
  nlinarith [mul_nonneg (sub_nonneg.mpr ht)
    (show 0 ≤ (2 : ℝ) ^ k + 1 by positivity)]

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.deterministic_rate := @_root_.OAI.TwoWayComplementation.deterministic_rate
