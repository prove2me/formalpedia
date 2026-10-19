-- Prove2me | solution 1 for OAI.FiniteCircle.exists_separating_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:56:38.31185+00:00
-- url     : https://prove2.me/submissions/9ec50745-e7b9-42a0-b89a-b64c46c26dc4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Separation.lean:L85-L105
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.exists_separating_scale. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Partitions
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Histograms
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Separation

-- ---- from OAI.Combinatorics.FiniteCircle.Separation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem exists_separating_scale {m q : ℕ} (hq : 0 < q) (hqm : q ≤ m) :
    ∃ k : Fin (Nat.log 2 m + 1), 1 ≤ 2^k.val ∧ 2^k.val ≤ m ∧
      q ≤ 4 * 2^k.val ∧ 2 * 2^k.val ≤ q+1 := by
  let n := (q+1)/2
  have hn : 0 < n := by dsimp [n]; omega
  have hnm : n ≤ m := by dsimp [n]; omega
  let k := Nat.log 2 n
  have hk : k ≤ Nat.log 2 m := Nat.log_mono_right hnm
  have hpow : 2^k ≤ n := Nat.pow_le_of_le_log hn.ne' le_rfl
  have hlt : n < 2^(k+1) := Nat.lt_pow_succ_log_self (by norm_num) n
  refine ⟨⟨k, by omega⟩, ?_, hpow.trans hnm, ?_, ?_⟩
  · change 1 ≤ 2^k
    have hp : 0 < 2^k := pow_pos (by norm_num) _
    omega
  · change q ≤ 4 * 2^k
    simp only [pow_succ] at hlt
    dsimp [n] at *
    omega
  · change 2 * 2^k ≤ q+1
    dsimp [n] at hpow
    omega

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical


theorem solution : type_of% @_root_.OAI.FiniteCircle.exists_separating_scale := @_root_.OAI.FiniteCircle.exists_separating_scale
