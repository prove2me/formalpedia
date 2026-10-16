-- Prove2me | solution 1 for OAI.TreeEdit.TorusTree.binaryWidth_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:21:28.933408+00:00
-- url     : https://prove2.me/submissions/9674d82f-907b-4e35-aeb6-f06aba74db09

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CircleParameters.lean:L26-L45
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.TorusTree.binaryWidth_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
import Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleObstruction
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleParameters

-- ---- from OAI.Combinatorics.TreeEdit.CircleParameters ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter

lemma binaryWidth_le {k : ℕ} (hk : 2 ≤ k) : binaryWidth k ≤ 40*k^2 := by
  have hkpow : k ≤ 2^k := (Nat.lt_two_pow_self).le
  have hm : branching k ≤ 2^(4+3*k) := by
    calc
      _ = 16*k^3 := by dsimp [branching]; ring
      _ ≤ 2^4*(2^k)^3 := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left hkpow 3)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  have hr : resolution k ≤ 2^(8*k^2) := by
    calc
      _ ≤ (2^k)^(8*k) := Nat.pow_le_pow_left hkpow _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have ha : alphabetSize k ≤ 2^(13*k^2) := by
    calc
      _ ≤ (2^(4+3*k))^k * 2^(8*k^2) := Nat.mul_le_mul (Nat.pow_le_pow_left hm k) hr
      _ = 2^((4+3*k)*k+8*k^2) := by rw [← pow_mul, ← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hc := Nat.clog_le_of_le_pow ha
  change Nat.clog 2 (alphabetSize k) ≤ 13*k^2 at hc
  dsimp only [binaryWidth]
  nlinarith

end TreeEdit.TorusTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter


theorem solution : type_of% @_root_.OAI.TreeEdit.TorusTree.binaryWidth_le := @_root_.OAI.TreeEdit.TorusTree.binaryWidth_le
