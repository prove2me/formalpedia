-- Prove2me | solution 1 for OAI.TreeEdit.TorusTree.sampled_separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:19:21.842285+00:00
-- url     : https://prove2.me/submissions/169dd3c9-1394-46d9-b3f2-a1dba0f9e546

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CircleObstruction.lean:L214-L240
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.TorusTree.sampled_separation. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_TorusTree_fine_parameters
import Theorems.Thm_OAI_TreeEdit_TorusTree_separation

-- ---- from OAI.Combinatorics.TreeEdit.RandomCircle ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

lemma mapState_diagonal {A B : Type} [AddCommGroup A] [AddCommGroup B] {m : ℕ}
    (f : A →+ B) (h : ℕ) (a : A) :
    mapState (m := m) f h (diagonal (A := A) (m := m) h a) = diagonal (A := B) (m := m) h (f a) := by
  induction h with
  | zero => rfl
  | succ h ih => exact funext fun _ => ih

lemma point_grid {M P : ℕ} [NeZero M] (hP : 0 < P) (hPM : P ∣ M) :
    ZMod.toAddCircle (M / P : ZMod M) = point P := by
  rw [ZMod.toAddCircle_natCast]
  dsimp [point]
  congr 1
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hPr : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have he : ((M / P : ℕ) : ℝ) * P = M := by exact_mod_cast Nat.div_mul_cancel hPM
  field_simp
  linarith

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

end TreeEdit.TorusTree

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CircleObstruction ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter FiniteProbability

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter

lemma sampled_separation {k : ℕ} (hk : 2 ≤ k) (j : Fin (16*k) ↪ Pool k)
    (C : Config (Pool k) (residueModulus k) (branching k) k)
    [NeZero (fineModulus j)] [NeZero (resolution k)]
    (hgood : Good (resolution k : ℝ)⁻¹ poolPrime j k C (point 2))
    (x : State (ZMod (fineModulus j)) (branching k) k) :
    FiniteTree.length (branching k) (repetitions k) k ≤ 128^k * deficit
      (sampledWord poolPrime j (repetitions k) (resolution k) k C x).val
      (sampledWord poolPrime j (repetitions k) (resolution k) k C
        (x + diagonal (A := ZMod (fineModulus j)) (m := branching k) k (fineModulus j/2 : ℕ))).val := by
  have hm : 4 ≤ branching k := by dsimp [branching]; nlinarith [sq_nonneg (k : ℤ)]
  have ht : 0 < repetitions k := pow_pos (by omega) _
  have hh := separation (fun p => (pool_properties p).1.pos) hm ht C (sample (M := fineModulus j) (m := branching k) k x) (point 2) hgood
  have hs : sample (M := fineModulus j) (m := branching k) k
      (x + diagonal (A := ZMod (fineModulus j)) (m := branching k) k (fineModulus j/2 : ℕ)) =
      sample (M := fineModulus j) (m := branching k) k x + diagonal (A := UnitAddCircle) (m := branching k) k (point 2) := by
    dsimp only [sample]
    rw [map_add, mapState_diagonal, point_grid (M := fineModulus j) (by norm_num : 0 < 2) (fine_parameters hk j).2.1]
  have hhNat : FiniteTree.length (branching k) (repetitions k) k ≤ 128^k * deficit
      (word poolPrime j (repetitions k) (resolution k) k C (sample (M := fineModulus j) (m := branching k) k x)).val
      (word poolPrime j (repetitions k) (resolution k) k C (sample (M := fineModulus j) (m := branching k) k x + diagonal (A := UnitAddCircle) (m := branching k) k (point 2))).val := by
    exact_mod_cast hh
  have hyw : (sampledWord poolPrime j (repetitions k) (resolution k) k C
        (x + diagonal (A := ZMod (fineModulus j)) (m := branching k) k (fineModulus j/2 : ℕ))).val =
      (word poolPrime j (repetitions k) (resolution k) k C (sample (M := fineModulus j) (m := branching k) k x + diagonal (A := UnitAddCircle) (m := branching k) k (point 2))).val :=
    congrArg (fun z : State UnitAddCircle (branching k) k => (word poolPrime j (repetitions k) (resolution k) k C z).val) hs
  rw [hyw]
  exact hhNat

end TreeEdit.TorusTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter


theorem solution : type_of% @_root_.OAI.TreeEdit.TorusTree.sampled_separation := @_root_.OAI.TreeEdit.TorusTree.sampled_separation
