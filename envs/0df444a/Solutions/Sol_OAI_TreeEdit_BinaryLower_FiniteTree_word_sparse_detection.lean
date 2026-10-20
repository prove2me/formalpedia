-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteTree.word_sparse_detection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:43:16.829911+00:00
-- url     : https://prove2.me/submissions/165d493e-7dad-44ff-9806-6f9df07ae987

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteWordDetection.lean:L113-L140
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteTree.word_sparse_detection. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteActivity_characterSparse_detection
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_extendPrefix_append
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteVectors_agrees_child_iff
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteVectors_leafPeriod_dvd
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteVectors_prefixPeriod_child
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteVectors_prefixPeriod_eq_prod_cast

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteVectors ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

/-! Concrete vectors for the finite tree (finite-tree.tex, finite-vectors).
A prefix is represented by its depth and any full leaf path extending it.
All definitions ignore the unused tail of that representative. No primality
assumption is needed for the annihilation and recursive vector identities. -/

namespace TreeEdit.BinaryLower.FiniteVectors

open scoped BigOperators

variable {m k : ℕ}

lemma suffixScale_succ (p : Fin k → Fin m → ℕ) (j : ℕ) (hj : j < k) :
    suffixScale p j = levelProduct p ⟨j, hj⟩ * suffixScale p (j + 1) := by
  have hs : Finset.univ.filter (fun q : Fin k => j ≤ q.val) =
      insert ⟨j, hj⟩ (Finset.univ.filter (fun q : Fin k => j + 1 ≤ q.val)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hq
      by_cases he : q.val = j
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (by omega)
    · rintro (rfl | hq)
      · exact le_rfl
      · omega
  have hn : (⟨j, hj⟩ : Fin k) ∉
      Finset.univ.filter (fun q : Fin k => j + 1 ≤ q.val) := by simp
  simp only [suffixScale, hs, Finset.prod_insert hn]

/-- Every node vector is annihilated by its prescribed prefix period. -/
theorem prefixPeriod_nsmul_w (p : Fin k → Fin m → ℕ) (j : ℕ) (a : Leaf m k) :
    prefixPeriod p j a • w p j a = 0 := by
  funext b
  change prefixPeriod p j a • (if Agrees j a b then
    (suffixScale p j : ZMod (leafPeriod p b)) else 0) = 0
  by_cases hab : Agrees j a b
  · rw [ite_eq_left hab, nsmul_eq_mul, ← Nat.cast_mul]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (leafPeriod_dvd p j a b hab)
  · simp [hab]

/-- Multiplication of the cheap vector by the current level product gives `w`. -/
theorem w_eq_level_nsmul_u (p : Fin k → Fin m → ℕ) (j : ℕ) (hj : j < k)
    (a : Leaf m k) : w p j a = levelProduct p ⟨j, hj⟩ • u p j a := by
  funext b
  change (if Agrees j a b then (suffixScale p j : ZMod (leafPeriod p b)) else 0) =
    levelProduct p ⟨j, hj⟩ • (if Agrees j a b then
      (suffixScale p (j + 1) : ZMod (leafPeriod p b)) else 0)
  by_cases hab : Agrees j a b
  · simp only [ite_eq_left hab, nsmul_eq_mul, suffixScale_succ p j hj, Nat.cast_mul]
  · simp [hab]

/-- The cheap vector is exactly the sum of the children's distinguished vectors. -/
theorem u_eq_sum_child_w (p : Fin k → Fin m → ℕ) (j : ℕ) (hj : j < k)
    (a : Leaf m k) :
    u p j a = ∑ i : Fin m, w p (j + 1) (Function.update a ⟨j, hj⟩ i) := by
  funext b
  simp only [u, w, Finset.sum_apply, agrees_child_iff j hj a b]
  by_cases hab : Agrees j a b
  · simp [hab]
  · simp [hab]

lemma leafPeriod_pos (p : Fin k → Fin m → ℕ) (hp : ∀ q i, 0 < p q i) (a : Leaf m k) :
    0 < leafPeriod p a := by
  unfold leafPeriod
  apply Nat.mul_pos (by norm_num)
  apply Finset.prod_pos
  intro q hq
  exact hp q (a q)

lemma prefixPeriod_pos (p : Fin k → Fin m → ℕ) (hp : ∀ q i, 0 < p q i)
    (j : ℕ) (a : Leaf m k) : 0 < prefixPeriod p j a := by
  unfold prefixPeriod
  apply Nat.mul_pos (by norm_num)
  apply Finset.prod_pos
  intro q hq
  exact hp q (a q)

/-- The source's period upper bound, on the concrete vector prefix periods. -/
lemma prefixPeriod_le (p : Fin k → Fin m → ℕ) (hp : ∀ q i, p q i ≤ k ^ 5)
    (j : ℕ) (hj : j ≤ k) (a : Leaf m k) : prefixPeriod p j a ≤ 2 * k ^ (5 * j) := by
  rw [prefixPeriod_eq_prod_cast p j hj a]
  apply Nat.mul_le_mul_left
  calc
    _ ≤ ∏ _q : Fin j, k ^ 5 := Finset.prod_le_prod' fun q _ => hp _ _
    _ = k ^ (5 * j) := by simp [← pow_mul]

end TreeEdit.BinaryLower.FiniteVectors

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteTreeInstantiation ----
namespace OAI

/-! Instantiate the recursive word evaluator with the explicit finite state
group and subtree vectors. -/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteTree

/-- The exact prescribed period annihilates the actual word's node vector. -/
theorem wordPeriod_nsmul_wordW {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (p : List (Fin m)) :
    wordPeriod primes i₀ p • wordW primes i₀ p = 0 := by
  funext l
  exact congrFun (FiniteVectors.prefixPeriod_nsmul_w primes p.length
    (extendPrefix i₀ p)) (leafEquiv m k l)

end TreeEdit.BinaryLower.FiniteTree

end

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteWordDetection ----
namespace OAI

/-!
# Sparse detection for the concrete recursive word model

The list-prefix vectors used by `finiteWord` satisfy the same exact recursion
and period bounds as the function-prefix vectors. This closes the algebraic
inputs of the finite spectral detector in the actual word-state presentation.
-/

noncomputable section

open scoped BigOperators
open Classical

namespace TreeEdit.BinaryLower.FiniteTree

variable {m k : ℕ}

theorem wordState_finite (primes : Fin k → Fin m → ℕ)
    (hp : ∀ q i, 0 < primes q i) : Finite (State (wordPeriods primes)) := by
  let : ∀ l : Leaf m k, NeZero (wordPeriods primes l) := fun l =>
    ⟨ne_of_gt (FiniteVectors.leafPeriod_pos primes hp (leafEquiv m k l))⟩
  infer_instance

theorem wordPeriod_pos (primes : Fin k → Fin m → ℕ)
    (hp : ∀ q i, 0 < primes q i) (i₀ : Fin m) (p : List (Fin m)) :
    0 < wordPeriod primes i₀ p :=
  FiniteVectors.prefixPeriod_pos primes hp p.length (extendPrefix i₀ p)

theorem wordPeriod_le (primes : Fin k → Fin m → ℕ)
    (hp : ∀ q i, primes q i ≤ k ^ 5) (i₀ : Fin m) (p : List (Fin m))
    (hlen : p.length ≤ k) : wordPeriod primes i₀ p ≤ 2 * k ^ (5 * p.length) :=
  FiniteVectors.prefixPeriod_le primes hp p.length hlen (extendPrefix i₀ p)

theorem wordPeriod_child (primes : Fin k → Fin m → ℕ)
    (i₀ i : Fin m) (p : List (Fin m)) (hp : p.length < k) :
    wordPeriod primes i₀ (p ++ [i]) =
      wordPeriod primes i₀ p * primes ⟨p.length, hp⟩ i := by
  simp only [wordPeriod, List.length_append, List.length_singleton,
    extendPrefix_append i₀ i p hp]
  exact FiniteVectors.prefixPeriod_child primes p.length hp (extendPrefix i₀ p) i

/-- The distinguished word-state vector is the level product times the
actual cheap word-state vector. -/
theorem wordW_eq_level_nsmul_wordU (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (p : List (Fin m)) (hp : p.length < k) :
    wordW primes i₀ p = FiniteVectors.levelProduct primes ⟨p.length, hp⟩ •
      wordU primes i₀ p := by
  unfold wordW wordU
  rw [FiniteVectors.w_eq_level_nsmul_u primes p.length hp (extendPrefix i₀ p)]
  rfl

/-- The cheap word-state vector is exactly the sum of the children's
distinguished vectors, with the same list indices used for branching. -/
theorem wordU_eq_sum_child_wordW (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (p : List (Fin m)) (hp : p.length < k) :
    wordU primes i₀ p = ∑ i : Fin m, wordW primes i₀ (p ++ [i]) := by
  unfold wordU wordW wordPeriods
  simp only [List.length_append, List.length_singleton, extendPrefix_append i₀ _ p hp]
  rw [FiniteVectors.u_eq_sum_child_w primes p.length hp (extendPrefix i₀ p)]
  funext l
  simp only [pullState, Finset.sum_apply]

/-- A sparse active node is detected by short averages of cheap shifts
in the canonical word-state group. -/
theorem word_sparse_detection (primes : Fin k → Fin m → ℕ) (i₀ : Fin m)
    (hk : 1 ≤ k) (hppos : ∀ q i, 0 < primes q i)
    (hp : ∀ q i, primes q i ≤ k ^ 5)
    (v : FiniteActivity.InternalNode (Fin m) k)
    (χ : AddChar (State (wordPeriods primes)) ℂ)
    (hsparse : FiniteActivity.characterSparse (wordW primes i₀) k v χ) :
    ((4 * k ^ (10 * k) : ℕ) : ℝ) ≤
      ∑ s : Fin (4 * k ^ (10 * k)),
        ‖1 - χ ((s.val + 1) • wordU primes i₀ (List.ofFn v.2))‖ ^ 2 := by
  let : Finite (State (wordPeriods primes)) := wordState_finite primes hppos
  let p := List.ofFn v.2
  have hlen : p.length < k := by simp [p]
  apply FiniteActivity.characterSparse_detection (wordW primes i₀) v
    (wordU primes i₀ p) (wordPeriod primes i₀ p)
    (FiniteVectors.levelProduct primes ⟨p.length, hlen⟩)
    (primes ⟨p.length, hlen⟩) hk
  · exact wordPeriod_pos primes hppos i₀ p
  · simpa [p] using wordPeriod_le primes hp i₀ p hlen.le
  · exact hppos _
  · exact hp _
  · exact wordW_eq_level_nsmul_wordU primes i₀ p hlen
  · exact wordU_eq_sum_child_wordW primes i₀ p hlen
  · intro i
    rw [← wordPeriod_child primes i₀ i p hlen]
    exact wordPeriod_nsmul_wordW primes i₀ (p ++ [i])
  · exact hsparse

end TreeEdit.BinaryLower.FiniteTree

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.word_sparse_detection := @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.word_sparse_detection
