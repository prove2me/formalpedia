-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteTree.finiteWord_separation_of_half_children
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:56:46.930472+00:00
-- url     : https://prove2.me/submissions/46f21af3-34a4-4ad3-88b5-663183a388aa

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteSeparation.lean:L54-L120
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteTree.finiteWord_separation_of_half_children. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_BlockExtraction_extract_flatten_fixed
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_extendPrefix_append
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_nodeWord_state_congr
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_row_deficit_charge
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_singleton_deficit_of_ne
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_symbol_prefix_of_mem
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteVectors_agrees_child_iff
import Theorems.Thm_OAI_TreeEdit_BinaryLower_TaggedExtraction_equal_symbols_same_tag
import Theorems.Thm_OAI_TreeEdit_BinaryLower_TaggedRow_sum_deficit_le_row_deficit
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Tagged_tagged_slice_alignment

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteTreeGeometry ----
namespace OAI

/-! Concrete tagged leaf states and subtree locality for the finite tree. -/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteTree

/-- At a valid leaf, equality is exactly equality of that leaf's state. -/
theorem leafDecoder_eq_iff {m k : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (p : List (Fin m)) (hp : p.length = k) (x y : State Q) :
    leafDecoder Q base p x = leafDecoder Q base p y ↔
      x ⟨p, hp⟩ = y ⟨p, hp⟩ := by
  simp [leafDecoder, hp]

/-- A nonzero residue shift changes the tagged symbol at a leaf. -/
theorem leafDecoder_ne_of_not_dvd {m k : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (p : List (Fin m)) (hp : p.length = k)
    (x z : State Q) (hz : z ⟨p, hp⟩ = 1) (t : ℤ)
    (ht : ¬ (Q ⟨p, hp⟩ : ℤ) ∣ t) :
    leafDecoder Q base p (x + t • z) ≠ leafDecoder Q base p x := by
  intro he
  have he' := (leafDecoder_eq_iff Q base p hp (x + t • z) x).1 he
  have hcast : (t : ZMod (Q ⟨p, hp⟩)) = 0 := by
    simpa [hz, add_eq_left] using he'
  exact ht ((ZMod.intCast_zmod_eq_zero_iff_dvd t _).1 hcast)

/-- The base case of finite separation, with the actual canonical deficit. -/
theorem leaf_deficit_of_not_dvd {m k : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (p : List (Fin m)) (hp : p.length = k)
    (x z : State Q) (hz : z ⟨p, hp⟩ = 1) (t : ℤ)
    (ht : ¬ (Q ⟨p, hp⟩ : ℤ) ∣ t) :
    deficit 1 [leafDecoder Q base p x] [leafDecoder Q base p (x + t • z)] = 1 := by
  apply singleton_deficit_of_ne
  exact (leafDecoder_ne_of_not_dvd Q base p hp x z hz t ht).symm

/-- The relative input shift between source row `a` and target row `b` in a
child is `(b-a+tR)` times its distinguished vector. The two support hypotheses
are precisely the coordinate restrictions of the explicit subtree vectors. -/
theorem child_relative_shift {T m k : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (u : List (Fin m) → State Q)
    (h : ℕ) (p : List (Fin m)) (hlen : p.length + h = k)
    (x wp up wc : State Q) (R t : ℤ) (a b : ℕ)
    (hu : ∀ l : Leaf m k, p <+: l.val → up l = wc l)
    (hw : ∀ l : Leaf m k, p <+: l.val → wp l = R • wc l) :
    nodeWord T (leafDecoder Q base) u h p (x + t • wp + b • up) =
      nodeWord T (leafDecoder Q base) u h p
        (x + a • up + ((b : ℤ) - (a : ℤ) + t * R) • wc) := by
  apply nodeWord_state_congr Q base u h p hlen
  intro l hl
  simp only [Pi.add_apply, Pi.smul_apply, hu l hl, hw l hl]
  simp only [zsmul_eq_mul, nsmul_eq_mul, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast]
  ring

end TreeEdit.BinaryLower.FiniteTree

end

end OAI

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

end TreeEdit.BinaryLower.FiniteVectors

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteVectorRestrictions ----
namespace OAI

/-! Coordinate restrictions of the finite subtree vectors. -/

namespace TreeEdit.BinaryLower.FiniteVectors

variable {m k : ℕ}

/-- On a child's subtree the parent's cheap vector equals that child's
 distinguished vector. -/
theorem u_on_child (p : Fin k → Fin m → ℕ) (j : ℕ) (hj : j < k)
    (a b : Leaf m k) (i : Fin m)
    (hab : Agrees (j + 1) (Function.update a ⟨j, hj⟩ i) b) :
    u p j a b = w p (j + 1) (Function.update a ⟨j, hj⟩ i) b := by
  have hp := ((agrees_child_iff j hj a b i).1 hab).1
  simp [u, w, hp, hab]

end TreeEdit.BinaryLower.FiniteVectors

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteTreeInstantiation ----
namespace OAI

/-! Instantiate the recursive word evaluator with the explicit finite state
group and subtree vectors. -/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteTree

/-- Concrete vector restriction to a child in the list-path presentation. -/
theorem wordU_on_child {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ i : Fin m) (p : List (Fin m)) (hp : p.length < k)
    (l : Leaf m k) (hl : p ++ [i] <+: l.val) :
    wordU primes i₀ p l = wordW primes i₀ (p ++ [i]) l := by
  have hc : FiniteVectors.Agrees (p.length + 1)
      (Function.update (extendPrefix i₀ p) ⟨p.length, hp⟩ i) (leafEquiv m k l) := by
    have ha := (agrees_extendPrefix_iff i₀ (p ++ [i])
      (by simp; omega) (leafEquiv m k l)).2 (by simpa using hl)
    simpa [extendPrefix_append i₀ i p hp] using ha
  change FiniteVectors.u primes p.length (extendPrefix i₀ p) (leafEquiv m k l) =
    FiniteVectors.w primes (p ++ [i]).length (extendPrefix i₀ (p ++ [i])) (leafEquiv m k l)
  simpa [extendPrefix_append i₀ i p hp] using
    FiniteVectors.u_on_child primes p.length hp (extendPrefix i₀ p) (leafEquiv m k l) i hc

/-- Distinguished parent shift restricts to the current level product times
the distinguished child shift. -/
theorem wordW_on_child {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ i : Fin m) (p : List (Fin m)) (hp : p.length < k)
    (l : Leaf m k) (hl : p ++ [i] <+: l.val) :
    wordW primes i₀ p l =
      (FiniteVectors.levelProduct primes ⟨p.length, hp⟩ : ℤ) •
        wordW primes i₀ (p ++ [i]) l := by
  have h := congrFun (FiniteVectors.w_eq_level_nsmul_u primes p.length hp
    (extendPrefix i₀ p)) (leafEquiv m k l)
  change wordW primes i₀ p l =
    FiniteVectors.levelProduct primes ⟨p.length, hp⟩ • wordU primes i₀ p l at h
  rw [wordU_on_child primes i₀ i p hp l hl] at h
  simpa using h

/-- Base case of the separation proposition for the concrete word construction. -/
theorem finiteWord_leaf_deficit {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (T : ℕ) (p : List (Fin m)) (hp : p.length = k)
    (x : State (wordPeriods primes)) (t : ℤ)
    (ht : ¬ (wordPeriod primes i₀ p : ℤ) ∣ t) :
    deficit 1 (finiteWord primes i₀ T 0 p x)
      (finiteWord primes i₀ T 0 p (x + t • wordW primes i₀ p)) = 1 := by
  apply leaf_deficit_of_not_dvd (wordPeriods primes)
    ⟨List.replicate k i₀, by simp⟩ p hp x (wordW primes i₀ p)
  · exact wordW_leaf_self primes i₀ p hp
  · simpa [wordPeriod_leaf primes i₀ p hp] using ht

/-- The actual relative child translation in any two rows of a node. -/
theorem finiteWord_child_relative {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ i : Fin m) (T h : ℕ) (p : List (Fin m))
    (hlen : p.length + (h + 1) = k) (x : State (wordPeriods primes))
    (t : ℤ) (a b : ℕ) :
    finiteWord primes i₀ T h (p ++ [i])
        (x + t • wordW primes i₀ p + b • wordU primes i₀ p) =
      finiteWord primes i₀ T h (p ++ [i])
        (x + a • wordU primes i₀ p +
          ((b : ℤ) - (a : ℤ) + t *
            (FiniteVectors.levelProduct primes ⟨p.length, by omega⟩ : ℤ)) •
              wordW primes i₀ (p ++ [i])) := by
  have hp : p.length < k := by omega
  apply child_relative_shift (wordPeriods primes) ⟨List.replicate k i₀, by simp⟩
    (wordU primes i₀) h (p ++ [i]) (by simp; omega)
  · intro l hl
    exact wordU_on_child primes i₀ i p hp l hl
  · intro l hl
    exact wordW_on_child primes i₀ i p hp l hl

end TreeEdit.BinaryLower.FiniteTree

end

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteTreeTags ----
namespace OAI

/-!
# Concrete tagged alphabets below finite-tree nodes

The generic row lemma needs disjoint alphabets for distinct children. Here
that hypothesis is proved for the actual tagged cyclic-state symbols, not
postulated as an additional property of the construction.
-/

namespace TreeEdit.BinaryLower.FiniteTree

lemma mem_subtreeAlphabet_of_mem {m k T : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (u : List (Fin m) → State Q)
    (h : ℕ) (p : List (Fin m)) (hlen : p.length + h = k)
    (x : State Q) (s : Symbol Q)
    (hs : s ∈ nodeWord T (leafDecoder Q base) u h p x) :
    s ∈ subtreeAlphabet Q p := symbol_prefix_of_mem Q base u h p hlen x s hs

lemma child_eq_of_prefixes {α : Type*} (p l : List α) (i j : α)
    (hi : p ++ [i] <+: l) (hj : p ++ [j] <+: l) : i = j := by
  have he : p ++ [i] = p ++ [j] := by
    calc
      p ++ [i] = l.take (p ++ [i]).length := List.prefix_iff_eq_take.mp hi
      _ = l.take (p ++ [j]).length := by simp
      _ = p ++ [j] := (List.prefix_iff_eq_take.mp hj).symm
  simpa using List.append_cancel_left he

/-- Immediate child alphabets are pairwise disjoint, uniformly in all states. -/
theorem subtreeAlphabet_children_pairwise_disjoint {m k : ℕ}
    (Q : Leaf m k → ℕ) (p : List (Fin m)) :
    Pairwise fun i j : Fin m =>
      Disjoint (subtreeAlphabet Q (p ++ [i])) (subtreeAlphabet Q (p ++ [j])) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro s hi hj
  exact hij (child_eq_of_prefixes p s.1.val i j hi hj)

end TreeEdit.BinaryLower.FiniteTree

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteSeparationArithmetic ----
namespace OAI

/-!
# Deficit charges in the finite-tree separation induction

The exact deficit charges are those of `prop:finite-separation`.
-/

namespace TreeEdit.BinaryLower.FiniteTree

/-- The chosen row charge is no larger than the tagged transition gap. -/
theorem finite_charge_le_gap (m h : ℕ) (hm : 2 ≤ m) (B : ℝ) (hB : 0 ≤ B) :
    (m : ℝ) * (B / (4 : ℝ) ^ h) / 2 ≤ ((m : ℝ) - 1) * B := by
  have hp : (1 : ℝ) ≤ (4 : ℝ) ^ h := one_le_pow₀ (by norm_num)
  have hp0 : 0 < (4 : ℝ) ^ h := by positivity
  have hq : B / (4 : ℝ) ^ h ≤ B := by
    apply (div_le_iff₀ hp0).2
    nlinarith
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hq hm0]

end TreeEdit.BinaryLower.FiniteTree

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedGaps ----
namespace OAI

/-! Gap accounting for split rows in ordered-tag alignments. -/

namespace TreeEdit.BinaryLower.Tagged

open Finset

/-- The harmonic lower bound implies the convenient half-minimum form. -/
theorem half_min_le_harmonic {d g T : ℝ} (hd : 0 ≤ d) (hg : 0 < g)
    (hT : 0 ≤ T) :
    T / 2 * min d g ≤ T * d * g / (d + g) := by
  have hden : 0 < d + g := by linarith
  apply (le_div_iff₀ hden).2
  rcases le_total d g with h | h
  · rw [min_eq_left h]
    have hmul := mul_nonneg hT (mul_nonneg hd (sub_nonneg.mpr h))
    nlinarith
  · rw [min_eq_right h]
    have hmul := mul_nonneg hT (mul_nonneg (le_of_lt hg) (sub_nonneg.mpr h))
    nlinarith

end TreeEdit.BinaryLower.Tagged

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedExtraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace TreeEdit.BinaryLower
namespace TaggedExtraction

universe u
variable {α : Type u}

/-- Ordered tags expressed as a single decoder imply the disjointness premise above. -/
lemma cross_disjoint_of_tags {T m B : ℕ}
    (X Y : Fin T → Fin m → Word α B) (tag : α → Fin m)
    (hX : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → tag s = i)
    (hY : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → tag s = i) :
    ∀ (a b : Fin T) (i j : Fin m) (s : α),
      s ∈ (X a i).val → s ∈ (Y b j).val → i = j := by
  intro a b i j s hx hy
  exact (hX a i s hx).symm.trans (hY b j s hy)

/-- The global-symbol interface required by the tagged slice-alignment theorem. -/
lemma equal_symbols_same_tag_of_decoder {T m B : ℕ}
    (X Y : Fin T → Fin m → Word α B) (tag : α → Fin m)
    (hX : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → tag s = i)
    (hY : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → tag s = i)
    (hm : 0 < m) (hB : 0 < B)
    (p q : ℕ) (hp : p < T * m * B) (hq : q < T * m * B)
    (heq : (rows X)[p]'(by rw [length_rows]; exact hp) =
      (rows Y)[q]'(by rw [length_rows]; exact hq)) :
    p / B % m = q / B % m :=
  equal_symbols_same_tag X Y hm hB (cross_disjoint_of_tags X Y tag hX hY) p q hp hq heq

end TaggedExtraction
end TreeEdit.BinaryLower

end

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.BlockExtraction ----
namespace OAI

/-! Exact contiguous-window extraction from fixed-width block concatenations. -/

namespace TreeEdit.BinaryLower
namespace BlockExtraction

/-- Window extraction for an indexed family of fixed-width words. -/
theorem extract_flatten_ofFn {α : Type*} {n B : ℕ}
    (blocks : Fin n → Word α B) (i : Fin n) :
    ((List.ofFn (fun j => (blocks j).val)).flatten.drop (i.val * B)).take B =
      (blocks i).val := by
  have hb : ∀ z ∈ List.ofFn (fun j => (blocks j).val), z.length = B := by
    intro z hz
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    exact (blocks j).property
  simpa using extract_flatten_fixed (List.ofFn (fun j => (blocks j).val)) B hb
    i.val (by simp)

/-- Exact extraction from the finite-range flatMap presentation. -/
theorem extract_concatenate {α : Type*} {n B : ℕ}
    (blocks : Fin n → Word α B) (i : Fin n) :
    ((concatenate blocks).drop (i.val * B)).take B = (blocks i).val := by
  simpa only [concatenate, List.flatMap_def, ← List.ofFn_eq_map] using
    extract_flatten_ofFn blocks i

/-- Taking the a-th row of the nested concatenation recovers that precise row. -/
theorem extract_row {α : Type*} {T m B : ℕ}
    (blocks : Fin T → Fin m → Word α B) (a : Fin T) :
    ((concatenateRows blocks).drop (a.val * (m * B))).take (m * B) =
      concatenate (blocks a) := by
  exact extract_concatenate (fun a => rowWord (blocks a)) a

end BlockExtraction
end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedRowLCS ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Longest common subsequence bounds for rows over disjoint tagged alphabets. -/
namespace TreeEdit.BinaryLower.TaggedRow
open scoped BigOperators

/-- Exact length of an equal-block row. -/
theorem length_row {α : Type*} {m B : ℕ} (X : Fin m → List α)
    (hX : ∀ i, (X i).length = B) : (row X).length = m * B := by
  simp [row, List.length_flatMap, hX]

/-- Real-valued LCS row capacity, convenient when a separate matching
restriction lemma has already bounded a row-pair count by its LCS. -/
theorem lcs_row_le_capacity_sub {α : Type*} {m B : ℕ}
    (tag : α → Fin m) (X Y : Fin m → List α)
    (hX : ∀ i, ∀ a ∈ X i, tag a = i)
    (hY : ∀ i, ∀ a ∈ Y i, tag a = i)
    (hXL : ∀ i, (X i).length = B)
    {d : ℝ} (hd : d ≤ ∑ i, (deficit B (X i) (Y i) : ℝ)) :
    (lcs (row X) (row Y) : ℝ) ≤ (m : ℝ) * B - d := by
  have hdef := sum_deficit_le_row_deficit tag X Y hX hY hXL
  have hlen : lcs (row X) (row Y) ≤ m * B := by
    simpa [length_row X hXL] using lcs_le_length_left (row X) (row Y)
  have hnat : (∑ i, deficit B (X i) (Y i)) + lcs (row X) (row Y) ≤ m * B := by
    change (∑ i, deficit B (X i) (Y i)) ≤ m * B - lcs (row X) (row Y) at hdef
    omega
  have hreal : (∑ i, (deficit B (X i) (Y i) : ℝ)) +
      (lcs (row X) (row Y) : ℝ) ≤ (m : ℝ) * B := by
    exact_mod_cast hnat
  linarith

/-- Pairwise disjoint alphabets admit a tag on the ambient alphabet. Values
outside their union are irrelevant and receive an arbitrary default tag. -/
theorem exists_tag_of_pairwise_disjoint {α I : Type*} [Nonempty I]
    (Γ : I → Set α) (hΓ : Pairwise fun i j => Disjoint (Γ i) (Γ j)) :
    ∃ tag : α → I, ∀ i, ∀ a ∈ Γ i, tag a = i := by
  classical
  let tag : α → I := fun a =>
    if h : ∃ i, a ∈ Γ i then h.choose else Classical.arbitrary I
  refine ⟨tag, ?_⟩
  intro i a ha
  dsimp [tag]
  split_ifs with h
  · by_contra hne
    exact Set.disjoint_left.mp (hΓ hne) h.choose_spec ha
  · exact False.elim (h ⟨i, ha⟩)

end TreeEdit.BinaryLower.TaggedRow

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedArrayPrerequisites ----
namespace OAI

/-! Literal array-to-slice hypotheses for the common tagged alignment lemma. -/
namespace TreeEdit.BinaryLower.TaggedExtraction

open scoped BigOperators

/-- A blockwise deficit bound gives the local slice capacity,
with all slices taken from the actual nested concatenation. -/
theorem local_slice_capacity {α : Type*} {T m B : ℕ}
    (X Y : Fin T → Fin m → Word α B) (tag : α → Fin m)
    (hX : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → tag s = i)
    (hY : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → tag s = i)
    {d : ℝ} (hd : ∀ a b, d ≤ ∑ i, (deficit B (X a i).val (Y b i).val : ℝ))
    (a b : Fin T) :
    (lcs (((rows X).drop (a.val * (m * B))).take (m * B))
      (((rows Y).drop (b.val * (m * B))).take (m * B)) : ℝ) ≤
        (m : ℝ) * B - d := by
  change (lcs (((BlockExtraction.concatenateRows X).drop (a.val * (m * B))).take (m * B))
    (((BlockExtraction.concatenateRows Y).drop (b.val * (m * B))).take (m * B)) : ℝ) ≤ _
  rw [BlockExtraction.extract_row, BlockExtraction.extract_row]
  exact TaggedRow.lcs_row_le_capacity_sub tag
    (fun i => (X a i).val) (fun i => (Y b i).val)
    (hX a) (hY b) (fun i => (X a i).property) (hd a b)

/-- Pairwise disjoint alphabets admit a common tag decoder. -/
theorem exists_array_decoder {α : Type*} {T m B : ℕ}
    (X Y : Fin T → Fin m → Word α B) (hm : 0 < m)
    (Γ : Fin m → Set α) (hΓ : Pairwise fun i j => Disjoint (Γ i) (Γ j))
    (hX : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → s ∈ Γ i)
    (hY : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → s ∈ Γ i) :
    ∃ tag : α → Fin m,
      (∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → tag s = i) ∧
      (∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → tag s = i) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨tag, ht⟩ := TaggedRow.exists_tag_of_pairwise_disjoint Γ hΓ
  refine ⟨tag, ?_, ?_⟩
  · intro a i s hs
    exact ht i s (hX a i s hs)
  · intro a i s hs
    exact ht i s (hY a i s hs)

end TreeEdit.BinaryLower.TaggedExtraction

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedArrays ----
namespace OAI

/-! Ordered-tag alignment bounds for arrays. -/
namespace TreeEdit.BinaryLower.Tagged

open scoped BigOperators
open TaggedExtraction

/-- Harmonic deficit bound for literal arrays of fixed-width, ordered-tag blocks. -/
theorem tagged_arrays_harmonic {α : Type*} {T m B : ℕ}
    (hT : 0 < T) (hm : 2 ≤ m) (hB : 0 < B)
    (X Y : Fin T → Fin m → Word α B) (tag : α → Fin m)
    (hX : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → tag s = i)
    (hY : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → tag s = i)
    (d : ℝ) (hd : 0 ≤ d)
    (hlocal : ∀ a b, d ≤ ∑ i, (deficit B (X a i).val (Y b i).val : ℝ)) :
    (T : ℝ) * d * (((m - 1) * B : ℕ) : ℝ) /
      (d + (((m - 1) * B : ℕ) : ℝ)) ≤
        (deficit (T * m * B) (rows X) (rows Y) : ℝ) := by
  apply tagged_slice_alignment hT hm hB (rows X) (rows Y)
    (length_rows X) (length_rows Y)
  · intro p hp q hq heq
    exact equal_symbols_same_tag_of_decoder X Y tag hX hY (by omega) hB p q
      (by simpa only [length_rows] using hp)
      (by simpa only [length_rows] using hq) heq
  · exact hd
  · intro a ha b hb
    simpa only [Nat.cast_mul] using
      local_slice_capacity X Y tag hX hY hlocal ⟨a, ha⟩ ⟨b, hb⟩

/-- Both inequalities in `eq:tagged-result`, with no matching-alignment premise. -/
theorem tagged_arrays_bounds {α : Type*} {T m B : ℕ}
    (hT : 0 < T) (hm : 2 ≤ m) (hB : 0 < B)
    (X Y : Fin T → Fin m → Word α B) (tag : α → Fin m)
    (hX : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → tag s = i)
    (hY : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → tag s = i)
    (d : ℝ) (hd : 0 ≤ d)
    (hlocal : ∀ a b, d ≤ ∑ i, (deficit B (X a i).val (Y b i).val : ℝ)) :
    ((T : ℝ) * d * (((m - 1) * B : ℕ) : ℝ) /
      (d + (((m - 1) * B : ℕ) : ℝ)) ≤
        (deficit (T * m * B) (rows X) (rows Y) : ℝ)) ∧
    ((T : ℝ) / 2 * min d (((m - 1) * B : ℕ) : ℝ) ≤
      (T : ℝ) * d * (((m - 1) * B : ℕ) : ℝ) /
        (d + (((m - 1) * B : ℕ) : ℝ))) := by
  refine ⟨tagged_arrays_harmonic hT hm hB X Y tag hX hY d hd hlocal, ?_⟩
  apply half_min_le_harmonic hd _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.mul_pos (by omega : 0 < m - 1) hB

/-- The convenient `Td/2` form used in both tree separation inductions. -/
theorem tagged_arrays_half {α : Type*} {T m B : ℕ}
    (hT : 0 < T) (hm : 2 ≤ m) (hB : 0 < B)
    (X Y : Fin T → Fin m → Word α B) (tag : α → Fin m)
    (hX : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → tag s = i)
    (hY : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → tag s = i)
    (d : ℝ) (hd : 0 ≤ d)
    (hlocal : ∀ a b, d ≤ ∑ i, (deficit B (X a i).val (Y b i).val : ℝ))
    (hdg : d ≤ (((m - 1) * B : ℕ) : ℝ)) :
    (T : ℝ) * d / 2 ≤ (deficit (T * m * B) (rows X) (rows Y) : ℝ) := by
  obtain ⟨hmain, hhalf⟩ := tagged_arrays_bounds hT hm hB X Y tag hX hY d hd hlocal
  rw [min_eq_left hdg] at hhalf
  have h := hhalf.trans hmain
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- Ordered-tag alignment for pairwise disjoint alphabets.
The decoder used internally is constructed, not an additional hypothesis. -/
theorem rows_with_ordered_tags {α : Type*} {T m B : ℕ}
    (hT : 0 < T) (hm : 2 ≤ m) (hB : 0 < B)
    (Γ : Fin m → Set α) (hΓ : Pairwise fun i j => Disjoint (Γ i) (Γ j))
    (X Y : Fin T → Fin m → Word α B)
    (hX : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → s ∈ Γ i)
    (hY : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → s ∈ Γ i)
    (d : ℝ) (hd : 0 ≤ d)
    (hlocal : ∀ a b, d ≤ ∑ i, (deficit B (X a i).val (Y b i).val : ℝ)) :
    ((T : ℝ) * d * (((m - 1) * B : ℕ) : ℝ) /
      (d + (((m - 1) * B : ℕ) : ℝ)) ≤
        (deficit (T * m * B) (rows X) (rows Y) : ℝ)) ∧
    ((T : ℝ) / 2 * min d (((m - 1) * B : ℕ) : ℝ) ≤
      (T : ℝ) * d * (((m - 1) * B : ℕ) : ℝ) /
        (d + (((m - 1) * B : ℕ) : ℝ))) ∧
    (d ≤ (((m - 1) * B : ℕ) : ℝ) →
      (T : ℝ) * d / 2 ≤ (deficit (T * m * B) (rows X) (rows Y) : ℝ)) := by
  obtain ⟨tag, htX, htY⟩ := exists_array_decoder X Y (by omega) Γ hΓ hX hY
  obtain ⟨hh, hm'⟩ := tagged_arrays_bounds hT hm hB X Y tag htX htY d hd hlocal
  exact ⟨hh, hm', tagged_arrays_half hT hm hB X Y tag htX htY d hd hlocal⟩

end TreeEdit.BinaryLower.Tagged

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteSeparation ----
namespace OAI

/-!
# Geometric separation for the concrete finite tree

The prime construction supplies the half-child condition in the
geometric induction.
-/

noncomputable section
namespace TreeEdit.BinaryLower.FiniteTree

open scoped BigOperators

theorem finiteWord_succ_eq_rows {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (T h : ℕ) (p : List (Fin m)) (x : State (wordPeriods primes)) :
    finiteWord primes i₀ T (h + 1) p x =
      TaggedExtraction.rows (finiteBlocks primes i₀ T h p x) := by
  have hrange : (List.finRange T).map Fin.val = List.range T := by
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      simp
  unfold finiteWord nodeWord
  rw [← hrange, List.flatMap_map]
  rfl

/-- Ordered-tag alignment and half-child nondivisibility imply separation
for arbitrary common-subsequence matchings. -/
theorem finiteWord_separation_of_half_children {m k T : ℕ}
    (primes : Fin k → Fin m → ℕ) (i₀ : Fin m) (hm : 2 ≤ m) (hT : 0 < T)
    (hhalf : ∀ p (hp : p.length < k) (a b : Fin T) (t : ℤ),
      ¬ (wordPeriod primes i₀ p : ℤ) ∣ t →
      m ≤ 2 * (separatedChildren primes i₀ p hp a b t).card)
    (h : ℕ) (p : List (Fin m)) (hlen : p.length + h = k)
    (x : State (wordPeriods primes)) (t : ℤ)
    (ht : ¬ (wordPeriod primes i₀ p : ℤ) ∣ t) :
    (((m * T) ^ h : ℕ) : ℝ) / (4 : ℝ) ^ h ≤
      (deficit ((m * T) ^ h) (finiteWord primes i₀ T h p x)
        (finiteWord primes i₀ T h p (x + t • wordW primes i₀ p)) : ℝ) := by
  classical
  induction h generalizing p x t with
  | zero =>
      have hp : p.length = k := by simpa using hlen
      simpa using (finiteWord_leaf_deficit primes i₀ T p hp x t ht).symm.le
  | succ h ih =>
      have hp : p.length < k := by omega
      let B : ℕ := (m * T) ^ h
      let q : ℝ := (B : ℝ) / (4 : ℝ) ^ h
      let d : ℝ := (m : ℝ) * q / 2
      let X := finiteBlocks primes i₀ T h p x
      let Y := finiteBlocks primes i₀ T h p (x + t • wordW primes i₀ p)
      have hB : 0 < B := by dsimp [B]; exact pow_pos (Nat.mul_pos (by omega) hT) _
      have hq : 0 ≤ q := by dsimp [q]; positivity
      have hd : 0 ≤ d := by dsimp [d]; positivity
      have hlocal (a b : Fin T) : d ≤ ∑ i, (deficit B (X a i).val (Y b i).val : ℝ) := by
        apply row_deficit_charge (separatedChildren primes i₀ p hp a b t) _ q hq
          (fun i => Nat.cast_nonneg _) _ (hhalf p hp a b t ht)
        intro i hi
        have hnot : ¬ (wordPeriod primes i₀ (p ++ [i]) : ℤ) ∣
            finiteRowShift primes p hp a b t := (Finset.mem_filter.mp hi).2
        change q ≤ (deficit B
          (finiteWord primes i₀ T h (p ++ [i]) (x + a.val • wordU primes i₀ p))
          (finiteWord primes i₀ T h (p ++ [i])
            (x + t • wordW primes i₀ p + b.val • wordU primes i₀ p)) : ℝ)
        rw [finiteWord_child_relative primes i₀ i T h p hlen x t a.val b.val]
        exact ih (p ++ [i]) (by simp; omega) _ _ hnot
      have hX : ∀ (a : Fin T) (i : Fin m) (s : Symbol (wordPeriods primes)),
          s ∈ (X a i).val → s ∈ subtreeAlphabet (wordPeriods primes) (p ++ [i]) := by
        intro a i s hs
        exact mem_subtreeAlphabet_of_mem (wordPeriods primes)
          ⟨List.replicate k i₀, by simp⟩ (wordU primes i₀) h (p ++ [i])
          (by simp; omega) _ s hs
      have hY : ∀ (a : Fin T) (i : Fin m) (s : Symbol (wordPeriods primes)),
          s ∈ (Y a i).val → s ∈ subtreeAlphabet (wordPeriods primes) (p ++ [i]) := by
        intro a i s hs
        exact mem_subtreeAlphabet_of_mem (wordPeriods primes)
          ⟨List.replicate k i₀, by simp⟩ (wordU primes i₀) h (p ++ [i])
          (by simp; omega) _ s hs
      have hdg : d ≤ (((m - 1) * B : ℕ) : ℝ) := by
        have hh := finite_charge_le_gap m h hm (B : ℝ) (Nat.cast_nonneg _)
        simpa [d, q, Nat.cast_mul, Nat.cast_sub (show 1 ≤ m by omega)] using hh
      have hsep := (Tagged.rows_with_ordered_tags hT hm hB
        (fun i => subtreeAlphabet (wordPeriods primes) (p ++ [i]))
        (subtreeAlphabet_children_pairwise_disjoint (wordPeriods primes) p)
        X Y hX hY d hd hlocal).2.2 hdg
      have hN : T * m * B = (m * T) ^ (h + 1) := by dsimp [B]; rw [pow_succ]; ring
      have hcharge : (T : ℝ) * d / 2 = (((m * T) ^ (h + 1) : ℕ) : ℝ) / (4 : ℝ) ^ (h + 1) := by
        dsimp [d, q, B]
        push_cast
        rw [pow_succ, pow_succ]
        ring
      rw [hcharge, hN] at hsep
      simpa only [X, Y, ← finiteWord_succ_eq_rows] using hsep

end TreeEdit.BinaryLower.FiniteTree

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.finiteWord_separation_of_half_children := @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.finiteWord_separation_of_half_children
