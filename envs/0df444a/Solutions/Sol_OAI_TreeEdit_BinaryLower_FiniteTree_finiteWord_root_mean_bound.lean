-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteTree.finiteWord_root_mean_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:53:59.931203+00:00
-- url     : https://prove2.me/submissions/beadbcfd-d86e-4a30-b615-473300bb6c8a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteWordL1Mean.lean:L39-L86
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteTree.finiteWord_root_mean_bound. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteActivity_finite_tree_l1_mean_bound
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_nodeWord_leaf_script
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_root_internal_supported_normalized_cost
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_word_sparse_detection

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

end TreeEdit.BinaryLower.FiniteTree

end

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteVectors ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Concrete vectors for the finite tree (finite-tree.tex, finite-vectors).
A prefix is represented by its depth and any full leaf path extending it.
All definitions ignore the unused tail of that representative. No primality
assumption is needed for the annihilation and recursive vector identities. -/

namespace TreeEdit.BinaryLower.FiniteVectors

open scoped BigOperators

variable {m k : ℕ}

lemma leafPeriod_pos (p : Fin k → Fin m → ℕ) (hp : ∀ q i, 0 < p q i) (a : Leaf m k) :
    0 < leafPeriod p a := by
  unfold leafPeriod
  apply Nat.mul_pos (by norm_num)
  apply Finset.prod_pos
  intro q hq
  exact hp q (a q)

end TreeEdit.BinaryLower.FiniteVectors

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

/-- Whole-coordinate averaging uses only integer multiples of the actual
word leaf vector, as in the pointwise inexpensive-leaf-translation lemma. -/
theorem wordLeafCoordinate_eq_val_zsmul (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (f : Fin k → Fin m)
    [NeZero (FiniteVectors.leafPeriod primes f)]
    (z : ZMod (FiniteVectors.leafPeriod primes f)) :
    wordLeafCoordinate primes f z = (z.val : ℤ) • wordW primes i₀ (List.ofFn f) := by
  have hz : (z.val : ℤ) • (1 : ZMod (FiniteVectors.leafPeriod primes f)) = z := by
    simp
  calc
    wordLeafCoordinate primes f z = wordLeafCoordinate primes f ((z.val : ℤ) • 1) :=
      congrArg _ hz.symm
    _ = (z.val : ℤ) • wordLeafCoordinate primes f 1 := map_zsmul _ _ _
    _ = (z.val : ℤ) • wordW primes i₀ (List.ofFn f) := by rw [wordLeafCoordinate_one primes i₀]

end TreeEdit.BinaryLower.FiniteTree

end

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.CheapTranslations ----
namespace OAI

/-!
# Inexpensive translations

Elementary unrestricted edit scripts give the translation estimates in
`lem:finite-cost`.
-/

namespace TreeEdit.BinaryLower.CheapTranslations

universe u v

variable {α : Type u}

theorem editDistance_le_script {x y : List α} {n : ℕ}
    (h : EditScript x y n) : ed x y ≤ n := by
  exact csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ h

end TreeEdit.BinaryLower.CheapTranslations

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteTreeConcreteCosts ----
namespace OAI

/-!
Concrete tagged cyclic-state versions of `lem:finite-cost`. The only input
about a translated vector is its actual coordinate support. In particular no
injectivity of the word map, period identity, or distortion hypothesis is used.
-/

namespace TreeEdit.BinaryLower.FiniteTree

theorem root_leaf_supported_script {m k : ℕ} (T : ℕ)
    (Q : Leaf m k → ℕ) (base ell : Leaf m k)
    (u : List (Fin m) → State Q) (z x : State Q)
    (hsupport : ∀ l : Leaf m k, l ≠ ell → z l = 0) :
    EditScript (nodeWord T (leafDecoder Q base) u k [] x)
      (nodeWord T (leafDecoder Q base) u k [] (x + z)) (T ^ k) := by
  have hout : ∀ r : List (Fin m), r.length = ell.val.length → r ≠ ell.val →
      ∀ y, leafDecoder Q base ([] ++ r) (y + z) = leafDecoder Q base ([] ++ r) y := by
    intro r hr hn y
    have hlen : r.length = k := hr.trans ell.property
    have hne : (⟨r, hlen⟩ : Leaf m k) ≠ ell := by
      intro he
      exact hn (congrArg Subtype.val he)
    apply (leafDecoder_eq_iff Q base r hlen (y + z) y).2
    simp only [Pi.add_apply, hsupport _ hne, add_zero]
  simpa only [ell.property] using
    nodeWord_leaf_script T (leafDecoder Q base) u ell.val [] z hout x

/-- The pointwise single-coordinate cost, for any value of the translation in
that cyclic coordinate and at every state. -/
theorem root_leaf_supported_cost {m k : ℕ} (T : ℕ)
    (Q : Leaf m k → ℕ) (base ell : Leaf m k)
    (u : List (Fin m) → State Q) (z x : State Q)
    (hsupport : ∀ l : Leaf m k, l ≠ ell → z l = 0) :
    ed (nodeWord T (leafDecoder Q base) u k [] x)
      (nodeWord T (leafDecoder Q base) u k [] (x + z)) ≤ T ^ k :=
  CheapTranslations.editDistance_le_script
    (root_leaf_supported_script T Q base ell u z x hsupport)

theorem root_leaf_supported_normalized_cost {m k : ℕ} (T : ℕ) (hm : 0 < m)
    (Q : Leaf m k → ℕ) (base ell : Leaf m k)
    (u : List (Fin m) → State Q) (z x : State Q)
    (hsupport : ∀ l : Leaf m k, l ≠ ell → z l = 0) :
    (ed (nodeWord T (leafDecoder Q base) u k [] x)
      (nodeWord T (leafDecoder Q base) u k [] (x + z)) : ℝ) ≤
      ((m * T : ℕ) : ℝ) ^ k / (m : ℝ) ^ k := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hb := root_leaf_supported_cost T Q base ell u z x hsupport
  have hn : (ed (nodeWord T (leafDecoder Q base) u k [] x)
      (nodeWord T (leafDecoder Q base) u k [] (x + z)) : ℝ) ≤ (T : ℝ) ^ k := by
    exact_mod_cast hb
  simpa only [Nat.cast_mul, mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hm0)]
    using hn

end TreeEdit.BinaryLower.FiniteTree

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteTreeCostTheorem ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# The finite tree’s pointwise translation estimates

The concrete `finiteWord` and cyclic-state vectors satisfy `lem:finite-cost`.
Coordinate support follows from the vector definitions.
-/

namespace TreeEdit.BinaryLower.FiniteTree

theorem wordU_off_prefix {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (q : List (Fin m)) (hq : q.length ≤ k)
    (l : Leaf m k) (hl : ¬ q.IsPrefix l.val) :
    wordU primes i₀ q l = 0 := by
  change FiniteVectors.u primes q.length (extendPrefix i₀ q) (leafEquiv m k l) = 0
  apply FiniteVectors.u_off_subtree
  intro ha
  have hp := (agrees_extendPrefix_iff i₀ q hq (leafEquiv m k l)).1 ha
  exact hl (by simpa only [ofFn_leafEquiv] using hp)

theorem wordW_leaf_other {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (ell l : Leaf m k) (hne : l ≠ ell) :
    wordW primes i₀ ell.val l = 0 := by
  change FiniteVectors.w primes ell.val.length (extendPrefix i₀ ell.val)
    (leafEquiv m k l) = 0
  rw [ell.property, extendPrefix_leaf i₀ ell.val ell.property]
  have hn : leafEquiv m k l ≠ leafEquiv m k ell := by
    intro he
    exact hne ((leafEquiv m k).injective he)
  simp only [FiniteVectors.w_leaf, ite_eq_right hn]

/-- First assertion of `lem:finite-cost`: every state and every integer
multiple of a leaf unit vector has edit cost at most `M/m^k`. -/
theorem finiteWord_leaf_translation_cost {m k : ℕ}
    (primes : Fin k → Fin m → ℕ) (i₀ : Fin m) (T : ℕ)
    (ell : Leaf m k) (t : ℤ) (x : State (wordPeriods primes)) :
    (ed (finiteWord primes i₀ T k [] x)
      (finiteWord primes i₀ T k [] (x + t • wordW primes i₀ ell.val)) : ℝ) ≤
      ((m * T : ℕ) : ℝ) ^ k / (m : ℝ) ^ k := by
  have hm : 0 < m := by have hi := i₀.isLt; omega
  apply root_leaf_supported_normalized_cost T hm (wordPeriods primes)
    ⟨List.replicate k i₀, by simp⟩ ell (wordU primes i₀)
  intro l hne
  simp only [Pi.smul_apply, wordW_leaf_other primes i₀ ell l hne, smul_zero]

/-- Equation `eq:finite-cost` with the concrete root word, actual cheap
vector, and exact source constants. It holds uniformly at every state and
also includes the harmless zero shift. -/
theorem finiteWord_node_translation_cost {m k : ℕ}
    (primes : Fin k → Fin m → ℕ) (i₀ : Fin m) (T : ℕ) (hT : 0 < T)
    (q : List (Fin m)) (hq : q.length < k)
    (s : ℕ) (hs : s ≤ T) (x : State (wordPeriods primes)) :
    (ed (finiteWord primes i₀ T k [] x)
      (finiteWord primes i₀ T k [] (x + s • wordU primes i₀ q)) : ℝ) ≤
      (2 * (s : ℝ) / T) * (((m * T : ℕ) : ℝ) ^ k / (m : ℝ) ^ q.length) := by
  have hm : 0 < m := by have hi := i₀.isLt; omega
  apply root_internal_supported_normalized_cost T hm hT (wordPeriods primes)
    ⟨List.replicate k i₀, by simp⟩ (wordU primes i₀) (k - (q.length + 1)) q
    (by omega) s hs
  exact wordU_off_prefix primes i₀ q hq.le

end TreeEdit.BinaryLower.FiniteTree

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteWordL1Mean ----
namespace OAI

/-!
# The actual finite word's averaged ℓ₁ displacement

This specializes the proved finite-group Fourier obstruction to the concrete
cyclic parameter space and recursive word evaluator. The only metric input is
that the chosen map into actual ℓ₁ does not expand ordinary edit distance.
-/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteTree

open Classical
open scoped BigOperators

/-- The leaf cyclic tests have the required pointwise cost for every map
which is nonexpanding on pairs of actual finite words. -/
theorem finiteWord_leaf_l1_cost {m k : ℕ}
    (p : Fin k → Fin m → ℕ) (i₀ : Fin m) (T : ℕ)
    (F : State (wordPeriods p) → RealL1)
    (hF : ∀ x y, ‖F x - F y‖ ≤
      (ed (finiteWord p i₀ T k [] x) (finiteWord p i₀ T k [] y) : ℝ))
    (a : Fin k → Fin m) [NeZero (FiniteVectors.leafPeriod p a)]
    (z : ZMod (FiniteVectors.leafPeriod p a)) (x : State (wordPeriods p)) :
    ‖F (x + wordLeafCoordinate p a z) - F x‖ ≤
      ((m * T : ℕ) : ℝ) ^ k / (m : ℝ) ^ k := by
  rw [norm_sub_rev]
  apply (hF x (x + wordLeafCoordinate p a z)).trans
  rw [wordLeafCoordinate_eq_val_zsmul p i₀]
  exact finiteWord_leaf_translation_cost p i₀ T
    ⟨List.ofFn a, List.length_ofFn⟩ z.val x

/-- The actual finite word satisfies the full Fourier root estimate. All
leaf costs and sparse-node tests are proved from its concrete construction. -/
theorem finiteWord_root_mean_bound {m k : ℕ}
    (p : Fin k → Fin m → ℕ) (i₀ : Fin m) (hk : 1 ≤ k)
    (hppos : ∀ q i, 0 < p q i) (hp : ∀ q i, p q i ≤ k ^ 5)
    (T : ℕ) (hT : 0 < T) (hJT : 4 * k ^ (10 * k) ≤ T)
    [Fintype (State (wordPeriods p))]
    (F : State (wordPeriods p) → RealL1)
    (hF : ∀ x y, ‖F x - F y‖ ≤
      (ed (finiteWord p i₀ T k [] x) (finiteWord p i₀ T k [] y) : ℝ)) :
    (𝔼 x : State (wordPeriods p), ‖F (x + wordW p i₀ []) - F x‖) ≤
      4 * ((k : ℝ) * ((2 * ((4 * k ^ (10 * k) : ℕ) : ℝ) / T) *
        ((m * T : ℕ) : ℝ) ^ k) +
        ((m * T : ℕ) : ℝ) ^ k / (2 * (k : ℝ) ^ k)) := by
  let : ∀ f : Fin k → Fin m, NeZero (FiniteVectors.leafPeriod p f) :=
    fun f => ⟨ne_of_gt (FiniteVectors.leafPeriod_pos p hppos f)⟩
  have hJpos : 0 < 4 * k ^ (10 * k) := by positivity
  let : Nonempty (Fin (4 * k ^ (10 * k))) := ⟨⟨0, hJpos⟩⟩
  let shift : FiniteActivity.InternalNode (Fin m) k → Fin (4 * k ^ (10 * k)) →
      State (wordPeriods p) := fun v s => (s.val + 1) • wordU p i₀ (List.ofFn v.2)
  have hm : m ≠ 0 := by have hi := i₀.isLt; omega
  apply FiniteActivity.finite_tree_l1_mean_bound m k k hm (by omega)
    (wordW p i₀) (FiniteVectors.leafPeriod p) (wordLeafCoordinate p)
    (fun f => (wordLeafCoordinate_one p i₀ f).symm) F shift
    (((m * T : ℕ) : ℝ) ^ k)
    ((2 * ((4 * k ^ (10 * k) : ℕ) : ℝ) / T) * ((m * T : ℕ) : ℝ) ^ k)
  · intro f z x
    exact finiteWord_leaf_l1_cost p i₀ T F hF f z x
  · intro v χ hv
    simpa only [Fintype.card_fin] using word_sparse_detection p i₀ hk hppos hp v χ hv
  · intro v s x
    have hs : s.val + 1 ≤ 4 * k ^ (10 * k) := Nat.succ_le_of_lt s.isLt
    have hsR : ((s.val + 1 : ℕ) : ℝ) ≤ ((4 * k ^ (10 * k) : ℕ) : ℝ) :=
      by exact_mod_cast hs
    have hcost := finiteWord_node_translation_cost p i₀ T hT (List.ofFn v.2)
      (by simp) (s.val + 1) (hs.trans hJT) x
    simp only [List.length_ofFn] at hcost
    rw [norm_sub_rev]
    apply (hF x (x + shift v s)).trans
    calc
      _ ≤ (2 * ((s.val + 1 : ℕ) : ℝ) / T) *
          (((m * T : ℕ) : ℝ) ^ k / (m : ℝ) ^ v.1.val) := hcost
      _ ≤ (2 * ((4 * k ^ (10 * k) : ℕ) : ℝ) / T) *
          (((m * T : ℕ) : ℝ) ^ k / (m : ℝ) ^ v.1.val) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsR (by norm_num)) (Nat.cast_nonneg T)
      _ = _ := by ring

end TreeEdit.BinaryLower.FiniteTree

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree
open Classical
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.finiteWord_root_mean_bound := @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.finiteWord_root_mean_bound
