-- Prove2me | solution 1 for OAI.Problem335.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:49:16.106987+00:00
-- url     : https://prove2.me/submissions/923fb7d3-eb21-4fc6-9d12-477889adbbd7

import Mathlib
import Definitions.Def_DepthFive
import Definitions.Def_OAIQWDF000
import Theorems.Thm_OAI_Problem335_complex_depth_five_lower_bound_of_eventual_second_trace

section
-- module Solutions.OAIQW_Problem335.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LowerParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer parameters for the lower-bound rank measure. -/
namespace Problem335.LowerParameters

noncomputable section

theorem s_le_sqrt (n : ℕ) : (s n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have h : (s n : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast s_le_nat_sqrt n
  exact h.trans Real.nat_sqrt_le_real_sqrt

theorem s_le_quarter {n : ℕ} (hn : 16 ≤ n) : (s n : ℝ) ≤ (n : ℝ) / 4 := by
  have hs := s_le_sqrt n
  have hroot : 4 ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    exact_mod_cast hn
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  nlinarith

theorem three_mul_n_le_eight_mul_k {n : ℕ} (hn : 16 ≤ n) :
    3 * n ≤ 8 * k n := by
  have hs := s_le_quarter hn
  have hk : 2 * (k n : ℝ) + (s n : ℝ) = (n : ℝ) := by
    exact_mod_cast two_mul_k_add_s n
  have h : 3 * (n : ℝ) ≤ 8 * (k n : ℝ) := by linarith
  exact_mod_cast h

theorem rho_pos {n : ℕ} (hn : 4 ≤ n) : 0 < rho n := by
  unfold rho
  apply div_pos <;> exact_mod_cast (by first | exact k_pos hn | exact m_pos hn)

theorem m_le_n (n : ℕ) : m n ≤ n := by
  have := k_add_m n
  omega

theorem n_le_two_mul_m (n : ℕ) : n ≤ 2 * m n := by
  have := two_mul_m n
  omega

theorem one_sub_rho {n : ℕ} (hn : 4 ≤ n) :
    1 - rho n = (s n : ℝ) / (m n : ℝ) := by
  have hm : (m n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (m_pos hn))
  have h : (m n : ℝ) = (k n : ℝ) + (s n : ℝ) := by
    exact_mod_cast m_eq_k_add_s n
  unfold rho
  field_simp
  linarith

theorem u_pos {n : ℕ} (hn : 4 ≤ n) : 0 < u n := by
  unfold u
  exact Nat.mul_pos (m_pos hn) (Nat.pow_pos (by omega))

end
end Problem335.LowerParameters

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BalancedSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem335
namespace BalancedSchedule

lemma chunkLength_pos (k s i : ℕ) : 0 < chunkLength k s i := by
  unfold chunkLength
  omega

lemma discrepancy_wordPrefix_eq_mod {k : ℕ} (hk : 0 < k) (s r : ℕ) :
    discrepancy k s (wordPrefix k s r) = ((r * s % k : ℕ) : ℝ) / (k + s) := by
  simp only [discrepancy, count_true_wordPrefix, count_false_wordPrefix, Nat.cast_add]
  have hd := Nat.mod_add_div (r * s) k
  have hd' : ((r * s % k : ℕ) : ℝ) + (k : ℝ) * ((r * s / k : ℕ) : ℝ) =
      (r : ℝ) * s := by exact_mod_cast hd
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hks : (0 : ℝ) < k + s := by positivity
  unfold rho
  field_simp
  nlinarith

lemma discrepancy_wordPrefix_nonneg {k : ℕ} (hk : 0 < k) (s r : ℕ) :
    0 ≤ discrepancy k s (wordPrefix k s r) := by
  rw [discrepancy_wordPrefix_eq_mod hk]
  positivity

lemma discrepancy_wordPrefix_lt_rho {k : ℕ} (hk : 0 < k) (s r : ℕ) :
    discrepancy k s (wordPrefix k s r) < rho k s := by
  rw [discrepancy_wordPrefix_eq_mod hk]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hks : (0 : ℝ) < k + s := by positivity
  apply (div_lt_div_iff_of_pos_right hks).2
  exact_mod_cast Nat.mod_lt (r * s) hk

lemma take_chunk_discrepancy (k s i p : ℕ) (hp : 0 < p) :
    discrepancy k s ((chunk k s i).take p) =
      1 - rho k s * (min (p - 1) (chunkLength k s i) : ℕ) := by
  simp [chunk, List.take_cons hp, discrepancy, List.count_replicate]

/-- Every prefix of the balanced schedule stays in a strip of width `1+ρ`. -/
lemma take_wordPrefix_discrepancy_bounds {k : ℕ} (hk : 0 < k) (s r p : ℕ) :
    0 ≤ discrepancy k s ((wordPrefix k s r).take p) ∧
      discrepancy k s ((wordPrefix k s r).take p) < 1 + rho k s := by
  have hrho : 0 ≤ rho k s := by unfold rho; positivity
  induction r with
  | zero => simp [wordPrefix]; positivity
  | succ r ih =>
    change 0 ≤ discrepancy k s ((wordPrefix k s r ++ chunk k s r).take p) ∧
      discrepancy k s ((wordPrefix k s r ++ chunk k s r).take p) < 1 + rho k s
    by_cases hp : p ≤ (wordPrefix k s r).length
    · simpa only [List.take_append_of_le_length hp] using ih
    · have hlt : (wordPrefix k s r).length < p := by omega
      rw [List.take_append, List.take_of_length_le hlt.le, discrepancy_append]
      rw [take_chunk_discrepancy k s r _ (by omega)]
      have hmin : ((min (p - (wordPrefix k s r).length - 1) (chunkLength k s r) : ℕ) : ℝ) ≤
          (chunkLength k s r : ℝ) := by exact_mod_cast Nat.min_le_right _ _
      have hmul := mul_le_mul_of_nonneg_left hmin hrho
      have hnonneg := discrepancy_wordPrefix_nonneg hk s (r + 1)
      simp only [wordPrefix, discrepancy_append, discrepancy_chunk] at hnonneg
      have hupper := discrepancy_wordPrefix_lt_rho hk s r
      have hprod : 0 ≤ rho k s *
          ((min (p - (wordPrefix k s r).length - 1) (chunkLength k s r) : ℕ) : ℝ) := by positivity
      constructor <;> linarith

/-- Every interval of layers has discrepancy strictly less than `1+ρ`. -/
lemma interval_discrepancy_lt {k : ℕ} (hk : 0 < k) (s r a len : ℕ) :
    discrepancy k s (((wordPrefix k s r).drop a).take len) < 1 + rho k s := by
  have h₁ := (take_wordPrefix_discrepancy_bounds hk s r a).1
  have h₂ := (take_wordPrefix_discrepancy_bounds hk s r (a + len)).2
  rw [List.take_add, discrepancy_append] at h₂
  linarith

lemma infix_discrepancy_lt {k : ℕ} (hk : 0 < k) (s r : ℕ) {w : List Bool}
    (hw : w <:+: wordPrefix k s r) : discrepancy k s w < 1 + rho k s := by
  rcases hw with ⟨l, z, heq⟩
  have h := interval_discrepancy_lt hk s r l.length w.length
  rw [← heq, List.append_assoc, List.drop_left, List.take_left] at h
  exact h

@[simp] lemma discrepancy_word {k : ℕ} (hk : 0 < k) (s : ℕ) :
    discrepancy k s (word k s) = 0 := by
  rw [word, discrepancy_wordPrefix_eq_mod hk]
  simp

@[simp] lemma chunk_last (k s i : ℕ) : (chunk k s i).getLast? = some false := by
  have hp := chunkLength_pos k s i
  simp [chunk, List.getLast?_cons, List.getLast?_replicate, Nat.ne_of_gt hp]

lemma wordPrefix_head {r : ℕ} (hr : 0 < r) (k s : ℕ) :
    (wordPrefix k s r).head? = some true := by
  induction r with
  | zero => omega
  | succ r ih =>
    cases r with
    | zero => simp [wordPrefix]
    | succ r =>
      change (wordPrefix k s (r + 1) ++ chunk k s (r + 1)).head? = some true
      rw [List.head?_append, ih (by omega)]
      rfl

lemma wordPrefix_last {r : ℕ} (hr : 0 < r) (k s : ℕ) :
    (wordPrefix k s r).getLast? = some false := by
  cases r with
  | zero => omega
  | succ r => simp [wordPrefix, List.getLast?_append]

lemma replicate_no_adjacent_V (d : ℕ) :
    (List.replicate d false).IsChain (fun a b => a = false ∨ b = false) := by
  rw [List.isChain_iff_getElem]
  simp

lemma chunk_no_adjacent_V (k s i : ℕ) :
    (chunk k s i).IsChain (fun a b => a = false ∨ b = false) := by
  unfold chunk
  apply (List.isChain_cons).2
  constructor
  · intro y hy
    right
    exact List.eq_of_mem_replicate (List.mem_of_mem_head? hy)
  · exact replicate_no_adjacent_V _

/-- No two `V` layers are adjacent, a key independence property of the schedule. -/
lemma wordPrefix_no_adjacent_V (k s r : ℕ) :
    (wordPrefix k s r).IsChain (fun a b => a = false ∨ b = false) := by
  induction r with
  | zero => simp [wordPrefix]
  | succ r ih =>
    apply ih.append (chunk_no_adjacent_V k s r)
    intro x hx y hy
    cases r with
    | zero => simp [wordPrefix] at hx
    | succ r =>
      left
      have hlast := wordPrefix_last (r := r + 1) (by omega) k s
      rw [hlast] at hx
      simpa [eq_comm] using hx

lemma word_no_adjacent_V (k s : ℕ) :
    (word k s).IsChain (fun a b => a = false ∨ b = false) :=
  wordPrefix_no_adjacent_V k s k

lemma internalEnds_disjoint_of_not_adjacent {n : ℕ} {i j : Fin n}
    (hne : i ≠ j) (hij : ¬ adjacent i j) :
    Disjoint (internalEnds i) (internalEnds j) := by
  apply Finset.disjoint_left.2
  intro v hvi hvj
  have hi := (Finset.mem_filter.mp hvi).2
  have hj := (Finset.mem_filter.mp hvj).2
  have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
  unfold adjacent at hij
  omega

end BalancedSchedule
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ScheduleEnds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335.BalancedSchedule

lemma adjacent_left_right {n : ℕ} (v : Fin (n - 1)) :
    adjacent (leftLayer v) (rightLayer v) := Or.inl rfl

lemma internalEnds_cases {n : ℕ} {i : Fin n} {v : Fin (n - 1)}
    (hv : v ∈ internalEnds i) : leftLayer v = i ∨ rightLayer v = i := by
  rcases (Finset.mem_filter.mp hv).2 with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

end Problem335.BalancedSchedule

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ScheduleInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335.BalancedSchedule

lemma card_internalEnds_eq_two {n : ℕ} (i : Fin n) (hfirst : 0 < i.val)
    (hlast : i.val + 1 < n) : (internalEnds i).card = 2 := by
  let l : Fin (n - 1) := ⟨i.val - 1, by omega⟩
  let r : Fin (n - 1) := ⟨i.val, by omega⟩
  apply Finset.card_eq_two.mpr
  refine ⟨l, r, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    dsimp [l, r] at hv
    omega
  · ext v
    simp only [internalEnds, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inr (Fin.ext h)
      · left
        apply Fin.ext
        dsimp [l]
        omega
    · rintro (rfl | rfl)
      · dsimp [l]
        omega
      · exact Or.inl rfl

end Problem335.BalancedSchedule

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LowerSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335.LowerParameters

lemma balancedLayer_ofFn {n : ℕ} (hn : 4 ≤ n) :
    List.ofFn (balancedLayer hn) = balancedWord n := by
  apply List.ext_getElem
  · simp [balancedWord_length hn]
  · intro i h₁ h₂
    simp [balancedLayer]

lemma balancedLayer_card_true {n : ℕ} (hn : 4 ≤ n) :
    (Finset.univ.filter (fun i => balancedLayer hn i = true)).card = k n := by
  let vec : List.Vector Bool n := ⟨balancedWord n, balancedWord_length hn⟩
  have h := Fin.card_filter_univ_eq_vector_get_eq_count true vec
  change (Finset.univ.filter (fun i => balancedLayer hn i = true)).card =
    (balancedWord n).count true at h
  simpa [balancedWord] using h

lemma balancedLayer_card_false {n : ℕ} (hn : 4 ≤ n) :
    (Finset.univ.filter (fun i => balancedLayer hn i = false)).card = m n := by
  let vec : List.Vector Bool n := ⟨balancedWord n, balancedWord_length hn⟩
  have h := Fin.card_filter_univ_eq_vector_get_eq_count false vec
  change (Finset.univ.filter (fun i => balancedLayer hn i = false)).card =
    (balancedWord n).count false at h
  simpa [balancedWord, BalancedSchedule.word_count_false (k_pos hn), m_eq_k_add_s] using h

lemma balancedSchedule_rho (n : ℕ) : BalancedSchedule.rho (k n) (s n) = rho n := by
  simp only [BalancedSchedule.rho, rho, m_eq_k_add_s, Nat.cast_add]

lemma balancedLayer_infix_discrepancy {n : ℕ} (hn : 4 ≤ n) (b : List (Fin n))
    (hb : b <:+: List.ofFn id) :
    (b.countP (balancedLayer hn) : ℝ) - rho n *
      (b.countP (fun i => !balancedLayer hn i) : ℝ) < 1 + rho n := by
  have hmap := hb.map (balancedLayer hn)
  have heq : (List.ofFn (id : Fin n → Fin n)).map (balancedLayer hn) = balancedWord n := by
    rw [List.map_ofFn]
    exact balancedLayer_ofFn hn
  rw [heq] at hmap
  have h := BalancedSchedule.infix_discrepancy_lt (k_pos hn) (s n) (k n) hmap
  simpa [BalancedSchedule.discrepancy, List.count_eq_countP, List.countP_map,
    Function.comp_def, balancedSchedule_rho] using h

lemma balancedLayer_no_adjacent {n : ℕ} (hn : 4 ≤ n) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    balancedLayer hn i = false ∨ balancedLayer hn j = false := by
  have hlt : i.val + 1 < (balancedWord n).length := by
    rw [balancedWord_length hn, hij]
    exact j.isLt
  have h := List.isChain_iff_getElem.mp (BalancedSchedule.word_no_adjacent_V (k n) (s n))
    i.val hlt
  simpa only [balancedLayer, balancedWord, List.get_eq_getElem, hij] using h

lemma balancedLayer_independent {n : ℕ} (hn : 4 ≤ n) {i j : Fin n}
    (hi : balancedLayer hn i = true) (hj : balancedLayer hn j = true) :
    ¬ BalancedSchedule.adjacent i j := by
  rintro (hij | hji)
  · have h := balancedLayer_no_adjacent hn i j hij
    simp [hi, hj] at h
  · have h := balancedLayer_no_adjacent hn j i hji
    simp [hi, hj] at h

lemma balancedLayer_first {n : ℕ} (hn : 4 ≤ n) :
    balancedLayer hn ⟨0, by omega⟩ = true := by
  have h := BalancedSchedule.wordPrefix_head (r := k n) (k_pos hn) (k n) (s n)
  change (balancedWord n).head? = some true at h
  have hlen : 0 < (balancedWord n).length := by rw [balancedWord_length hn]; omega
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen] at h
  simpa only [balancedLayer, List.get_eq_getElem] using Option.some.inj h

lemma balancedLayer_final {n : ℕ} (hn : 4 ≤ n) :
    balancedLayer hn ⟨n - 1, by omega⟩ = false := by
  have h := BalancedSchedule.wordPrefix_last (r := k n) (k_pos hn) (k n) (s n)
  change (balancedWord n).getLast? = some false at h
  have hlen : (balancedWord n).length - 1 < (balancedWord n).length := by
    rw [balancedWord_length hn]; omega
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlen] at h
  simpa only [balancedLayer, List.get_eq_getElem, balancedWord_length hn] using Option.some.inj h

/-- The actual V-layer coincidence events use pairwise disjoint vertex coordinates. -/
lemma balancedLayer_internalEnds_disjoint {n : ℕ} (hn : 4 ≤ n) {i j : Fin n}
    (hi : balancedLayer hn i = true) (hj : balancedLayer hn j = true) (hne : i ≠ j) :
    Disjoint (BalancedSchedule.internalEnds i) (BalancedSchedule.internalEnds j) :=
  BalancedSchedule.internalEnds_disjoint_of_not_adjacent hne (balancedLayer_independent hn hi hj)

lemma balancedVariable_card_true {n : ℕ} (hn : 4 ≤ n) :
    Fintype.card {x : Fin n × Fin n × Fin n // balancedLayer hn x.1 = true} = v n := by
  classical
  rw [Fintype.card_congr (layerVariableEquiv (balancedLayer hn) true)]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype]
  rw [balancedLayer_card_true]
  simp [v, pow_two]

lemma balancedVariable_card_false {n : ℕ} (hn : 4 ≤ n) :
    Fintype.card {x : Fin n × Fin n × Fin n // balancedLayer hn x.1 = false} = u n := by
  classical
  rw [Fintype.card_congr (layerVariableEquiv (balancedLayer hn) false)]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype]
  rw [balancedLayer_card_false]
  simp [u, pow_two]

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.IsolatedFlip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical removal of isolated positions in an independent set.

The value `true` denotes the D type from the manuscript.  The set `S`
contains the positions allowed to flip (interior V layers), and `R a b`
means that `b` is a neighbor of `a`.  Independence is the only property
of the path graph needed for the fiber calculation.
-/

noncomputable section

open scoped BigOperators

namespace Problem335.IsolatedFlip

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem flip_idempotent {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S) (w : α → Bool) :
    flip S R (flip S R w) = flip S R w := by
  classical
  funext a
  simp only [flip, eligible_flip hS]
  split_ifs <;> rfl

/-! Each fiber of the canonicalization is exactly a powerset. -/

theorem fiber_sum_pow {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    (w : α → Bool) (hw : flip S R w = w)
    {K : Type*} [CommSemiring K] (c : K) :
    (∑ z : {z : α → Bool // flip S R z = w},
      c ^ (removed S R z).card) = (1 + c) ^ (eligible S R w).card := by
  classical
  calc
    _ = ∑ T : {T : Finset α // T ⊆ eligible S R w}, c ^ T.val.card :=
      Fintype.sum_equiv (fiberEquiv hS w hw) _ _ (fun _ => rfl)
    _ = ∑ T ∈ (eligible S R w).powerset, c ^ T.card :=
      (Finset.sum_subtype (p := fun T : Finset α => T ⊆ eligible S R w)
        (eligible S R w).powerset (fun _ => Finset.mem_powerset)
        (fun T => c ^ T.card)).symm
    _ = _ := by
      simpa [Finset.prod_const, add_comm] using
        (Finset.prod_add_one (f := fun _ : α => c) (eligible S R w)).symm

theorem fiber_weight_sum {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    (w : α → Bool) (hw : flip S R w = w)
    {K : Type*} [CommSemiring K] (c : K) (W : (α → Bool) → K)
    (hW : ∀ z, flip S R z = w → W z = W w * c ^ (removed S R z).card) :
    (∑ z : {z : α → Bool // flip S R z = w}, W z) =
      W w * (1 + c) ^ (eligible S R w).card := by
  classical
  calc
    _ = ∑ z : {z : α → Bool // flip S R z = w},
        W w * c ^ (removed S R z).card :=
      Finset.sum_congr rfl (fun z _ => hW z z.property)
    _ = W w * ∑ z : {z : α → Bool // flip S R z = w},
        c ^ (removed S R z).card := (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [fiber_sum_pow hS w hw]

theorem total_weight_sum {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    {K : Type*} [CommSemiring K] (c : K) (W : (α → Bool) → K)
    (hW : ∀ z, W z = W (flip S R z) * c ^ (removed S R z).card) :
    (∑ z, W z) = ∑ w ∈ Finset.univ.filter (fun w => flip S R w = w),
      W w * (1 + c) ^ (eligible S R w).card := by
  classical
  rw [Finset.sum_filter]
  calc
    _ = ∑ w, ∑ z : {z : α → Bool // flip S R z = w}, W z :=
      (Fintype.sum_fiberwise (flip S R) W).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : flip S R w = w
      · rw [ite_eq_left hw]
        apply fiber_weight_sum hS w hw c W
        intro z hz
        simpa only [hz] using hW z
      · rw [ite_eq_right hw]
        have hempty : IsEmpty {z : α → Bool // flip S R z = w} := by
          refine ⟨fun z => hw ?_⟩
          exact (congrArg (flip S R) z.property.symm).trans
            ((flip_idempotent hS z).trans z.property)
        let := hempty
        simp

theorem correction_removal {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    (c : ℝ) (hc : 0 ≤ c) (W : (α → Bool) → ℝ)
    (hWnonneg : ∀ z, 0 ≤ W z)
    (hW : ∀ z, W z = W (flip S R z) * c ^ (removed S R z).card) :
    (∑ z, W z) ≤ (1 + c) ^ S.card *
      ∑ w ∈ Finset.univ.filter (fun w => flip S R w = w), W w := by
  classical
  rw [total_weight_sum hS c W hW, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _
  rw [mul_comm ((1 + c) ^ S.card)]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + c)
      (Finset.card_le_card (eligible_subset S R w))) (hWnonneg w)

end Problem335.IsolatedFlip

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.SwitchRestoration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem335.SwitchRestoration

variable {ι : Type*} [DecidableEq ι]

private theorem edge_switch_restore (S : Finset ι) (y : ι → Bool) (a b : ι)
    (hnear : a ∈ S ∨ b ∈ S → y a = true ∧ y b = true)
    (hind : ¬ (a ∈ S ∧ b ∈ S)) :
    (if (if a ∈ S then false else y a) ≠ (if b ∈ S then false else y b) then 1 else 0) =
      (if y a ≠ y b then 1 else 0) +
        (if a ∈ S then 1 else 0) + (if b ∈ S then 1 else 0) := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · exact False.elim (hind ⟨ha, hb⟩)
  · obtain ⟨hya, hyb⟩ := hnear (Or.inl ha)
    simp [ha, hb, hya, hyb]
  · obtain ⟨hya, hyb⟩ := hnear (Or.inr hb)
    simp [ha, hb, hya, hyb]
  · simp [ha, hb]

/-- Restoring an independent subset of all-true neighborhoods creates one switch per incident edge. -/
theorem switchCount_restore_eq (edges : Finset (ι × ι)) (S : Finset ι) (y : ι → Bool)
    (hnear : ∀ e ∈ edges, e.1 ∈ S ∨ e.2 ∈ S → y e.1 = true ∧ y e.2 = true)
    (hind : ∀ e ∈ edges, ¬ (e.1 ∈ S ∧ e.2 ∈ S)) :
    switchCount edges (fun i => if i ∈ S then false else y i) =
      switchCount edges y + ∑ i ∈ S, endpointDegree edges i := by
  unfold switchCount endpointDegree
  rw [Finset.sum_comm (s := S) (t := edges)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_add_distrib]
  have ha : (∑ i ∈ S, if e.1 = i then 1 else 0) = if e.1 ∈ S then 1 else 0 := by
    simp [eq_comm]
  have hb : (∑ i ∈ S, if e.2 = i then 1 else 0) = if e.2 ∈ S then 1 else 0 := by
    simp [eq_comm]
  rw [ha, hb]
  simpa [Nat.add_assoc] using edge_switch_restore S y e.1 e.2 (hnear e he) (hind e he)

/-- Every restored interior vertex of a path creates exactly two switches. -/
theorem switchCount_restore_eq_add_twice_card
    (edges : Finset (ι × ι)) (S : Finset ι) (y : ι → Bool)
    (hnear : ∀ e ∈ edges, e.1 ∈ S ∨ e.2 ∈ S → y e.1 = true ∧ y e.2 = true)
    (hind : ∀ e ∈ edges, ¬ (e.1 ∈ S ∧ e.2 ∈ S))
    (hdegree : ∀ i ∈ S, endpointDegree edges i = 2) :
    switchCount edges (fun i => if i ∈ S then false else y i) =
      switchCount edges y + 2 * S.card := by
  rw [switchCount_restore_eq edges S y hnear hind]
  congr 1
  calc
    ∑ i ∈ S, endpointDegree edges i = ∑ _i ∈ S, 2 :=
      Finset.sum_congr rfl hdegree
    _ = 2 * S.card := by simp [Nat.mul_comm]


theorem path_edge_injective (n : ℕ) :
    Function.Injective (fun i : Fin n => (i.castSucc, i.succ)) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun e : Fin (n + 1) × Fin (n + 1) => e.1.val) h

/-- This switch count agrees with the usual adjacent-position sum. -/
theorem switchCount_pathEdges (n : ℕ) (w : Fin (n + 1) → Bool) :
    switchCount (pathEdges n) w =
      ∑ i : Fin n, if w i.castSucc ≠ w i.succ then 1 else 0 := by
  unfold switchCount pathEdges
  rw [Finset.sum_image]
  exact fun i hi j hj h => path_edge_injective n h

/-- Restoring false symbols removes exactly the chosen true symbols. -/
theorem trueVertices_restore_eq_sdiff (V S : Finset ι) (y : ι → Bool) :
    (V.filter fun i => (if i ∈ S then false else y i) = true) =
      (V.filter fun i => y i = true) \ S := by
  ext i
  by_cases hi : i ∈ S <;> simp [hi, and_comm]

/-- Cardinal form without truncated subtraction, suitable for exponent arithmetic. -/
theorem trueVertices_restore_card_add (V S : Finset ι) (y : ι → Bool)
    (hS : S ⊆ V) (hy : ∀ i ∈ S, y i = true) :
    (V.filter fun i => (if i ∈ S then false else y i) = true).card + S.card =
      (V.filter fun i => y i = true).card := by
  rw [trueVertices_restore_eq_sdiff]
  apply Finset.card_sdiff_add_card_eq_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨hS hi, hy i hi⟩

end Problem335.SwitchRestoration

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.IsolatedWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.IsolatedWeight

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restoring any subset of an independent V set does not change the
neighbors of any V position. Endpoints are allowed in V. -/
theorem falseNeighbors_unset {V T : Finset ι} {R : ι → ι → Prop}
    (hT : T ⊆ V) (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (w : ι → Bool) {i : ι} (hi : i ∈ V) :
    falseNeighbors R (IsolatedFlip.unset w T) i = falseNeighbors R w i := by
  classical
  ext j
  by_cases hr : R i j
  · have hj : j ∉ T := fun ht => hV i hi j hr (hT ht)
    simp [falseNeighbors, IsolatedFlip.unset, hr, hj]
  · simp [falseNeighbors, hr]

omit [DecidableEq ι] in
theorem falseNeighbors_eq_empty {R : ι → ι → Prop} {w : ι → Bool} {i : ι}
    (h : ∀ j, R i j → w j = true) : falseNeighbors R w i = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have hh := Finset.mem_filter.mp hj
  have heq := h j hh.2.1
  simp only [heq, Bool.true_eq_false] at hh
  exact hh.2.2

omit [Fintype ι] in
/-- The normal V positions after restoration consist of the old normal
positions together with the restored subset. -/
theorem falseVertices_unset {V T : Finset ι} (hT : T ⊆ V)
    (w : ι → Bool) :
    (V.filter fun i => IsolatedFlip.unset w T i = false) =
      (V.filter fun i => w i = false) ∪ T := by
  classical
  ext i
  by_cases hi : i ∈ T
  · simp [IsolatedFlip.unset, hi, hT hi]
  · simp [IsolatedFlip.unset, hi]

omit [Fintype ι] [DecidableEq ι] in
theorem falseVertices_disjoint {V T : Finset ι} (w : ι → Bool)
    (hw : ∀ i ∈ T, w i = true) :
    Disjoint (V.filter fun i => w i = false) T := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi ht
  have hf := (Finset.mem_filter.mp hi).2
  have ht := hw i ht
  simp only [ht, Bool.true_eq_false] at hf

/-- The exact local correction-product factor in the isolated-position flip.
Every restored position has no normal neighbors, and hence contributes `1+A`. -/
theorem correction_unset {V T : Finset ι} {R : ι → ι → Prop}
    (hT : T ⊆ V) (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (w : ι → Bool) (hw : ∀ i ∈ T, w i = true)
    (hnear : ∀ i ∈ T, ∀ j, R i j → w j = true) (A x : ℝ) :
    correction V R A x (IsolatedFlip.unset w T) =
      correction V R A x w * (1 + A) ^ T.card := by
  classical
  unfold correction
  rw [falseVertices_unset hT w, Finset.prod_union (falseVertices_disjoint w hw)]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [falseNeighbors_unset hT hV w (Finset.mem_filter.mp hi).1]
  · calc
      _ = ∏ _i ∈ T, (1 + A) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [falseNeighbors_unset hT hV w (hT hi),
          falseNeighbors_eq_empty (hnear i hi)]
        simp
      _ = (1 + A) ^ T.card := by simp

/-- True positions in the complementary variable group are unchanged. -/
theorem complement_trueVertices_unset {V T : Finset ι} (hT : T ⊆ V)
    (w : ι → Bool) :
    ((Finset.univ \ V).filter fun i => IsolatedFlip.unset w T i = true) =
      ((Finset.univ \ V).filter fun i => w i = true) := by
  classical
  ext i
  by_cases hi : i ∈ V
  · simp [hi]
  · have hit : i ∉ T := fun ht => hi (hT ht)
    simp [IsolatedFlip.unset, hi, hit]

/-- Exact isolated-flip weight identity given the switch-count increment.
The switch increment is supplied by `switchCount_restore_eq_add_twice_card`.
No bound or positivity is needed except nonvanishing of the D-layer weight. -/
theorem weight_unset {edges : Finset (ι × ι)} {V T : Finset ι}
    {R : ι → ι → Prop} (hT : T ⊆ V)
    (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (w : ι → Bool) (hw : ∀ i ∈ T, w i = true)
    (hnear : ∀ i ∈ T, ∀ j, R i j → w j = true)
    (hswitch : SwitchRestoration.switchCount edges (IsolatedFlip.unset w T) =
      SwitchRestoration.switchCount edges w + 2 * T.card)
    {A : ℝ} (hA : A ≠ 0) (B x : ℝ) :
    weight edges V R A B x (IsolatedFlip.unset w T) =
      weight edges V R A B x w * (x ^ 2 * (1 + A) / A) ^ T.card := by
  classical
  have hcount := SwitchRestoration.trueVertices_restore_card_add V T w hT hw
  change (V.filter fun i => IsolatedFlip.unset w T i = true).card + T.card =
      (V.filter fun i => w i = true).card at hcount
  unfold weight
  rw [hswitch, complement_trueVertices_unset hT w,
    correction_unset hT hV w hw hnear A x, ← hcount]
  simp only [pow_add, pow_mul, mul_pow, div_pow]
  field_simp

/-- The isolated-flip identity for the actual word weight. Only interior
positions (of edge degree two) may flip, while V may also contain endpoints. -/
theorem weight_flip {edges : Finset (ι × ι)} {V S : Finset ι}
    {R : ι → ι → Prop} (hS : S ⊆ V)
    (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (hR : ∀ e ∈ edges, R e.1 e.2 ∧ R e.2 e.1)
    (hdegree : ∀ i ∈ S, SwitchRestoration.endpointDegree edges i = 2)
    {A : ℝ} (hA : A ≠ 0) (B x : ℝ) (w : ι → Bool) :
    weight edges V R A B x w =
      weight edges V R A B x (IsolatedFlip.flip S R w) *
        (x ^ 2 * (1 + A) / A) ^ (IsolatedFlip.removed S R w).card := by
  classical
  let T := IsolatedFlip.removed S R w
  let y := IsolatedFlip.flip S R w
  have hTe : T ⊆ IsolatedFlip.eligible S R w := IsolatedFlip.removed_subset S R w
  have hTS : T ⊆ S := hTe.trans (IsolatedFlip.eligible_subset S R w)
  have hTV : T ⊆ V := hTS.trans hS
  have hy : ∀ i ∈ T, y i = true := by
    intro i hi
    simp only [y, IsolatedFlip.flip, ite_eq_left (hTe hi)]
  have hnear : ∀ i ∈ T, ∀ j, R i j → y j = true := by
    intro i hi j hij
    have hwj := (IsolatedFlip.mem_eligible.mp (hTe hi)).2 j hij
    simp [y, IsolatedFlip.flip, hwj]
  have hsw : SwitchRestoration.switchCount edges (IsolatedFlip.unset y T) =
      SwitchRestoration.switchCount edges y + 2 * T.card := by
    apply SwitchRestoration.switchCount_restore_eq_add_twice_card
    · intro e he h
      rcases h with h | h
      · exact ⟨hy _ h, hnear _ h _ (hR e he).1⟩
      · exact ⟨hnear _ h _ (hR e he).2, hy _ h⟩
    · intro e he h
      exact hV e.1 (hTV h.1) e.2 (hR e he).1 (hTV h.2)
    · intro i hi
      exact hdegree i (hTS hi)
  have h := weight_unset hTV hV y hy hnear hsw hA B x
  simpa only [y, T, IsolatedFlip.unset_flip_removed] using h

/-- Nonnegative parameters give a nonnegative word weight. -/
theorem weight_nonneg (edges : Finset (ι × ι)) (V : Finset ι)
    (R : ι → ι → Prop) {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x)
    (w : ι → Bool) : 0 ≤ weight edges V R A B x w := by
  classical
  unfold weight correction
  positivity

/-- A normal position in the flip set of a fixed word has at least one
normal neighbor: otherwise the canonical flip would change it. -/
theorem falseNeighbors_card_pos_of_fixed {S : Finset ι} {R : ι → ι → Prop}
    {w : ι → Bool} (hw : IsolatedFlip.flip S R w = w)
    {i : ι} (hi : i ∈ S) (hwi : w i = false) :
    0 < (falseNeighbors R w i).card := by
  classical
  have hn : ¬ ∀ j, R i j → w j = true := by
    intro h
    have he : i ∈ IsolatedFlip.eligible S R w := IsolatedFlip.mem_eligible.mpr ⟨hi, h⟩
    have hh := congrFun hw i
    simp [IsolatedFlip.flip, he, hwi] at hh
  push Not at hn
  obtain ⟨j, hij, hj⟩ := hn
  have hwj : w j = false := by cases h : w j <;> simp_all
  exact Finset.card_pos.mpr ⟨j, by simp [falseNeighbors, hij, hwj]⟩

/-- The coincidence correction of a word with no isolated eligible position.
The exceptional positions `V \ S` include the external endpoint. -/
theorem correction_le_of_fixed {V S : Finset ι} {R : ι → ι → Prop}
    (hS : S ⊆ V) {w : ι → Bool} (hw : IsolatedFlip.flip S R w = w)
    {A x : ℝ} (hA : 0 ≤ A) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    correction V R A x w ≤
      (1 + A * x) ^ S.card * (1 + A) ^ (V \ S).card := by
  classical
  unfold correction
  rw [Finset.prod_filter]
  calc
    _ ≤ ∏ i ∈ V, if i ∈ S then 1 + A * x else 1 + A := by
      apply Finset.prod_le_prod
      · intro i hi
        split_ifs <;> positivity
      · intro i hi
        by_cases his : i ∈ S <;> by_cases hwi : w i = false
        · simp only [ite_eq_left his, ite_eq_left hwi]
          have hc := falseNeighbors_card_pos_of_fixed hw his hwi
          have hp : x ^ (falseNeighbors R w i).card ≤ x := by
            simpa using pow_le_pow_of_le_one hx hx1 (show 1 ≤ (falseNeighbors R w i).card by omega)
          linarith [mul_le_mul_of_nonneg_left hp hA]
        · simp only [ite_eq_left his, ite_eq_right hwi]
          nlinarith [mul_nonneg hA hx]
        · simp only [ite_eq_right his, ite_eq_left hwi]
          have hp : x ^ (falseNeighbors R w i).card ≤ 1 := pow_le_one₀ hx hx1
          nlinarith
        · simp only [ite_eq_right his, ite_eq_right hwi]
          linarith
    _ = (1 + A * x) ^ S.card * (1 + A) ^ (V \ S).card := by
      rw [Finset.prod_ite]
      have hmem : V.filter (fun i => i ∈ S) = S := by
        ext i
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
      have hnot : V.filter (fun i => ¬ i ∈ S) = V \ S := by
        ext i
        simp
      rw [hmem, hnot]
      simp

/-- With at most one exceptional V endpoint, the fixed-word correction has
the exact uniform bound used in the manuscript. -/
theorem correction_le_endpoint_bound {V S : Finset ι} {R : ι → ι → Prop}
    (hS : S ⊆ V) (hend : (V \ S).card ≤ 1)
    {w : ι → Bool} (hw : IsolatedFlip.flip S R w = w)
    {A x : ℝ} (hA : 0 ≤ A) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    correction V R A x w ≤ (1 + A) * (1 + A * x) ^ V.card := by
  have hpow : (1 + A * x) ^ S.card ≤ (1 + A * x) ^ V.card :=
    pow_le_pow_right₀ (by nlinarith) (Finset.card_le_card hS)
  have hendpow : (1 + A) ^ (V \ S).card ≤ 1 + A := by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ 1 + A) hend
  calc
    correction V R A x w ≤ (1 + A * x) ^ S.card * (1 + A) ^ (V \ S).card :=
      correction_le_of_fixed hS hw hA hx hx1
    _ ≤ (1 + A * x) ^ V.card * (1 + A) :=
      mul_le_mul hpow hendpow (by positivity) (by positivity)
    _ = (1 + A) * (1 + A * x) ^ V.card := mul_comm _ _

end Problem335.IsolatedWeight

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ScheduleWeightBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem335.BalancedSchedule

/-- On a successor number of layers this is the canonical path graph. -/
theorem internalEdges_eq_pathEdges (n : ℕ) :
    internalEdges (n + 1) = SwitchRestoration.pathEdges n := rfl

/-- Each graph edge joins adjacent layers in either direction. -/
theorem internalEdges_adjacent {n : ℕ} {e : Fin n × Fin n}
    (he : e ∈ internalEdges n) : adjacent e.1 e.2 ∧ adjacent e.2 e.1 := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
  exact ⟨adjacent_left_right v, (adjacent_left_right v).symm⟩

/-- Graph incidence degree and internal-end cardinality agree exactly. -/
theorem endpointDegree_internalEdges {n : ℕ} (i : Fin n) :
    SwitchRestoration.endpointDegree (internalEdges n) i = (internalEnds i).card := by
  classical
  unfold SwitchRestoration.endpointDegree internalEdges
  rw [Finset.sum_image]
  · rw [internalEnds, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro v hv
    have hl : leftLayer v = i ↔ v.val = i.val := by
      constructor
      · exact fun h => congrArg Fin.val h
      · exact fun h => Fin.ext h
    have hr : rightLayer v = i ↔ v.val + 1 = i.val := by
      constructor
      · exact fun h => congrArg Fin.val h
      · exact fun h => Fin.ext h
    change (if leftLayer v = i then 1 else 0) +
      (if rightLayer v = i then 1 else 0) =
        if v.val = i.val ∨ v.val + 1 = i.val then 1 else 0
    simp only [hl, hr]
    by_cases hleft : v.val = i.val
    · simp [hleft]
    · by_cases hright : v.val + 1 = i.val <;> simp [hleft, hright]
  · intro v hv w hw h
    apply Fin.ext
    exact congrArg (fun e : Fin n × Fin n => e.1.val) h

/-- Normal neighbors of a normal layer are in bijection with its internal
vertices having two normal incident layers. This identifies the correction
exponents in the graph-word and path-pairing formulations. -/
theorem falseNeighbors_card_eq_nnInternalEnds_card {n : ℕ}
    (τ : Fin n → Bool) (i : Fin n) (hi : τ i = false) :
    (IsolatedWeight.falseNeighbors adjacent τ i).card =
      (nnInternalEnds τ i).card := by
  classical
  apply Finset.card_bij (fun j hj =>
    (⟨min i.val j.val, by
      have hadj := (Finset.mem_filter.mp hj).2.1
      unfold adjacent at hadj
      have hin := i.isLt
      have hjn := j.isLt
      rcases hadj with h | h <;> omega⟩ : Fin (n - 1)))
  · intro j hj
    have hadj := (Finset.mem_filter.mp hj).2.1
    have hjfalse := (Finset.mem_filter.mp hj).2.2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · unfold adjacent at hadj
        dsimp
        rcases hadj with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
    · unfold adjacent at hadj
      rcases hadj with h | h
      · have hl : leftLayer ⟨min i.val j.val, by omega⟩ = i := by
          apply Fin.ext
          dsimp [leftLayer]
          omega
        have hr : rightLayer ⟨min i.val j.val, by omega⟩ = j := by
          apply Fin.ext
          dsimp [rightLayer]
          omega
        simpa only [hl, hr] using And.intro hi hjfalse
      · have hl : leftLayer ⟨min i.val j.val, by omega⟩ = j := by
          apply Fin.ext
          dsimp [leftLayer]
          omega
        have hr : rightLayer ⟨min i.val j.val, by omega⟩ = i := by
          apply Fin.ext
          dsimp [rightLayer]
          omega
        simpa only [hl, hr] using And.intro hjfalse hi
  · intro a ha b hb hab
    have hadj := (Finset.mem_filter.mp ha).2.1
    have hbadj := (Finset.mem_filter.mp hb).2.1
    have habv := congrArg Fin.val hab
    apply Fin.ext
    unfold adjacent at hadj hbadj
    dsimp at habv
    omega
  · intro v hv
    have hends := (Finset.mem_filter.mp hv).1
    have hfalse := (Finset.mem_filter.mp hv).2
    rcases internalEnds_cases hends with hl | hr
    · refine ⟨rightLayer v, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_, hfalse.2⟩
        rw [← hl]
        exact adjacent_left_right v
      · apply Fin.ext
        have hiv := congrArg Fin.val hl
        dsimp [leftLayer, rightLayer] at hiv ⊢
        omega
    · refine ⟨leftLayer v, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_, hfalse.1⟩
        rw [← hr]
        exact (adjacent_left_right v).symm
      · apply Fin.ext
        have hiv := congrArg Fin.val hr
        dsimp [leftLayer, rightLayer] at hiv ⊢
        omega

/-- The complete coincidence correction in the internal-vertex formulation. -/
theorem correction_eq_nnInternalEnds_product {n : ℕ}
    (V : Finset (Fin n)) (τ : Fin n → Bool) (A x : ℝ) :
    IsolatedWeight.correction V adjacent A x τ =
      ∏ i ∈ V.filter (fun i => τ i = false),
        (1 + A * x ^ (nnInternalEnds τ i).card) := by
  classical
  unfold IsolatedWeight.correction
  apply Finset.prod_congr rfl
  intro i hi
  rw [falseNeighbors_card_eq_nnInternalEnds_card τ i (Finset.mem_filter.mp hi).2]

end Problem335.BalancedSchedule

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.WordSwitches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boolean words are uniquely specified by their initial bit and their switches.
This gives the exact binomial count used in the path-type sum. -/

open scoped BigOperators

namespace Problem335
namespace WordSwitches

/-- The switch-count generating function. -/
theorem sum_pow_switches {R : Type*} [CommSemiring R] (n : ℕ) (x : R) :
    (∑ w : Fin (n + 1) → Bool, x ^ (switches w).card) =
      2 * (1 + x) ^ n := by
  calc
    _ = ∑ p : Bool × Finset (Fin n), x ^ p.2.card :=
      Fintype.sum_equiv (wordEquiv n) _ _ (fun _ => rfl)
    _ = 2 * ∑ s : Finset (Fin n), x ^ s.card := by
      rw [Fintype.sum_prod_type]
      simp [two_mul]
    _ = 2 * (1 + x) ^ n := by
      congr 1
      simpa using (Finset.prod_one_add (f := fun _ : Fin n => x) Finset.univ).symm

/-- An exponential upper bound for a switch-penalized word sum. -/
theorem sum_pow_switches_le_exp (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (∑ w : Fin (n + 1) → Bool, x ^ (switches w).card) ≤
      2 * Real.exp ((n : ℝ) * x) := by
  rw [sum_pow_switches]
  have h : (1 + x) ^ n ≤ (Real.exp x) ^ n := by
    gcongr
    simpa [add_comm] using Real.add_one_le_exp x
  calc
    2 * (1 + x) ^ n ≤ 2 * (Real.exp x) ^ n := by gcongr
    _ = 2 * Real.exp ((n : ℝ) * x) := by rw [Real.exp_nat_mul]

end WordSwitches
end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.WordRuns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counts of true runs, and their relation to adjacent switches. -/

open scoped BigOperators

namespace Problem335.WordRuns

/-- Every switch is exactly a rise or a fall. -/
theorem switches_card_eq_rises_add_falls {n : ℕ} (w : Fin (n + 1) → Bool) :
    (WordSwitches.switches w).card = riseCount w + fallCount w := by
  rw [WordSwitches.switches, Finset.card_filter]
  unfold riseCount fallCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases w i.castSucc <;> cases w i.succ <;> decide

/-- Incoming and outgoing changes balance, up to the endpoint bits. -/
theorem rise_first_eq_fall_last {n : ℕ} (w : Fin (n + 1) → Bool) :
    riseCount w + (w 0).toNat = fallCount w + (w (Fin.last n)).toNat := by
  induction n with
  | zero => simp [riseCount, fallCount, Fin.last_zero]
  | succ n ih =>
    obtain ⟨⟨b, v⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 2) => Bool)).surjective w
    have hv := ih v
    have hb : (if b = false ∧ v 0 = true then 1 else 0) + b.toNat =
        (if b = true ∧ v 0 = false then 1 else 0) + (v 0).toNat := by
      cases b <;> cases v 0 <;> decide
    change riseCount (Fin.cons b v) + b.toNat =
      fallCount (Fin.cons b v) + (v (Fin.last n)).toNat
    rw [riseCount_cons, fallCount_cons]
    omega

theorem endpointRunCount_le_two {n : ℕ} (w : Fin (n + 1) → Bool) :
    endpointRunCount w ≤ 2 := by
  unfold endpointRunCount
  cases w 0 <;> cases w (Fin.last n) <;> decide

end Problem335.WordRuns

end OAI
end

section
-- module Solutions.OAIQW_Problem335.RunBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contiguous true blocks, with an exact block-count and product factorization. -/

open scoped BigOperators

namespace Problem335.WordRuns

variable {α : Type*}

/-- The initial block is genuinely a prefix, including when empty. -/
theorem splitTrueAux_fst_prefix (p : α → Bool) (l : List α) :
    (splitTrueAux p l).1 <+: l := by
  induction l with
  | nil => simp [splitTrueAux]
  | cons a l ih =>
    cases hp : p a <;> simp [splitTrueAux, hp, ih]

/-- Splitting does not lose or duplicate any selected position. -/
theorem splitTrueAux_flatten (p : α → Bool) (l : List α) :
    (splitTrueAux p l).1 ++ (splitTrueAux p l).2.flatten = l.filter p := by
  induction l with
  | nil => simp [splitTrueAux]
  | cons a l ih =>
    cases hp : p a <;> simp [splitTrueAux, hp, ih]

@[simp] theorem trueBlocks_flatten (p : α → Bool) (l : List α) :
    (trueBlocks p l).flatten = l.filter p := by
  simpa [trueBlocks, List.flatten_filter_not_isEmpty] using splitTrueAux_flatten p l

private theorem splitTrueAux_infix (p : α → Bool) (l : List α) :
    ∀ b ∈ (splitTrueAux p l).1 :: (splitTrueAux p l).2, b <:+: l := by
  induction l with
  | nil => simp [splitTrueAux]
  | cons a l ih =>
    intro b hb
    cases hp : p a with
    | false =>
      simp only [splitTrueAux, hp, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact List.nil_infix
      · exact List.infix_cons (ih _ (List.mem_cons.mpr hb))
    | true =>
      simp only [splitTrueAux, hp, ↓reduceIte, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact (show a :: (splitTrueAux p l).1 <+: a :: l from
          List.cons_prefix_cons.mpr ⟨rfl, splitTrueAux_fst_prefix p l⟩).isInfix
      · exact List.infix_cons (ih _ (List.mem_cons_of_mem _ hb))

/-- Every true block is a contiguous interval of the original ordered list. -/
theorem trueBlocks_infix (p : α → Bool) (l : List α) {b : List α}
    (hb : b ∈ trueBlocks p l) : b <:+: l :=
  splitTrueAux_infix p l b (List.mem_filter.mp hb).1

/-- Adding one letter either extends the first block or creates one new block. -/
theorem trueBlocks_length_cons (p : α → Bool) (a : α) (l : List α) :
    (trueBlocks p (a :: l)).length = (trueBlocks p l).length +
      if p a = true ∧ (splitTrueAux p l).1 = [] then 1 else 0 := by
  unfold trueBlocks
  cases hq : splitTrueAux p l with
  | mk r rs =>
    cases hp : p a <;> cases r <;> simp [splitTrueAux, hp, hq]

/-- For a nonempty list of word positions, block count is the true run count. -/
theorem trueBlocks_ofFn_length {n : ℕ} (w : Fin (n + 1) → Bool) :
    (trueBlocks w (List.ofFn id)).length = runCount w := by
  have hgen : ∀ (α : Type) (m : ℕ) (f : Fin (m + 1) → α) (p : α → Bool),
      (trueBlocks p (List.ofFn f)).length = runCount (p ∘ f) := by
    intro α m
    induction m with
    | zero =>
      intro f p
      simp [List.ofFn_succ, List.ofFn_zero, trueBlocks, splitTrueAux, runCount, riseCount]
      cases p (f 0) <;> rfl
    | succ m ih =>
      intro f p
      rw [List.ofFn_succ, trueBlocks_length_cons]
      change (trueBlocks p (List.ofFn (Fin.tail f))).length +
        (if p (f 0) = true ∧ (splitTrueAux p (List.ofFn (Fin.tail f))).1 = []
          then 1 else 0) = runCount (p ∘ f)
      have htail := ih (Fin.tail f) p
      rw [htail]
      have hempty : (splitTrueAux p (List.ofFn (Fin.tail f))).1 = [] ↔
          p (f 1) = false := by
        rw [List.ofFn_succ, splitTrueAux_fst_nil_cons]
        rfl
      simp only [hempty]
      have hb := rise_first_eq_fall_last (p ∘ f)
      have hbt := rise_first_eq_fall_last (p ∘ Fin.tail f)
      have hfall : fallCount (p ∘ f) =
          (if p (f 0) = true ∧ p (f 1) = false then 1 else 0) +
            fallCount (p ∘ Fin.tail f) := by
        have heq : p ∘ f = Fin.cons (p (f 0)) (p ∘ Fin.tail f) := by
          funext i
          cases i using Fin.cases <;> rfl
        rw [heq, fallCount_cons]
        rfl
      have hlast : (p ∘ Fin.tail f) (Fin.last m) = (p ∘ f) (Fin.last (m + 1)) := rfl
      unfold runCount
      rw [hlast] at hbt
      omega
  simpa using hgen (Fin (n + 1)) n (id : Fin (n + 1) → Fin (n + 1)) w

/-- Products over selected positions factor exactly into products over true blocks. -/
theorem trueBlocks_prod {R : Type*} [Monoid R] (p : α → Bool) (l : List α) (f : α → R) :
    ((l.filter p).map f).prod =
      ((trueBlocks p l).map (fun b => (b.map f).prod)).prod := by
  rw [← trueBlocks_flatten p l, List.map_flatten, List.prod_flatten, List.map_map]
  rfl

private theorem prod_run_majorants (B : ℝ) (g : α → ℝ) (bs : List (List α)) :
    (bs.map (fun b => B * Real.exp ((b.map g).sum))).prod =
      B ^ bs.length * Real.exp (((bs.flatten).map g).sum) := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, List.flatten_cons,
      List.map_append, List.sum_append, ih, Real.exp_add, pow_succ]
    ring

/-- Interval majorants with local exponential losses multiply once per run,
while the exponential losses add only once per selected position. -/
theorem selected_prod_le_pow_runCount_mul_exp {n : ℕ}
    (w : Fin (n + 1) → Bool) (f g : Fin (n + 1) → ℝ) (B : ℝ)
    (hf : ∀ i, 0 ≤ f i)
    (hB : ∀ b ∈ trueBlocks w (List.ofFn id),
      (b.map f).prod ≤ B * Real.exp ((b.map g).sum)) :
    (((List.ofFn id).filter w).map f).prod ≤
      B ^ runCount w * Real.exp ((((List.ofFn id).filter w).map g).sum) := by
  rw [trueBlocks_prod]
  have hnonneg : ∀ b ∈ trueBlocks w (List.ofFn id), 0 ≤ (b.map f).prod := by
    intro b hb
    apply List.prod_nonneg
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hf i
  have h := List.prod_map_le_prod_map₀ (fun b : List (Fin (n + 1)) => (b.map f).prod)
    (fun b => B * Real.exp ((b.map g).sum)) hnonneg hB
  rwa [prod_run_majorants, trueBlocks_ofFn_length, trueBlocks_flatten] at h

end Problem335.WordRuns

end OAI
end

section
-- module Solutions.OAIQW_Problem335.RunWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic weight estimates for the D-runs in the path-type sum. -/

open scoped BigOperators
noncomputable section
namespace Problem335
namespace RunWeights

/-- The interval discrepancy estimate converts directly into a bound on its weight. -/
lemma interval_weight_le {α β ρ ε N : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hβ : 0 ≤ β) (hβupper : β ≤ α ^ ρ * Real.exp ε)
    (hscale : α ^ (-(1 + ρ)) ≤ N) (v u : ℕ)
    (hdiscrepancy : (v : ℝ) - ρ * u ≤ 1 + ρ) :
    α ^ (-(v : ℝ)) * β ^ u ≤ N * Real.exp (ε * u) := by
  have hp : β ^ u ≤ (α ^ ρ * Real.exp ε) ^ u := by gcongr
  calc
    α ^ (-(v : ℝ)) * β ^ u ≤
        α ^ (-(v : ℝ)) * (α ^ ρ * Real.exp ε) ^ u := by
      exact mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hα.le _)
    _ = α ^ (-(v : ℝ) + ρ * u) * Real.exp (ε * u) := by
      rw [mul_pow, ← Real.rpow_natCast (α ^ ρ) u,
        ← Real.rpow_mul hα.le, ← Real.exp_nat_mul]
      rw [mul_comm (u : ℝ) ε, ← mul_assoc, ← Real.rpow_add hα]
    _ ≤ α ^ (-(1 + ρ)) * Real.exp (ε * u) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact Real.rpow_le_rpow_of_exponent_ge hα hα1 (by linarith)
    _ ≤ N * Real.exp (ε * u) := by
      exact mul_le_mul_of_nonneg_right hscale (Real.exp_pos _).le

/-- The parameter bound on alpha controls the common cost of every run. -/
lemma scale_le_of_inv_le_sqrt {α ρ N : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hρ : ρ ≤ 1) (hN : 0 ≤ N) (hinv : α⁻¹ ≤ Real.sqrt N) :
    α ^ (-(1 + ρ)) ≤ N := by
  calc
    α ^ (-(1 + ρ)) ≤ α ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hα hα1 (by linarith)
    _ = (α⁻¹) ^ 2 := by
      rw [show (-2 : ℝ) = (-1) * 2 by norm_num, Real.rpow_mul hα.le,
        Real.rpow_two, Real.rpow_neg_one]
    _ ≤ (Real.sqrt N) ^ 2 := by gcongr
    _ = N := Real.sq_sqrt hN

lemma one_add_pow_le_exp (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (1 + x) ^ k ≤ Real.exp ((k : ℝ) * x) := by
  rw [Real.exp_nat_mul]
  gcongr
  linarith [Real.add_one_le_exp x]

/-- The isolated-position correction prefactor costs at most exp(3 sqrt N). -/
lemma correction_prefactor_le_exp {N a : ℝ} (hN : 1 ≤ N)
    (ha : 0 ≤ a) (haN : a ≤ Real.sqrt N) (k : ℕ) (hk : 2 * (k : ℝ) ≤ N) :
    (1 + 2 / N ^ 2) ^ k * (1 + a) * (1 + a / N) ^ k ≤
      Real.exp (3 * Real.sqrt N) := by
  have hNpos : 0 < N := by linarith
  have hsqrt : 1 ≤ Real.sqrt N := by
    simpa using Real.sqrt_le_sqrt hN
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkN : (k : ℝ) ≤ N := by linarith
  have hfirst : (k : ℝ) * (2 / N ^ 2) ≤ 1 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos hNpos)).2
    nlinarith
  have hthird : (k : ℝ) * (a / N) ≤ a := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hNpos).2
    nlinarith
  calc
    (1 + 2 / N ^ 2) ^ k * (1 + a) * (1 + a / N) ^ k ≤
        Real.exp ((k : ℝ) * (2 / N ^ 2)) * Real.exp a *
          Real.exp ((k : ℝ) * (a / N)) := by
      gcongr
      · exact one_add_pow_le_exp _ (by positivity) k
      · linarith [Real.add_one_le_exp a]
      · exact one_add_pow_le_exp _ (by positivity) k
    _ = Real.exp ((k : ℝ) * (2 / N ^ 2) + a + (k : ℝ) * (a / N)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (3 * Real.sqrt N) := Real.exp_le_exp.mpr (by linarith)

end RunWeights
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.RunLayerWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete layer weights combined with contiguous true-run decomposition. -/

open scoped BigOperators

namespace Problem335.RunLayerWeights

variable {ι : Type*}

/-- A product of two possible layer weights depends only on the two layer counts. -/
theorem prod_ite_eq_powers {R : Type*} [CommMonoid R]
    (p : ι → Bool) (l : List ι) (a b : R) :
    (l.map (fun i => if p i then a else b)).prod =
      a ^ l.countP p * b ^ l.countP (fun i => !p i) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    cases hp : p i <;> simp [hp, ih, pow_succ, mul_assoc, mul_left_comm, mul_comm]

/-- The derivative/multiplication layer product in the notation of the manuscript. -/
theorem layer_product_eq (p : ι → Bool) (l : List ι) (α β : ℝ) (hα : 0 < α) :
    (l.map (fun i => if p i then α⁻¹ else β)).prod =
      α ^ (-(l.countP p : ℝ)) * β ^ l.countP (fun i => !p i) := by
  rw [prod_ite_eq_powers]
  congr 1
  rw [Real.rpow_neg hα.le, Real.rpow_natCast, inv_pow]

/-- The rounding loss counts only multiplication layers. -/
theorem layer_loss_sum_eq (p : ι → Bool) (l : List ι) (ε : ℝ) :
    (l.map (fun i => if p i then 0 else ε)).sum =
      ε * (l.countP (fun i => !p i) : ℝ) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    cases hp : p i <;> simp [hp, ih, Nat.cast_add, mul_add, add_comm]

/-- An interval discrepancy bound gives the required majorant on each true block. -/
theorem selected_layer_product_le {n : ℕ}
    (isV w : Fin (n + 1) → Bool) {α β ρ ε N : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 ≤ β)
    (hβupper : β ≤ α ^ ρ * Real.exp ε) (hscale : α ^ (-(1 + ρ)) ≤ N)
    (hdiscrepancy : ∀ b : List (Fin (n + 1)), b <:+: List.ofFn id →
      (b.countP isV : ℝ) - ρ * b.countP (fun i => !isV i) ≤ 1 + ρ) :
    ((((List.ofFn id).filter w).map (fun i => if isV i then α⁻¹ else β))).prod ≤
      N ^ WordRuns.runCount w *
        Real.exp (ε * (((List.ofFn id).filter w).countP (fun i => !isV i) : ℝ)) := by
  have h := WordRuns.selected_prod_le_pow_runCount_mul_exp w
    (fun i => if isV i then α⁻¹ else β) (fun i => if isV i then 0 else ε) N
    (by intro i; split <;> positivity) ?_
  · simpa only [layer_loss_sum_eq] using h
  · intro b hb
    rw [layer_product_eq isV b α β hα, layer_loss_sum_eq]
    exact RunWeights.interval_weight_le hα hα1 hβ hβupper hscale _ _
      (hdiscrepancy b (WordRuns.trueBlocks_infix w (List.ofFn id) hb))

/-- The total rounding cost is bounded by the length of the entire word. -/
theorem selected_layer_product_le_length {n : ℕ}
    (isV w : Fin (n + 1) → Bool) {α β ρ ε N : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 ≤ β) (hε : 0 ≤ ε)
    (hβupper : β ≤ α ^ ρ * Real.exp ε) (hscale : α ^ (-(1 + ρ)) ≤ N)
    (hdiscrepancy : ∀ b : List (Fin (n + 1)), b <:+: List.ofFn id →
      (b.countP isV : ℝ) - ρ * b.countP (fun i => !isV i) ≤ 1 + ρ) :
    ((((List.ofFn id).filter w).map (fun i => if isV i then α⁻¹ else β))).prod ≤
      N ^ WordRuns.runCount w * Real.exp (ε * (n + 1 : ℕ)) := by
  have hN : 0 ≤ N := (Real.rpow_nonneg hα.le _).trans hscale
  apply (selected_layer_product_le isV w hα hα1 hβ hβupper hscale hdiscrepancy).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hN _)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hε
  exact_mod_cast (List.countP_le_length.trans (List.length_filter_le _ _)).trans
    (by simp : (List.ofFn (id : Fin (n + 1) → Fin (n + 1))).length ≤ n + 1)

/-- List counts on the selected positions coincide with the finite-set cardinality. -/
theorem selected_countP_eq_card {n : ℕ} (w : Fin n → Bool) (V : Finset (Fin n)) :
    ((List.ofFn id).filter w).countP (fun i => decide (i ∈ V)) =
      (V.filter (fun i => w i = true)).card := by
  rw [List.countP_eq_length_filter]
  have hn : (((List.ofFn (id : Fin n → Fin n)).filter w).filter
      (fun i => decide (i ∈ V))).Nodup :=
    ((List.nodup_ofFn.mpr Function.injective_id).filter _).filter _
  rw [← List.toFinset_card_of_nodup hn]
  congr 1
  ext i
  simp [and_comm]

/-- The local layer product is exactly the count-based weight used by isolated flipping. -/
theorem selected_layer_product_eq_powers {n : ℕ} (w : Fin n → Bool)
    (V : Finset (Fin n)) (A B : ℝ) :
    ((((List.ofFn id).filter w).map (fun i => if i ∈ V then A else B))).prod =
      A ^ (V.filter (fun i => w i = true)).card *
        B ^ ((Finset.univ \ V).filter (fun i => w i = true)).card := by
  have hp := prod_ite_eq_powers (fun i : Fin n => decide (i ∈ V))
    ((List.ofFn id).filter w) A B
  have hV := selected_countP_eq_card w V
  have hU := selected_countP_eq_card w (Finset.univ \ V)
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, decide_not] at hU
  simpa only [decide_eq_true_eq, hV, hU] using hp

/-- Exact count-based per-word estimate consumed by the corrected word-sum proof. -/
theorem count_weight_le_exp_mul_runCount {n : ℕ} (w : Fin (n + 1) → Bool)
    (V : Finset (Fin (n + 1))) {α β ρ ε N : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 ≤ β) (hε : 0 ≤ ε)
    (hβupper : β ≤ α ^ ρ * Real.exp ε) (hscale : α ^ (-(1 + ρ)) ≤ N)
    (hdiscrepancy : ∀ b : List (Fin (n + 1)), b <:+: List.ofFn id →
      (b.countP (fun i => decide (i ∈ V)) : ℝ) -
        ρ * b.countP (fun i => !decide (i ∈ V)) ≤ 1 + ρ) :
    (α⁻¹) ^ (V.filter (fun i => w i = true)).card *
        β ^ ((Finset.univ \ V).filter (fun i => w i = true)).card ≤
      Real.exp (ε * (n + 1 : ℕ)) * N ^ WordRuns.runCount w := by
  have h := selected_layer_product_le_length (fun i => decide (i ∈ V)) w
    hα hα1 hβ hε hβupper hscale hdiscrepancy
  simp only [decide_eq_true_eq] at h
  rw [selected_layer_product_eq_powers] at h
  simpa only [mul_comm] using h

end Problem335.RunLayerWeights

end OAI
end

section
-- module Solutions.OAIQW_Problem335.RunSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative run-weight sums for the path-type estimate. -/

open scoped BigOperators

namespace Problem335.RunSum

/-- A pointwise switch-weight bound gives an exponential bound after summing all words. -/
theorem sum_le_exp_of_switch_bound (n : ℕ) (q A : ℝ) (hq : 0 ≤ q) (hA : 0 ≤ A)
    (F : (Fin (n + 1) → Bool) → ℝ)
    (hF : ∀ w, F w ≤ A * q ^ (WordSwitches.switches w).card) :
    (∑ w, F w) ≤ 2 * A * Real.exp ((n : ℝ) * q) := by
  calc
    (∑ w, F w) ≤ ∑ w, A * q ^ (WordSwitches.switches w).card :=
      Finset.sum_le_sum (fun w _ => hF w)
    _ = A * ∑ w, q ^ (WordSwitches.switches w).card := (Finset.mul_sum _ _ _).symm
    _ ≤ A * (2 * Real.exp ((n : ℝ) * q)) :=
      mul_le_mul_of_nonneg_left (WordSwitches.sum_pow_switches_le_exp n q hq) hA
    _ = 2 * A * Real.exp ((n : ℝ) * q) := by ring

/-- Absorb the polynomial factor in the elementary run estimate into a square-root exponential. -/
theorem two_mul_self_mul_exp_sqrt_le {x : ℝ} (hx : 1 ≤ x) :
    2 * x * Real.exp (Real.sqrt x) ≤ Real.exp (4 * Real.sqrt x) := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hs1 : 1 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0).mpr (by simpa using hx)
  have hs0 := Real.sqrt_nonneg x
  have h2 : 2 ≤ Real.exp (Real.sqrt x) := by linarith [Real.add_one_le_exp (Real.sqrt x)]
  have hs : Real.sqrt x ≤ Real.exp (Real.sqrt x) := by linarith [Real.add_one_le_exp (Real.sqrt x)]
  have hxx : x ≤ Real.exp (2 * Real.sqrt x) := by
    calc
      x = Real.sqrt x ^ 2 := (Real.sq_sqrt hx0).symm
      _ ≤ Real.exp (Real.sqrt x) ^ 2 := pow_le_pow_left₀ hs0 hs 2
      _ = Real.exp (2 * Real.sqrt x) := by simpa using (Real.exp_nat_mul (Real.sqrt x) 2).symm
  calc
    2 * x * Real.exp (Real.sqrt x) ≤
        Real.exp (Real.sqrt x) * Real.exp (2 * Real.sqrt x) * Real.exp (Real.sqrt x) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul h2 hxx hx0 (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = Real.exp (4 * Real.sqrt x) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring


/-- Counting both endpoint bits (including twice for a constant true run) gives an exact balance. -/
theorem switches_card_add_endpoint_eq_two_runs {n : ℕ} (w : Fin (n + 1) → Bool) :
    (WordSwitches.switches w).card + WordRuns.endpointRunCount w =
      2 * WordRuns.runCount w := by
  rw [WordRuns.switches_card_eq_rises_add_falls]
  have h := WordRuns.rise_first_eq_fall_last w
  unfold WordRuns.runCount WordRuns.endpointRunCount
  omega

/-- Switch penalties pay for all but at most one square scale of the run weights.
The constant words are included, so no exceptional-case partition is needed. -/
theorem switch_penalty_mul_run_weight_le {n : ℕ} (w : Fin (n + 1) → Bool)
    {N : ℝ} (hN : 1 ≤ N) :
    N⁻¹ ^ (WordSwitches.switches w).card * N ^ WordRuns.runCount w ≤
      N * (Real.sqrt N)⁻¹ ^ (WordSwitches.switches w).card := by
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hs1 : 1 ≤ Real.sqrt N := (Real.le_sqrt (by norm_num) hN0.le).mpr (by simpa using hN)
  have he := switches_card_add_endpoint_eq_two_runs w
  have he2 := WordRuns.endpointRunCount_le_two w
  have hr : 2 * WordRuns.runCount w ≤ (WordSwitches.switches w).card + 2 := by omega
  have hpow : N ^ WordRuns.runCount w ≤
      Real.sqrt N ^ ((WordSwitches.switches w).card + 2) := by
    calc
      N ^ WordRuns.runCount w = Real.sqrt N ^ (2 * WordRuns.runCount w) := by
        rw [pow_mul, Real.sq_sqrt hN0.le]
      _ ≤ _ := pow_le_pow_right₀ hs1 hr
  calc
    N⁻¹ ^ (WordSwitches.switches w).card * N ^ WordRuns.runCount w ≤
        N⁻¹ ^ (WordSwitches.switches w).card *
          Real.sqrt N ^ ((WordSwitches.switches w).card + 2) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = N * (Real.sqrt N)⁻¹ ^ (WordSwitches.switches w).card := by
      rw [pow_add, Real.sq_sqrt hN0.le]
      have hNinv : N⁻¹ = (Real.sqrt N)⁻¹ ^ 2 := by rw [inv_pow, Real.sq_sqrt hN0.le]
      rw [hNinv, ← pow_mul, Nat.mul_comm 2 _, pow_mul]
      simp only [inv_pow]
      field_simp

/-- Direct application to products of interval weights: a factor `N` per true run,
with `N⁻¹` per switch, yields the required square-root exponential sum. -/
theorem sum_switch_penalty_mul_run_weight_le_exp (n : ℕ) :
    (∑ w : Fin (n + 1) → Bool,
      (((n + 1 : ℕ) : ℝ)⁻¹) ^ (WordSwitches.switches w).card *
        ((n + 1 : ℕ) : ℝ) ^ WordRuns.runCount w) ≤
      Real.exp (4 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsum := sum_le_exp_of_switch_bound n ((Real.sqrt N)⁻¹) N (by positivity) hN0.le
    (fun w => N⁻¹ ^ (WordSwitches.switches w).card * N ^ WordRuns.runCount w)
    (fun w => switch_penalty_mul_run_weight_le w hN)
  have hexponent : (n : ℝ) * (Real.sqrt N)⁻¹ ≤ Real.sqrt N := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hs0).mpr
    have hsq := Real.sq_sqrt hN0.le
    have hnN : (n : ℝ) + 1 = N := by simp [N]
    nlinarith
  exact hsum.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
    (by positivity)).trans (two_mul_self_mul_exp_sqrt_le hN))

/-- Summation interface requiring only a pointwise product-of-runs bound. -/
theorem sum_weighted_switch_penalty_le_exp (n : ℕ) (C : ℝ)
    (F : (Fin (n + 1) → Bool) → ℝ)
    (hF : ∀ w, F w ≤ Real.exp C * ((n + 1 : ℕ) : ℝ) ^ WordRuns.runCount w) :
    (∑ w, (((n + 1 : ℕ) : ℝ)⁻¹) ^ (WordSwitches.switches w).card * F w) ≤
      Real.exp (C + 4 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  calc
    _ ≤ ∑ w, Real.exp C * ((((n + 1 : ℕ) : ℝ)⁻¹) ^ (WordSwitches.switches w).card *
        ((n + 1 : ℕ) : ℝ) ^ WordRuns.runCount w) := by
      apply Finset.sum_le_sum
      intro w _
      calc
        _ ≤ (((n + 1 : ℕ) : ℝ)⁻¹) ^ (WordSwitches.switches w).card *
            (Real.exp C * ((n + 1 : ℕ) : ℝ) ^ WordRuns.runCount w) :=
          mul_le_mul_of_nonneg_left (hF w) (by positivity)
        _ = _ := by ring
    _ = Real.exp C * ∑ w, ((((n + 1 : ℕ) : ℝ)⁻¹) ^ (WordSwitches.switches w).card *
        ((n + 1 : ℕ) : ℝ) ^ WordRuns.runCount w) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp C * Real.exp (4 * Real.sqrt ((n + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_switch_penalty_mul_run_weight_le_exp n) (Real.exp_nonneg C)
    _ = _ := (Real.exp_add _ _).symm

end Problem335.RunSum

end OAI
end

section
-- module Solutions.OAIQW_Problem335.WordSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assembly of the numeric and finite-word estimates in the path-type sum.
The remaining application-specific hypotheses describe the actual path weights. -/

open scoped BigOperators
noncomputable section

namespace Problem335
namespace WordSum

/-- Combine exact smoothing fibers, surviving local corrections, and interior-run counting. -/
lemma corrected_sum_le_exp_of_sum (n k : ℕ) (a c : ℝ)
    (S : Finset (Fin (n + 1))) (R : Fin (n + 1) → Fin (n + 1) → Prop)
    (hS : ∀ i ∈ S, ∀ j, R i j → j ∉ S)
    (hcard : S.card ≤ k)
    (hk : 2 * (k : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
    (ha : 0 ≤ a) (haN : a ≤ Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hc : 0 ≤ c) (hcN : c ≤ 2 / (((n + 1 : ℕ) : ℝ) ^ 2))
    (W Z : (Fin (n + 1) → Bool) → ℝ)
    (hWnonneg : ∀ w, 0 ≤ W w) (hZnonneg : ∀ w, 0 ≤ Z w)
    (hratio : ∀ w, W w = W (IsolatedFlip.flip S R w) *
      c ^ (IsolatedFlip.removed S R w).card)
    (hfixed : ∀ w, IsolatedFlip.flip S R w = w →
      W w ≤ (1 + a) * (1 + a / ((n + 1 : ℕ) : ℝ)) ^ k * Z w)
    (hZbound : (∑ w, Z w) ≤ Real.exp (5 * Real.sqrt ((n + 1 : ℕ) : ℝ))) :
    (∑ w, W w) ≤ Real.exp (8 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  classical
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let Q : ℝ := (1 + a) * (1 + a / N) ^ k
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hNpos : 0 < N := by linarith
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hZsum : 0 ≤ ∑ w, Z w := Finset.sum_nonneg (fun w _ => hZnonneg w)
  have hfixedsum :
      (∑ w ∈ Finset.univ.filter (fun w => IsolatedFlip.flip S R w = w), W w) ≤
        Q * ∑ w, Z w := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro w _
    by_cases hw : IsolatedFlip.flip S R w = w
    · rw [ite_eq_left hw]
      exact hfixed w hw
    · rw [ite_eq_right hw]
      exact mul_nonneg hQ (hZnonneg w)
  have hcpow : (1 + c) ^ S.card ≤ (1 + 2 / N ^ 2) ^ k := by
    calc
      (1 + c) ^ S.card ≤ (1 + 2 / N ^ 2) ^ S.card := by gcongr
      _ ≤ (1 + 2 / N ^ 2) ^ k := by
        exact pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) hcard
  have hpref : (1 + 2 / N ^ 2) ^ k * Q ≤ Real.exp (3 * Real.sqrt N) := by
    dsimp [Q]
    rw [← mul_assoc]
    exact RunWeights.correction_prefactor_le_exp hN ha haN k hk
  change (∑ w, W w) ≤ Real.exp (8 * Real.sqrt N)
  calc
    (∑ w, W w) ≤ (1 + c) ^ S.card *
        ∑ w ∈ Finset.univ.filter (fun w => IsolatedFlip.flip S R w = w), W w :=
      IsolatedFlip.correction_removal hS c hc W hWnonneg hratio
    _ ≤ (1 + c) ^ S.card * (Q * ∑ w, Z w) := by gcongr
    _ ≤ (1 + 2 / N ^ 2) ^ k * (Q * ∑ w, Z w) := by gcongr
    _ = ((1 + 2 / N ^ 2) ^ k * Q) * ∑ w, Z w := by ring
    _ ≤ Real.exp (3 * Real.sqrt N) * Real.exp (5 * Real.sqrt N) := by gcongr
    _ = Real.exp (8 * Real.sqrt N) := by rw [← Real.exp_add]; congr 1; ring

/-- The actual word weights satisfy the square-root exponential bound once
run intervals and the surviving coincidence corrections have been estimated. -/
lemma sum_actual_weight_le_exp (n : ℕ) (A B E : ℝ)
    (edges : Finset (Fin (n + 1) × Fin (n + 1)))
    (V S : Finset (Fin (n + 1))) (R : Fin (n + 1) → Fin (n + 1) → Prop)
    (hS : S ⊆ V) (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (hR : ∀ e ∈ edges, R e.1 e.2 ∧ R e.2 e.1)
    (hdegree : ∀ i ∈ S, SwitchRestoration.endpointDegree edges i = 2)
    (hswitch : ∀ w, SwitchRestoration.switchCount edges w = (WordSwitches.switches w).card)
    (hcard : 2 * (V.card : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
    (hA : 1 ≤ A) (hAN : A ≤ Real.sqrt ((n + 1 : ℕ) : ℝ)) (hB : 0 ≤ B)
    (hE : E ≤ Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hprod : ∀ w : Fin (n + 1) → Bool,
      A ^ (V.filter fun i => w i = true).card *
        B ^ ((Finset.univ \ V).filter fun i => w i = true).card ≤
          Real.exp E * ((n + 1 : ℕ) : ℝ) ^ WordRuns.runCount w)
    (hcorr : ∀ w, IsolatedFlip.flip S R w = w →
      IsolatedWeight.correction V R A (((n + 1 : ℕ) : ℝ)⁻¹) w ≤
        (1 + A) * (1 + A / ((n + 1 : ℕ) : ℝ)) ^ V.card) :
    (∑ w, IsolatedWeight.weight edges V R A B (((n + 1 : ℕ) : ℝ)⁻¹) w) ≤
      Real.exp (8 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  classical
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let F : (Fin (n + 1) → Bool) → ℝ := fun w =>
    A ^ (V.filter fun i => w i = true).card *
      B ^ ((Finset.univ \ V).filter fun i => w i = true).card
  let Z : (Fin (n + 1) → Bool) → ℝ := fun w =>
    N⁻¹ ^ (WordSwitches.switches w).card * F w
  let W := IsolatedWeight.weight edges V R A B N⁻¹
  let c : ℝ := N⁻¹ ^ 2 * (1 + A) / A
  have hN : 0 < N := by dsimp [N]; positivity
  have hApos : 0 < A := by linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcN : c ≤ 2 / N ^ 2 := by
    have hr : (1 + A) / A ≤ 2 := (div_le_iff₀ hApos).2 (by linarith)
    calc
      c = N⁻¹ ^ 2 * ((1 + A) / A) := by dsimp [c]; ring
      _ ≤ N⁻¹ ^ 2 * 2 := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = 2 / N ^ 2 := by rw [inv_pow]; ring
  have hW : ∀ w, 0 ≤ W w :=
    IsolatedWeight.weight_nonneg edges V R hApos.le hB (by positivity)
  have hZ : ∀ w, 0 ≤ Z w := by intro w; dsimp [Z, F]; positivity
  have hZsum : (∑ w, Z w) ≤ Real.exp (5 * Real.sqrt N) := by
    have hh := RunSum.sum_weighted_switch_penalty_le_exp n E F hprod
    exact hh.trans (Real.exp_le_exp.mpr (by change E + 4 * Real.sqrt N ≤ _; linarith))
  apply corrected_sum_le_exp_of_sum n V.card A c S R
  · intro i hi j hij hj
    exact hV i (hS hi) j hij (hS hj)
  · exact Finset.card_le_card hS
  · exact hcard
  · exact hApos.le
  · exact hAN
  · exact hc
  · exact hcN
  · exact hW
  · exact hZ
  · intro w
    exact IsolatedWeight.weight_flip hS hV hR hdegree hApos.ne' B N⁻¹ w
  · intro w hw
    have hh := mul_le_mul_of_nonneg_left (hcorr w hw) (hZ w)
    dsimp [W, IsolatedWeight.weight, Z, F] at hh ⊢
    rw [hswitch]
    nlinarith [hh]
  · exact hZsum

/-- Full corrected-word bound with the actual fixed-word correction estimate discharged.
Only the graph structure and the per-word product-of-runs estimate remain as inputs. -/
lemma sum_actual_weight_le_exp_of_endpoints (n : ℕ) (A B E : ℝ)
    (edges : Finset (Fin (n + 1) × Fin (n + 1)))
    (V S : Finset (Fin (n + 1))) (R : Fin (n + 1) → Fin (n + 1) → Prop)
    (hS : S ⊆ V) (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (hR : ∀ e ∈ edges, R e.1 e.2 ∧ R e.2 e.1)
    (hdegree : ∀ i ∈ S, SwitchRestoration.endpointDegree edges i = 2)
    (hswitch : ∀ w, SwitchRestoration.switchCount edges w = (WordSwitches.switches w).card)
    (hend : (V \ S).card ≤ 1)
    (hcard : 2 * (V.card : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
    (hA : 1 ≤ A) (hAN : A ≤ Real.sqrt ((n + 1 : ℕ) : ℝ)) (hB : 0 ≤ B)
    (hE : E ≤ Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hprod : ∀ w : Fin (n + 1) → Bool,
      A ^ (V.filter fun i => w i = true).card *
        B ^ ((Finset.univ \ V).filter fun i => w i = true).card ≤
          Real.exp E * ((n + 1 : ℕ) : ℝ) ^ WordRuns.runCount w) :
    (∑ w, IsolatedWeight.weight edges V R A B (((n + 1 : ℕ) : ℝ)⁻¹) w) ≤
      Real.exp (8 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  apply sum_actual_weight_le_exp n A B E edges V S R hS hV hR hdegree hswitch
    hcard hA hAN hB hE hprod
  intro w hw
  have hN : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  simpa only [div_eq_mul_inv] using IsolatedWeight.correction_le_endpoint_bound
    hS hend hw (show 0 ≤ A by linarith) (by positivity)
    (inv_le_one_of_one_le₀ hN)

end WordSum
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BalancedWordSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.LowerParameters

/-- The full graph-word estimate for the actual balanced layer partition.
All path-graph, endpoint, flip, and cardinality premises are discharged. -/
lemma balanced_word_sum_bound_of_product {n : ℕ} (hn : 4 ≤ n + 1)
    (A B E : ℝ) (hA : 1 ≤ A) (hAN : A ≤ Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hB : 0 ≤ B) (hE : E ≤ Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hprod : ∀ w : Fin (n + 1) → Bool,
      A ^ ((Finset.univ.filter (fun i => balancedLayer hn i = true)).filter
        (fun i => w i = true)).card *
      B ^ ((Finset.univ \ Finset.univ.filter (fun i => balancedLayer hn i = true)).filter
        (fun i => w i = true)).card ≤
      Real.exp E * ((n + 1 : ℕ) : ℝ) ^ WordRuns.runCount w) :
    (∑ w : Fin (n + 1) → Bool,
      IsolatedWeight.weight (BalancedSchedule.internalEdges (n + 1))
        (Finset.univ.filter (fun i => balancedLayer hn i = true))
        BalancedSchedule.adjacent A B (((n + 1 : ℕ) : ℝ)⁻¹) w) ≤
      Real.exp (8 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  classical
  let V := Finset.univ.filter (fun i => balancedLayer hn i = true)
  let first : Fin (n + 1) := ⟨0, by omega⟩
  let S := V.erase first
  have hfirst : first ∈ V := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, balancedLayer_first hn⟩
  apply WordSum.sum_actual_weight_le_exp_of_endpoints n A B E
    (BalancedSchedule.internalEdges (n + 1)) V S BalancedSchedule.adjacent
  · exact Finset.erase_subset _ _
  · intro i hi j hij hj
    exact balancedLayer_independent hn (Finset.mem_filter.mp hi).2
      (Finset.mem_filter.mp hj).2 hij
  · intro e he
    exact BalancedSchedule.internalEdges_adjacent he
  · intro i hi
    obtain ⟨hifirst, hiV⟩ := Finset.mem_erase.mp hi
    have hival : i.val ≠ 0 := by
      intro h
      exact hifirst (Fin.ext h)
    have hlast : i.val + 1 < n + 1 := by
      by_contra hf
      have heq : i = ⟨(n + 1) - 1, by omega⟩ := by
        apply Fin.ext
        change i.val = (n + 1) - 1
        have := i.isLt
        omega
      have hitrue := (Finset.mem_filter.mp hiV).2
      rw [heq, balancedLayer_final hn] at hitrue
      cases hitrue
    rw [BalancedSchedule.endpointDegree_internalEdges]
    exact BalancedSchedule.card_internalEnds_eq_two i (by omega) hlast
  · intro w
    rw [BalancedSchedule.internalEdges_eq_pathEdges,
      SwitchRestoration.switchCount_pathEdges]
    simp [WordSwitches.switches, Finset.card_filter]
  · change (V \ V.erase first).card ≤ 1
    rw [Finset.sdiff_erase hfirst]
    simp
  · have hcard : V.card = k (n + 1) := balancedLayer_card_true hn
    rw [hcard]
    have hle : 2 * k (n + 1) ≤ n + 1 := by
      have h := two_mul_k_add_s (n + 1)
      omega
    exact_mod_cast hle
  · exact hA
  · exact hAN
  · exact hB
  · exact hE
  · exact hprod

/-- The canonical balanced schedule satisfies the complete corrected-word bound.
The only premises are the scalar parameter inequalities. -/
lemma balanced_word_sum_bound {n : ℕ} (hn : 4 ≤ n) {α β ε : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hαN : α⁻¹ ≤ Real.sqrt (n : ℝ))
    (hβ : 0 ≤ β) (hβupper : β ≤ α ^ rho n * Real.exp ε)
    (hscale : α ^ (-(1 + rho n)) ≤ (n : ℝ))
    (hε : 0 ≤ ε) (hεN : ε * (n : ℝ) ≤ Real.sqrt (n : ℝ)) :
    (∑ w : Fin n → Bool,
      IsolatedWeight.weight (BalancedSchedule.internalEdges n)
        (Finset.univ.filter (fun i => balancedLayer hn i = true))
        BalancedSchedule.adjacent α⁻¹ β ((n : ℝ)⁻¹) w) ≤
      Real.exp (8 * Real.sqrt (n : ℝ)) := by
  classical
  cases n with
  | zero => omega
  | succ n =>
    apply balanced_word_sum_bound_of_product hn α⁻¹ β (ε * ((n + 1 : ℕ) : ℝ))
      ((one_le_inv₀ hα).2 hα1) hαN hβ hεN
    intro w
    apply RunLayerWeights.count_weight_le_exp_mul_runCount w
      (Finset.univ.filter (fun i => balancedLayer hn i = true))
      hα hα1 hβ hε hβupper hscale
    intro b hb
    simpa using (balancedLayer_infix_discrepancy hn b hb).le

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.AnalyticParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounded analytic parameters used by the lower-bound rank measure. -/
noncomputable section
namespace Problem335.LowerParameters

theorem sqrt_ge_two {n : ℕ} (hn : 4 ≤ n) : 2 ≤ Real.sqrt (n : ℝ) := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  exact_mod_cast hn

theorem a0_pos {n : ℕ} (hn : 4 ≤ n) : 0 < a0 n := by
  unfold a0
  apply div_pos
  · exact_mod_cast v_pos hn
  · have := sqrt_ge_two hn
    linarith

theorem a_pos {n : ℕ} (hn : 4 ≤ n) : 0 < a n := by
  exact Nat.ceil_pos.mpr (a0_pos hn)

theorem a0_le_a (n : ℕ) : a0 n ≤ (a n : ℝ) := Nat.le_ceil _

theorem alpha_pos {n : ℕ} (hn : 4 ≤ n) : 0 < alpha n := by
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos hn
  unfold alpha
  positivity

theorem inv_sqrt_le_alpha {n : ℕ} (hn : 4 ≤ n) :
    (Real.sqrt (n : ℝ))⁻¹ ≤ alpha n := by
  have hr := sqrt_ge_two hn
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos hn
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos hn
  have hround := a0_le_a n
  have hmul : (v n : ℝ) ≤ (a n : ℝ) * (Real.sqrt (n : ℝ) - 1) :=
    (div_le_iff₀ (by linarith)).mp hround
  rw [inv_eq_one_div, alpha]
  apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
  nlinarith

theorem inv_alpha_le_sqrt {n : ℕ} (hn : 4 ≤ n) :
    (alpha n)⁻¹ ≤ Real.sqrt (n : ℝ) := by
  have ha := alpha_pos hn
  have hs := sqrt_ge_two hn
  have h := inv_sqrt_le_alpha hn
  calc
    (alpha n)⁻¹ ≤ ((Real.sqrt (n : ℝ))⁻¹)⁻¹ :=
      (inv_le_inv₀ ha (inv_pos.mpr (by linarith))).mpr h
    _ = _ := inv_inv _

theorem k_mul_n_le_a0 {n : ℕ} (hn : 4 ≤ n) :
    (k n : ℝ) * (n : ℝ) ≤ a0 n := by
  have hr := sqrt_ge_two hn
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hbound : Real.sqrt (n : ℝ) - 1 ≤ (n : ℝ) := by nlinarith
  unfold a0
  apply (le_div_iff₀ (by linarith)).mpr
  have h := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ (k n : ℝ) * (n : ℝ) by positivity)
  simpa [v, Nat.cast_mul, Nat.cast_pow, pow_two, mul_assoc] using h

theorem k_mul_n_le_a {n : ℕ} (hn : 4 ≤ n) : k n * n ≤ a n := by
  have h := (k_mul_n_le_a0 hn).trans (a0_le_a n)
  exact_mod_cast h

theorem four_mul_n_le_a {n : ℕ} (hn : 16 ≤ n) : 4 * n ≤ a n := by
  have hk := three_mul_n_le_eight_mul_k hn
  have hka := k_mul_n_le_a (show 4 ≤ n by omega)
  have hk4 : 4 ≤ k n := by omega
  exact (Nat.mul_le_mul_right n hk4).trans hka

theorem alpha_rpow_rho_pos {n : ℕ} (hn : 4 ≤ n) :
    0 < (alpha n) ^ (rho n) := Real.rpow_pos_of_pos (alpha_pos hn) _

theorem alpha_rpow_rho_lt_one {n : ℕ} (hn : 4 ≤ n) :
    (alpha n) ^ (rho n) < 1 :=
  Real.rpow_lt_one (alpha_pos hn).le (alpha_lt_one hn) (rho_pos hn)

theorem alpha_le_alpha_rpow_rho {n : ℕ} (hn : 4 ≤ n) :
    alpha n ≤ (alpha n) ^ (rho n) :=
  Real.self_le_rpow_of_le_one (alpha_pos hn).le (alpha_lt_one hn).le (rho_lt_one hn).le

theorem b0_pos {n : ℕ} (hn : 4 ≤ n) : 0 < b0 n := by
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos hn
  have hp := alpha_rpow_rho_pos hn
  have hp1 := alpha_rpow_rho_lt_one hn
  unfold b0
  positivity

theorem b_pos {n : ℕ} (hn : 4 ≤ n) : 0 < b n :=
  Nat.ceil_pos.mpr (b0_pos hn)

theorem b0_le_b (n : ℕ) : b0 n ≤ (b n : ℝ) := Nat.le_ceil _

theorem b_lt_b0_add_one {n : ℕ} (hn : 4 ≤ n) : (b n : ℝ) < b0 n + 1 :=
  Nat.ceil_lt_add_one (b0_pos hn).le

theorem beta_pos {n : ℕ} (hn : 4 ≤ n) : 0 < beta n := by
  have hb : (0 : ℝ) < b n := by exact_mod_cast b_pos hn
  unfold beta
  positivity

theorem a_le_b0 {n : ℕ} (hn : 4 ≤ n) : (a n : ℝ) ≤ b0 n := by
  have hap := alpha_pos hn
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos hn
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos hn
  have hu : (v n : ℝ) ≤ u n := by
    have hkm : k n ≤ m n := (k_lt_m hn).le
    exact_mod_cast Nat.mul_le_mul_right (n ^ 2) hkm
  have hp := alpha_rpow_rho_pos hn
  have hp1 := alpha_rpow_rho_lt_one hn
  have hal := alpha_le_alpha_rpow_rho hn
  have heq : (a n : ℝ) * (1 - alpha n) = (v n : ℝ) * alpha n := by
    unfold alpha
    field_simp
    ring
  unfold b0
  apply (le_div_iff₀ (by linarith)).mpr
  calc
    (a n : ℝ) * (1 - (alpha n) ^ (rho n)) ≤ (a n : ℝ) * (1 - alpha n) := by
      gcongr
    _ = (v n : ℝ) * alpha n := heq
    _ ≤ (u n : ℝ) * (alpha n) ^ (rho n) :=
      mul_le_mul hu hal hap.le (by positivity)

theorem a_le_b {n : ℕ} (hn : 4 ≤ n) : a n ≤ b n := by
  exact_mod_cast (a_le_b0 hn).trans (b0_le_b n)

theorem four_mul_n_le_b {n : ℕ} (hn : 16 ≤ n) : 4 * n ≤ b n :=
  (four_mul_n_le_a hn).trans (a_le_b (by omega))

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FractionRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem335

/-- Quantitative monotonicity of the fraction used in the rounded rank parameters. -/
theorem fraction_rounding_ratio_bounds {x v a : ℝ} (hx : 0 < x) (hv : 0 < v)
    (hxa : x ≤ a) (hax : a ≤ x + 1) :
    1 ≤ (a / (a + v)) / (x / (x + v)) ∧
      (a / (a + v)) / (x / (x + v)) ≤ 1 + 1 / x := by
  have ha : 0 < a := lt_of_lt_of_le hx hxa
  have hxv : 0 < x + v := add_pos hx hv
  have hav : 0 < a + v := add_pos ha hv
  have hratio : (a / (a + v)) / (x / (x + v)) =
      a * (x + v) / (x * (a + v)) := by field_simp
  rw [hratio]
  constructor
  · apply (le_div_iff₀ (mul_pos hx hav)).mpr
    nlinarith
  · apply (div_le_iff₀ (mul_pos hx hav)).mpr
    have hxne : x ≠ 0 := ne_of_gt hx
    field_simp
    nlinarith

/-- Rounding upward by at most one changes the logarithm by at most `1/x`. -/
theorem fraction_rounding_log_bounds {x v a : ℝ} (hx : 0 < x) (hv : 0 < v)
    (hxa : x ≤ a) (hax : a ≤ x + 1) :
    0 ≤ Real.log ((a / (a + v)) / (x / (x + v))) ∧
      Real.log ((a / (a + v)) / (x / (x + v))) ≤ 1 / x := by
  obtain ⟨hlo, hhi⟩ := fraction_rounding_ratio_bounds hx hv hxa hax
  constructor
  · exact Real.log_nonneg hlo
  · have hpos : 0 < (a / (a + v)) / (x / (x + v)) := lt_of_lt_of_le zero_lt_one hlo
    have hlog := Real.log_le_sub_one_of_pos hpos
    linarith

/-- Once the unrounded value is at least one, the logarithmic loss is `2/a`. -/
theorem fraction_rounding_log_le_two_div {x v a : ℝ} (hx : 1 ≤ x) (hv : 0 < v)
    (hxa : x ≤ a) (hax : a ≤ x + 1) :
    Real.log ((a / (a + v)) / (x / (x + v))) ≤ 2 / a := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hapos : 0 < a := hxpos.trans_le hxa
  apply (fraction_rounding_log_bounds hxpos hv hxa hax).2.trans
  apply (div_le_div_iff₀ hxpos hapos).mpr
  nlinarith

/-- Equivalent multiplicative exponential form of the rounding estimate. -/
theorem fraction_rounding_bounds {x v a : ℝ} (hx : 0 < x) (hv : 0 < v)
    (hxa : x ≤ a) (hax : a ≤ x + 1) :
    x / (x + v) ≤ a / (a + v) ∧
      a / (a + v) ≤ x / (x + v) * Real.exp (1 / x) := by
  have hbase : 0 < x / (x + v) := div_pos hx (add_pos hx hv)
  obtain ⟨hlo, hhi⟩ := fraction_rounding_ratio_bounds hx hv hxa hax
  constructor
  · exact (one_le_div hbase).mp hlo
  · have hexp : 1 + 1 / x ≤ Real.exp (1 / x) := by
      simpa [add_comm] using Real.add_one_le_exp (1 / x)
    have hratio := hhi.trans hexp
    exact (div_le_iff₀ hbase).mp hratio |>.trans_eq (mul_comm _ _)

/-- The first rank parameter has ideal fraction `1/s`; here `s = sqrt n`. -/
theorem fraction_natCeil_inverse_bounds {s v : ℝ} (hs : 1 < s) (hv : 0 < v) :
    let a : ℝ := ⌈v / (s - 1)⌉₊
    1 / s ≤ a / (a + v) ∧
      a / (a + v) ≤ 1 / s * Real.exp ((s - 1) / v) := by
  have hsm : 0 < s - 1 := sub_pos.mpr hs
  have hx : 0 < v / (s - 1) := div_pos hv hsm
  have hbase : (v / (s - 1)) / (v / (s - 1) + v) = 1 / s := by
    field_simp
    ring
  have hinv : 1 / (v / (s - 1)) = (s - 1) / v := by
    rw [one_div_div]
  have h := fraction_rounding_bounds hx hv (Nat.le_ceil _) (le_of_lt (Nat.ceil_lt_add_one hx.le))
  simpa only [hbase, hinv] using h

/-- The second rank parameter is rounded from a prescribed target fraction `p`. -/
theorem fraction_natCeil_target_bounds {p v : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hv : 0 < v) :
    let b : ℝ := ⌈v * p / (1 - p)⌉₊
    p ≤ b / (b + v) ∧
      b / (b + v) ≤ p * Real.exp ((1 - p) / (v * p)) := by
  have hpm : 0 < 1 - p := sub_pos.mpr hp1
  have hx : 0 < v * p / (1 - p) := div_pos (mul_pos hv hp) hpm
  have hbase : (v * p / (1 - p)) / (v * p / (1 - p) + v) = p := by
    field_simp
    ring
  have hinv : 1 / (v * p / (1 - p)) = (1 - p) / (v * p) := by
    rw [one_div_div]
  have h := fraction_rounding_bounds hx hv (Nat.le_ceil _) (le_of_lt (Nat.ceil_lt_add_one hx.le))
  simpa only [hbase, hinv] using h

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BetaRefinements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem335.LowerParameters

/-- The rounded multiplication fraction has logarithmic error at most `2/b`. -/
theorem beta_log_error_bounds {n : ℕ} (hn : 16 ≤ n) :
    0 ≤ Real.log (beta n / ((alpha n) ^ (rho n))) ∧
      Real.log (beta n / ((alpha n) ^ (rho n))) ≤ 2 / (b n : ℝ) := by
  have hn4 : 4 ≤ n := by omega
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos hn4
  have hp : 0 < (alpha n) ^ (rho n) := alpha_rpow_rho_pos hn4
  have hp1 : (alpha n) ^ (rho n) < 1 := alpha_rpow_rho_lt_one hn4
  have hpm : 0 < 1 - (alpha n) ^ (rho n) := sub_pos.mpr hp1
  have hx := b0_pos hn4
  have hab := a_le_b0 hn4
  have ha : 4 * (n : ℝ) ≤ (a n : ℝ) := by exact_mod_cast four_mul_n_le_a hn
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hxone : 1 ≤ b0 n := by linarith
  have hbase : b0 n / (b0 n + (u n : ℝ)) = (alpha n) ^ (rho n) := by
    unfold b0
    field_simp [ne_of_gt hu, ne_of_gt hpm]
    ring
  have hratio : ((b n : ℝ) / ((b n : ℝ) + (u n : ℝ))) /
      (b0 n / (b0 n + (u n : ℝ))) = beta n / ((alpha n) ^ (rho n)) := by
    rw [hbase, beta]
  constructor
  · rw [← hratio]
    exact (fraction_rounding_log_bounds hx hu (b0_le_b n) (b_lt_b0_add_one hn4).le).1
  · rw [← hratio]
    exact fraction_rounding_log_le_two_div hxone hu (b0_le_b n) (b_lt_b0_add_one hn4).le

/-- Sharp multiplicative rounding bound used when summing path runs. -/
theorem beta_le_rpow_mul_exp_two_div {n : ℕ} (hn : 16 ≤ n) :
    beta n ≤ (alpha n) ^ (rho n) * Real.exp (2 / (b n : ℝ)) := by
  have hn4 : 4 ≤ n := by omega
  have hp : 0 < (alpha n) ^ (rho n) := alpha_rpow_rho_pos hn4
  have hratio : 0 < beta n / ((alpha n) ^ (rho n)) := div_pos (beta_pos hn4) hp
  have h := (Real.log_le_iff_le_exp hratio).mp (beta_log_error_bounds hn).2
  exact ((div_le_iff₀ hp).mp h).trans_eq (mul_comm _ _)

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.WordWeightParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete numerical hypotheses for the balanced path-word sum. -/
noncomputable section

namespace Problem335.LowerParameters

/-- Every true run costs at most one factor of the matrix dimension. -/
theorem alpha_run_scale_le {n : ℕ} (hn : 4 ≤ n) :
    (alpha n) ^ (-(1 + rho n)) ≤ (n : ℝ) :=
  RunWeights.scale_le_of_inv_le_sqrt (alpha_pos hn) (alpha_lt_one hn).le
    (rho_lt_one hn).le (Nat.cast_nonneg n) (inv_alpha_le_sqrt hn)

/-- The accumulated beta rounding error is already bounded by one half. -/
theorem word_error_mul_n_le_half {n : ℕ} (hn : 16 ≤ n) :
    (2 / (b n : ℝ)) * (n : ℝ) ≤ 1 / 2 := by
  have hb : (0 : ℝ) < b n := by exact_mod_cast b_pos (by omega : 4 ≤ n)
  have hbn : 4 * (n : ℝ) ≤ (b n : ℝ) := by
    exact_mod_cast four_mul_n_le_b hn
  calc
    (2 / (b n : ℝ)) * (n : ℝ) = (2 * (n : ℝ)) / (b n : ℝ) := by ring
    _ ≤ 1 / 2 := (div_le_iff₀ hb).mpr (by linarith)

theorem word_error_mul_n_le_sqrt {n : ℕ} (hn : 16 ≤ n) :
    (2 / (b n : ℝ)) * (n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have hs := sqrt_ge_two (show 4 ≤ n by omega)
  exact (word_error_mul_n_le_half hn).trans (by linarith)

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ActualBalancedWordSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.LowerParameters

/-- The complete corrected path-word estimate at the actual lower-bound
parameters and balanced schedule. There are no remaining weight assumptions. -/
theorem actual_balanced_word_sum_bound {n : ℕ} (hn : 16 ≤ n) :
    (∑ w : Fin n → Bool,
      IsolatedWeight.weight (BalancedSchedule.internalEdges n)
        (Finset.univ.filter (fun i => balancedLayer (show 4 ≤ n by omega) i = true))
        BalancedSchedule.adjacent (alpha n)⁻¹ (beta n) ((n : ℝ)⁻¹) w) ≤
      Real.exp (8 * Real.sqrt (n : ℝ)) := by
  have hn4 : 4 ≤ n := by omega
  exact balanced_word_sum_bound hn4 (alpha_pos hn4) (alpha_lt_one hn4).le
    (inv_alpha_le_sqrt hn4) (beta_pos hn4).le (beta_le_rpow_mul_exp_two_div hn)
    (alpha_run_scale_le hn4) (by positivity) (word_error_mul_n_le_sqrt hn)

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.HomogeneousSpaceDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

universe u v w

/-- The number of monomials of total degree `d`. -/
theorem card_degree_exponents (σ : Type u) [Fintype σ] (d : ℕ) :
    Nat.card { m : σ →₀ ℕ // m.degree = d } =
      Nat.multichoose (Fintype.card σ) d := by
  rw [Nat.card_congr (degreeExponentsEquivSym σ d)]
  simpa only [Nat.card_eq_fintype_card] using Sym.natCard_sym_eq_multichoose (α := σ) d

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OperatorRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bigraded polynomial spaces used by the differentiation--multiplication rank measure.
The Boolean partition assigns derivative variables to `true` and multiplication
variables to `false`.
-/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ K : Type*}

variable [CommSemiring K]

 theorem bidegreeComponent_eq_self {isV : σ → Bool} {a b : ℕ}
    {p : MvPolynomial σ K} (hp : p ∈ bidegreeSubmodule isV a b) :
    bidegreeComponent isV a b p = p :=
  MvPolynomial.weightedHomogeneousComponent_eq_self hp

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BidegreeDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

universe u v

/-- Counting bidegree monomials separates into the two variable groups. -/
theorem card_bidegree_finsupp_exponents {σ : Type u} [Fintype σ]
    (side : σ → Bool) (a b : ℕ) :
    Nat.card {m : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) m = (a, b)} =
      Nat.multichoose (Fintype.card {i : σ // side i = true}) a *
      Nat.multichoose (Fintype.card {i : σ // side i = false}) b := by
  rw [Nat.card_congr (bidegreeFinsuppExponentsEquiv side a b), Nat.card_prod,
    card_degree_exponents, card_degree_exponents]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ConfiguredRankData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common, concrete data for the two sides of the IMM rank comparison. -/

noncomputable section

namespace Problem335.LowerParameters

theorem rankDimension_nonneg (n : ℕ) : 0 ≤ rankDimension n := by
  unfold rankDimension
  positivity

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FockMonomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
lemma complexFockBasis_apply (d : σ →₀ ℕ) :
    complexFockBasis d = complexFockMonomial d := by
  simp [complexFockBasis, Module.Basis.isUnitSMul_apply, complexFockMonomial_eq,
    MvPolynomial.smul_monomial]

omit [DecidableEq σ] in
lemma complexFockBasis_repr (p : MvPolynomial σ ℂ) (d : σ →₀ ℕ) :
    complexFockBasis.repr p d =
      (Real.sqrt (multiFactorial d : ℝ) : ℂ) * p.coeff d := by
  simp only [complexFockBasis, Module.Basis.repr_isUnitSMul, Units.smul_def,
    IsUnit.unit_spec, Units.val_inv_eq_inv_val, Complex.ofReal_inv, inv_inv]
  rfl

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FockPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] [DecidableEq σ] in
lemma occupationAmplitude_eq_zero_iff (isV : σ → Bool) (d : σ →₀ ℕ) (i : σ) :
    occupationAmplitude isV d i = 0 ↔ isV i = true ∧ d i = 0 := by
  cases h : isV i
  · have hp : 0 < (d i : ℝ) + 1 := by positivity
    simp [occupationAmplitude, h, (Real.sqrt_pos.2 hp).ne']
  · simp [occupationAmplitude, h, Real.sqrt_eq_zero (Nat.cast_nonneg (d i))]

omit [Fintype σ] [DecidableEq σ] in
lemma pathAmplitude_eq_zero_iff (isV : σ → Bool) (l : List σ) (d : σ →₀ ℕ) :
    (l.map (occupationAmplitude isV d)).prod = 0 ↔
      ∃ i ∈ l, isV i = true ∧ d i = 0 := by
  simp only [List.prod_eq_zero_iff, List.mem_map, occupationAmplitude_eq_zero_iff]

omit [Fintype σ] [DecidableEq σ] in
lemma signedOccupation_injective : Function.Injective (signedOccupation (σ := σ)) := by
  intro d e h
  ext i
  have hi := congrArg (fun x : σ →₀ ℤ => x i) h
  simp only [signedOccupation_apply] at hi
  exact_mod_cast hi

omit [Fintype σ] [DecidableEq σ] in
@[simp] lemma signedOccupation_eq_iff (d e : σ →₀ ℕ) :
    signedOccupation d = signedOccupation e ↔ d = e :=
  signedOccupation_injective.eq_iff

omit [Fintype σ] [DecidableEq σ] in
lemma signedOccupation_step (isV : σ → Bool) (d : σ →₀ ℕ) (i : σ)
    (hvalid : isV i = true → 0 < d i) :
    signedOccupation (stepOccupation isV i d) =
      signedOccupation d + Finsupp.single i (if isV i then (-1 : ℤ) else 1) := by
  classical
  ext j
  by_cases hij : i = j
  · subst j
    cases hside : isV i
    · simp [signedOccupation, stepOccupation, hside]
    · have hp := hvalid hside
      simp [signedOccupation, stepOccupation, hside]
      omega
  · cases hside : isV i <;> simp [signedOccupation, stepOccupation, hside, hij]

omit [Fintype σ] [DecidableEq σ] in
lemma signedOccupation_path_of_valid (isV : σ → Bool) (l : List σ)
    (hl : l.Nodup) (d : σ →₀ ℕ)
    (hvalid : ∀ i ∈ l, isV i = true → 0 < d i) :
    signedOccupation (pathOccupation isV l d) = signedOccupation d + occupationShift isV l := by
  induction l with
  | nil => simp [pathOccupation, occupationShift]
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
    have hv : isV i = true → 0 < pathOccupation isV l d i := by
      rw [pathOccupation_apply_of_not_mem isV l d hi]
      exact hvalid i (by simp)
    have htail := ih hl (fun j hj => hvalid j (List.mem_cons_of_mem _ hj))
    change signedOccupation (stepOccupation isV i (pathOccupation isV l d)) = _
    rw [signedOccupation_step isV _ i hv, htail]
    simp [occupationShift, add_comm, add_left_comm]

omit [Fintype σ] [DecidableEq σ] in
/-- A nonzero path amplitude guarantees that natural subtraction agrees with
the signed path shift, including at every intermediate occupation. -/
theorem signedOccupation_path_of_amplitude_ne_zero (isV : σ → Bool) (l : List σ)
    (hl : l.Nodup) (d : σ →₀ ℕ)
    (hamp : (l.map (occupationAmplitude isV d)).prod ≠ 0) :
    signedOccupation (pathOccupation isV l d) = signedOccupation d + occupationShift isV l := by
  apply signedOccupation_path_of_valid isV l hl d
  intro i hi hs
  by_contra h
  have hz : d i = 0 := by omega
  exact hamp ((pathAmplitude_eq_zero_iff isV l d).2 ⟨i, hi, hs, hz⟩)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {K : Type*} [CommSemiring K]

/-- Matrix multiplication adds weighted degrees, including repeated layer occurrences. -/
theorem matrix_list_map_prod_isWeightedHomogeneous {σ ι τ M : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (w : σ → M) (A : τ → Matrix ι ι (MvPolynomial σ K)) (d : τ → M)
    (L : List τ) (hA : ∀ t ∈ L, ∀ i j, (A t i j).IsWeightedHomogeneous w (d t))
    (i j : ι) :
    ((L.map A).prod i j).IsWeightedHomogeneous w (L.map d).sum := by
  induction L generalizing i j with
  | nil =>
      simp only [List.map_nil, List.prod_nil, List.sum_nil, Matrix.one_apply]
      split_ifs
      · exact MvPolynomial.isWeightedHomogeneous_one K w
      · exact MvPolynomial.isWeightedHomogeneous_zero K w 0
  | cons t L ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, Matrix.mul_apply]
      apply MvPolynomial.IsWeightedHomogeneous.sum
      intro k hk
      exact (hA t List.mem_cons_self i k).mul
        (ih (fun s hs => hA s (List.mem_cons_of_mem t hs)) k j)

/-- Every monomial of IMM uses each matrix layer once, expressed with arbitrary additive weights. -/
theorem imm_isWeightedHomogeneous (K : Type*) [CommSemiring K] (n : ℕ)
    {M : Type*} [AddCommMonoid M] (w : Fin n → M) :
    (imm K n).IsWeightedHomogeneous (fun x => w x.1) (∑ t, w t) := by
  classical
  unfold imm
  split_ifs with hn
  · simpa only [← List.ofFn_eq_map, List.sum_ofFn] using
      matrix_list_map_prod_isWeightedHomogeneous
        (fun x : Fin n × Fin n × Fin n => w x.1) (immLayer K n) w (List.finRange n)
        (fun t ht i j => MvPolynomial.isWeightedHomogeneous_X K _ (t, i, j))
        (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n)
  · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _

@[simp] theorem immIdentityEvaluation_imm (n : ℕ) (hn : 0 < n) :
    immIdentityEvaluation K n (imm K n) = 1 := by
  classical
  unfold imm
  simp only [dite_eq_left hn]
  have h : (immIdentityEvaluation K n).mapMatrix
      (List.ofFn (fun t : Fin n => immLayer K n t)).prod = 1 := by
    rw [map_list_prod, List.map_ofFn]
    simp only [Function.comp_def, immIdentityEvaluation_layer]
    simp
  exact congrArg (fun A : Matrix (Fin n) (Fin n) K =>
    A ⟨0, hn⟩ ⟨0, hn⟩) h

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmBidegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- With a layerwise partition, IMM is already in the selected bidegree. -/
theorem imm_mem_bidegreeSubmodule (K : Type*) [CommSemiring K] (n : ℕ)
    (side : Fin n → Bool) :
    imm K n ∈ bidegreeSubmodule (fun x => side x.1)
      (Finset.univ.filter (fun t => side t = true)).card
      (Finset.univ.filter (fun t => side t = false)).card := by
  classical
  have h := imm_isWeightedHomogeneous K n (bidegreeWeight side)
  have hs : (∑ t, bidegreeWeight side t) =
      ((Finset.univ.filter (fun t => side t = true)).card,
       (Finset.univ.filter (fun t => side t = false)).card) := by
    apply Prod.ext
    · simp only [Prod.fst_sum, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro t ht
      cases hs : side t <;> simp [bidegreeWeight, hs]
    · simp only [Prod.snd_sum, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro t ht
      cases hs : side t <;> simp [bidegreeWeight, hs]
  rw [hs] at h
  exact h

/-- A bidegree projection does not change IMM when the selected index is its layer count. -/
theorem bidegreeComponent_imm (K : Type*) [CommSemiring K] (n : ℕ)
    (side : Fin n → Bool) :
    bidegreeComponent (fun x => side x.1)
      (Finset.univ.filter (fun t => side t = true)).card
      (Finset.univ.filter (fun t => side t = false)).card (imm K n) = imm K n :=
  bidegreeComponent_eq_self (imm_mem_bidegreeSubmodule K n side)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.MatrixPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ ι R : Type*}

theorem list_sum_map_flatMap [AddMonoid R] {α β : Type*}
    (xs : List α) (f : α → List β) (g : β → R) :
    ((xs.flatMap f).map g).sum = (xs.map fun a => ((f a).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- Matrix multiplication is the sum of the products along its labelled paths. -/
theorem matrixEntryPaths_sum_prod [Fintype ι] [DecidableEq ι] [Semiring R]
    (A : σ → Matrix ι ι R) (labels : List σ) (i j : ι) :
    ((matrixEntryPaths labels i j).map
      (fun p => (p.map (fun e => A e.1 e.2.1 e.2.2)).prod)).sum =
      ((labels.map A).prod) i j := by
  induction labels generalizing i with
  | nil => by_cases hij : i = j <;> simp [matrixEntryPaths, hij]
  | cons t ts ih =>
      cases ts with
      | nil => simp [matrixEntryPaths]
      | cons u us =>
          rw [matrixEntryPaths, list_sum_map_flatMap]
          simp only [List.map_map, Function.comp_def, List.map_cons, List.prod_cons]
          simp_rw [List.sum_map_mul_left, ih]
          simp [Finset.sum_map_toList, Matrix.mul_apply]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmOperatorPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

open MvPolynomial

variable {K : Type*} [CommSemiring K]

/-- The endpoint IMM polynomial is the sum of its labelled path monomials. -/
theorem imm_eq_sum_path_products (n : ℕ) (hn : 0 < n) :
    imm K n = ((immPaths n hn).map fun p => (p.map (X (R := K))).prod).sum := by
  have h := matrixEntryPaths_sum_prod (immLayer K n) (List.finRange n)
    (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n)
  simp only [imm, dite_eq_left hn, List.ofFn_eq_map]
  exact h.symm

/-- The full IMM polynomial operator is a sum of products of its edge operators. -/
theorem mixedOperator_imm_eq_sum_paths (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool) :
    mixedOperator (K := K) isV (imm K n) =
      ((immPaths n hn).map fun p =>
        (p.map (variableOperator (K := K) isV)).prod).sum := by
  rw [imm_eq_sum_path_products n hn, map_list_sum]
  simp only [List.map_map, Function.comp_def, map_list_prod, mixedOperator_X]

/-- The operator expansion indexed by the finite type of paths. -/
theorem mixedOperator_imm_eq_sum_paths_fin (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool) :
    mixedOperator (K := K) isV (imm K n) =
      ∑ p : Fin (immPaths n hn).length,
        (((immPaths n hn).get p).map (variableOperator (K := K) isV)).prod := by
  rw [mixedOperator_imm_eq_sum_paths n hn isV]
  symm
  simpa only [List.get_eq_getElem] using
    (Fin.sum_univ_fun_getElem (immPaths n hn)
      (fun p => (p.map (variableOperator (K := K) isV)).prod))

/-- Applying the IMM operator is the sum of its individual path actions. -/
theorem mixedOperator_imm_apply_eq_sum_paths (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (f : MvPolynomial (Fin n × Fin n × Fin n) K) :
    mixedOperator isV (imm K n) f =
      ∑ p : Fin (immPaths n hn).length,
        ((((immPaths n hn).get p).map (variableOperator isV)).prod) f := by
  rw [mixedOperator_imm_eq_sum_paths_fin n hn isV, LinearMap.sum_apply]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmFockMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The actual IMM operator on a normalized monomial is the sum of its sparse path actions. -/
theorem mixedOperator_imm_complexFockMonomial (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (d : (Fin n × Fin n × Fin n) →₀ ℕ) :
    mixedOperator isV (imm ℂ n) (complexFockMonomial d) =
      ∑ p : Fin (immPaths n hn).length,
        (immPathAmplitude n hn isV d p : ℂ) •
          complexFockMonomial (immPathOccupation n hn isV d p) := by
  rw [mixedOperator_imm_apply_eq_sum_paths n hn isV]
  apply Finset.sum_congr rfl
  intro p hp
  have h := mixedOperator_path_complexFockMonomial isV ((immPaths n hn).get p)
    (immPaths_nodup n hn _ (List.get_mem _ p)) d
  simpa only [map_list_prod, List.map_map, Function.comp_def, mixedOperator_X,
    immPathAmplitude, immPathOccupation] using h

/-- Normalized matrix entries of the actual IMM operator are weighted path-shift counts. -/
theorem complexFockBasis_repr_mixedOperator_imm (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (d e : (Fin n × Fin n × Fin n) →₀ ℕ) :
    complexFockBasis.repr (mixedOperator isV (imm ℂ n) (complexFockMonomial d)) e =
      ∑ p : Fin (immPaths n hn).length,
        if immPathOccupation n hn isV d p = e then (immPathAmplitude n hn isV d p : ℂ)
        else 0 := by
  classical
  rw [mixedOperator_imm_complexFockMonomial n hn isV]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← complexFockBasis_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PathInjectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ ι : Type*}

/-- The signed list shift is the sum of the individual signed coordinates. -/
theorem edgeListShift_eq_sum (side : σ → Bool) (p : List (σ × ι × ι)) :
    edgeListShift side p =
      (p.map (fun e => Finsupp.single e (if side e.1 then (-1 : ℤ) else 1))).sum := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [edgeListShift, ih]

/-- In an ordered edge list, the edge in position `t` is labelled by `t`. -/
theorem edgeProfile_label {n : ℕ} (p : List (Fin n × ι × ι))
    (hp : p.map Prod.fst = List.finRange n) (t : Fin n) :
    (p[t.val]'(by rw [edgeList_length p hp]; exact t.isLt)).1 = t := by
  have hidx : t.val < (p.map Prod.fst).length := by
    simp only [List.length_map, edgeList_length p hp]
    exact t.isLt
  have h : (p.map Prod.fst)[t.val]'hidx = t := by simp [hp]
  simpa only [List.getElem_map] using h

/-- Rebuilding the ordered edge list from its profile changes nothing. -/
theorem edgeList_eq_ofFn_profile {n : ℕ} (p : List (Fin n × ι × ι))
    (hp : p.map Prod.fst = List.finRange n) :
    p = List.ofFn (fun t : Fin n => (t, edgeProfile p hp t)) := by
  apply List.ext_getElem (by simp [edgeList_length p hp])
  intro k hk hk'
  have hkn : k < n := by simpa using hk'
  simp only [List.getElem_ofFn]
  exact Prod.ext (edgeProfile_label p hp ⟨k, hkn⟩) rfl

/-- The list shift agrees with the layerwise finite sum used by profile operators. -/
theorem edgeListShift_eq_sum_profile {n : ℕ} (side : Fin n → Bool)
    (p : List (Fin n × ι × ι)) (hp : p.map Prod.fst = List.finRange n) :
    edgeListShift side p = ∑ t : Fin n,
      Finsupp.single (t, edgeProfile p hp t) (if side t then (-1 : ℤ) else 1) := by
  rw [edgeListShift_eq_sum]
  conv_lhs => rw [edgeList_eq_ofFn_profile p hp, List.map_ofFn, Fin.sum_ofFn]
  rfl

/-- Read a signed edge-list shift using its unique coordinate profile in one layer. -/
theorem edgeListShift_apply_profile [DecidableEq ι] {n : ℕ}
    (side : Fin n → Bool) (p : List (Fin n × ι × ι))
    (hp : p.map Prod.fst = List.finRange n) (t : Fin n) (a b : ι) :
    edgeListShift side p (t, a, b) =
      if edgeProfile p hp t = (a, b) then (if side t then -1 else 1) else 0 := by
  classical
  rw [edgeListShift_eq_sum_profile side p hp, Finsupp.finsetSum_apply,
    Finset.sum_eq_single t]
  · simp [Finsupp.single_apply]
  · intro j hj hjt
    simp [hjt]
  · simp

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.TraceExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite matrix expansions for the two trace moments in the IMM argument.
These identities contain no analytic or asymptotic assumptions. -/

noncomputable section
open scoped BigOperators Matrix

namespace Problem335

variable {I J P R : Type*} [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq J]

/-- The second moment is the sum of squares of all Gram entries. -/
theorem trace_gram_sq {I : Type u_1} {J : Type u_2}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (A : Matrix J I ℝ) :
    Matrix.trace ((A.transpose * A) ^ 2) =
      ∑ i, ∑ k, (∑ j, A j i * A j k) ^ 2 := by
  simp only [pow_two, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The Gram entry is a weighted count of pairs of paths with equal shifts. -/
theorem pathShiftMatrix_gram_apply
    {I : Type u_1} {J : Type u_2} {P : Type u_3} {R : Type u_4}
    [Fintype I] [Fintype J] [Fintype P] [DecidableEq I] [DecidableEq J] [CommSemiring R]
    (shift : I → P → J) (weight : I → P → R) (i k : I) :
    ((pathShiftMatrix shift weight).transpose * pathShiftMatrix shift weight) i k =
      ∑ p, ∑ q, if shift i p = shift k q then weight i p * weight k q else 0 := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pathShiftMatrix]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  simp [eq_comm]

/-- The second trace is the squared-overlap sum of the weighted path shifts. -/
theorem pathShiftMatrix_second_trace
    (shift : I → P → J) (weight : I → P → ℝ) :
    Matrix.trace (((pathShiftMatrix shift weight).transpose *
      pathShiftMatrix shift weight) ^ 2) =
      ∑ i, ∑ k, (∑ p, ∑ q,
        if shift i p = shift k q then weight i p * weight k q else 0) ^ 2 := by
  rw [trace_gram_sq]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact pathShiftMatrix_gram_apply shift weight i k

/-- The complete four-path expansion of the second trace moment. -/
theorem pathShiftMatrix_second_trace_four_paths
    (shift : I → P → J) (weight : I → P → ℝ) :
    Matrix.trace (((pathShiftMatrix shift weight).transpose *
      pathShiftMatrix shift weight) ^ 2) =
      ∑ i, ∑ k, ∑ p, ∑ q, ∑ r, ∑ s,
        if shift i p = shift k q ∧ shift i r = shift k s then
          weight i p * weight k q * weight i r * weight k s else 0 := by
  rw [pathShiftMatrix_second_trace]
  simp only [pow_two]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h₁ : shift i p = shift k q <;>
    by_cases h₂ : shift i r = shift k s <;> simp [h₁, h₂, mul_assoc]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmFiniteMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- Each finite normalized matrix entry is exactly the weighted sum of its IMM path shifts. -/
theorem immNormalizedMatrix_apply (n : ℕ) (hn : 0 < n) (side : Fin n → Bool)
    (a b : ℕ) (e : ImmTargetIndex n side a b) (d : ImmSourceIndex n side a b) :
    immNormalizedMatrix n side a b e d =
      ∑ p : Fin (immPaths n hn).length,
        if immPathOccupation n hn (fun x => side x.1) d.1 p = e.1
        then (immPathAmplitude n hn (fun x => side x.1) d.1 p : ℂ) else 0 := by
  classical
  unfold immNormalizedMatrix
  rw [LinearMap.toMatrix_apply, bidegreeComplexFockBasis_repr]
  change (Real.sqrt (multiFactorial e.1 : ℝ) : ℂ) *
    (mixedOperator (fun x => side x.1)
        (bidegreeComponent (fun x => side x.1) (immLayerVCount side) (immLayerUCount side)
          (imm ℂ n))
        ((bidegreeComplexFockBasis (σ := Fin n × Fin n × Fin n)
          (fun x => side x.1) a b d) : MvPolynomial (Fin n × Fin n × Fin n) ℂ)).coeff e.1 = _
  rw [bidegreeComplexFockBasis_apply]
  simp only [immLayerVCount, immLayerUCount, bidegreeComponent_imm]
  rw [← complexFockBasis_repr]
  exact complexFockBasis_repr_mixedOperator_imm n hn (fun x => side x.1) d.1 e.1

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.TraceComplexification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real nonnegative path matrix can be read over the complex numbers
without changing either of its two trace moments. -/

noncomputable section
open scoped BigOperators Matrix

namespace Problem335

variable {I J P : Type*} [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq J]

/-- Real entrywise complexification sends the real Gram matrix to the complex Gram matrix. -/
theorem complexify_gram {I : Type u_1} {J : Type u_2}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (A : Matrix J I ℝ) :
    (A.map Complex.ofReal).conjTranspose * A.map Complex.ofReal =
      (A.transpose * A).map Complex.ofReal := by
  ext i k
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Complex.ofReal_sum, Complex.ofReal_mul]

/-- Entrywise complexification preserves the real part of the trace. -/
theorem trace_complexify_re {I : Type u_1} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) :
    (A.map Complex.ofReal).trace.re = A.trace := by
  simp [Matrix.trace, Matrix.map_apply]

/-- Second moment agrees over the real and complex coefficient fields. -/
theorem complexify_second_trace (A : Matrix J I ℝ) :
    (((A.map Complex.ofReal).conjTranspose * A.map Complex.ofReal) ^ 2).trace.re =
      ((A.transpose * A) ^ 2).trace := by
  rw [complexify_gram]
  have h : ((A.transpose * A).map Complex.ofReal) ^ 2 =
      ((A.transpose * A) ^ 2).map Complex.ofReal := by
    exact (Matrix.map_pow (A.transpose * A) Complex.ofRealHom 2).symm
  rw [h, trace_complexify_re]

/-- Complexifying a path matrix complexifies just its weights. -/
theorem pathShiftMatrix_complexify {I : Type u_1} {J : Type u_2} {P : Type u_3}
    [Fintype I] [Fintype J] [Fintype P] [DecidableEq I] [DecidableEq J]
    (shift : I → P → J) (weight : I → P → ℝ) :
    (pathShiftMatrix shift weight).map Complex.ofReal =
      pathShiftMatrix shift (fun i p => (weight i p : ℂ)) := by
  ext j i
  simp only [pathShiftMatrix, Matrix.map_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

/-- Four-path expression of the second complex trace for real path weights. -/
theorem complex_path_second_trace_four_paths
    (shift : I → P → J) (weight : I → P → ℝ) :
    let A := pathShiftMatrix shift (fun i p => (weight i p : ℂ))
    ((A.conjTranspose * A) ^ 2).trace.re =
      ∑ i, ∑ k, ∑ p, ∑ q, ∑ r, ∑ s,
        if shift i p = shift k q ∧ shift i r = shift k s then
          weight i p * weight k q * weight i r * weight k s else 0 := by
  dsimp
  rw [← pathShiftMatrix_complexify, complexify_second_trace]
  exact pathShiftMatrix_second_trace_four_paths shift weight

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.AlphaParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem335.LowerParameters

theorem sqrt_ge_four {n : ℕ} (hn : 16 ≤ n) : 4 ≤ Real.sqrt (n : ℝ) := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  exact_mod_cast hn

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OccupationRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- Uniform upper bound for the occupation ratio. -/
theorem occupationRatio_le_one {t r : ℝ} {H : ℕ}
    (ht : 0 < t) (hr : 0 < r) (hH : (H : ℝ) ≤ t) :
    occupationRatio t r H ≤ 1 := by
  apply Finset.prod_le_one
  · intro j hj
    have hjH : (j : ℝ) ≤ H := by exact_mod_cast (Finset.mem_range.mp hj).le
    have hjt : (j : ℝ) / t ≤ 1 := (div_le_one ht).2 (hjH.trans hH)
    apply div_nonneg (by linarith)
    positivity
  · intro j hj
    have htj : 0 ≤ (j : ℝ) / t := by positivity
    have hrj : 0 ≤ (j : ℝ) / r := by positivity
    apply (div_le_one (by positivity : 0 < 1 + (j : ℝ) / r)).2
    linarith

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OccupationRatioAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- Algebraic removal of the geometric normalization from the occupation ratio. -/
theorem occupationRatio_mul_mean_pow {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (H : ℕ) :
    occupationRatio t r H * (t / r) ^ H =
      (∏ j ∈ Finset.range H, (t - (j : ℝ))) /
        (∏ j ∈ Finset.range H, (r + (j : ℝ))) := by
  have hconst : (t / r) ^ H = ∏ _j ∈ Finset.range H, t / r := by simp [div_pow]
  rw [occupationRatio, hconst, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hsum : r + (j : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hden : 1 + (j : ℝ) / r ≠ 0 := ne_of_gt (by positivity)
  field_simp

/-- The exact factorial-moment ratio over weak compositions. -/
theorem descFactorial_div_ascFactorial_eq_ratio {t r H : ℕ}
    (ht : 0 < t) (hr : 0 < r) (hH : H ≤ t) :
    (t.descFactorial H : ℝ) / (r.ascFactorial H : ℝ) =
      occupationRatio t r H * ((t : ℝ) / r) ^ H := by
  rw [occupationRatio_mul_mean_pow (by exact_mod_cast ht) (by exact_mod_cast hr)]
  congr 1
  · rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro j hj
    exact Nat.cast_sub (le_trans (Finset.mem_range.mp hj).le hH)
  · rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro j hj
    exact Nat.cast_add r j

/-- Every factorial order admits the independent geometric upper comparison. -/
theorem descFactorial_div_ascFactorial_le_mean_pow {t r H : ℕ}
    (ht : 0 < t) (hr : 0 < r) :
    (t.descFactorial H : ℝ) / (r.ascFactorial H : ℝ) ≤ ((t : ℝ) / r) ^ H := by
  by_cases hH : H ≤ t
  · rw [descFactorial_div_ascFactorial_eq_ratio ht hr hH]
    have hratio := occupationRatio_le_one (t := (t : ℝ)) (r := (r : ℝ)) (H := H) (by exact_mod_cast ht)
      (by exact_mod_cast hr) (by exact_mod_cast hH)
    calc
      occupationRatio t r H * ((t : ℝ) / r) ^ H ≤ 1 * ((t : ℝ) / r) ^ H :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = _ := one_mul _
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hH)]
    simp only [Nat.cast_zero, zero_div]
    positivity

/-- Zero total occupation is also allowed in the geometric upper comparison. -/
theorem descFactorial_div_ascFactorial_le_mean_pow_of_pos {t r H : ℕ} (hr : 0 < r) :
    (t.descFactorial H : ℝ) / (r.ascFactorial H : ℝ) ≤ ((t : ℝ) / r) ^ H := by
  by_cases ht : 0 < t
  · exact descFactorial_div_ascFactorial_le_mean_pow ht hr
  · have ht0 : t = 0 := by omega
    subst t
    cases H with
    | zero => simp
    | succ H => simp [Nat.descFactorial_succ]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OccupationComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- Upper comparison for nonnegative expansions in two independent groups. -/
theorem weighted_two_group_factorialMoment_sum_le {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (h k : ι → ℕ) {a v b u : ℕ} (hv : 0 < v) (hu : 0 < u)
    (hc : ∀ i ∈ s, 0 ≤ c i) :
    (∑ i ∈ s, c i *
      (((a.descFactorial (h i) : ℝ) / (v.ascFactorial (h i) : ℝ)) *
       ((b.descFactorial (k i) : ℝ) / (u.ascFactorial (k i) : ℝ)))) ≤
    ∑ i ∈ s, c i * (((a : ℝ) / v) ^ h i * ((b : ℝ) / u) ^ k i) := by
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hc i hi)
  exact mul_le_mul (descFactorial_div_ascFactorial_le_mean_pow_of_pos hv)
    (descFactorial_div_ascFactorial_le_mean_pow_of_pos hu) (by positivity) (by positivity)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OccupationSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

private lemma fallingFactorialSeries_eq (d : ℕ) :
    fallingFactorialSeries d = PowerSeries.C (d.factorial : ℝ) *
      (PowerSeries.X ^ d * (PowerSeries.mk 1 : PowerSeries ℝ) ^ (d + 1)) := by
  ext j
  rw [fallingFactorialSeries, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.mk_one_pow_eq_mk_choose_add]
  by_cases h : d ≤ j
  · rw [ite_eq_left h, PowerSeries.coeff_mk, Nat.add_sub_of_le h,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  · rw [ite_eq_right h, mul_zero, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

private lemma fallingFactorialSeries_prod {ι : Type*} [Fintype ι] (d : ι → ℕ) :
    (∏ i, fallingFactorialSeries (d i)) =
      PowerSeries.C (∏ i, (d i).factorial : ℝ) *
        (PowerSeries.X ^ (∑ i, d i) *
          (PowerSeries.mk 1 : PowerSeries ℝ) ^ ((∑ i, d i) + Fintype.card ι)) := by
  simp only [fallingFactorialSeries_eq, Finset.prod_mul_distrib,
    ← map_prod, Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

/-- Exact weighted weak-composition sum, with the impossible-degree case
explicitly zero. This is the coefficient-extraction form of the occupation
factorial moment identity. -/
theorem occupation_factorial_sum {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ι → ℕ) (t : ℕ) :
    (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) t,
      ∏ i, ((M i).descFactorial (d i) : ℝ)) =
      (∏ i, (d i).factorial : ℝ) *
        if (∑ i, d i) ≤ t then
          ((t + Fintype.card ι - 1).choose (t - ∑ i, d i) : ℝ) else 0 := by
  classical
  have hr : 0 < Fintype.card ι := Fintype.card_pos
  let H := ∑ i, d i
  have heq : H + Fintype.card ι = (H + Fintype.card ι - 1) + 1 := by omega
  have hcoeff := PowerSeries.coeff_prod (fun i => fallingFactorialSeries (d i)) t Finset.univ
  simp only [fallingFactorialSeries, PowerSeries.coeff_mk] at hcoeff
  rw [← hcoeff]
  change PowerSeries.coeff t (∏ i, fallingFactorialSeries (d i)) = _
  rw [fallingFactorialSeries_prod]
  change PowerSeries.coeff t (PowerSeries.C (∏ i, (d i).factorial : ℝ) *
    (PowerSeries.X ^ H * (PowerSeries.mk 1 : PowerSeries ℝ) ^
      (H + Fintype.card ι))) = _
  rw [heq, PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul']
  by_cases hH : H ≤ t
  · rw [ite_eq_left hH, PowerSeries.coeff_mk, ite_eq_left hH]
    have harr : H + Fintype.card ι - 1 + (t - H) = t + Fintype.card ι - 1 := by
      omega
    rw [harr]
    congr 2
    apply Nat.choose_symm_of_eq_add
    dsimp [H] at *
    omega
  · rw [ite_eq_right hH, ite_eq_right hH]

/-- Stars-and-bars count for the same finite weak-composition index set. -/
theorem occupation_composition_card {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (t : ℕ) :
    (Finset.finsuppAntidiag (Finset.univ : Finset ι) t).card =
      (t + Fintype.card ι - 1).choose t := by
  classical
  have h := occupation_factorial_sum (ι := ι) (fun _ => 0) t
  simp at h
  exact_mod_cast h

lemma occupation_choose_ratio (t r H : ℕ) (hr : 0 < r) (hH : H ≤ t) :
    ((t + r - 1).choose (t - H) : ℝ) / ((t + r - 1).choose t : ℝ) =
      (t.descFactorial H : ℝ) / (r.ascFactorial H : ℝ) := by
  have hfac (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by positivity
  have hdesc : (t.descFactorial H : ℝ) =
      (t.factorial : ℝ) / ((t - H).factorial : ℝ) := by
    apply (eq_div_iff (hfac _)).2
    exact_mod_cast (by simpa only [Nat.mul_comm] using
      Nat.factorial_mul_descFactorial hH)
  have hasc : (r.ascFactorial H : ℝ) =
      ((r + H - 1).factorial : ℝ) / ((r - 1).factorial : ℝ) := by
    apply (eq_div_iff (hfac _)).2
    exact_mod_cast (by simpa only [Nat.mul_comm] using
      Nat.factorial_mul_ascFactorial' r H hr)
  rw [Nat.cast_choose ℝ (by omega : t - H ≤ t + r - 1),
    Nat.cast_choose ℝ (by omega : t ≤ t + r - 1), hdesc, hasc]
  rw [show t + r - 1 - (t - H) = r + H - 1 by omega,
    show t + r - 1 - t = r - 1 by omega]
  field_simp

/-- The normalized factorial moment of the uniform distribution on weak
compositions. The result includes total orders above `t`, where both sides
vanish. -/
theorem occupation_factorial_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (d : ι → ℕ) (t : ℕ) :
    (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) t,
      ∏ i, ((M i).descFactorial (d i) : ℝ)) /
        (Finset.finsuppAntidiag (Finset.univ : Finset ι) t).card =
      (t.descFactorial (∑ i, d i) : ℝ) /
        ((Fintype.card ι).ascFactorial (∑ i, d i) : ℝ) *
          (∏ i, (d i).factorial : ℝ) := by
  rw [occupation_factorial_sum, occupation_composition_card]
  by_cases hH : (∑ i, d i) ≤ t
  · rw [ite_eq_left hH]
    rw [mul_div_assoc, occupation_choose_ratio t (Fintype.card ι) _
      Fintype.card_pos hH]
    ring
  · rw [ite_eq_right hH, mul_zero, zero_div,
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero,
      zero_div, zero_mul]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ActualImmRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the concrete rank measure with the finite normalized
matrix used in the IMM trace estimates. -/

noncomputable section

namespace Problem335.LowerParameters

theorem card_immSourceIndex_eq_rankDimension {n : ℕ} (hn : 4 ≤ n) :
    (Fintype.card (ImmSourceIndex n (balancedLayer hn) (a n) (b n)) : ℝ) =
      rankDimension n := by
  have h := card_bidegree_finsupp_exponents
    (fun x : Fin n × Fin n × Fin n => balancedLayer hn x.1) (a n) (b n)
  rw [balancedVariable_card_true hn, balancedVariable_card_false hn,
    Nat.multichoose_eq, Nat.multichoose_eq] at h
  simp only [Nat.card_eq_fintype_card] at h
  unfold rankDimension homogeneousDim
  exact_mod_cast h

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.IndependentCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace IndependentCoordinates


/-- Uniform finite averages are unchanged by relabeling. -/
theorem average_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : average (fun x => f (e x)) = average f := by
  simp only [average, e.sum_comp, Fintype.card_congr e]

/-- Independent coordinates factor the average of a product. -/
theorem average_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (f : ∀ i, α i → ℝ) :
    average (fun x : ∀ i, α i => ∏ i, f i (x i)) = ∏ i, average (f i) := by
  classical
  simp only [average, Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]
  congr 1
  exact (Fintype.prod_sum f).symm

/-- One independent pair of uniform labels agrees with probability `1 / card α`. -/
theorem average_pair_eq {α : Type*} [Fintype α] [DecidableEq α] :
    average (fun x : α × α => if x.1 = x.2 then (1 : ℝ) else 0) =
      (Fintype.card α : ℝ)⁻¹ := by
  rw [average, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_prod, Nat.cast_mul]
  by_cases h : (Fintype.card α : ℝ) = 0
  · simp [h]
  · field_simp

theorem average_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    average (fun x => f x + g x) = average f + average g := by
  simp [average, Finset.sum_add_distrib, add_div]

theorem average_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α => c) = c := by
  simp [average, Fintype.card_ne_zero]

theorem average_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    average (fun x => c * f x) = c * average f := by
  simp [average, ← Finset.mul_sum, mul_div_assoc]

/-- Extra independent coordinates that do not appear in the integrand cancel. -/
theorem average_ignore_right {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty β] (f : α → ℝ) :
    average (fun x : α × β => f x.1) = average f := by
  rw [average, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, Fintype.card_prod, Nat.cast_mul, average]
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_cases hα : (Fintype.card α : ℝ) = 0
  · simp [hα]
  · field_simp

/-- Pairwise disjoint subsets give an injective family of coordinate inclusions. -/
theorem sigma_val_injective {σ ι : Type*} (s : ι → Finset σ)
    (hs : Pairwise (fun i j => Disjoint (s i) (s j))) :
    Function.Injective (fun x : Σ i, s i => (x.2 : σ)) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ hxy
  change (x : σ) = (y : σ) at hxy
  have hij : i = j := by
    by_contra hne
    exact (Finset.disjoint_left.mp (hs hne)) x.property (hxy.symm ▸ y.property)
  subst j
  have h : x = y := Subtype.ext hxy
  subst y
  rfl

/-- Marginals of a uniform finite product are uniform, allowing different
coordinate types at different vertices. -/
theorem average_precomp_injective_dependent {σ τ : Type*} {β : σ → Type*}
    [Fintype σ] [Fintype τ] [∀ s, Fintype (β s)] [∀ s, Nonempty (β s)]
    [DecidableEq σ] [DecidableEq τ]
    (j : τ → σ) (hj : Function.Injective j) (f : (∀ t, β (j t)) → ℝ) :
    average (fun x : ∀ s, β s => f (fun t => x (j t))) = average f := by
  classical
  calc
    _ = average (fun x : (∀ t, β (j t)) ×
        (∀ s : {s // s ∉ Set.range j}, β s) => f x.1) :=
      average_equiv (restrictDependentAssignmentEquiv β j hj) _
    _ = _ := average_ignore_right f

theorem average_sigma_prod_dependent {ι : Type*} {κ : ι → Type*}
    {β : (Σ i, κ i) → Type*}
    [Fintype ι] [∀ i, Fintype (κ i)] [∀ s, Fintype (β s)]
    [DecidableEq ι] [∀ i, DecidableEq (κ i)]
    (f : ∀ i, (∀ t : κ i, β ⟨i,t⟩) → ℝ) :
    average (fun x : ∀ s, β s => ∏ i, f i (fun t => x ⟨i,t⟩)) =
      ∏ i, average (f i) := by
  let e := Equiv.piCurry (fun i (t : κ i) => β ⟨i,t⟩)
  have h := average_equiv e (fun x : ∀ i, ∀ t : κ i, β ⟨i,t⟩ => ∏ i, f i (x i))
  change average (fun x : ∀ s, β s => ∏ i, f i (fun t => x ⟨i,t⟩)) = _ at h
  exact h.trans (average_prod f)

theorem average_embedded_prod_dependent {σ ι : Type*} {κ : ι → Type*}
    {β : σ → Type*}
    [Fintype σ] [Fintype ι] [∀ i, Fintype (κ i)]
    [∀ s, Fintype (β s)] [∀ s, Nonempty (β s)]
    [DecidableEq σ] [DecidableEq ι] [∀ i, DecidableEq (κ i)]
    (j : ∀ i, κ i → σ) (hj : Function.Injective (Sigma.uncurry j))
    (f : ∀ i, (∀ t : κ i, β (j i t)) → ℝ) :
    average (fun x : ∀ s, β s => ∏ i, f i (fun t => x (j i t))) =
      ∏ i, average (f i) := by
  have h := average_precomp_injective_dependent (β := β) (Sigma.uncurry j) hj
    (fun x : ∀ s : Σ i, κ i, β (j s.1 s.2) => ∏ i, f i (fun t => x ⟨i,t⟩))
  exact h.trans (average_sigma_prod_dependent
    (β := fun s : Σ i, κ i => β (j s.1 s.2)) f)

/-- Disjoint coordinate families remain independent when vertex alphabets vary. -/
theorem average_disjoint_finset_prod_dependent {σ ι : Type*} {β : σ → Type*}
    [Fintype σ] [Fintype ι] [∀ s, Fintype (β s)] [∀ s, Nonempty (β s)]
    [DecidableEq σ] [DecidableEq ι]
    (s : ι → Finset σ) (hs : Pairwise (fun i j => Disjoint (s i) (s j)))
    (f : ∀ i, (∀ t : s i, β t) → ℝ) :
    average (fun x : ∀ s, β s => ∏ i, f i (fun t => x t)) =
      ∏ i, average (f i) := by
  exact average_embedded_prod_dependent (fun i (t : s i) => (t : σ))
    (sigma_val_injective s hs) f

end IndependentCoordinates
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.Pairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four-path pairing identities for the mixed-operator moment argument. -/

namespace Problem335
namespace Pairings

open scoped BigOperators

theorem ExactRespects.respects {α : Type*} {τ : Kind} {x : Labels α}
    (h : ExactRespects τ x) : Respects τ x := by
  cases τ
  · exact h
  · exact ⟨h.1, h.2.1⟩

/-- Equal pairings give two independent labels; different pairings give one. -/
theorem card_vertex (α : Type*) [Fintype α] [DecidableEq α] (τ σ : Kind) :
    Fintype.card (Vertex α τ σ) =
      Fintype.card α ^ (if τ = σ then 2 else 1) := by
  cases τ <;> cases σ
  · simpa [pow_two] using Fintype.card_congr (normalVertexEquiv α)
  · simpa using Fintype.card_congr (mixedVertexEquiv α)
  · simpa using Fintype.card_congr
      ((swapVertexEquiv α .diagonal .normal).trans (mixedVertexEquiv α))
  · simpa [pow_two] using Fintype.card_congr (diagonalVertexEquiv α)

/-- Each unchanged interface has two free labels, and each changed interface has one. -/
theorem free_label_exponent {β : Type*} [DecidableEq β] {L : ℕ}
    (τ : Fin (L + 1) → β) :
    (∑ i : Fin L, if τ i.castSucc = τ i.succ then 2 else 1) =
      2 * L - adjacentSwitches τ := by
  have h : (∑ i : Fin L, if τ i.castSucc = τ i.succ then 2 else 1) +
      adjacentSwitches τ = 2 * L := by
    rw [adjacentSwitches, Finset.card_eq_sum_ones, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    calc
      _ = ∑ _i : Fin L, 2 := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp_all
      _ = 2 * L := by simp [Nat.mul_comm]
  omega

/-- Exact unweighted count of relaxed assignments for a fixed pairing word. -/
theorem card_assignments (α : Type*) [Fintype α] [DecidableEq α]
    {L : ℕ} (τ : Fin (L + 1) → Kind) :
    Fintype.card (Assignments α τ) =
      Fintype.card α ^ (2 * L - adjacentSwitches τ) := by
  unfold Assignments
  rw [Fintype.card_pi]
  simp_rw [card_vertex]
  rw [Finset.prod_pow_eq_pow_sum, free_label_exponent]

end Pairings
end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PairingWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.Pairings
open IndependentCoordinates

theorem average_vertexPairEq (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α]
    (τ σ : Kind) :
    average (vertexPairEq (α := α) (τ := τ) (σ := σ)) =
      if τ = .normal ∧ σ = .normal then (Fintype.card α : ℝ)⁻¹ else 1 := by
  cases τ <;> cases σ
  · change average (fun x : Vertex α .normal .normal =>
      pairEq (normalVertexEquiv α x)) = (Fintype.card α : ℝ)⁻¹
    exact (average_equiv (normalVertexEquiv α) pairEq).trans (average_pair_eq (α := α))
  · have h : vertexPairEq (α := α) (τ := .normal) (σ := .diagonal) = fun _ => (1 : ℝ) := by
      funext x
      simp [vertexPairEq, x.property.2.1]
    simp [h, average_const]
  · have h : vertexPairEq (α := α) (τ := .diagonal) (σ := .normal) = fun _ => (1 : ℝ) := by
      funext x
      simp [vertexPairEq, x.property.1.1]
    simp [h, average_const]
  · have h : vertexPairEq (α := α) (τ := .diagonal) (σ := .diagonal) = fun _ => (1 : ℝ) := by
      funext x
      simp [vertexPairEq, x.property.1.1]
    simp [h, average_const]

theorem average_endpoint_group (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α]
    {L : ℕ} (τ : Fin (L + 1) → Kind) (s : Finset (Fin L)) :
    average (fun x : ∀ v : s, Vertex α (τ v.val.castSucc) (τ v.val.succ) =>
      ∏ v, vertexPairEq (x v)) =
      (Fintype.card α : ℝ)⁻¹ ^ normalEndpointCount τ s := by
  rw [average_prod]
  simp_rw [average_vertexPairEq]
  rw [Finset.prod_coe_sort s (fun v : Fin L =>
    if τ v.castSucc = .normal ∧ τ v.succ = .normal then
      (Fintype.card α : ℝ)⁻¹ else 1), ← Finset.prod_filter]
  simp [normalEndpointCount]

theorem average_endpoint_correction (α : Type*) [Fintype α] [DecidableEq α]
    [Nonempty α] {L : ℕ} (τ : Fin (L + 1) → Kind) (s : Finset (Fin L)) (c : ℝ) :
    average (fun x : ∀ v : s, Vertex α (τ v.val.castSucc) (τ v.val.succ) =>
      1 + c * ∏ v, vertexPairEq (x v)) =
      1 + c * (Fintype.card α : ℝ)⁻¹ ^ normalEndpointCount τ s := by
  rw [average_add, average_const, average_const_mul, average_endpoint_group]

/-- Exact average of normal-layer corrections for disjoint endpoint sets in
actual relaxed vertex assignments, including forced-equality interfaces. -/
theorem average_assignment_corrections (α : Type*) [Fintype α] [DecidableEq α]
    [Nonempty α] {L : ℕ} (τ : Fin (L + 1) → Kind)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Finset (Fin L)) (hs : Pairwise (fun i j => Disjoint (s i) (s j)))
    (c : ι → ℝ) :
    average (fun x : Assignments α τ => ∏ i, (1 + c i * endpointCoincidence (s i) x)) =
      ∏ i, (1 + c i * (Fintype.card α : ℝ)⁻¹ ^ normalEndpointCount τ (s i)) := by
  change average (fun x : Assignments α τ =>
    ∏ i, (1 + c i * ∏ v : s i, vertexPairEq (x v))) = _
  have h := average_disjoint_finset_prod_dependent
    (β := fun v : Fin L => Vertex α (τ v.castSucc) (τ v.succ)) s hs
    (fun i (x : ∀ v : s i, Vertex α (τ v.val.castSucc) (τ v.val.succ)) =>
      1 + c i * ∏ v, vertexPairEq (x v))
  apply h.trans
  apply Finset.prod_congr rfl
  intro i _
  exact average_endpoint_correction α τ (s i) (c i)

/-- The weighted relaxed-assignment count: its unweighted count times the
product of the independent normal-layer correction averages. -/
theorem sum_assignment_corrections (α : Type*) [Fintype α] [DecidableEq α]
    [Nonempty α] {L : ℕ} (τ : Fin (L + 1) → Kind)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Finset (Fin L)) (hs : Pairwise (fun i j => Disjoint (s i) (s j)))
    (c : ι → ℝ) :
    (∑ x : Assignments α τ, ∏ i, (1 + c i * endpointCoincidence (s i) x)) =
      (Fintype.card α : ℝ) ^ (2 * L - adjacentSwitches τ) *
        ∏ i, (1 + c i * (Fintype.card α : ℝ)⁻¹ ^ normalEndpointCount τ (s i)) := by
  have h := average_assignment_corrections α τ s hs c
  rw [average] at h
  have hc : (Fintype.card (Assignments α τ) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum := (div_eq_iff hc).mp h
  rw [card_assignments, Nat.cast_pow] at hsum
  simpa only [mul_comm] using hsum

theorem layer_coordinate_eq_iff {α : Type*} {L : ℕ}
    (a : α) (x : Fin L → Labels α) (t : Fin (L + 1)) :
    (zipLabels (closePaths a x t.castSucc) (closePaths a x t.succ)).p =
      (zipLabels (closePaths a x t.castSucc) (closePaths a x t.succ)).r ↔
    ∀ v ∈ internalEndpointSet t, (x v).p = (x v).r := by
  simp only [zipLabels, Prod.mk.injEq]
  constructor
  · intro h v hv
    rcases (Finset.mem_filter.mp hv).2 with hv | hv
    · subst t
      simpa only [closePaths_internal] using h.2
    · subst t
      simpa only [Fin.castSucc_succ, closePaths_internal] using h.1
  · intro h
    constructor
    · have hleft : ∀ t : Fin (L + 1),
          (∀ v ∈ internalEndpointSet t, (x v).p = (x v).r) →
          (closePaths a x t.castSucc).p = (closePaths a x t.castSucc).r := by
        intro t
        refine Fin.cases ?_ (fun i => ?_) t
        · intro _
          rfl
        · intro hi
          simpa only [Fin.castSucc_succ, closePaths_internal] using
            hi i (by simp [internalEndpointSet])
      exact hleft t h
    · have hright : ∀ t : Fin (L + 1),
          (∀ v ∈ internalEndpointSet t, (x v).p = (x v).r) →
          (closePaths a x t.succ).p = (closePaths a x t.succ).r := by
        intro t
        refine Fin.lastCases ?_ (fun i => ?_) t
        · intro _
          simp [Fin.succ_last, closePaths_last, constantLabels]
        · intro hi
          simpa only [closePaths_internal] using
            hi i (by simp [internalEndpointSet])
      exact hright t h

/-- The product of endpoint indicators is exactly the full layer-coordinate
coincidence indicator, including either fixed external endpoint. -/
theorem endpointCoincidence_eq_layer_indicator {α : Type*} [DecidableEq α]
    {L : ℕ} (a : α) (τ : Fin (L + 1) → Kind) (x : Assignments α τ)
    (t : Fin (L + 1)) :
    endpointCoincidence (internalEndpointSet t) x =
      if (zipLabels (closePaths a (fun v => (x v).val) t.castSucc)
          (closePaths a (fun v => (x v).val) t.succ)).p =
        (zipLabels (closePaths a (fun v => (x v).val) t.castSucc)
          (closePaths a (fun v => (x v).val) t.succ)).r then 1 else 0 := by
  simp only [endpointCoincidence, vertexPairEq, Fintype.prod_boole,
    layer_coordinate_eq_iff, Subtype.forall]

/-- Exact weighted count in terms of the actual layer coordinates of relaxed
endpoint-fixed path quadruples.  The sole combinatorial hypothesis is that the
selected layers have disjoint internal endpoint sets. -/
theorem sum_relaxedPaths_layer_corrections (α : Type*) [Fintype α]
    [DecidableEq α] [Nonempty α] {L : ℕ} (a : α) (τ : Fin (L + 1) → Kind)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → Fin (L + 1))
    (ht : Pairwise (fun i j => Disjoint (internalEndpointSet (t i))
      (internalEndpointSet (t j)))) (c : ι → ℝ) :
    (∑ x : RelaxedPaths α a τ, ∏ i,
      (1 + c i * if
        (zipLabels (closePaths a x.val (t i).castSucc)
          (closePaths a x.val (t i).succ)).p =
        (zipLabels (closePaths a x.val (t i).castSucc)
          (closePaths a x.val (t i).succ)).r then 1 else 0)) =
      (Fintype.card α : ℝ) ^ (2 * L - adjacentSwitches τ) *
        ∏ i, (1 + c i * (Fintype.card α : ℝ)⁻¹ ^
          normalEndpointCount τ (internalEndpointSet (t i))) := by
  calc
    _ = ∑ x : Assignments α τ, ∏ i,
        (1 + c i * endpointCoincidence (internalEndpointSet (t i)) x) := by
      apply Fintype.sum_equiv (relaxedPathsEquivAssignments α a τ)
      intro x
      apply Finset.prod_congr rfl
      intro i _
      rw [endpointCoincidence_eq_layer_indicator a τ]
      rfl
    _ = _ := sum_assignment_corrections α τ (fun i => internalEndpointSet (t i)) ht c

end Problem335.Pairings

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PairingNeighborCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.Pairings

/-- The actual path endpoints coincide with the schedule's internal ends. -/
theorem internalEndpointSet_eq_internalEnds {L : ℕ} (t : Fin (L + 1)) :
    internalEndpointSet t = BalancedSchedule.internalEnds t := by
  ext v
  simp [internalEndpointSet, BalancedSchedule.internalEnds, Fin.ext_iff]

/-- Boolean word form of the normal-endpoint exponent in the weighted
relaxed-path count, using the canonical schedule coincidence set. -/
theorem normalEndpointCount_eq_nnInternalEnds_card {L : ℕ}
    (w : Fin (L + 1) → Bool) (t : Fin (L + 1)) :
    normalEndpointCount (fun i => boolKindEquiv (w i)) (internalEndpointSet t) =
      (BalancedSchedule.nnInternalEnds w t).card := by
  have hbool (b : Bool) : boolKindEquiv b = .normal ↔ b = false := by
    cases b <;> simp
  unfold normalEndpointCount BalancedSchedule.nnInternalEnds
  rw [internalEndpointSet_eq_internalEnds]
  congr 1
  apply Finset.filter_congr
  intro v hv
  simp only [hbool]
  rfl

/-- The complete word correction expressed in the exponents supplied by the
actual relaxed-path averaging theorem. -/
theorem correction_eq_normalEndpointCount_product {L : ℕ}
    (V : Finset (Fin (L + 1))) (w : Fin (L + 1) → Bool) (A x : ℝ) :
    IsolatedWeight.correction V BalancedSchedule.adjacent A x w =
      ∏ t ∈ V.filter (fun t => w t = false),
        (1 + A * x ^ normalEndpointCount (fun i => boolKindEquiv (w i))
          (internalEndpointSet t)) := by
  rw [BalancedSchedule.correction_eq_nnInternalEnds_product]
  simp_rw [normalEndpointCount_eq_nnInternalEnds_card]

end Problem335.Pairings

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PairingPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem335.Pairings

open scoped BigOperators

/-- Regroup sums whose weight remembers the canonical pairing word. -/
theorem sum_compatiblePaths_pairingWeight {α R : Type*}
    [Fintype α] [DecidableEq α] [AddCommMonoid R] {L : ℕ}
    (a : α) (w : (Fin (L + 1) → Kind) → (Fin L → Labels α) → R) :
    (∑ x : CompatiblePaths α (L := L) a,
      w (fun t => classify (layerLabels a x.1 t)) x.1) =
      ∑ τ : Fin (L + 1) → Kind, ∑ x : ExactPaths α a τ, w τ x.1 := by
  classical
  simpa only [Fintype.sum_sigma] using
    (Fintype.sum_equiv (compatiblePathsEquivSigma α a)
      (fun x : CompatiblePaths α (L := L) a =>
        w (fun t => classify (layerLabels a x.1 t)) x.1)
      (fun x : Σ τ : Fin (L + 1) → Kind, ExactPaths α a τ => w x.1 x.2.1)
      (fun _ => rfl))

/-- Enlarging a finite summation domain preserves inequalities for nonnegative weights. -/
theorem sum_subtype_le_of_imp {ι : Type*} [Fintype ι]
    (P Q : ι → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ x, P x → Q x) (w : ι → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x : {x // P x}, w x.1) ≤ ∑ x : {x // Q x}, w x.1 := by
  classical
  calc
    _ = ∑ x ∈ Finset.univ.filter P, w x :=
      (Finset.sum_subtype _ (by intro x; simp) w).symm
    _ ≤ ∑ x ∈ Finset.univ.filter Q, w x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hPQ x hx
      · intro x _ _
        exact hw x
    _ = _ := Finset.sum_subtype _ (by intro x; simp) w

/-- Dropping the diagonal inequalities introduces only nonnegative summands. -/
theorem sum_exactPaths_le_sum_relaxedPaths {α : Type*}
    [Fintype α] [DecidableEq α] {L : ℕ} (a : α)
    (τ : Fin (L + 1) → Kind) (w : (Fin L → Labels α) → ℝ)
    (hw : ∀ x, 0 ≤ w x) :
    (∑ x : ExactPaths α a τ, w x.1) ≤ ∑ x : RelaxedPaths α a τ, w x.1 := by
  apply sum_subtype_le_of_imp _ _ ?_ w hw
  intro x hx t
  exact (hx t).respects

/-- Exact grouping followed by relaxation: the combinatorial second-trace upper bound. -/
theorem sum_compatiblePaths_le_sum_relaxedPaths {α : Type*}
    [Fintype α] [DecidableEq α] {L : ℕ} (a : α)
    (w : (Fin (L + 1) → Kind) → (Fin L → Labels α) → ℝ)
    (hw : ∀ τ x, 0 ≤ w τ x) :
    (∑ x : CompatiblePaths α (L := L) a,
      w (fun t => classify (layerLabels a x.1 t)) x.1) ≤
      ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths α a τ, w τ x.1 := by
  rw [sum_compatiblePaths_pairingWeight]
  exact Finset.sum_le_sum (fun τ _ => sum_exactPaths_le_sum_relaxedPaths a τ (w τ) (hw τ))

end Problem335.Pairings

end OAI
end

section
-- module Solutions.OAIQW_Problem335.SecondMomentPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact four-path pairing classes are disjoint.  Dropping the diagonal
inequalities enlarges each class, and therefore increases every nonnegative
weighted second-moment sum. -/

noncomputable section
open scoped BigOperators

namespace Problem335.MomentPairing

open Pairings

lemma layerWeight_nonneg {γ : Type*} {c : ℝ} (hc : 0 ≤ c)
    (τ : Kind) (x : Labels γ) : 0 ≤ layerWeight c τ x := by
  classical
  cases τ <;> simp only [layerWeight]
  · positivity
  · exact hc

lemma pathWeight_nonneg {γ : Type*} {L : ℕ} (isV : Fin (L + 1) → Bool)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (endpoint : γ)
    (τ : Fin (L + 1) → Kind) (x : Fin L → Labels γ) :
    0 ≤ pathWeight isV α β endpoint τ x := by
  apply Finset.prod_nonneg
  intro t _
  apply layerWeight_nonneg
  split <;> positivity

/-- The exact weighted relaxation step in the four-path second-moment proof. -/
theorem sum_compatible_pathWeight_le {γ : Type*} [Fintype γ] [DecidableEq γ] {L : ℕ}
    (isV : Fin (L + 1) → Bool) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (endpoint : γ) :
    (∑ x : {x : Fin L → Labels γ // Compatible endpoint x},
      pathWeight isV α β endpoint (classifyWord endpoint x.1) x.1) ≤
    ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
      pathWeight isV α β endpoint τ x.1 := by
  have hc (x : Fin L → Labels γ) : classifyWord endpoint x =
      (fun t => Pairings.classify (Pairings.layerLabels endpoint x t)) := by
    classical
    funext t
    unfold classifyWord classifyLayer Pairings.classify layerLabels Pairings.layerLabels
    split_ifs <;> rfl
  simp_rw [hc]
  exact Pairings.sum_compatiblePaths_le_sum_relaxedPaths endpoint
    (fun τ x => pathWeight isV α β endpoint τ x)
    (fun τ x => pathWeight_nonneg isV hα hβ endpoint τ x)


end Problem335.MomentPairing

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.RelaxedWeightBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335.MomentPairing

open scoped BigOperators
open Pairings

/-- Extract all diagonal weights and bound each U coincidence factor by `1+β`. -/
theorem pathWeight_le_extracted {γ : Type*} [DecidableEq γ] {L : ℕ}
    (isV : Fin (L + 1) → Bool) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (endpoint : γ) (τ : Fin (L + 1) → Kind) (x : Fin L → Labels γ) :
    pathWeight isV α β endpoint τ x ≤
      α⁻¹ ^ diagonalVCount isV τ * β ^ diagonalUCount isV τ *
        (1 + β) ^ uLayerCount isV * normalVCorrection isV α endpoint τ x := by
  classical
  let vd (t : Fin (L + 1)) : ℝ :=
    if isV t = true ∧ τ t = .diagonal then α⁻¹ else 1
  let ud (t : Fin (L + 1)) : ℝ :=
    if isV t = false ∧ τ t = .diagonal then β else 1
  let ub (t : Fin (L + 1)) : ℝ := if isV t = false then 1 + β else 1
  let nv (t : Fin (L + 1)) : ℝ :=
    if isV t = true ∧ τ t = .normal then
      1 + α⁻¹ * if (layerLabels endpoint x t).p = (layerLabels endpoint x t).r then 1 else 0
    else 1
  have hlocal (t : Fin (L + 1)) :
      layerWeight (if isV t then α⁻¹ else β) (τ t) (layerLabels endpoint x t) ≤
        vd t * ud t * ub t * nv t := by
    cases hv : isV t <;> cases ht : τ t <;>
      by_cases he : (layerLabels endpoint x t).p = (layerLabels endpoint x t).r <;>
      simp [layerWeight, vd, ud, ub, nv, hv, ht, he] <;> nlinarith [sq_nonneg β]
  have hprod : pathWeight isV α β endpoint τ x ≤
      (∏ t, vd t) * (∏ t, ud t) * (∏ t, ub t) * (∏ t, nv t) := by
    unfold pathWeight
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro t _
      apply layerWeight_nonneg
      split <;> positivity
    · intro t _
      exact hlocal t
  have hvd : (∏ t, vd t) = α⁻¹ ^ diagonalVCount isV τ := by
    simp only [vd, ← Finset.prod_filter, Finset.prod_const, diagonalVCount]
  have hud : (∏ t, ud t) = β ^ diagonalUCount isV τ := by
    simp only [ud, ← Finset.prod_filter, Finset.prod_const, diagonalUCount]
  have hub : (∏ t, ub t) = (1 + β) ^ uLayerCount isV := by
    simp only [ub, ← Finset.prod_filter, Finset.prod_const, uLayerCount]
  have hnv : (∏ t, nv t) = normalVCorrection isV α endpoint τ x := by
    simpa [nv, normalVCorrection, normalVLayers, Finset.prod_filter] using
      (Finset.prod_coe_sort (normalVLayers isV τ) (fun t : Fin (L + 1) =>
        1 + α⁻¹ * if (layerLabels endpoint x t).p = (layerLabels endpoint x t).r
          then 1 else 0)).symm
  simpa only [hvd, hud, hub, hnv] using hprod

/-- The full weighted relaxed-quadruple bound used in the second trace. -/
theorem sum_relaxed_pathWeight_le {γ : Type*} [Fintype γ] [DecidableEq γ]
    [Nonempty γ] {L : ℕ} (isV : Fin (L + 1) → Bool)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (endpoint : γ)
    (τ : Fin (L + 1) → Kind)
    (hs : Pairwise (fun t u : normalVLayers isV τ =>
      Disjoint (internalEndpointSet t.1) (internalEndpointSet u.1))) :
    (∑ x : RelaxedPaths γ endpoint τ, pathWeight isV α β endpoint τ x.1) ≤
      α⁻¹ ^ diagonalVCount isV τ * β ^ diagonalUCount isV τ *
        (1 + β) ^ uLayerCount isV *
        ((Fintype.card γ : ℝ) ^ (2 * L - adjacentSwitches τ) *
          ∏ t : normalVLayers isV τ,
            (1 + α⁻¹ * (Fintype.card γ : ℝ)⁻¹ ^
              normalEndpointCount τ (internalEndpointSet t.1))) := by
  classical
  calc
    _ ≤ ∑ x : RelaxedPaths γ endpoint τ,
        (α⁻¹ ^ diagonalVCount isV τ * β ^ diagonalUCount isV τ *
          (1 + β) ^ uLayerCount isV) * normalVCorrection isV α endpoint τ x.1 := by
      apply Finset.sum_le_sum
      intro x _
      exact pathWeight_le_extracted isV hα hβ endpoint τ x.1
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact sum_relaxedPaths_layer_corrections γ endpoint τ
        (fun t : normalVLayers isV τ => t.1) hs (fun _ => α⁻¹)

/-- Separate the free two-path count from the switch penalty. -/
theorem assignmentPower_eq_normalized {L : ℕ} (τ : Fin (L + 1) → Kind)
    {N : ℝ} (hN : N ≠ 0) :
    N ^ (2 * L - adjacentSwitches τ) = N ^ (2 * L) * N⁻¹ ^ adjacentSwitches τ := by
  have hsw : adjacentSwitches τ ≤ L := by
    unfold adjacentSwitches
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin L))
      (fun i => τ i.castSucc ≠ τ i.succ)
  have hle : adjacentSwitches τ ≤ 2 * L := by omega
  have heq : N ^ (2 * L) = N ^ (2 * L - adjacentSwitches τ) *
      N ^ adjacentSwitches τ := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [heq, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hN), mul_one]

/-- Full combinatorial moment reduction, summed over all pairing words. -/
theorem sum_relaxed_pathWeight_le_wordSum {γ : Type*} [Fintype γ] [DecidableEq γ]
    [Nonempty γ] {L : ℕ} (isV : Fin (L + 1) → Bool)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (endpoint : γ)
    (hs : ∀ τ : Fin (L + 1) → Kind,
      Pairwise (fun t u : normalVLayers isV τ =>
        Disjoint (internalEndpointSet t.1) (internalEndpointSet u.1))) :
    (∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
      pathWeight isV α β endpoint τ x.1) ≤
      (1 + β) ^ uLayerCount isV * (Fintype.card γ : ℝ) ^ (2 * L) *
        ∑ τ : Fin (L + 1) → Kind, relaxedWordWeight isV (Fintype.card γ) α β τ := by
  have hN : (Fintype.card γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ∑ τ : Fin (L + 1) → Kind,
        (1 + β) ^ uLayerCount isV * (Fintype.card γ : ℝ) ^ (2 * L) *
          relaxedWordWeight isV (Fintype.card γ) α β τ := by
      apply Finset.sum_le_sum
      intro τ _
      have h := sum_relaxed_pathWeight_le isV hα hβ endpoint τ (hs τ)
      rw [assignmentPower_eq_normalized τ hN] at h
      apply h.trans_eq
      unfold relaxedWordWeight
      ring
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Reindex all pairing words using the canonical false-normal, true-diagonal encoding. -/
theorem sum_relaxedWordWeight_eq_bool {L : ℕ} (isV : Fin (L + 1) → Bool)
    (N α β : ℝ) :
    (∑ τ : Fin (L + 1) → Kind, relaxedWordWeight isV N α β τ) =
      ∑ w : Fin (L + 1) → Bool,
        relaxedWordWeight isV N α β (fun t => boolKindEquiv (w t)) := by
  exact (Equiv.sum_comp (Equiv.piCongrRight (fun _ : Fin (L + 1) => boolKindEquiv))
    (relaxedWordWeight isV N α β)).symm

/-- Consume a Boolean-word estimate after the full relaxed-path averaging. -/
theorem sum_relaxed_pathWeight_le_of_boolWordSum {γ : Type*} [Fintype γ]
    [DecidableEq γ] [Nonempty γ] {L : ℕ} (isV : Fin (L + 1) → Bool)
    {α β B : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (endpoint : γ)
    (hs : ∀ τ : Fin (L + 1) → Kind,
      Pairwise (fun t u : normalVLayers isV τ =>
        Disjoint (internalEndpointSet t.1) (internalEndpointSet u.1)))
    (hword : (∑ w : Fin (L + 1) → Bool,
      relaxedWordWeight isV (Fintype.card γ) α β (fun t => boolKindEquiv (w t))) ≤ B) :
    (∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
      pathWeight isV α β endpoint τ x.1) ≤
      (1 + β) ^ uLayerCount isV * (Fintype.card γ : ℝ) ^ (2 * L) * B := by
  apply (sum_relaxed_pathWeight_le_wordSum isV hα hβ endpoint hs).trans
  rw [sum_relaxedWordWeight_eq_bool]
  exact mul_le_mul_of_nonneg_left hword (by positivity)

end Problem335.MomentPairing

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.RelaxedWordBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.MomentPairing
open Pairings

/-- The averaged pairing summand is exactly the canonical Boolean-word weight. -/
theorem relaxedWordWeight_eq_isolatedWeight {L : ℕ}
    (isV w : Fin (L + 1) → Bool) (N α β : ℝ) :
    relaxedWordWeight isV N α β (fun i => boolKindEquiv (w i)) =
      IsolatedWeight.weight (BalancedSchedule.internalEdges (L + 1))
        (Finset.univ.filter (fun i => isV i = true))
        BalancedSchedule.adjacent α⁻¹ β N⁻¹ w := by
  classical
  have hn (b : Bool) : boolKindEquiv b = Kind.normal ↔ b = false := by
    cases b <;> simp
  have hd (b : Bool) : boolKindEquiv b = Kind.diagonal ↔ b = true := by
    cases b <;> simp
  have hs : adjacentSwitches (fun i => boolKindEquiv (w i)) =
      SwitchRestoration.switchCount (BalancedSchedule.internalEdges (L + 1)) w := by
    rw [BalancedSchedule.internalEdges_eq_pathEdges, SwitchRestoration.switchCount_pathEdges]
    simp only [adjacentSwitches, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    simp only [show (boolKindEquiv (w i.castSucc) ≠ boolKindEquiv (w i.succ)) ↔
      w i.castSucc ≠ w i.succ from not_congr boolKindEquiv.injective.eq_iff]
  have hv : diagonalVCount isV (fun i => boolKindEquiv (w i)) =
      ((Finset.univ.filter (fun i => isV i = true)).filter (fun i => w i = true)).card := by
    simp only [diagonalVCount, hd, Finset.filter_filter]
  have hu : diagonalUCount isV (fun i => boolKindEquiv (w i)) =
      ((Finset.univ \ Finset.univ.filter (fun i => isV i = true)).filter
        (fun i => w i = true)).card := by
    unfold diagonalUCount
    congr 1
    ext i
    simp only [ Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
      true_and, hd]
    cases isV i <;> simp
  have hnV : normalVLayers isV (fun i => boolKindEquiv (w i)) =
      (Finset.univ.filter (fun i => isV i = true)).filter (fun i => w i = false) := by
    ext i
    simp [normalVLayers, hn]
  unfold relaxedWordWeight IsolatedWeight.weight
  rw [hs, hv, hu, correction_eq_normalEndpointCount_product]
  congr 1
  simpa only [hnV] using
    (Finset.prod_coe_sort (normalVLayers isV (fun i => boolKindEquiv (w i)))
      (fun t : Fin (L + 1) => 1 + α⁻¹ * N⁻¹ ^
        normalEndpointCount (fun i => boolKindEquiv (w i)) (internalEndpointSet t)))

end Problem335.MomentPairing

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ActualRelaxedWeightBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335.MomentPairing
open Pairings LowerParameters

theorem balanced_normalV_endpoints_disjoint {L : ℕ} (hn : 4 ≤ L + 1)
    (τ : Fin (L + 1) → Kind) :
    Pairwise (fun t u : normalVLayers (balancedLayer hn) τ =>
      Disjoint (internalEndpointSet t.1) (internalEndpointSet u.1)) := by
  intro t u htu
  rw [internalEndpointSet_eq_internalEnds, internalEndpointSet_eq_internalEnds]
  apply balancedLayer_internalEnds_disjoint hn
  · exact (Finset.mem_filter.mp t.property).2.1
  · exact (Finset.mem_filter.mp u.property).2.1
  · exact fun h => htu (Subtype.ext h)

theorem sum_relaxed_pathWeight_balanced_le_exp {L : ℕ} (hn : 16 ≤ L + 1)
    (endpoint : Fin (L + 1)) :
    (∑ τ : Fin (L + 1) → Kind,
      ∑ x : RelaxedPaths (Fin (L + 1)) endpoint τ,
        pathWeight (balancedLayer (show 4 ≤ L + 1 by omega))
          (alpha (L + 1)) (beta (L + 1)) endpoint τ x.1) ≤
      (1 + beta (L + 1)) ^ m (L + 1) * ((L + 1 : ℕ) : ℝ) ^ (2 * L) *
        Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ)) := by
  have hn4 : 4 ≤ L + 1 := by omega
  have h := sum_relaxed_pathWeight_le_of_boolWordSum
    (balancedLayer hn4) (alpha_pos hn4).le (beta_pos hn4).le endpoint
    (balanced_normalV_endpoints_disjoint hn4)
    (B := Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ)))
  have hw : (∑ w : Fin (L + 1) → Bool,
      relaxedWordWeight (balancedLayer hn4) (Fintype.card (Fin (L + 1)))
        (alpha (L + 1)) (beta (L + 1)) (fun t => boolKindEquiv (w t))) ≤
      Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ)) := by
    simpa only [Fintype.card_fin, relaxedWordWeight_eq_isolatedWeight] using
      actual_balanced_word_sum_bound hn
  simpa only [Fintype.card_fin, uLayerCount, balancedLayer_card_false] using h hw

end Problem335.MomentPairing

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PowerPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small change in exponent from one to `rho` does not destroy the
inverse-square-root scale of the rounded operator parameters. -/

noncomputable section
open Filter Topology

namespace Problem335.PowerPerturbation

lemma tendsto_error : Tendsto error atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  convert (hlog.const_mul 2).add (hinv.const_mul 2) using 1
  · funext x
    simp [error, div_eq_mul_inv, mul_assoc]
  · norm_num

lemma eventually_error_le_log_two :
    ∀ᶠ n : ℝ in atTop, error n ≤ Real.log 2 := by
  exact tendsto_error.eventually_le_const (Real.log_pos (by norm_num))

/-- Deterministic perturbation estimate, with all rounding and exponent
hypotheses explicit. The extra `exp (1/n)` allows a second ceiling error. -/
lemma rpow_mul_exp_le {n a e : ℝ} (hn : 1 ≤ n) (ha : 0 < a)
    (haUpper : a ≤ n ^ (-(1 / 2 : ℝ)) * Real.exp (1 / n))
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hgap : 1 - e ≤ 4 / Real.sqrt n) :
    a ^ e * Real.exp (1 / n) ≤
      n ^ (-(1 / 2 : ℝ)) * Real.exp (error n) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg hn
  have hi0 : 0 ≤ 1 / n := by positivity
  have hlog : Real.log a ≤ -(Real.log n / 2) + 1 / n := by
    have h := Real.log_le_log ha haUpper
    rw [Real.log_mul (Real.rpow_pos_of_pos hn0 _).ne' (Real.exp_ne_zero _),
      Real.log_rpow hn0, Real.log_exp] at h
    convert h using 1; ring
  have h1 := mul_le_mul_of_nonneg_right hlog he0
  have h2 := mul_le_mul_of_nonneg_right hgap hl0
  have h3 := mul_le_mul_of_nonneg_right he1 hi0
  have hexp : Real.log a * e + 1 / n ≤
      Real.log n * (-(1 / 2 : ℝ)) + error n := by
    unfold error
    simp only [div_eq_mul_inv] at h1 h2 h3 ⊢
    nlinarith
  rw [Real.rpow_def_of_pos ha, ← Real.exp_add,
    Real.rpow_def_of_pos hn0, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hexp

lemma rpow_mul_exp_le_two {n a e : ℝ} (hn : 1 ≤ n) (ha : 0 < a)
    (haUpper : a ≤ n ^ (-(1 / 2 : ℝ)) * Real.exp (1 / n))
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hgap : 1 - e ≤ 4 / Real.sqrt n)
    (herr : error n ≤ Real.log 2) :
    a ^ e * Real.exp (1 / n) ≤ 2 / Real.sqrt n := by
  calc
    a ^ e * Real.exp (1 / n) ≤ n ^ (-(1 / 2 : ℝ)) * Real.exp (error n) :=
      rpow_mul_exp_le hn ha haUpper he0 he1 hgap
    _ ≤ n ^ (-(1 / 2 : ℝ)) * 2 := by
      gcongr
      exact (Real.exp_le_exp.mpr herr).trans_eq (Real.exp_log (by norm_num))
    _ = 2 / Real.sqrt n := by
      rw [Real.rpow_neg (by linarith), ← Real.sqrt_eq_rpow]
      ring

/-- Uniform in both the rounded parameter and the varying exponent. -/
theorem eventually_rpow_mul_exp_le_two :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ a e : ℝ,
      0 < a → a ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (1 / (n : ℝ)) →
      0 ≤ e → e ≤ 1 → 1 - e ≤ 4 / Real.sqrt (n : ℝ) →
      a ^ e * Real.exp (1 / (n : ℝ)) ≤ 2 / Real.sqrt (n : ℝ) := by
  have he := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually eventually_error_le_log_two
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 he
  refine ⟨max n₀ 1, fun n hn a e ha haUpper he0 he1 hgap => ?_⟩
  apply rpow_mul_exp_le_two (by exact_mod_cast (le_trans (le_max_right _ _) hn))
    ha haUpper he0 he1 hgap
  exact hn₀ n (le_trans (le_max_left _ _) hn)

/-- The exponent used for `q` is also covered by the uniform estimate. -/
theorem eventually_q_beta_bounds :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ a rho beta : ℝ,
      0 < a → a ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (1 / (n : ℝ)) →
      0 ≤ rho → rho ≤ 1 → 1 - rho ≤ 4 / Real.sqrt (n : ℝ) →
      beta ≤ a ^ rho * Real.exp (1 / (n : ℝ)) →
      a ^ ((1 + rho) / 2) ≤ 2 / Real.sqrt (n : ℝ) ∧
      beta ≤ 2 / Real.sqrt (n : ℝ) := by
  obtain ⟨n₀, h⟩ := eventually_rpow_mul_exp_le_two
  refine ⟨n₀, fun n hn a rho beta ha haUpper hr0 hr1 hgap hbeta => ?_⟩
  constructor
  · have he0 : 0 ≤ (1 + rho) / 2 := by linarith
    have he1 : (1 + rho) / 2 ≤ 1 := by linarith
    have hegap : 1 - (1 + rho) / 2 ≤ 4 / Real.sqrt (n : ℝ) := by linarith
    calc
      a ^ ((1 + rho) / 2) = a ^ ((1 + rho) / 2) * 1 := (mul_one _).symm
      _ ≤ a ^ ((1 + rho) / 2) * Real.exp (1 / (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ha.le _)
        exact Real.one_le_exp_iff.mpr (by positivity)
      _ ≤ 2 / Real.sqrt (n : ℝ) := h n hn a _ ha haUpper he0 he1 hegap
  · exact hbeta.trans (h n hn a rho ha haUpper hr0 hr1 hgap)

end Problem335.PowerPerturbation

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ParameterBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assembly of the numerical inequalities for the actual rank parameters. -/
noncomputable section
namespace Problem335.LowerParameters

theorem n_le_a0 {n : ℕ} (hn : 4 ≤ n) : (n : ℝ) ≤ a0 n := by
  have hk : (1 : ℝ) ≤ k n := by exact_mod_cast k_pos hn
  calc
    (n : ℝ) ≤ (k n : ℝ) * (n : ℝ) := by nlinarith
    _ ≤ a0 n := k_mul_n_le_a0 hn

theorem n_le_b0 {n : ℕ} (hn : 4 ≤ n) : (n : ℝ) ≤ b0 n :=
  ((n_le_a0 hn).trans (a0_le_a n)).trans (a_le_b0 hn)

theorem alpha_le_inv_sqrt_mul_exp {n : ℕ} (hn : 4 ≤ n) :
    alpha n ≤ (Real.sqrt (n : ℝ))⁻¹ * Real.exp (1 / (n : ℝ)) := by
  have hs := sqrt_ge_two hn
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hraw : alpha n ≤ (Real.sqrt (n : ℝ))⁻¹ *
      Real.exp ((Real.sqrt (n : ℝ) - 1) / (v n : ℝ)) := by
    simpa [alpha, a, a0, one_div] using
      (fraction_natCeil_inverse_bounds (by linarith : 1 < Real.sqrt (n : ℝ)) hv).2
  have herr : (Real.sqrt (n : ℝ) - 1) / (v n : ℝ) ≤ 1 / (n : ℝ) := by
    have h := one_div_le_one_div_of_le hn' (n_le_a0 hn)
    simpa [a0, one_div_div] using h
  exact hraw.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr herr)
    (by positivity))

theorem alpha_le_rpow_mul_exp {n : ℕ} (hn : 4 ≤ n) :
    alpha n ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (1 / (n : ℝ)) := by
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  exact alpha_le_inv_sqrt_mul_exp hn

theorem beta_le_rpow_mul_exp {n : ℕ} (hn : 4 ≤ n) :
    beta n ≤ (alpha n) ^ (rho n) * Real.exp (1 / (n : ℝ)) := by
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hraw : beta n ≤ (alpha n) ^ (rho n) *
      Real.exp ((1 - (alpha n) ^ (rho n)) / ((u n : ℝ) * (alpha n) ^ (rho n))) := by
    simpa [beta, b, b0] using (fraction_natCeil_target_bounds
      (alpha_rpow_rho_pos hn) (alpha_rpow_rho_lt_one hn) hu).2
  have herr : (1 - (alpha n) ^ (rho n)) / ((u n : ℝ) * (alpha n) ^ (rho n)) ≤
      1 / (n : ℝ) := by
    have h := one_div_le_one_div_of_le hn' (n_le_b0 hn)
    simpa [b0, one_div_div] using h
  exact hraw.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr herr)
    (alpha_rpow_rho_pos hn).le)

theorem one_sub_rho_le_two_div_sqrt {n : ℕ} (hn : 4 ≤ n) :
    1 - rho n ≤ 2 / Real.sqrt (n : ℝ) := by
  have hm : (0 : ℝ) < m n := by exact_mod_cast m_pos hn
  have hs := sqrt_ge_two hn
  have hsn := s_le_sqrt n
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hnm : (n : ℝ) ≤ 2 * (m n : ℝ) := by exact_mod_cast n_le_two_mul_m n
  rw [one_sub_rho hn]
  apply (div_le_div_iff₀ hm (by linarith)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hsn (Real.sqrt_nonneg (n : ℝ))]

theorem one_sub_rho_le_four_div_sqrt {n : ℕ} (hn : 4 ≤ n) :
    1 - rho n ≤ 4 / Real.sqrt (n : ℝ) := by
  exact (one_sub_rho_le_two_div_sqrt hn).trans
    (div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _))

theorem eventually_q_beta_le_two_div_sqrt :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      q n ≤ 2 / Real.sqrt (n : ℝ) ∧ beta n ≤ 2 / Real.sqrt (n : ℝ) := by
  obtain ⟨n₀, h⟩ := PowerPerturbation.eventually_q_beta_bounds
  refine ⟨max n₀ 4, fun n hn => ?_⟩
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  exact h n ((le_max_left _ _).trans hn) (alpha n) (rho n) (beta n)
    (alpha_pos hn4) (alpha_le_rpow_mul_exp hn4)
    (rho_pos hn4).le (rho_lt_one hn4).le
    (one_sub_rho_le_four_div_sqrt hn4) (beta_le_rpow_mul_exp hn4)

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.MomentLossParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem335.LowerParameters

/-- The actual U-layer correction has square-root exponential cost. -/
theorem u_layer_correction_le_exp {n : ℕ} (hn : 16 ≤ n)
    (hbeta : beta n ≤ 2 / Real.sqrt (n : ℝ)) :
    (1 + beta n) ^ m n ≤ Real.exp (2 * Real.sqrt (n : ℝ)) := by
  have hb : 0 ≤ beta n := (beta_pos (by omega : 4 ≤ n)).le
  have hm : (m n : ℝ) ≤ n := by exact_mod_cast m_le_n n
  have hs := sqrt_ge_four hn
  have hspos : 0 < Real.sqrt (n : ℝ) := by linarith
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hmul : (m n : ℝ) * beta n ≤ (n : ℝ) * (2 / Real.sqrt (n : ℝ)) := by
    gcongr
  have heq : (n : ℝ) * (2 / Real.sqrt (n : ℝ)) = 2 * Real.sqrt (n : ℝ) := by
    rw [← mul_div_assoc]
    apply (div_eq_iff hspos.ne').mpr
    nlinarith
  calc
    (1 + beta n) ^ m n ≤ (Real.exp (beta n)) ^ m n := by
      gcongr
      linarith [Real.add_one_le_exp (beta n)]
    _ = Real.exp ((m n : ℝ) * beta n) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (hmul.trans_eq heq)

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LocalMomentWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of the local geometric occupation moments in the four-path
trace expansion. Missing derivative occupations are handled by local-polynomial
identities, preserving the repeated-coordinate second moment rather than
treating it as a product of independent moments. -/

noncomputable section
open scoped BigOperators

namespace Problem335.LocalMomentWeights

/-- Repeated-coordinate geometric second moments give the additional term
`alpha⁻¹` or `beta` exactly. -/
theorem moment_eq_scale_mul_weight (isV isD same : Bool) {A B : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) :
    moment isV isD same A B =
      scale isV A B * weight isV isD same (A / (A + 1)) (B / (B + 1)) := by
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hAp : A + 1 ≠ 0 := by linarith
  have hBp : B + 1 ≠ 0 := by linarith
  cases isV <;> cases isD <;> cases same <;>
    simp [moment, scale, weight] <;> field_simp <;> ring

/-- A pointwise normalization can be factored out of the entire layer product. -/
theorem prod_moment_eq {ι : Type*} (s : Finset ι)
    (isV isD same : ι → Bool) {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) :
    (∏ i ∈ s, moment (isV i) (isD i) (same i) A B) =
      (∏ i ∈ s, scale (isV i) A B) *
      ∏ i ∈ s, weight (isV i) (isD i) (same i) (A / (A + 1)) (B / (B + 1)) := by
  simp_rw [moment_eq_scale_mul_weight _ _ _ hA hB]
  exact Finset.prod_mul_distrib

/-- The product of the local normalization factors is exactly `mu^2`. -/
theorem prod_scale_eq {ι : Type*} (s : Finset ι) (isV : ι → Bool) (A B : ℝ) :
    (∏ i ∈ s, scale (isV i) A B) =
      (A ^ (s.filter (fun i => isV i = true)).card *
        (B + 1) ^ (s.filter (fun i => isV i = false)).card) ^ 2 := by
  classical
  simp only [scale]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hfilter : s.filter (fun i => ¬isV i = true) =
      s.filter (fun i => isV i = false) := by
    ext i
    cases isV i <;> simp
  rw [hfilter, mul_pow]
  congr 1 <;> rw [← pow_mul, ← pow_mul] <;> congr 1 <;> omega

/-- Full local-weight normalization for a fixed four-path pairing pattern. -/
theorem prod_moment_eq_mu_sq_mul {ι : Type*} (s : Finset ι)
    (isV isD same : ι → Bool) {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) :
    (∏ i ∈ s, moment (isV i) (isD i) (same i) A B) =
      (A ^ (s.filter (fun i => isV i = true)).card *
        (B + 1) ^ (s.filter (fun i => isV i = false)).card) ^ 2 *
      ∏ i ∈ s, weight (isV i) (isD i) (same i) (A / (A + 1)) (B / (B + 1)) := by
  rw [prod_moment_eq s isV isD same hA hB, prod_scale_eq]

end Problem335.LocalMomentWeights

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.SecondMomentNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete normalization and reindexing of the geometric upper bound for
four-path occupation moments. -/

noncomputable section
open scoped BigOperators

namespace Problem335.MomentPairing

open Pairings

lemma localWeight_eq_layerWeight {γ : Type*} (isV : Bool)
    (α β : ℝ) (τ : Kind) (x : Labels γ) :
    LocalMomentWeights.weight isV (isDiagonal τ) (coincides x) α β =
      layerWeight (if isV then α⁻¹ else β) τ x := by
  classical
  cases τ <;> cases isV <;> by_cases h : x.p = x.r <;>
    simp [LocalMomentWeights.weight, layerWeight, isDiagonal, coincides, h]

/-- Local normalizations multiply to precisely the square of the first moment. -/
theorem pathGeometricMoment_eq {γ : Type*} {L : ℕ}
    (isV : Fin (L + 1) → Bool) {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (endpoint : γ) (τ : Fin (L + 1) → Kind) (x : Fin L → Labels γ) :
    pathGeometricMoment isV A B endpoint τ x =
      pathMean isV A B ^ 2 *
        pathWeight isV (A / (A + 1)) (B / (B + 1)) endpoint τ x := by
  unfold pathGeometricMoment pathMean pathWeight
  rw [LocalMomentWeights.prod_moment_eq_mu_sq_mul _ _ _ _ hA hB]
  congr 1
  apply Finset.prod_congr rfl
  intro t _
  exact localWeight_eq_layerWeight _ _ _ _ _

/-- Summing the geometric local moments over the exact compatible quadruples
is bounded by the relaxed pairing sum with its common `mu^2` normalization. -/
theorem sum_compatible_geometricMoment_le {γ : Type*} [Fintype γ] [DecidableEq γ]
    {L : ℕ} (isV : Fin (L + 1) → Bool) {A B : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (endpoint : γ) :
    (∑ x : {x : Fin L → Labels γ // Compatible endpoint x},
      pathGeometricMoment isV A B endpoint (classifyWord endpoint x.1) x.1) ≤
    pathMean isV A B ^ 2 *
      ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
        pathWeight isV (A / (A + 1)) (B / (B + 1)) endpoint τ x.1 := by
  simp_rw [pathGeometricMoment_eq isV hA hB]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact sum_compatible_pathWeight_le isV (by positivity) (by positivity) endpoint

/-- After the actual occupation comparison has bounded each compatible
quadruple, all source and path sums combine with only one source-size factor. -/
theorem sum_sources_compatible_le {ι γ : Type*} [Fintype ι]
    [Fintype γ] [DecidableEq γ] {L : ℕ}
    (isV : Fin (L + 1) → Bool) {A B D : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hD : 0 ≤ D) (endpoint : γ)
    (C : ι → (Fin L → Labels γ) → ℝ)
    (hexpect : ∀ x, Compatible endpoint x →
      (∑ i, C i x) ≤ D *
        pathGeometricMoment isV A B endpoint (classifyWord endpoint x) x) :
    (∑ i, ∑ x : {x : Fin L → Labels γ // Compatible endpoint x}, C i x.1) ≤
      D * pathMean isV A B ^ 2 *
        ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
          pathWeight isV (A / (A + 1)) (B / (B + 1)) endpoint τ x.1 := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ x : {x : Fin L → Labels γ // Compatible endpoint x},
        D * pathGeometricMoment isV A B endpoint (classifyWord endpoint x.1) x.1 := by
      apply Finset.sum_le_sum
      intro x _
      exact hexpect x.1 x.2
    _ = D * ∑ x : {x : Fin L → Labels γ // Compatible endpoint x},
        pathGeometricMoment isV A B endpoint (classifyWord endpoint x.1) x.1 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ D * (pathMean isV A B ^ 2 *
        ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
          pathWeight isV (A / (A + 1)) (B / (B + 1)) endpoint τ x.1) :=
      mul_le_mul_of_nonneg_left (sum_compatible_geometricMoment_le isV hA hB endpoint) hD
    _ = _ := by ring

end Problem335.MomentPairing

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ActualSecondMomentParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact normalization and uniform numerical losses for the configured second
trace. The actual trace-to-path inequality is deliberately an explicit premise. -/

noncomputable section

namespace Problem335.LowerParameters

open MomentPairing

/-- The path mean for the balanced partition uses exactly the configured
numbers of differentiation and multiplication layers. -/
theorem configured_pathMean_eq {L : ℕ} (hn : 4 ≤ L + 1) :
    pathMean (balancedLayer hn)
      ((a (L + 1) : ℝ) / v (L + 1))
      ((b (L + 1) : ℝ) / u (L + 1)) =
    ((a (L + 1) : ℝ) / v (L + 1)) ^ k (L + 1) *
      (1 + (b (L + 1) : ℝ) / u (L + 1)) ^ m (L + 1) := by
  simp only [pathMean, balancedLayer_card_true, balancedLayer_card_false]
  rw [add_comm ((b (L + 1) : ℝ) / u (L + 1)) 1]

/-- The common first-moment scale is the path count times the path mean. -/
theorem rankMomentScale_eq_pathMean {L : ℕ} (hn : 4 ≤ L + 1) :
    rankMomentScale (L + 1) = ((L + 1 : ℕ) : ℝ) ^ L *
      pathMean (balancedLayer hn)
        ((a (L + 1) : ℝ) / v (L + 1))
        ((b (L + 1) : ℝ) / u (L + 1)) := by
  rw [configured_pathMean_eq]
  simp only [rankMomentScale, Nat.add_sub_cancel, mul_assoc]

/-- The U-layer correction and the balanced-word factor cost at most ten
square-root units in the exponent, without an occupation upper-loss factor. -/
theorem configured_word_loss_le_exp {n : ℕ} (hn : 16 ≤ n)
    (hbeta : beta n ≤ 2 / Real.sqrt (n : ℝ)) :
    (1 + beta n) ^ m n * Real.exp (8 * Real.sqrt (n : ℝ)) ≤
      Real.exp (10 * Real.sqrt (n : ℝ)) := by
  calc
    _ ≤ Real.exp (2 * Real.sqrt (n : ℝ)) *
        Real.exp (8 * Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_right (u_layer_correction_le_exp hn hbeta)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Rearrangement of the actual path normalization, including the square of
its path-count factor. -/
theorem configured_second_scale_identity {L : ℕ} (hn : 4 ≤ L + 1)
    (W : ℝ) :
    rankDimension (L + 1) *
        pathMean (balancedLayer hn)
          ((a (L + 1) : ℝ) / v (L + 1))
          ((b (L + 1) : ℝ) / u (L + 1)) ^ 2 *
        (((L + 1 : ℕ) : ℝ) ^ (2 * L) * W) =
      rankDimension (L + 1) * rankMomentScale (L + 1) ^ 2 * W := by
  rw [rankMomentScale_eq_pathMean hn, Nat.mul_comm 2 L, pow_mul]
  ring

/-- Numerical endpoint consumed by the actual trace-to-relaxed-path assembly.
There is only one source-dimension factor. -/
theorem configured_second_bound_of_path_bound {L : ℕ} (hn : 16 ≤ L + 1)
    (hbeta : beta (L + 1) ≤ 2 / Real.sqrt ((L + 1 : ℕ) : ℝ))
    (T : ℝ)
    (hT : T ≤ rankDimension (L + 1) *
      pathMean (balancedLayer (show 4 ≤ L + 1 by omega))
        ((a (L + 1) : ℝ) / v (L + 1))
        ((b (L + 1) : ℝ) / u (L + 1)) ^ 2 *
      ((1 + beta (L + 1)) ^ m (L + 1) *
        ((L + 1 : ℕ) : ℝ) ^ (2 * L) *
        Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ)))) :
    T ≤ rankDimension (L + 1) * rankMomentScale (L + 1) ^ 2 *
      Real.exp (10 * Real.sqrt ((L + 1 : ℕ) : ℝ)) := by
  have hn4 : 4 ≤ L + 1 := by omega
  have hid := configured_second_scale_identity hn4
    ((1 + beta (L + 1)) ^ m (L + 1) *
      Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ)))
  have hT' : T ≤ rankDimension (L + 1) * rankMomentScale (L + 1) ^ 2 *
      ((1 + beta (L + 1)) ^ m (L + 1) *
        Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ))) := by
    rw [← hid]
    convert hT using 1; ring
  exact hT'.trans (mul_le_mul_of_nonneg_left
    (configured_word_loss_le_exp hn hbeta)
    (mul_nonneg (rankDimension_nonneg _) (sq_nonneg _)))

/-- A single absolute threshold discharges every numerical premise of the
configured second-moment normalization. -/
theorem exists_second_moment_parameter_cutoff :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      16 ≤ n ∧ beta n ≤ 2 / Real.sqrt (n : ℝ) ∧
        (1 + beta n) ^ m n * Real.exp (8 * Real.sqrt (n : ℝ)) ≤
          Real.exp (10 * Real.sqrt (n : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_q_beta_le_two_div_sqrt
  refine ⟨max N 16, ?_⟩
  intro n hn
  have hn16 : 16 ≤ n := (le_max_right _ _).trans hn
  have hb := (hN n ((le_max_left _ _).trans hn)).2
  exact ⟨hn16, hb, configured_word_loss_le_exp hn16 hb⟩

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BidegreeCompositionReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

private theorem double_sum_coe_sort {α β : Type*} (s : Finset α) (t : Finset β)
    (f : α → β → ℝ) :
    (∑ x : s, ∑ y : t, f x y) = ∑ x ∈ s, ∑ y ∈ t, f x y := by
  rw [Finset.sum_coe_sort s (fun x => ∑ y : t, f x y)]
  apply Finset.sum_congr rfl
  intro x hx
  exact Finset.sum_coe_sort t (f x)

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem bidegreeAntidiagEquiv_join (side : σ → Bool) (a b : ℕ)
    (d : {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a,b)}) :
    (fun i => if h : side i = true then
      (bidegreeAntidiagEquiv side a b d).1.val ⟨i,h⟩ else
      (bidegreeAntidiagEquiv side a b d).2.val ⟨i,h⟩) = d.val := by
  funext i
  by_cases h : side i = true <;>
    simp [bidegreeAntidiagEquiv, bidegreeExponentsEquiv,
      homogeneousFunctionsEquivAntidiag, Equiv.subtypeProdEquivProd, h]

/-- Arbitrary, not necessarily separated, functions may be summed in the two groups. -/
theorem bidegree_sum_eq_double_antidiag (side : σ → Bool) (a b : ℕ)
    [Fintype {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a,b)}]
    (f : (σ → ℕ) → ℝ) :
    (∑ d : {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a,b)}, f d.val) =
      ∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset {i // side i = true}) a,
        ∑ N ∈ Finset.finsuppAntidiag (Finset.univ : Finset {i // ¬ side i = true}) b,
          f (fun i => if h : side i = true then M ⟨i,h⟩ else N ⟨i,h⟩) := by
  let e := bidegreeAntidiagEquiv side a b
  have h := e.sum_comp (fun z => f (fun i =>
    if h : side i = true then z.1.val ⟨i,h⟩ else z.2.val ⟨i,h⟩))
  dsimp only [e] at h
  simp only [bidegreeAntidiagEquiv_join] at h
  rw [h, Fintype.sum_prod_type]
  exact double_sum_coe_sort
    (Finset.finsuppAntidiag (Finset.univ : Finset {i // side i = true}) a)
    (Finset.finsuppAntidiag (Finset.univ : Finset {i // ¬ side i = true}) b)
    (fun M N =>
    f (fun i => if h : side i = true then M ⟨i,h⟩ else N ⟨i,h⟩))

/-- Uniform bidegree averages are the nested uniform occupation means. -/
theorem bidegree_average_eq_double_antidiag (side : σ → Bool) (a b : ℕ)
    [Fintype {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a,b)}]
    (f : (σ → ℕ) → ℝ) :
    (∑ d : {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a,b)}, f d.val) /
      (Fintype.card {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a,b)} : ℝ) =
      (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset {i // side i = true}) a,
        (∑ N ∈ Finset.finsuppAntidiag (Finset.univ : Finset {i // ¬ side i = true}) b,
          f (fun i => if h : side i = true then M ⟨i,h⟩ else N ⟨i,h⟩)) /
          ((Finset.finsuppAntidiag (Finset.univ : Finset {i // ¬ side i = true}) b).card : ℝ)) /
        ((Finset.finsuppAntidiag (Finset.univ : Finset {i // side i = true}) a).card : ℝ) := by
  have hc := Fintype.card_congr (bidegreeAntidiagEquiv side a b)
  simp only [Fintype.card_prod, Fintype.card_coe] at hc
  rw [bidegree_sum_eq_double_antidiag, hc, Nat.cast_mul]
  rw [← Finset.sum_div, div_div, mul_comm]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FactorialPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegative falling-factorial expansions for the local trace weights. -/
namespace Problem335

open scoped BigOperators

universe u

attribute [instance] FactorialExpansion.indexFintype

namespace FactorialExpansion

variable {σ : Type u} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
/-- The same expansion as a real-valued sum, ready for expectation comparisons. -/
theorem eval_real {f : (σ → ℕ) → ℕ} {S : Finset σ} {D : ℕ}
    (F : FactorialExpansion f S D) (M : σ → ℕ) :
    (f M : ℝ) = ∑ j, (F.coeff j : ℝ) * (factorialMonomial (F.degree j) M : ℝ) := by
  exact_mod_cast F.eval_eq M

end FactorialExpansion
end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LocalMomentPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace LocalMoments

lemma mass_nonneg (derivative : Bool) (z : ℕ) : 0 ≤ mass derivative z := by
  cases derivative <;> dsimp [mass]
  all_goals positivity

@[simp] lemma coefficient_sq (derivative : Bool) (z : ℕ) :
    coefficient derivative z ^ 2 = mass derivative z :=
  Real.sq_sqrt (mass_nonneg derivative z)

/-- The normal pairing has zero occupation shift. -/
lemma normal_fourCoefficient (derivative : Bool) (a b : ℕ) :
    fourCoefficient derivative a a b b = mass derivative a * mass derivative b := by
  calc
    _ = coefficient derivative a ^ 2 * coefficient derivative b ^ 2 := by
      unfold fourCoefficient
      ring
    _ = _ := by rw [coefficient_sq, coefficient_sq]

/-- Differentiating diagonal pairing: the second path receives one occupation. -/
lemma derivative_diagonal_fourCoefficient (a b : ℕ) :
    fourCoefficient true a (b + 1) a (b + 1) = (a : ℝ) * ((b : ℝ) + 1) := by
  calc
    _ = coefficient true a ^ 2 * coefficient true (b + 1) ^ 2 := by
      unfold fourCoefficient
      ring
    _ = _ := by simp [mass]

/-- Multiplying diagonal pairing, expressed without natural subtraction. -/
lemma multiplication_diagonal_fourCoefficient (a b : ℕ) :
    fourCoefficient false a b a b = ((a : ℝ) + 1) * ((b : ℝ) + 1) := by
  calc
    _ = coefficient false a ^ 2 * coefficient false b ^ 2 := by
      unfold fourCoefficient
      ring
    _ = _ := by simp [mass]

/-- Move the four path products into a product of local four-factor entries. -/
lemma four_products_eq_product {ι : Type*} (s : Finset ι)
    (derivative : ι → Bool) (a b c d : ι → ℕ) :
    (∏ i ∈ s, coefficient (derivative i) (a i)) *
      (∏ i ∈ s, coefficient (derivative i) (b i)) *
      (∏ i ∈ s, coefficient (derivative i) (c i)) *
      (∏ i ∈ s, coefficient (derivative i) (d i)) =
    ∏ i ∈ s, fourCoefficient (derivative i) (a i) (b i) (c i) (d i) := by
  simp only [fourCoefficient, Finset.prod_mul_distrib]

lemma derivative_diagonal_layer {σ : Type*} (M M' : σ → ℕ) (i j : σ)
    (hj : M' j = M j + 1) :
    fourCoefficient true (M i) (M' j) (M i) (M' j) =
      (M i : ℝ) * ((M j : ℝ) + 1) := by
  rw [hj, derivative_diagonal_fourCoefficient]

lemma multiplication_diagonal_layer {σ : Type*} (M M' : σ → ℕ) (i j : σ)
    (hj : M' j + 1 = M j) :
    fourCoefficient false (M i) (M' j) (M i) (M' j) =
      ((M i : ℝ) + 1) * (M j : ℝ) := by
  rw [multiplication_diagonal_fourCoefficient]
  have hr := congrArg (fun n : ℕ => (n : ℝ)) hj
  push_cast at hr
  rw [hr]

end LocalMoments
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FourPathLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace LocalMoments

lemma shiftRelation_normal {σ : Type*} (derivative : Bool) (M M' : σ → ℕ) (p : σ)
    (h : ShiftRelation derivative M M' p p) : M' = M := by
  funext x
  have hx := h x
  simp only [sub_self, Finsupp.zero_apply, mul_zero, add_zero] at hx
  exact_mod_cast hx

lemma shiftRelation_derivative {σ : Type*} (M M' : σ → ℕ) (p q : σ) (hpq : p ≠ q)
    (h : ShiftRelation true M M' p q) : M' q = M q + 1 := by
  classical
  have hq := h q
  simp [Finsupp.sub_apply, Ne.symm hpq] at hq
  omega

lemma shiftRelation_multiplication {σ : Type*} (M M' : σ → ℕ) (p q : σ) (hpq : p ≠ q)
    (h : ShiftRelation false M M' p q) : M' q + 1 = M q := by
  classical
  have hq := h q
  simp [Finsupp.sub_apply, Ne.symm hpq] at hq
  omega

/-- Matching signed coordinate differences and the actual source shift imply precisely
    the normal/diagonal local polynomial table from the four-path expansion. -/
theorem fourCoefficient_eq_localPolynomial {σ : Type*} [DecidableEq σ]
    (derivative : Bool) (M M' : σ → ℕ) (p q r s : σ)
    (hmatch : Finsupp.single p (1 : ℤ) - Finsupp.single q 1 =
      Finsupp.single r 1 - Finsupp.single s 1)
    (hshift : ShiftRelation derivative M M' p q) :
    fourCoefficient derivative (M p) (M' q) (M r) (M' s) =
      localPolynomial derivative M p q r := by
  rcases (Pairings.coordinate_difference_eq_iff_exclusive p q r s).mp hmatch with hN | hD
  · rcases hN with ⟨hpq, hrs⟩
    subst q
    subst s
    have hM := shiftRelation_normal derivative M M' p hshift
    subst M'
    simp [localPolynomial, normal_fourCoefficient]
  · rcases hD with ⟨hpr, hqs, hpq⟩
    subst r
    subst s
    cases derivative
    · have hq := shiftRelation_multiplication M M' p q hpq hshift
      simpa [localPolynomial, hpq] using
        multiplication_diagonal_layer M M' p q hq
    · have hq := shiftRelation_derivative M M' p q hpq hshift
      simpa [localPolynomial, hpq] using derivative_diagonal_layer M M' p q hq

lemma localPolynomial_nonneg {σ : Type*} [DecidableEq σ] (derivative : Bool)
    (M : σ → ℕ) (p q r : σ) : 0 ≤ localPolynomial derivative M p q r := by
  unfold localPolynomial
  split_ifs
  · exact mul_nonneg (mass_nonneg _ _) (mass_nonneg _ _)
  all_goals positivity

/-- The local table applies simultaneously at all layers, converting the four path
coefficient products into a product of occupation polynomials. -/
theorem four_path_products_eq_localPolynomial_product {ι σ : Type*} [DecidableEq σ]
    (layers : Finset ι) (derivative : ι → Bool) (M M' : ι → σ → ℕ)
    (p q r s : ι → σ)
    (hmatch : ∀ t ∈ layers,
      Finsupp.single (p t) (1 : ℤ) - Finsupp.single (q t) 1 =
        Finsupp.single (r t) 1 - Finsupp.single (s t) 1)
    (hshift : ∀ t ∈ layers, ShiftRelation (derivative t) (M t) (M' t) (p t) (q t)) :
    (∏ t ∈ layers, coefficient (derivative t) (M t (p t))) *
      (∏ t ∈ layers, coefficient (derivative t) (M' t (q t))) *
      (∏ t ∈ layers, coefficient (derivative t) (M t (r t))) *
      (∏ t ∈ layers, coefficient (derivative t) (M' t (s t))) =
      ∏ t ∈ layers, localPolynomial (derivative t) (M t) (p t) (q t) (r t) := by
  rw [four_products_eq_product]
  apply Finset.prod_congr rfl
  intro t ht
  exact fourCoefficient_eq_localPolynomial (derivative t) (M t) (M' t)
    (p t) (q t) (r t) (s t) (hmatch t ht) (hshift t ht)

end LocalMoments
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LocalFactorialExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual local four-path table has bounded nonnegative factorial expansions. -/
namespace Problem335

open scoped BigOperators

namespace LocalMoments

variable {σ : Type*} [DecidableEq σ]

/-- Layer-labelled coordinates automatically have disjoint local supports. -/
theorem layered_support_disjoint {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (layers : Finset ι) (p q r : ι → κ) :
    (layers : Set ι).Pairwise fun i j =>
      Disjoint ({(i, p i), (i, q i), (i, r i)} : Finset (ι × κ))
        {(j, p j), (j, q j), (j, r j)} := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx' : x.1 = i := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h <;> simp [h]
  have hy' : x.1 = j := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h <;> simp [h]
  exact hij (hx'.symm.trans hy')

end LocalMoments
end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FactorialGeometricValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite geometric-moment evaluation of nonnegative factorial expansions. -/
namespace Problem335

open scoped BigOperators

variable {σ : Type*} [Fintype σ]

namespace FactorialExpansion

variable [DecidableEq σ]

@[simp] theorem geometricValue_normalDerivative (i j : σ) (G : σ → ℝ) :
    (normalDerivative i j).geometricValue G =
      if i = j then 2 * G i ^ 2 + G i else G i * G j := by
  by_cases h : i = j
  · subst j
    simp [normalDerivative]
  · simp only [normalDerivative, dite_eq_right h, ite_eq_right h]
    change ((occupation i).mul (occupation j) (by simpa using h)).geometricValue G = _
    rw [geometricValue_mul]
    simp

@[simp] theorem geometricValue_normalMultiplication (i j : σ) (G : σ → ℝ) :
    (normalMultiplication i j).geometricValue G =
      if i = j then 2 * G i ^ 2 + 3 * G i + 1 else (G i + 1) * (G j + 1) := by
  by_cases h : i = j
  · subst j
    simp [normalMultiplication]
  · simp only [normalMultiplication, dite_eq_right h, ite_eq_right h]
    change ((successor i).mul (successor j) (by simpa using h)).geometricValue G = _
    rw [geometricValue_mul]
    simp

/-- The value depends only on the coordinates allowed by the expansion support. -/
theorem geometricValue_congr_on {f : (σ → ℕ) → ℕ} {S : Finset σ} {D : ℕ}
    (F : FactorialExpansion f S D) (G H : σ → ℝ)
    (heq : ∀ i ∈ S, G i = H i) : F.geometricValue G = F.geometricValue H := by
  unfold geometricValue
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  unfold geometricFactorialMonomial
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hS : i ∈ S
  · rw [heq i hS]
  · simp [F.supported j i hS]

/-- Choose the finite product expansion together with its exact independent
geometric factorial value. -/
theorem exists_prod_geometricValue {ι : Type*} (s : Finset ι)
    (f : ι → (σ → ℕ) → ℕ) (S : ι → Finset σ) (D : ι → ℕ)
    (F : ∀ i, FactorialExpansion (f i) (S i) (D i)) (G : σ → ℝ)
    (hdis : (s : Set ι).Pairwise fun i j => Disjoint (S i) (S j)) :
    ∃ H : FactorialExpansion (fun M => ∏ i ∈ s, f i M)
      (s.biUnion S) (∑ i ∈ s, D i),
      H.geometricValue G = ∏ i ∈ s, (F i).geometricValue G := by
  classical
  revert hdis
  induction s using Finset.induction_on with
  | empty =>
    intro hdis
    exact ⟨constant 1, by simp⟩
  | @insert a s ha ih =>
    intro hdis
    have hs : (s : Set ι).Pairwise fun i j => Disjoint (S i) (S j) := by
      intro i hi j hj hij
      exact hdis (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
    obtain ⟨H, hH⟩ := ih hs
    have hd : Disjoint (S a) (s.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hdis (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj)
        (by intro h; subst j; exact ha hj)
    let E := ((F a).mul H hd).reframe
      (g := fun M => ∏ i ∈ insert a s, f i M)
      (T := (insert a s).biUnion S) (E := ∑ i ∈ insert a s, D i)
      (by intro M; simp [ha]) (by simp) (by simp [ha])
    refine ⟨E, ?_⟩
    change (((F a).mul H hd).reframe _ _ _).geometricValue G = _
    rw [geometricValue_reframe, geometricValue_mul, hH, Finset.prod_insert ha]

end FactorialExpansion

namespace LocalMoments

variable [DecidableEq σ]

@[simp] theorem geometricValue_localPolynomialExpansion (derivative : Bool)
    (p q r : σ) (G : ℝ) :
    (localPolynomialExpansion derivative p q r).geometricValue (fun _ => G) =
      localGeometricMass derivative G p q r := by
  by_cases hpq : p = q
  · subst q
    by_cases hpr : p = r
    · subst r
      cases derivative <;> simp [localPolynomialExpansion, localGeometricMass,
        normalGeometricMass, pow_two]
    · cases derivative <;> simp [localPolynomialExpansion, hpr, localGeometricMass,
        normalGeometricMass, pow_two]
  · cases derivative <;> simp [localPolynomialExpansion, hpq, localGeometricMass,
      diagonalGeometricMass, mul_comm]

/-- Local evaluation when only the three relevant coordinate means agree. -/
theorem geometricValue_localPolynomialExpansion_of_eq (derivative : Bool)
    (p q r : σ) (G : σ → ℝ) (g : ℝ)
    (hp : G p = g) (hq : G q = g) (hr : G r = g) :
    (localPolynomialExpansion derivative p q r).geometricValue G =
      localGeometricMass derivative g p q r := by
  rw [FactorialExpansion.geometricValue_congr_on
    (localPolynomialExpansion derivative p q r) G (fun _ => g)]
  · exact geometricValue_localPolynomialExpansion derivative p q r g
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h | h
    · simpa [h] using hp
    · simpa [h] using hq
    · simpa [h] using hr

/-- Different layers may have different geometric means. In particular this
handles mean `A` on derivative layers and mean `B` on multiplication layers. -/
theorem exists_localProduct_geometricValue_of_eq {ι : Type*} (layers : Finset ι)
    (derivative : ι → Bool) (p q r : ι → σ) (G : σ → ℝ) (g : ι → ℝ)
    (hp : ∀ t ∈ layers, G (p t) = g t)
    (hq : ∀ t ∈ layers, G (q t) = g t)
    (hr : ∀ t ∈ layers, G (r t) = g t)
    (hdis : (layers : Set ι).Pairwise fun i j =>
      Disjoint ({p i, q i, r i} : Finset σ) {p j, q j, r j}) :
    ∃ F : FactorialExpansion (localProductNat layers derivative p q r)
      (layers.biUnion fun i => {p i, q i, r i}) (2 * layers.card),
      F.geometricValue G =
        ∏ t ∈ layers, localGeometricMass (derivative t) (g t) (p t) (q t) (r t) := by
  obtain ⟨F, hF⟩ := FactorialExpansion.exists_prod_geometricValue layers
    (fun i M => localPolynomialNat (derivative i) M (p i) (q i) (r i))
    (fun i => {p i, q i, r i}) (fun _ => 2)
    (fun i => localPolynomialExpansion (derivative i) (p i) (q i) (r i)) G hdis
  let H := F.reframe (g := localProductNat layers derivative p q r)
    (T := layers.biUnion fun i => {p i, q i, r i}) (E := 2 * layers.card)
    (by intro M; rfl) (by rfl) (by simp [Nat.mul_comm])
  refine ⟨H, ?_⟩
  change F.geometricValue G = _
  rw [hF]
  apply Finset.prod_congr rfl
  intro t ht
  exact geometricValue_localPolynomialExpansion_of_eq (derivative t)
    (p t) (q t) (r t) G (g t) (hp t ht) (hq t ht) (hr t ht)

end LocalMoments
end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OccupationExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- Linearity and the exact occupation factorial-moment identity. -/
theorem compositionExpansionMean_eq {ι J : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (s : Finset J) (c : J → ℝ) (d : J → ι → ℕ) (t : ℕ) :
    compositionExpansionMean s c d t =
      ∑ j ∈ s, (c j * ∏ i, (d j i).factorial : ℝ) *
        ((t.descFactorial (∑ i, d j i) : ℝ) /
          ((Fintype.card ι).ascFactorial (∑ i, d j i) : ℝ)) := by
  unfold compositionExpansionMean factorialExpansionValue
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum, mul_div_assoc, occupation_factorial_moment]
  push_cast
  ring

theorem twoGroupCompositionExpansionMean_eq {ι κ J : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (s : Finset J) (c : J → ℝ) (d : J → ι → ℕ) (e : J → κ → ℕ) (a b : ℕ) :
    twoGroupCompositionExpansionMean s c d e a b =
      ∑ j ∈ s, (c j * (∏ i, (d j i).factorial : ℝ) * (∏ i, (e j i).factorial : ℝ)) *
        (((a.descFactorial (∑ i, d j i) : ℝ) /
          ((Fintype.card ι).ascFactorial (∑ i, d j i) : ℝ)) *
         ((b.descFactorial (∑ i, e j i) : ℝ) /
          ((Fintype.card κ).ascFactorial (∑ i, e j i) : ℝ))) := by
  unfold twoGroupCompositionExpansionMean
  simp_rw [compositionExpansionMean_eq]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (c j * (∏ i, (e j i).factorial : ℝ) *
          ((b.descFactorial (∑ i, e j i) : ℝ) /
            ((Fintype.card κ).ascFactorial (∑ i, e j i) : ℝ))) *
        ((∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) a,
          ∏ i, ((M i).descFactorial (d j i) : ℝ)) /
            (Finset.finsuppAntidiag (Finset.univ : Finset ι) a).card) := by
      simp only [Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M hM
      push_cast
      ring
    _ = _ := by
      rw [occupation_factorial_moment]
      ring

/-- Actual upper occupation comparison for nonnegative two-group expansions. -/
theorem twoGroupCompositionExpansionMean_le_geometric {ι κ J : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (s : Finset J) (c : J → ℝ) (d : J → ι → ℕ) (e : J → κ → ℕ) (a b : ℕ)
    (hc : ∀ j ∈ s, 0 ≤ c j) :
    twoGroupCompositionExpansionMean s c d e a b ≤
      twoGroupGeometricExpansionValue s c d e
        ((a : ℝ) / Fintype.card ι) ((b : ℝ) / Fintype.card κ) := by
  rw [twoGroupCompositionExpansionMean_eq]
  apply weighted_two_group_factorialMoment_sum_le s _ _ _
    Fintype.card_pos Fintype.card_pos
  intro j hj
  exact mul_nonneg (mul_nonneg (hc j hj) (by positivity)) (by positivity)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LocalOccupationAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ : Type*} [Fintype σ]

theorem factorialMonomial_joinOccupation (side : σ → Bool) (d : σ → ℕ)
    (M : {i // side i = true} → ℕ) (N : {i // ¬ side i = true} → ℕ) :
    factorialMonomial d (joinOccupation side M N) =
      (∏ i, (M i).descFactorial (d i)) * (∏ i, (N i).descFactorial (d i)) := by
  classical
  unfold factorialMonomial
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => side i = true)]
  simp

variable [DecidableEq σ]

namespace FactorialExpansion
variable {f : (σ → ℕ) → ℕ} {S : Finset σ} {D : ℕ}

theorem partitionCompositionMean_eq (F : FactorialExpansion f S D)
    (side : σ → Bool) (a b : ℕ) :
    Problem335.partitionCompositionMean side (fun M => (f M : ℝ)) a b =
      twoGroupCompositionExpansionMean Finset.univ (fun j => (F.coeff j : ℝ))
        (fun j (i : {i // side i = true}) => F.degree j i)
        (fun j (i : {i // ¬ side i = true}) => F.degree j i) a b := by
  classical
  unfold Problem335.partitionCompositionMean twoGroupCompositionExpansionMean
    compositionExpansionMean factorialExpansionValue
  apply congrArg (fun x : ℝ => x / _)
  apply Finset.sum_congr rfl
  intro M hM
  apply congrArg (fun x : ℝ => x / _)
  apply Finset.sum_congr rfl
  intro N hN
  dsimp only
  rw [F.eval_real]
  apply Finset.sum_congr rfl
  intro j hj
  rw [factorialMonomial_joinOccupation]
  push_cast
  ring

omit [DecidableEq σ] in
/-- The two means give one coordinate-wise geometric factorial monomial. -/
theorem partition_geometric_monomial (side : σ → Bool) (d : σ → ℕ) (A B : ℝ) :
    (∏ i, (d i).factorial * (if side i = true then A else B) ^ d i : ℝ) =
      (∏ i : {i // side i = true}, ((d i).factorial : ℝ)) *
      (∏ i : {i // ¬ side i = true}, ((d i).factorial : ℝ)) *
      (A ^ (∑ i : {i // side i = true}, d i) *
       B ^ (∑ i : {i // ¬ side i = true}, d i)) := by
  classical
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => side i = true)]
  have hV (i : {i // side i = true}) : (if side i = true then A else B) = A :=
    ite_eq_left i.property
  have hU (i : {i // ¬ side i = true}) : (if side i = true then A else B) = B :=
    ite_eq_right i.property
  simp_rw [hV, hU]
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

/-- Upper occupation comparison for every concrete nonnegative factorial expansion.
No total-order restriction is necessary for this upper bound. -/
theorem partitionCompositionMean_le (F : FactorialExpansion f S D)
    (side : σ → Bool) [Nonempty {i // side i = true}] [Nonempty {i // ¬ side i = true}]
    (a b : ℕ) :
    Problem335.partitionCompositionMean side (fun M => (f M : ℝ)) a b ≤
      ∑ j, (F.coeff j : ℝ) * ∏ i, ((F.degree j i).factorial : ℝ) *
        (if side i = true then (a : ℝ) / Fintype.card {i // side i = true}
         else (b : ℝ) / Fintype.card {i // ¬ side i = true}) ^ F.degree j i := by
  classical
  rw [F.partitionCompositionMean_eq]
  have h := twoGroupCompositionExpansionMean_le_geometric Finset.univ
    (fun j => (F.coeff j : ℝ))
    (fun j (i : {i // side i = true}) => F.degree j i)
    (fun j (i : {i // ¬ side i = true}) => F.degree j i) a b
    (by intro j hj; positivity)
  refine h.trans_eq ?_
  unfold twoGroupGeometricExpansionValue
  apply Finset.sum_congr rfl
  intro j hj
  rw [partition_geometric_monomial]
  ring

end FactorialExpansion
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LocalProductAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace LocalMoments

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ]

/-- The actual occupation average of the full local four-path table is bounded
by the product of its independent geometric local moments. -/
theorem partitionCompositionMean_localProduct_le
    (side : σ → Bool) [Nonempty {i // side i = true}] [Nonempty {i // ¬ side i = true}]
    (a b : ℕ) (layers : Finset ι) (derivative : ι → Bool) (p q r : ι → σ)
    (hp : ∀ t ∈ layers, side (p t) = derivative t)
    (hq : ∀ t ∈ layers, side (q t) = derivative t)
    (hr : ∀ t ∈ layers, side (r t) = derivative t)
    (hdis : (layers : Set ι).Pairwise fun i j =>
      Disjoint ({p i, q i, r i} : Finset σ) {p j, q j, r j}) :
    partitionCompositionMean side
      (fun M => ∏ t ∈ layers, localPolynomial (derivative t) M (p t) (q t) (r t)) a b ≤
      ∏ t ∈ layers, localGeometricMass (derivative t)
        (if derivative t = true then (a : ℝ) / Fintype.card {i // side i = true}
          else (b : ℝ) / Fintype.card {i // ¬ side i = true}) (p t) (q t) (r t) := by
  classical
  let G : σ → ℝ := fun i =>
    if side i = true then (a : ℝ) / Fintype.card {i // side i = true}
    else (b : ℝ) / Fintype.card {i // ¬ side i = true}
  let g : ι → ℝ := fun t =>
    if derivative t = true then (a : ℝ) / Fintype.card {i // side i = true}
    else (b : ℝ) / Fintype.card {i // ¬ side i = true}
  obtain ⟨F, hF⟩ := exists_localProduct_geometricValue_of_eq layers derivative p q r G g
    (by intro t ht; simp only [G, g, hp t ht])
    (by intro t ht; simp only [G, g, hq t ht])
    (by intro t ht; simp only [G, g, hr t ht]) hdis
  have hmean := F.partitionCompositionMean_le side a b
  change partitionCompositionMean side
    (fun M => (localProductNat layers derivative p q r M : ℝ)) a b ≤ F.geometricValue G at hmean
  rw [hF] at hmean
  simpa only [localProductNat_cast] using hmean

/-- Specialization to the matrix-layer coordinate shape: disjoint supports and
the common local mean are automatic, not additional analytic assumptions. -/
theorem partitionCompositionMean_layered_localProduct_le
    {κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (derivative : ι → Bool)
    [Nonempty {x : ι × κ // derivative x.1 = true}]
    [Nonempty {x : ι × κ // ¬ derivative x.1 = true}]
    (a b : ℕ) (layers : Finset ι) (p q r : ι → κ) :
    partitionCompositionMean (fun x : ι × κ => derivative x.1)
      (fun M => ∏ t ∈ layers, localPolynomial (derivative t) M
        (t, p t) (t, q t) (t, r t)) a b ≤
      ∏ t ∈ layers, localGeometricMass (derivative t)
        (if derivative t = true then
          (a : ℝ) / Fintype.card {x : ι × κ // derivative x.1 = true}
        else (b : ℝ) / Fintype.card {x : ι × κ // ¬ derivative x.1 = true})
        (t, p t) (t, q t) (t, r t) := by
  apply partitionCompositionMean_localProduct_le (fun x : ι × κ => derivative x.1)
    a b layers derivative (fun t => (t, p t)) (fun t => (t, q t)) (fun t => (t, r t))
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · exact layered_support_disjoint layers p q r

/-- Row-restriction presentation matching the actual four-path local table directly. -/
theorem partitionCompositionMean_layered_restrict_le
    {κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (derivative : ι → Bool)
    [Nonempty {x : ι × κ // derivative x.1 = true}]
    [Nonempty {x : ι × κ // ¬ derivative x.1 = true}]
    (a b : ℕ) (layers : Finset ι) (p q r : ι → κ) :
    partitionCompositionMean (fun x : ι × κ => derivative x.1)
      (fun M => ∏ t ∈ layers, localPolynomial (derivative t) (fun x => M (t, x))
        (p t) (q t) (r t)) a b ≤
      ∏ t ∈ layers, localGeometricMass (derivative t)
        (if derivative t = true then
          (a : ℝ) / Fintype.card {x : ι × κ // derivative x.1 = true}
        else (b : ℝ) / Fintype.card {x : ι × κ // ¬ derivative x.1 = true})
        (p t) (q t) (r t) := by
  simpa only [localPolynomial_layered, localGeometricMass_layered] using
    partitionCompositionMean_layered_localProduct_le derivative a b layers p q r

end LocalMoments
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BidegreeLocalProductAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

theorem bidegree_average_eq_partitionCompositionMean
    {σ : Type*} [Fintype σ] [DecidableEq σ] (side : σ → Bool) (a b : ℕ)
    [Fintype {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a, b)}]
    (f : (σ → ℕ) → ℝ) :
    (∑ d : {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a, b)}, f d.val) /
      (Fintype.card {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a, b)} : ℝ) =
        partitionCompositionMean side f a b := by
  unfold partitionCompositionMean
  unfold joinOccupation
  exact bidegree_average_eq_double_antidiag side a b f

namespace LocalMoments

/-- The second-moment occupation estimate on the actual canonical source
exponent subtype, presented in the same local coordinates as the four paths. -/
theorem bidegree_average_layered_localProduct_le
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (derivative : ι → Bool)
    [Nonempty {x : ι × κ // derivative x.1 = true}]
    [Nonempty {x : ι × κ // ¬ derivative x.1 = true}]
    (a b : ℕ)
    [Fintype {d : (ι × κ) →₀ ℕ //
      Finsupp.weight (bidegreeWeight (fun x => derivative x.1)) d = (a, b)}]
    (layers : Finset ι) (p q r : ι → κ) :
    (∑ d : {d : (ι × κ) →₀ ℕ //
        Finsupp.weight (bidegreeWeight (fun x => derivative x.1)) d = (a, b)},
      ∏ t ∈ layers, localPolynomial (derivative t) (fun x => d.val (t, x))
        (p t) (q t) (r t)) /
      (Fintype.card {d : (ι × κ) →₀ ℕ //
        Finsupp.weight (bidegreeWeight (fun x => derivative x.1)) d = (a, b)} : ℝ) ≤
      ∏ t ∈ layers, localGeometricMass (derivative t)
        (if derivative t = true then
          (a : ℝ) / Fintype.card {x : ι × κ // derivative x.1 = true}
        else (b : ℝ) / Fintype.card {x : ι × κ // ¬ derivative x.1 = true})
        (p t) (q t) (r t) := by
  have heq := bidegree_average_eq_partitionCompositionMean
    (fun x : ι × κ => derivative x.1) a b
    (fun M => ∏ t ∈ layers, localPolynomial (derivative t) (fun x => M (t, x))
      (p t) (q t) (r t))
  exact heq.trans_le (partitionCompositionMean_layered_restrict_le derivative a b layers p q r)

end LocalMoments
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.UpperGateCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite index counts for the consecutive-block depth-five construction. -/

open scoped BigOperators

namespace Problem335

/-- Count the monomials used for every entry of a nonempty block. -/
theorem block_entry_monomial_count (n d : ℕ) (hd : 1 ≤ d) :
    Fintype.card (Fin n × Fin n × (Fin (d - 1) → Fin n)) = n ^ (d + 1) := by
  have h : 2 + (d - 1) = d + 1 := by omega
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  rw [← mul_assoc, ← pow_two, ← pow_add, h]

end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.UpperBlockData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.BlockData

variable {n : ℕ}

theorem paths_length (blocks : List (List (Fin n)))
    (hne : ∀ b : Fin blocks.length, blocks.get b ≠ []) (m : Middle blocks) :
    (paths blocks m).length = n ^ ((blocks.get m.1).length - 1) := by
  simpa [paths] using matrixEntryPaths_length (blocks.get m.1) (hne m.1) m.2.1 m.2.2

theorem upperPaths_length (blocks : List (List (Fin n))) (hb : blocks ≠ []) (z : Fin n) :
    (upperPaths blocks z).length = n ^ (blocks.length - 1) := by
  have h : List.finRange blocks.length ≠ [] := by
    simpa using hb
  simpa [upperPaths] using matrixEntryPaths_length (List.finRange blocks.length) h z z

theorem card_upper (blocks : List (List (Fin n))) (hb : blocks ≠ []) (z : Fin n) :
    Fintype.card (Upper blocks z) = n ^ (blocks.length - 1) := by
  simpa only [Fintype.card_fin] using upperPaths_length blocks hb z

theorem card_lower (blocks : List (List (Fin n)))
    (hne : ∀ b : Fin blocks.length, blocks.get b ≠ []) :
    Fintype.card (Lower blocks) =
      ∑ b : Fin blocks.length, n ^ ((blocks.get b).length + 1) := by
  simp only [Lower, Fintype.card_sigma, Fintype.card_fin]
  simp_rw [paths_length blocks hne]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  have hd : 1 ≤ (blocks.get b).length := List.length_pos_iff.mpr (hne b)
  have hcount := block_entry_monomial_count n (blocks.get b).length hd
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_id, Nat.mul_assoc] using hcount

theorem card_lower_le (blocks : List (List (Fin n))) (t : ℕ)
    (hn : 1 ≤ n) (hne : ∀ b : Fin blocks.length, blocks.get b ≠ [])
    (hlen : ∀ b : Fin blocks.length, (blocks.get b).length ≤ t) :
    Fintype.card (Lower blocks) ≤ blocks.length * n ^ (t + 1) := by
  rw [card_lower blocks hne]
  calc
    ∑ b : Fin blocks.length, n ^ ((blocks.get b).length + 1) ≤
        ∑ _b : Fin blocks.length, n ^ (t + 1) := by
      exact Finset.sum_le_sum (fun b _ =>
        pow_le_pow_right₀ hn (Nat.add_le_add_right (hlen b) 1))
    _ = blocks.length * n ^ (t + 1) := by simp

end Problem335.BlockData

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BlockCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335.BlockData

variable {n : ℕ}

theorem circuit_size (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) :
    circuitSize (circuit K blocks z) = 2 * n ^ 3 +
      Fintype.card (Lower blocks) + Fintype.card (Middle blocks) +
        Fintype.card (Upper blocks z) + 1 := by
  rw [circuit, IndexedDepth5Circuit.circuitSize_toDepth5Circuit]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

end Problem335.BlockData

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.MatrixPathSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ ι R : Type*}

/-- The same expansion as a finite sum, convenient for finite-type gate constructors. -/
theorem matrixEntryPaths_fin_sum_prod [Fintype ι] [DecidableEq ι] [Semiring R]
    (A : σ → Matrix ι ι R) (labels : List σ) (i j : ι) :
    (∑ k : Fin (matrixEntryPaths labels i j).length,
      (((matrixEntryPaths labels i j).get k).map
        (fun e => A e.1 e.2.1 e.2.2)).prod) =
      ((labels.map A).prod) i j := by
  rw [← List.sum_ofFn]
  have h := congrArg
    (List.map (fun p : List (σ × ι × ι) => (p.map (fun e => A e.1 e.2.1 e.2.2)).prod))
    (List.ofFn_get (matrixEntryPaths labels i j))
  simp only [List.map_ofFn, Function.comp_def] at h
  rw [h]
  exact matrixEntryPaths_sum_prod A labels i j

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BlockMiddleSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335.BlockData

variable {n : ℕ}

/-- The weighted middle input list computes exactly the corresponding block matrix entry. -/
theorem middleInputs_value (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (m : Middle blocks) :
    ((middleInputs K blocks m).map (fun e =>
      MvPolynomial.C e.1 * lowerMonomial K blocks e.2)).sum =
      (((blocks.get m.1).map (immLayer K n)).prod) m.2.1 m.2.2 := by
  simp only [middleInputs, List.map_ofFn, Function.comp_def, lowerMonomial,
    lowerInputs, MvPolynomial.C_1, one_mul, List.sum_ofFn]
  exact matrixEntryPaths_fin_sum_prod (immLayer K n) (blocks.get m.1) m.2.1 m.2.2

end Problem335.BlockData

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- Regrouping consecutive layers does not change the iterated matrix product. -/
theorem imm_eq_blocks_prod (hn : 0 < n) (blocks : List (List (Fin n)))
    (hblocks : blocks.flatten = List.finRange n) :
    imm K n = ((blocks.map (immBlock K n)).prod) ⟨0, hn⟩ ⟨0, hn⟩ := by
  have hm : (blocks.map (fun b : List (Fin n) => b.map (immLayer K n))).flatten =
      (List.finRange n).map (immLayer K n) := by
    rw [← List.map_flatten, hblocks]
  have hp : (blocks.map (immBlock K n)).prod =
      ((List.finRange n).map (immLayer K n)).prod := by
    change (blocks.map (fun b : List (Fin n) => (b.map (immLayer K n)).prod)).prod = _
    simpa only [List.prod_flatten, List.map_map, Function.comp_def] using
      congrArg List.prod hm
  rw [hp]
  simp only [imm, dite_eq_left hn, List.ofFn_eq_map]


end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BlockCircuitValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.BlockData

variable {n : ℕ}

@[simp] theorem indexedCircuit_middleValue (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) (m : Middle blocks) :
    (indexedCircuit K blocks z).middleValue m =
      immBlock K n (blocks.get m.1) m.2.1 m.2.2 := by
  change ((middleInputs K blocks m).map (fun e =>
    MvPolynomial.C e.1 * (indexedCircuit K blocks z).lowerValue e.2)).sum = _
  simp_rw [indexedCircuit_lowerValue]
  exact middleInputs_value K blocks m

@[simp] theorem indexedCircuit_upperValue (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) (p : Upper blocks z) :
    (indexedCircuit K blocks z).upperValue p =
      ((upperInputs blocks z p).map (fun e =>
        immBlock K n (blocks.get e.1) e.2.1 e.2.2)).prod := by
  change ((upperInputs blocks z p).map
    (fun m => (indexedCircuit K blocks z).middleValue m)).prod = _
  simp only [indexedCircuit_middleValue]

/-- The block circuit computes the corresponding entry of the product of block matrices. -/
theorem indexedCircuit_circuitValue (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) :
    (indexedCircuit K blocks z).circuitValue =
      ((blocks.map (immBlock K n)).prod) z z := by
  change ((outputInputs K blocks z).map (fun e =>
    MvPolynomial.C e.1 * (indexedCircuit K blocks z).upperValue e.2)).sum = _
  simp only [indexedCircuit_upperValue, outputInputs, List.map_ofFn,
    Function.comp_def, MvPolynomial.C_1, one_mul, List.sum_ofFn]
  change (∑ k : Fin (matrixEntryPaths (List.finRange blocks.length) z z).length,
    (((matrixEntryPaths (List.finRange blocks.length) z z).get k).map
      (fun e => immBlock K n (blocks.get e.1) e.2.1 e.2.2)).prod) = _
  rw [matrixEntryPaths_fin_sum_prod (fun j : Fin blocks.length =>
    immBlock K n (blocks.get j))]
  simp [← List.ofFn_eq_map]

/-- Semantic correctness after converting all gate indices to `Fin`. -/
theorem circuit_value (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) :
    Problem335.circuitValue (circuit K blocks z) =
      ((blocks.map (immBlock K n)).prod) z z := by
  rw [circuit, IndexedDepth5Circuit.circuitValue_toDepth5Circuit,
    indexedCircuit_circuitValue]

/-- Any partition of the layers produces a circuit computing the qualified IMM polynomial. -/
theorem circuit_value_eq_imm (K : Type*) [CommSemiring K]
    (hn : 0 < n) (blocks : List (List (Fin n)))
    (hblocks : blocks.flatten = List.finRange n) :
    Problem335.circuitValue (circuit K blocks ⟨0, hn⟩) = imm K n := by
  rw [circuit_value, imm_eq_blocks_prod hn blocks hblocks]

end Problem335.BlockData

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BlockPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem335

theorem blockLengths_sum (n t : ℕ) : (blockLengths n t).sum = n := by
  simp only [blockLengths, List.sum_append, List.sum_replicate]
  split_ifs with h
  · simp only [List.sum_nil, add_zero]
    simpa [h, Nat.mul_comm] using Nat.div_add_mod n t
  · simpa [Nat.mul_comm] using Nat.div_add_mod n t

theorem blockLengths_pos {n t : ℕ} (ht : 0 < t) :
    ∀ d ∈ blockLengths n t, 0 < d := by
  intro d hd
  simp only [blockLengths, List.mem_append] at hd
  rcases hd with hd | hd
  · have : d = t := (List.mem_replicate.mp hd).2
    simpa [this] using ht
  · split_ifs at hd with h
    · simp at hd
    · have : d = n % t := by simpa using hd
      simpa [this] using (show 0 < n % t from Nat.pos_of_ne_zero h)

theorem blockLengths_le {n t : ℕ} (ht : 0 < t) :
    ∀ d ∈ blockLengths n t, d ≤ t := by
  intro d hd
  simp only [blockLengths, List.mem_append] at hd
  rcases hd with hd | hd
  · exact le_of_eq (List.mem_replicate.mp hd).2
  · split_ifs at hd with h
    · simp at hd
    · have : d = n % t := by simpa using hd
      simpa [this] using (Nat.mod_lt n ht).le

theorem blockLengths_length {n t : ℕ} (ht : 0 < t) :
    (blockLengths n t).length = ceilDiv n t := by
  simp only [blockLengths, List.length_append, List.length_replicate]
  have hm := Nat.mod_lt n ht
  have hd := Nat.div_add_mod n t
  have hs : n + t - 1 + 1 = n + t := by omega
  unfold ceilDiv
  split_ifs with h
  · simp only [List.length_nil, add_zero]
    symm
    apply Nat.div_eq_of_lt_le
    · nlinarith
    · nlinarith
  · simp only [List.length_singleton]
    have hp : 0 < n % t := Nat.pos_of_ne_zero h
    symm
    apply Nat.div_eq_of_lt_le
    · nlinarith
    · nlinarith

@[simp] theorem consecutiveBlocks_flatten {α : Type*} (t : ℕ) (l : List α) :
    (consecutiveBlocks t l).flatten = l := by
  apply List.flatten_splitLengths
  simp [blockLengths_sum]

@[simp] theorem consecutiveBlocks_map_length {α : Type*} (t : ℕ) (l : List α) :
    (consecutiveBlocks t l).map List.length = blockLengths l.length t := by
  apply List.map_splitLengths_length
  simp [blockLengths_sum]

theorem consecutiveBlocks_length {α : Type*} {t : ℕ} (ht : 0 < t) (l : List α) :
    (consecutiveBlocks t l).length = ceilDiv l.length t := by
  simpa only [consecutiveBlocks, List.length_splitLengths] using
    (blockLengths_length (n := l.length) ht)

theorem consecutiveBlocks_length_pos {α : Type*} {t : ℕ} (ht : 0 < t)
    (l : List α) {b : List α} (hb : b ∈ consecutiveBlocks t l) : 0 < b.length := by
  apply blockLengths_pos ht b.length
  rw [← consecutiveBlocks_map_length t l]
  exact List.mem_map_of_mem hb

theorem consecutiveBlocks_length_le {α : Type*} {t : ℕ} (ht : 0 < t)
    (l : List α) {b : List α} (hb : b ∈ consecutiveBlocks t l) : b.length ≤ t := by
  apply blockLengths_le ht b.length
  rw [← consecutiveBlocks_map_length t l]
  exact List.mem_map_of_mem hb

theorem consecutiveBlocks_nonempty {α : Type*} {t : ℕ} (ht : 0 < t)
    (l : List α) {b : List α} (hb : b ∈ consecutiveBlocks t l) : b ≠ [] := by
  have := consecutiveBlocks_length_pos ht l hb
  intro he
  simp [he] at this

@[simp] theorem layerBlocks_flatten (n t : ℕ) :
    (layerBlocks n t).flatten = List.finRange n :=
  consecutiveBlocks_flatten t _

theorem layerBlocks_length {n t : ℕ} (ht : 0 < t) :
    (layerBlocks n t).length = ceilDiv n t := by
  simpa [layerBlocks] using consecutiveBlocks_length ht (List.finRange n)

end Problem335

namespace Problem335

theorem layerBlocks_length_le {n t : ℕ} (ht : 0 < t)
    {b : List (Fin n)} (hb : b ∈ layerBlocks n t) : b.length ≤ t :=
  consecutiveBlocks_length_le ht _ hb

theorem layerBlocks_nonempty {n t : ℕ} (ht : 0 < t)
    {b : List (Fin n)} (hb : b ∈ layerBlocks n t) : b ≠ [] :=
  consecutiveBlocks_nonempty ht _ hb

theorem layerBlocks_get_length_le {n t : ℕ} (ht : 0 < t)
    (i : Fin (layerBlocks n t).length) : ((layerBlocks n t).get i).length ≤ t :=
  layerBlocks_length_le ht (List.get_mem ..)

@[simp] theorem layerBlocks_sum_lengths (n t : ℕ) :
    ((layerBlocks n t).map List.length).sum = n := by
  simp [layerBlocks, blockLengths_sum]

end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CoefficientDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v

namespace Problem335

variable {K : Type u} [Field K] {n : ℕ}

theorem restrictWeightedInputs_map_eval {ι : Type v} {β : Type*} (S : Subfield K)
    (l : List (K × ι)) (h : ∀ e ∈ l, e.1 ∈ S) (f : K × ι → β) :
    (restrictWeightedInputs S l h).map (fun e => f ((e.1 : K), e.2)) = l.map f := by
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map f) (restrictWeightedInputs_map_coe S l h)

@[simp] theorem map_bottomValue_restrictCircuit (c : Depth5Circuit K n)
    (i : Fin c.bottomCount) :
    MvPolynomial.map (circuitCoefficientField c).subtype
      (bottomValue (restrictCircuit c) i) = bottomValue c i := by
  simp only [bottomValue, map_list_sum, List.map_map, Function.comp_def, map_mul,
    MvPolynomial.map_C]
  change (List.map (fun e => MvPolynomial.C (e.1 : K) *
      MvPolynomial.map (circuitCoefficientField c).subtype
        (d5LeafValue (restrictLeaf c e.2)))
    (restrictWeightedInputs _ (c.bottomInputs i) (bottom_coeff_mem c i))).sum = _
  simp only [map_restrictLeaf_value]
  exact congrArg List.sum (restrictWeightedInputs_map_eval _ _ _
    (fun e : K × Fin c.leafCount => MvPolynomial.C e.1 * d5LeafValue (c.leaves e.2)))

@[simp] theorem map_lowerValue_restrictCircuit (c : Depth5Circuit K n)
    (i : Fin c.lowerCount) :
    MvPolynomial.map (circuitCoefficientField c).subtype
      (lowerValue (restrictCircuit c) i) = lowerValue c i := by
  simp only [lowerValue, map_list_prod, List.map_map, Function.comp_def]
  change (List.map (fun j => MvPolynomial.map (circuitCoefficientField c).subtype
    (bottomValue (restrictCircuit c) j)) (c.lowerInputs i)).prod = _
  exact congrArg List.prod (List.map_congr_left
    (fun index _ => map_bottomValue_restrictCircuit c index))

@[simp] theorem map_middleValue_restrictCircuit (c : Depth5Circuit K n)
    (i : Fin c.middleCount) :
    MvPolynomial.map (circuitCoefficientField c).subtype
      (middleValue (restrictCircuit c) i) = middleValue c i := by
  simp only [middleValue, map_list_sum, List.map_map, Function.comp_def, map_mul,
    MvPolynomial.map_C]
  change (List.map (fun e => MvPolynomial.C (e.1 : K) *
      MvPolynomial.map (circuitCoefficientField c).subtype
        (lowerValue (restrictCircuit c) e.2))
    (restrictWeightedInputs _ (c.middleInputs i) (middle_coeff_mem c i))).sum = _
  simp only [map_lowerValue_restrictCircuit]
  exact congrArg List.sum (restrictWeightedInputs_map_eval _ _ _
    (fun e : K × Fin c.lowerCount => MvPolynomial.C e.1 * lowerValue c e.2))

@[simp] theorem map_upperValue_restrictCircuit (c : Depth5Circuit K n)
    (i : Fin c.upperCount) :
    MvPolynomial.map (circuitCoefficientField c).subtype
      (upperValue (restrictCircuit c) i) = upperValue c i := by
  simp only [upperValue, map_list_prod, List.map_map, Function.comp_def]
  change (List.map (fun j => MvPolynomial.map (circuitCoefficientField c).subtype
    (middleValue (restrictCircuit c) j)) (c.upperInputs i)).prod = _
  exact congrArg List.prod (List.map_congr_left
    (fun index _ => map_middleValue_restrictCircuit c index))

@[simp] theorem map_circuitValue_restrictCircuit (c : Depth5Circuit K n) :
    MvPolynomial.map (circuitCoefficientField c).subtype
      (circuitValue (restrictCircuit c)) = circuitValue c := by
  simp only [circuitValue, map_list_sum, List.map_map, Function.comp_def, map_mul,
    MvPolynomial.map_C]
  change (List.map (fun e => MvPolynomial.C (e.1 : K) *
      MvPolynomial.map (circuitCoefficientField c).subtype
        (upperValue (restrictCircuit c) e.2))
    (restrictWeightedInputs _ c.outputInputs (output_coeff_mem c))).sum = _
  simp only [map_upperValue_restrictCircuit]
  exact congrArg List.sum (restrictWeightedInputs_map_eval _ _ _
    (fun e : K × Fin c.upperCount => MvPolynomial.C e.1 * upperValue c e.2))

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ComplexEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u

namespace Problem335

/-- Every countable characteristic-zero field admits an embedding into the complex numbers.
This applies to the subfield generated by the finitely many coefficients of a circuit. -/
theorem countable_field_embeds_complex (K : Type u) [Field K] [CharZero K] [Countable K] :
    Nonempty (K →+* ℂ) := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ
  have htcard : Cardinal.mk ℂ = Cardinal.mk t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
      (fun x : t => (x : ℂ)) ht Cardinal.mk_le_aleph0
      (by simpa using Cardinal.aleph0_lt_continuum)
  have : Infinite t := Cardinal.infinite_iff.mpr (by
    rw [← htcard]
    simpa using Cardinal.aleph0_lt_continuum.le)
  let e : s ↪ t := (Classical.choice (nonempty_embedding_nat s)).trans
    (Infinite.natEmbedding t)
  let v : s → ℂ := fun x => (e x : ℂ)
  have hv : AlgebraicIndependent ℚ v := ht.1.comp e e.injective
  let A := Algebra.adjoin ℚ (Set.range (fun x : s => (x : K)))
  let f : A →+* ℂ := (MvPolynomial.aeval v).toRingHom.comp hs.1.aevalEquiv.symm.toRingHom
  have hf : Function.Injective f :=
    (algebraicIndependent_iff_injective_aeval.mp hv).comp hs.1.aevalEquiv.symm.injective
  let : Algebra A ℂ := f.toAlgebra
  have : Module.IsTorsionFree A ℂ :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hf
  have : Algebra.IsAlgebraic A K := hs.isAlgebraic
  exact ⟨(IsAlgClosed.lift (R := A) (S := K) (M := ℂ)).toRingHom⟩

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u v

namespace Problem335

/-- Iterated matrix multiplication commutes with change of coefficient semiring. -/
@[simp] theorem map_imm {K : Type u} {L : Type v} [CommSemiring K] [CommSemiring L]
    (f : K →+* L) (n : ℕ) : MvPolynomial.map f (imm K n) = imm L n := by
  classical
  by_cases hn : 0 < n
  · simp only [imm, dite_eq_left hn]
    let F := (MvPolynomial.map (σ := Fin n × Fin n × Fin n) f).mapMatrix (m := Fin n)
    have h := F.map_list_prod (List.ofFn (fun t : Fin n => immLayer K n t))
    have hm : (List.ofFn (fun t : Fin n => immLayer K n t)).map F =
        List.ofFn (fun t : Fin n => immLayer L n t) := by
      simp only [List.map_ofFn]
      congr 1
      funext t i j
      simp [F, immLayer]
    change F (List.ofFn (fun t : Fin n => immLayer K n t)).prod =
      ((List.ofFn (fun t : Fin n => immLayer K n t)).map F).prod at h
    rw [hm] at h
    exact congrArg (fun M => M ⟨0, hn⟩ ⟨0, hn⟩) h
  · simp [imm, hn]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CharacteristicZeroTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u

namespace Problem335

/-- A circuit over a countable characteristic-zero field can be realized over
`ℂ`, with exactly the same number of gates and the same IMM identity. -/
theorem exists_complex_circuit_of_countable {K : Type u} [Field K] [CharZero K]
    [Countable K] {n : ℕ} (c : Depth5Circuit K n)
    (hc : circuitValue c = imm K n) :
    ∃ d : Depth5Circuit ℂ n, circuitValue d = imm ℂ n ∧ circuitSize d = circuitSize c := by
  obtain ⟨f⟩ := countable_field_embeds_complex K
  refine ⟨c.mapCoefficients f, ?_, circuitSize_mapCoefficients f c⟩
  rw [circuitValue_mapCoefficients, hc, map_imm]

/-- Restriction to the coefficient subfield preserves and reflects the IMM identity. -/
theorem restrictCircuit_computes_imm {K : Type u} [Field K] {n : ℕ}
    (c : Depth5Circuit K n) :
    circuitValue (restrictCircuit c) = imm (circuitCoefficientField c) n ↔
      circuitValue c = imm K n := by
  have hi := MvPolynomial.map_injective (σ := Fin n × Fin n × Fin n)
    (circuitCoefficientField c).subtype
    (circuitCoefficientField c).subtype.injective
  rw [← hi.eq_iff, map_circuitValue_restrictCircuit, map_imm]

/-- Every characteristic-zero IMM circuit has a same-size complex realization.
Only the finitely many occurring coefficients are embedded, not the entire field. -/
theorem exists_complex_circuit {K : Type u} [Field K] [CharZero K]
    {n : ℕ} (c : Depth5Circuit K n) (hc : circuitValue c = imm K n) :
    ∃ d : Depth5Circuit ℂ n, circuitValue d = imm ℂ n ∧ circuitSize d = circuitSize c := by
  obtain ⟨d, hd, hs⟩ := exists_complex_circuit_of_countable (restrictCircuit c)
    ((restrictCircuit_computes_imm c).mpr hc)
  exact ⟨d, hd, hs.trans (circuitSize_restrictCircuit c)⟩

/-- Pointwise complex gate lower bounds hold over any characteristic-zero field. -/
theorem circuit_bound_of_complex {K : Type u} [Field K] [CharZero K]
    {n : ℕ} {b : ℝ}
    (h : ∀ d : Depth5Circuit ℂ n,
      circuitValue d = imm ℂ n → b ≤ (circuitSize d : ℝ))
    (c : Depth5Circuit K n) (hc : circuitValue c = imm K n) :
    b ≤ (circuitSize c : ℝ) := by
  obtain ⟨d, hd, hs⟩ := exists_complex_circuit c hc
  simpa only [hs] using h d hd

/-- The extension to characteristic zero uses the same absolute threshold as
its complex counterpart. This implication has no lower-bound assumptions other
than the precise complex conclusion. -/
theorem characteristic_zero_depth_five_lower_bound_of_complex
    (h : ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ c : Depth5Circuit ℂ n,
      circuitValue c = imm ℂ n →
      (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤ (circuitSize c : ℝ)) :
    ∃ n0 : ℕ, ∀ (K : Type u) [Field K] [CharZero K], ∀ n : ℕ, n0 ≤ n →
      ∀ c : Depth5Circuit K n, circuitValue c = imm K n →
      (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤ (circuitSize c : ℝ) := by
  obtain ⟨n0, h0⟩ := h
  refine ⟨n0, ?_⟩
  intro K _ _ n hn c hc
  exact circuit_bound_of_complex (h0 n hn) c hc

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PathShifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- A coordinate in one layer can only come from that layer. -/
theorem pathShift_apply {α : Type*} [DecidableEq α] {n : ℕ} (sgn : Fin n → ℤ)
    (p : Fin (n + 1) → α) (t : Fin n) (a b : α) :
    pathShift sgn p (t, a, b) =
      if (p t.castSucc, p t.succ) = (a, b) then sgn t else 0 := by
  classical
  unfold pathShift
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single t]
  · simp [Finsupp.single_apply]
  · intro j hj hjt
    simp [hjt]
  · simp

/-- Global compatibility of four path shifts is exactly compatibility in
 each layer separately. The nonzero signs cancel, so the local condition
 is independent of whether that layer differentiates or multiplies. -/
theorem pathShift_sub_eq_iff {α : Type*} {n : ℕ}
    (sgn : Fin n → ℤ) (hs : ∀ t, sgn t ≠ 0)
    (p q r s : Fin (n + 1) → α) :
    pathShift sgn p - pathShift sgn q = pathShift sgn r - pathShift sgn s ↔
      ∀ t : Fin n,
        Finsupp.single (p t.castSucc, p t.succ) (1 : ℤ) -
          Finsupp.single (q t.castSucc, q t.succ) 1 =
        Finsupp.single (r t.castSucc, r t.succ) 1 -
          Finsupp.single (s t.castSucc, s t.succ) 1 := by
  classical
  constructor
  · intro heq t
    ext ab
    rcases ab with ⟨a, b⟩
    have h := congrArg (fun f => f (t, a, b)) heq
    simp only [Finsupp.sub_apply, pathShift_apply] at h
    apply mul_left_cancel₀ (hs t)
    simpa only [Finsupp.sub_apply, Finsupp.single_apply, mul_sub, mul_ite,
      mul_one, mul_zero] using h
  · intro heq
    ext tab
    rcases tab with ⟨t, a, b⟩
    have h := congrArg (fun f => sgn t * f (a, b)) (heq t)
    simpa only [Finsupp.sub_apply, pathShift_apply, Finsupp.single_apply,
      mul_sub, mul_ite, mul_one, mul_zero] using h

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmPathShifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The signed creation/annihilation shift of the actual IMM edge list is
exactly the layered vertex-path shift. -/
theorem occupationShift_immInternalPathEdges (d : ℕ) (side : Fin (d + 1) → Bool)
    (p : Fin d → Fin (d + 1)) :
    occupationShift (fun e => side e.1) (immInternalPathEdges d p) =
      pathShift (fun t => if side t then (-1 : ℤ) else 1)
        (immInternalPathVertices d p) := by
  simp only [occupationShift, immInternalPathEdges, List.map_ofFn,
    List.sum_ofFn, Function.comp_def, pathShift,
    immInternalPathVertices_castSucc, immInternalPathVertices_succ]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmPathCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

/-- Four genuine IMM path shifts are compatible exactly when their coordinate
vectors are compatible separately in each layer. -/
theorem immInternalPath_shift_sub_eq_iff (d : ℕ) (side : Fin (d + 1) → Bool)
    (p q r s : Fin d → Fin (d + 1)) :
    occupationShift (fun e => side e.1) (immInternalPathEdges d p) -
        occupationShift (fun e => side e.1) (immInternalPathEdges d q) =
      occupationShift (fun e => side e.1) (immInternalPathEdges d r) -
        occupationShift (fun e => side e.1) (immInternalPathEdges d s) ↔
      ∀ t, Finsupp.single (immInternalCoordinate d p t) (1 : ℤ) -
          Finsupp.single (immInternalCoordinate d q t) 1 =
        Finsupp.single (immInternalCoordinate d r t) 1 -
          Finsupp.single (immInternalCoordinate d s t) 1 := by
  simp only [occupationShift_immInternalPathEdges]
  exact pathShift_sub_eq_iff _ (fun t => by cases side t <;> norm_num) _ _ _ _

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmPairingCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

/-- Closing the four internal IMM paths gives the canonical endpoint-fixed labels. -/
theorem closePaths_immInternalPathVertices (d : ℕ)
    (p q r s : Fin d → Fin (d + 1)) (t : Fin (d + 2)) :
    Pairings.closePaths 0 (fun i => ⟨p i, q i, r i, s i⟩) t =
      (⟨immInternalPathVertices d p t, immInternalPathVertices d q t,
        immInternalPathVertices d r t, immInternalPathVertices d s t⟩ :
          Pairings.Labels (Fin (d + 1))) := by
  refine Fin.cases ?_ (fun i => ?_) t
  · rfl
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.succ_last, Pairings.closePaths_last, immInternalPathVertices_end]
      rfl
    · simp [Pairings.closePaths, immInternalPathVertices]

/-- Layer labels used in the relaxed pairing sum are the actual four IMM coordinates. -/
theorem layerLabels_immInternalCoordinate (d : ℕ)
    (p q r s : Fin d → Fin (d + 1)) (t : Fin (d + 1)) :
    MomentPairing.layerLabels 0 (fun i => ⟨p i, q i, r i, s i⟩) t =
      (⟨immInternalCoordinate d p t, immInternalCoordinate d q t,
        immInternalCoordinate d r t, immInternalCoordinate d s t⟩ :
          Pairings.Labels (Fin (d + 1) × Fin (d + 1))) := by
  simp only [MomentPairing.layerLabels, closePaths_immInternalPathVertices]
  rfl

/-- The actual four-path shift constraint is exactly the compatibility predicate
used by the weighted exact-to-relaxed pairing inequality. -/
theorem immInternalPath_shift_sub_eq_iff_compatible (d : ℕ)
    (side : Fin (d + 1) → Bool) (p q r s : Fin d → Fin (d + 1)) :
    occupationShift (fun e => side e.1) (immInternalPathEdges d p) -
        occupationShift (fun e => side e.1) (immInternalPathEdges d q) =
      occupationShift (fun e => side e.1) (immInternalPathEdges d r) -
        occupationShift (fun e => side e.1) (immInternalPathEdges d s) ↔
      MomentPairing.Compatible 0 (fun i => ⟨p i, q i, r i, s i⟩) := by
  rw [immInternalPath_shift_sub_eq_iff]
  simp only [MomentPairing.Compatible, layerLabels_immInternalCoordinate]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.MatrixPathPairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.Pairings

variable {α β σ : Type*}

/-- A sum over four-field records is precisely the iterated fourfold sum. -/
theorem sum_matrixPathLabels [Fintype α] {R : Type*} [AddCommMonoid R]
    (f : Labels α → R) :
    (∑ x : Labels α, f x) = ∑ p : α, ∑ q : α, ∑ r : α, ∑ s : α, f ⟨p,q,r,s⟩ := by
  simpa only [Fintype.sum_prod_type, matrixPathLabelsProdEquiv, Equiv.coe_fn_symm_mk] using
    (Equiv.sum_comp (matrixPathLabelsProdEquiv (α := α)).symm f).symm

/-- Reindex the complete four-path sum into the exact internal-label space used by
pairing classification. No positivity or compatibility premise is required. -/
theorem sum_four_matrixEntryPaths_eq [Fintype α] [DecidableEq α]
    {R : Type*} [AddCommMonoid R] (d : ℕ)
    (labels : Fin (d + 1) → σ) (a : α)
    (f : List (σ × α × α) → List (σ × α × α) →
      List (σ × α × α) → List (σ × α × α) → R) :
    (∑ p : Fin (matrixEntryPaths (List.ofFn labels) a a).length,
      ∑ q : Fin (matrixEntryPaths (List.ofFn labels) a a).length,
      ∑ r : Fin (matrixEntryPaths (List.ofFn labels) a a).length,
      ∑ s : Fin (matrixEntryPaths (List.ofFn labels) a a).length,
        f ((matrixEntryPaths (List.ofFn labels) a a).get p)
          ((matrixEntryPaths (List.ofFn labels) a a).get q)
          ((matrixEntryPaths (List.ofFn labels) a a).get r)
          ((matrixEntryPaths (List.ofFn labels) a a).get s)) =
      ∑ x : Fin d → Labels α,
        f (internalPathEdges labels a a (fun t => (x t).p))
          (internalPathEdges labels a a (fun t => (x t).q))
          (internalPathEdges labels a a (fun t => (x t).r))
          (internalPathEdges labels a a (fun t => (x t).s)) := by
  let g : Labels (Fin (matrixEntryPaths (List.ofFn labels) a a).length) → R :=
    fun x => f ((matrixEntryPaths (List.ofFn labels) a a).get x.p)
      ((matrixEntryPaths (List.ofFn labels) a a).get x.q)
      ((matrixEntryPaths (List.ofFn labels) a a).get x.r)
      ((matrixEntryPaths (List.ofFn labels) a a).get x.s)
  calc
    _ = ∑ x, g x := (sum_matrixPathLabels g).symm
    _ = _ := by
      simpa only [g, quadruplePathIndexEquiv_get_p, quadruplePathIndexEquiv_get_q,
        quadruplePathIndexEquiv_get_r, quadruplePathIndexEquiv_get_s] using
        (Equiv.sum_comp (quadruplePathIndexEquiv d labels a) g).symm

end Problem335.Pairings

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmPairingReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

/-- Filtered four-path IMM sums are exactly the compatible internal-label sums. -/
theorem sum_four_immPaths_compatible_eq {A : Type*} [AddCommMonoid A] (d : ℕ)
    (side : Fin (d + 1) → Bool)
    (f : List (Fin (d + 1) × Fin (d + 1) × Fin (d + 1)) →
      List (Fin (d + 1) × Fin (d + 1) × Fin (d + 1)) →
      List (Fin (d + 1) × Fin (d + 1) × Fin (d + 1)) →
      List (Fin (d + 1) × Fin (d + 1) × Fin (d + 1)) → A) :
    let paths := immPaths (d + 1) (Nat.succ_pos d)
    (∑ p : Fin paths.length, ∑ q : Fin paths.length,
      ∑ r : Fin paths.length, ∑ s : Fin paths.length,
        let P := paths.get p
        let Q := paths.get q
        let R := paths.get r
        let S := paths.get s
        if occupationShift (fun e => side e.1) P - occupationShift (fun e => side e.1) Q =
            occupationShift (fun e => side e.1) R - occupationShift (fun e => side e.1) S
        then f P Q R S else 0) =
      ∑ x : {x : Fin d → Pairings.Labels (Fin (d + 1)) // MomentPairing.Compatible 0 x},
        f (immInternalPathEdges d (fun t => (x.1 t).p))
          (immInternalPathEdges d (fun t => (x.1 t).q))
          (immInternalPathEdges d (fun t => (x.1 t).r))
          (immInternalPathEdges d (fun t => (x.1 t).s)) := by
  classical
  dsimp only
  have hp : immPaths (d + 1) (Nat.succ_pos d) =
      matrixEntryPaths (List.ofFn (id : Fin (d + 1) → Fin (d + 1))) 0 0 := by
    rw [List.ofFn_id]
    rfl
  rw [hp]
  rw [Pairings.sum_four_matrixEntryPaths_eq d (id : Fin (d + 1) → Fin (d + 1)) 0
    (fun P Q R S => if occupationShift (fun e => side e.1) P -
      occupationShift (fun e => side e.1) Q =
      occupationShift (fun e => side e.1) R - occupationShift (fun e => side e.1) S
      then f P Q R S else 0)]
  change (∑ x : Fin d → Pairings.Labels (Fin (d + 1)),
    if occupationShift (fun e => side e.1) (immInternalPathEdges d (fun t => (x t).p)) -
        occupationShift (fun e => side e.1) (immInternalPathEdges d (fun t => (x t).q)) =
      occupationShift (fun e => side e.1) (immInternalPathEdges d (fun t => (x t).r)) -
        occupationShift (fun e => side e.1) (immInternalPathEdges d (fun t => (x t).s))
    then f (immInternalPathEdges d (fun t => (x t).p))
      (immInternalPathEdges d (fun t => (x t).q))
      (immInternalPathEdges d (fun t => (x t).r))
      (immInternalPathEdges d (fun t => (x t).s)) else 0) = _
  simp only [immInternalPath_shift_sub_eq_iff_compatible]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LayeredFourPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace LayeredFourPath

/-- Compatibility of global signed shifts gives the local pairing identity at every layer. -/
theorem coordinate_matching_of_signedShift {T σ : Type*} [DecidableEq σ]
    (side : T → Bool) (p q r s : T → σ)
    (h : signedShift side p - signedShift side q =
      signedShift side r - signedShift side s) (t : T) :
    Finsupp.single (p t) (1 : ℤ) - Finsupp.single (q t) 1 =
      Finsupp.single (r t) 1 - Finsupp.single (s t) 1 := by
  ext x
  have hx := congrArg (fun f : T → σ → ℤ => f t x) h
  change (Finsupp.single (p t) (1 : ℤ)) x - (Finsupp.single (q t) 1) x =
    (Finsupp.single (r t) 1) x - (Finsupp.single (s t) 1) x
  cases ht : side t <;> simp [signedShift, ht] at hx <;> omega

/-- An actual shifted source automatically satisfies the local occupation relation. -/
theorem local_shift_of_signedOccupation {T σ : Type*} [DecidableEq σ]
    (side : T → Bool) (M M' : T → σ → ℕ) (p q : T → σ)
    (h : signedOccupation M' =
      signedOccupation M + signedShift side p - signedShift side q) (t : T) :
    LocalMoments.ShiftRelation (side t) (M t) (M' t) (p t) (q t) := by
  intro x
  have hx := congrArg (fun f : T → σ → ℤ => f t x) h
  change (M' t x : ℤ) = (M t x : ℤ) +
    (if side t then -1 else 1) * (Finsupp.single (p t) (1 : ℤ)) x -
    (if side t then -1 else 1) * (Finsupp.single (q t) (1 : ℤ)) x at hx
  rw [Finsupp.sub_apply]
  rw [hx]
  ring

/-- The entire valid four-path coefficient is the product of the local occupation table. -/
theorem amplitude_four_eq_local_product {T σ : Type*} [Fintype T] [DecidableEq σ]
    (side : T → Bool) (M M' : T → σ → ℕ) (p q r s : T → σ)
    (hmatch : signedShift side p - signedShift side q =
      signedShift side r - signedShift side s)
    (hshift : signedOccupation M' =
      signedOccupation M + signedShift side p - signedShift side q) :
    amplitude side M p * amplitude side M' q * amplitude side M r * amplitude side M' s =
      ∏ t, LocalMoments.localPolynomial (side t) (M t) (p t) (q t) (r t) := by
  exact LocalMoments.four_path_products_eq_localPolynomial_product Finset.univ
    side M M' p q r s
    (fun t _ => coordinate_matching_of_signedShift side p q r s hmatch t)
    (fun t _ => local_shift_of_signedOccupation side M M' p q hshift t)

/-- Lift the valid-source identity to a zero extension. Missing shifted source occupations
contribute zero, so an upper estimate needs no source-validity-closure hypothesis. -/
theorem zeroExtended_amplitude_four_le_local_product
    {I T σ : Type*} [Fintype T] [DecidableEq σ]
    (side : T → Bool) (M : I → T → σ → ℕ)
    (hinj : Function.Injective (fun i => signedOccupation (M i)))
    (i : I) (p q r s : T → σ)
    (hmatch : signedShift side p - signedShift side q =
      signedShift side r - signedShift side s) :
    amplitude side (M i) p *
        Function.extend (fun k => signedOccupation (M k))
          (fun k => amplitude side (M k) q) (fun _ => 0)
          (signedOccupation (M i) + signedShift side p - signedShift side q) *
      amplitude side (M i) r *
        Function.extend (fun k => signedOccupation (M k))
          (fun k => amplitude side (M k) s) (fun _ => 0)
          (signedOccupation (M i) + signedShift side p - signedShift side q) ≤
      ∏ t, LocalMoments.localPolynomial (side t) (M i t) (p t) (q t) (r t) := by
  classical
  let x := signedOccupation (M i) + signedShift side p - signedShift side q
  by_cases hx : ∃ k, signedOccupation (M k) = x
  · obtain ⟨k, hk⟩ := hx
    change amplitude side (M i) p *
        Function.extend (fun k => signedOccupation (M k))
          (fun k => amplitude side (M k) q) (fun _ => 0) x *
      amplitude side (M i) r *
        Function.extend (fun k => signedOccupation (M k))
          (fun k => amplitude side (M k) s) (fun _ => 0) x ≤ _
    rw [← hk, hinj.extend_apply, hinj.extend_apply]
    exact (amplitude_four_eq_local_product side (M i) (M k) p q r s hmatch hk).le
  · have hz := Function.extend_apply' (f := fun k => signedOccupation (M k))
      (fun k => amplitude side (M k) q) (fun _ => (0 : ℝ)) x hx
    change amplitude side (M i) p *
        Function.extend (fun k => signedOccupation (M k))
          (fun k => amplitude side (M k) q) (fun _ => 0) x *
      amplitude side (M i) r *
        Function.extend (fun k => signedOccupation (M k))
          (fun k => amplitude side (M k) s) (fun _ => 0) x ≤ _
    rw [hz]
    simp only [mul_zero, zero_mul]
    exact Finset.prod_nonneg (fun t _ => LocalMoments.localPolynomial_nonneg _ _ _ _ _)

end LayeredFourPath
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FockLayerProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335
namespace FockLayerProfile

variable {ι : Type*} {n : ℕ}

lemma currySigned_injective : Function.Injective (currySigned (n := n) (ι := ι)) := by
  intro f g h
  ext e
  exact congrFun (congrFun h e.1) e.2

/-- The list-path coefficient is exactly the coefficient of its layer profile. -/
theorem pathAmplitude_eq_layered (side : Fin n → Bool)
    (p : List (Fin n × ι × ι)) (hp : p.map Prod.fst = List.finRange n)
    (d : (Fin n × ι × ι) →₀ ℕ) :
    (p.map (occupationAmplitude (fun e => side e.1) d)).prod =
      LayeredFourPath.amplitude side (fun t x => d (t, x)) (edgeProfile p hp) := by
  conv_lhs => rw [edgeList_eq_ofFn_profile p hp, List.map_ofFn, Fin.prod_ofFn]
  rfl

/-- Signed list shifts and signed layer-profile shifts have identical coordinates. -/
theorem occupationShift_eq_layered [DecidableEq ι] (side : Fin n → Bool)
    (p : List (Fin n × ι × ι)) (hp : p.map Prod.fst = List.finRange n) :
    currySigned (occupationShift (fun e => side e.1) p) =
      LayeredFourPath.signedShift side (edgeProfile p hp) := by
  ext t x
  rcases x with ⟨a, b⟩
  change occupationShift (fun e => side e.1) p (t, a, b) = _
  have heq : occupationShift (fun e => side e.1) p = edgeListShift side p :=
    (edgeListShift_eq_sum side p).symm
  rw [heq, edgeListShift_apply_profile side p hp]
  simp only [LayeredFourPath.signedShift, Finsupp.single_apply, mul_ite, mul_one, mul_zero]

/-- Changing from finitely supported signed occupations to layer coordinates
preserves zero extension, including arguments outside the finite source. -/
theorem zeroExtend_eq_layered {I : Type*}
    (d : I → (Fin n × ι × ι) →₀ ℕ) (hd : Function.Injective d)
    (w : I → ℝ) (x : (Fin n × ι × ι) →₀ ℤ) :
    Function.extend (fun i => Problem335.signedOccupation (d i)) w (fun _ => 0) x =
      Function.extend (fun i => LayeredFourPath.signedOccupation (fun t y => d i (t, y)))
        w (fun _ => 0) (currySigned x) := by
  classical
  have hi : Function.Injective (fun i => Problem335.signedOccupation (d i)) :=
    Problem335.signedOccupation_injective.comp hd
  have hc : Function.Injective (fun i =>
      LayeredFourPath.signedOccupation (fun t y => d i (t, y))) :=
    currySigned_injective.comp hi
  by_cases hx : ∃ i, Problem335.signedOccupation (d i) = x
  · obtain ⟨i, rfl⟩ := hx
    rw [hi.extend_apply, currySigned_signedOccupation, hc.extend_apply]
  · rw [Function.extend_apply' _ _ _ hx, Function.extend_apply']
    rintro ⟨i, h⟩
    exact hx ⟨i, currySigned_injective h⟩

/-- The exact list-path four-amplitude summand is bounded by the local table
of its layer profiles. No closure assumption for the shifted source is needed. -/
theorem zeroExtended_pathAmplitude_four_le_local_product
    {I : Type*} [DecidableEq ι] (side : Fin n → Bool)
    (d : I → (Fin n × ι × ι) →₀ ℕ) (hd : Function.Injective d) (i : I)
    (p q r s : List (Fin n × ι × ι))
    (hp : p.map Prod.fst = List.finRange n)
    (hq : q.map Prod.fst = List.finRange n)
    (hr : r.map Prod.fst = List.finRange n)
    (hs : s.map Prod.fst = List.finRange n)
    (hmatch : occupationShift (fun e => side e.1) p - occupationShift (fun e => side e.1) q =
      occupationShift (fun e => side e.1) r - occupationShift (fun e => side e.1) s) :
    (p.map (occupationAmplitude (fun e => side e.1) (d i))).prod *
      Function.extend (fun k => Problem335.signedOccupation (d k))
        (fun k => (q.map (occupationAmplitude (fun e => side e.1) (d k))).prod)
        (fun _ => 0) (Problem335.signedOccupation (d i) +
          occupationShift (fun e => side e.1) p - occupationShift (fun e => side e.1) q) *
      (r.map (occupationAmplitude (fun e => side e.1) (d i))).prod *
      Function.extend (fun k => Problem335.signedOccupation (d k))
        (fun k => (s.map (occupationAmplitude (fun e => side e.1) (d k))).prod)
        (fun _ => 0) (Problem335.signedOccupation (d i) +
          occupationShift (fun e => side e.1) p - occupationShift (fun e => side e.1) q) ≤
      ∏ t, LocalMoments.localPolynomial (side t) (fun x => d i (t, x))
        (edgeProfile p hp t) (edgeProfile q hq t) (edgeProfile r hr t) := by
  have hinj : Function.Injective (fun k =>
      LayeredFourPath.signedOccupation (fun t x => d k (t, x))) :=
    currySigned_injective.comp (Problem335.signedOccupation_injective.comp hd)
  have hmatch' := congrArg (currySigned (n := n) (ι := ι)) hmatch
  simp only [map_sub, occupationShift_eq_layered side p hp,
    occupationShift_eq_layered side q hq, occupationShift_eq_layered side r hr,
    occupationShift_eq_layered side s hs] at hmatch'
  have h := LayeredFourPath.zeroExtended_amplitude_four_le_local_product side
    (fun k t x => d k (t, x)) hinj i
    (edgeProfile p hp) (edgeProfile q hq) (edgeProfile r hr) (edgeProfile s hs) hmatch'
  simp_rw [pathAmplitude_eq_layered side p hp, pathAmplitude_eq_layered side q hq,
    pathAmplitude_eq_layered side r hr, pathAmplitude_eq_layered side s hs]
  rw [zeroExtend_eq_layered d hd, zeroExtend_eq_layered d hd]
  simpa only [map_sub, map_add, currySigned_signedOccupation,
    occupationShift_eq_layered side p hp, occupationShift_eq_layered side q hq] using h

/-- The actual IMM list-path summand, with the second source zero-extended,
is bounded by its layerwise occupation table. -/
theorem imm_zeroExtended_amplitude_four_le_local_product
    {I : Type*} (n : ℕ) (hn : 0 < n) (side : Fin n → Bool)
    (d : I → (Fin n × Fin n × Fin n) →₀ ℕ) (hd : Function.Injective d) (i : I)
    (p q r s : Fin (immPaths n hn).length)
    (hmatch : occupationShift (fun e => side e.1) ((immPaths n hn).get p) -
        occupationShift (fun e => side e.1) ((immPaths n hn).get q) =
      occupationShift (fun e => side e.1) ((immPaths n hn).get r) -
        occupationShift (fun e => side e.1) ((immPaths n hn).get s)) :
    immPathAmplitude n hn (fun e => side e.1) (d i) p *
      Function.extend (fun k => Problem335.signedOccupation (d k))
        (fun k => immPathAmplitude n hn (fun e => side e.1) (d k) q) (fun _ => 0)
        (Problem335.signedOccupation (d i) +
          occupationShift (fun e => side e.1) ((immPaths n hn).get p) -
          occupationShift (fun e => side e.1) ((immPaths n hn).get q)) *
      immPathAmplitude n hn (fun e => side e.1) (d i) r *
      Function.extend (fun k => Problem335.signedOccupation (d k))
        (fun k => immPathAmplitude n hn (fun e => side e.1) (d k) s) (fun _ => 0)
        (Problem335.signedOccupation (d i) +
          occupationShift (fun e => side e.1) ((immPaths n hn).get p) -
          occupationShift (fun e => side e.1) ((immPaths n hn).get q)) ≤
      ∏ t, LocalMoments.localPolynomial (side t) (fun x => d i (t, x))
        (immProfile n hn p t) (immProfile n hn q t) (immProfile n hn r t) := by
  exact zeroExtended_pathAmplitude_four_le_local_product side d hd i
    ((immPaths n hn).get p) ((immPaths n hn).get q)
    ((immPaths n hn).get r) ((immPaths n hn).get s)
    (immPaths_labels n hn _ (List.get_mem _ p))
    (immPaths_labels n hn _ (List.get_mem _ q))
    (immPaths_labels n hn _ (List.get_mem _ r))
    (immPaths_labels n hn _ (List.get_mem _ s)) hmatch

end FockLayerProfile
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FourPathTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elimination of the second source index in the four-path trace formula. -/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {I P G : Type*} [Fintype I] [AddCommGroup G] [DecidableEq G]

/-- The second source in a compatible four-path term is uniquely determined.
The zero extension records absent (invalid) source occupations exactly. -/
theorem fourPath_eliminate_source (occupation : I → G)
    (hinj : Function.Injective occupation) (wq ws : I → ℝ)
    (M ep eq er es : G) (A C : ℝ) :
    (∑ k, if M + ep = occupation k + eq ∧ M + er = occupation k + es then
      A * wq k * C * ws k else 0) =
      if ep - eq = er - es then
        A * Function.extend occupation wq (fun _ => 0) (M + ep - eq) * C *
          Function.extend occupation ws (fun _ => 0) (M + ep - eq)
      else 0 := by
  classical
  let x := M + ep - eq
  have hfirst (k : I) : M + ep = occupation k + eq ↔ occupation k = x := by
    dsimp [x]
    constructor
    · intro h
      exact (eq_sub_iff_add_eq).2 h.symm
    · intro h
      exact ((eq_sub_iff_add_eq).1 h).symm
  have hsecond : M + er = x + es ↔ ep - eq = er - es := by
    have hx : x + es = M + ((ep - eq) + es) := by dsimp [x]; abel
    rw [hx, add_left_cancel_iff, eq_comm, ← eq_sub_iff_add_eq]
  by_cases hx : ∃ k, occupation k = x
  · obtain ⟨k, hk⟩ := hx
    have heq (l : I) : M + ep = occupation l + eq ↔ l = k := by
      rw [hfirst, ← hk, hinj.eq_iff]
    have hsec : M + er = occupation k + es ↔ ep - eq = er - es := by
      rw [hk]
      exact hsecond
    change _ = if ep - eq = er - es then
      A * Function.extend occupation wq (fun _ => 0) x * C *
        Function.extend occupation ws (fun _ => 0) x else 0
    rw [← hk, hinj.extend_apply, hinj.extend_apply]
    rw [Finset.sum_eq_single k]
    · simp [heq, hsec]
    · intro l hl hlk
      simp [heq, hlk]
    · simp
  · have hzq := Function.extend_apply' (f := occupation) wq (fun _ => (0 : ℝ)) x hx
    change _ = if ep - eq = er - es then
      A * Function.extend occupation wq (fun _ => 0) x * C *
        Function.extend occupation ws (fun _ => 0) x else 0
    rw [hzq]
    simp only [mul_zero, zero_mul, ite_self]
    apply Finset.sum_eq_zero
    intro k hk
    have hne : occupation k ≠ x := fun h => hx ⟨k, h⟩
    simp [hfirst, hne]

/-- The full four-path sum with the second source eliminated and invalid
source occupations retained through zero extension. -/
theorem fourPath_sum_eliminate_source [Fintype P]
    (occupation : I → G) (hinj : Function.Injective occupation)
    (eps : P → G) (weight : I → P → ℝ) :
    (∑ i, ∑ k, ∑ p, ∑ q, ∑ r, ∑ s,
      if occupation i + eps p = occupation k + eps q ∧
        occupation i + eps r = occupation k + eps s then
        weight i p * weight k q * weight i r * weight k s else 0) =
    ∑ i, ∑ p, ∑ q, ∑ r, ∑ s,
      if eps p - eps q = eps r - eps s then
        weight i p * Function.extend occupation (fun k => weight k q) (fun _ => 0)
          (occupation i + eps p - eps q) * weight i r *
        Function.extend occupation (fun k => weight k s) (fun _ => 0)
          (occupation i + eps p - eps q) else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  exact fourPath_eliminate_source occupation hinj (fun k => weight k q)
    (fun k => weight k s) (occupation i) (eps p) (eps q) (eps r) (eps s)
    (weight i p) (weight i r)

/-- The complex four-path trace with its second source removed. The signed
shift identity is required only for nonzero path weights, so invalid-path
fallback target indices do not affect the identity. -/
theorem complex_path_second_trace_eliminate_source
    {J : Type*} [Fintype J] [Fintype P] [DecidableEq I] [DecidableEq J]
    (occupation : I → G) (hinj : Function.Injective occupation)
    (targetOccupation : J → G) (htarget : Function.Injective targetOccupation)
    (eps : P → G) (shift : I → P → J) (weight : I → P → ℝ)
    (hshift : ∀ i p, weight i p ≠ 0 →
      targetOccupation (shift i p) = occupation i + eps p) :
    let A := pathShiftMatrix shift (fun i p => (weight i p : ℂ))
    ((A.conjTranspose * A) ^ 2).trace.re =
      ∑ i, ∑ p, ∑ q, ∑ r, ∑ s,
        if eps p - eps q = eps r - eps s then
          weight i p * Function.extend occupation (fun k => weight k q) (fun _ => 0)
            (occupation i + eps p - eps q) * weight i r *
          Function.extend occupation (fun k => weight k s) (fun _ => 0)
            (occupation i + eps p - eps q) else 0 := by
  classical
  dsimp
  rw [complex_path_second_trace_four_paths, ← fourPath_sum_eliminate_source occupation hinj]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hz : weight i p * weight k q * weight i r * weight k s = 0
  · simp [hz]
  · have hp' : weight i p ≠ 0 := by intro h; simp [h] at hz
    have hq' : weight k q ≠ 0 := by intro h; simp [h] at hz
    have hr' : weight i r ≠ 0 := by intro h; simp [h] at hz
    have hs' : weight k s ≠ 0 := by intro h; simp [h] at hz
    have h₁ : shift i p = shift k q ↔ occupation i + eps p = occupation k + eps q := by
      rw [← htarget.eq_iff, hshift i p hp', hshift k q hq']
    have h₂ : shift i r = shift k s ↔ occupation i + eps r = occupation k + eps s := by
      rw [← htarget.eq_iff, hshift i r hr', hshift k s hs']
    simp only [h₁, h₂]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmSecondTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second trace identity for the actual IMM operator in normalized
monomial coordinates.  Invalid path actions have zero amplitude, so their
chosen finite target index does not enter the trace. -/

noncomputable section
open scoped BigOperators

namespace Problem335

/-- Every nonzero actual path action has its prescribed signed displacement. -/
theorem signedOccupation_immPathOccupation (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (d : (Fin n × Fin n × Fin n) →₀ ℕ) (p : Fin (immPaths n hn).length)
    (hamp : immPathAmplitude n hn isV d p ≠ 0) :
    signedOccupation (immPathOccupation n hn isV d p) =
      signedOccupation d + immPathSignedShift n hn isV p := by
  exact signedOccupation_path_of_amplitude_ne_zero isV ((immPaths n hn).get p)
    (immPaths_nodup n hn _ (List.get_mem _ p)) d hamp

/-- The finite normalized coefficient matrix is the actual weighted path matrix
whenever all nonzero path actions are represented in its target coordinates. -/
theorem immCoefficientMatrix_eq_pathShiftMatrix {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (n : ℕ) (hn : 0 < n) (isV : (Fin n × Fin n × Fin n) → Bool)
    (source : I → (Fin n × Fin n × Fin n) →₀ ℕ)
    (target : J → (Fin n × Fin n × Fin n) →₀ ℕ)
    (htarget : Function.Injective target)
    (shift : I → Fin (immPaths n hn).length → J)
    (hshift : ∀ i p, immPathAmplitude n hn isV (source i) p ≠ 0 →
      target (shift i p) = immPathOccupation n hn isV (source i) p) :
    immCoefficientMatrix n isV source target =
      pathShiftMatrix shift (fun i p => (immPathAmplitude n hn isV (source i) p : ℂ)) := by
  classical
  ext j i
  change complexFockBasis.repr
    (mixedOperator isV (imm ℂ n) (complexFockMonomial (source i))) (target j) = _
  rw [complexFockBasis_repr_mixedOperator_imm n hn isV]
  unfold pathShiftMatrix
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hz : immPathAmplitude n hn isV (source i) p = 0
  · simp [hz]
  · simp only [← hshift i p hz, htarget.eq_iff]

/-- Source-eliminated second trace for the genuine finite IMM coefficient
matrix.  The only coordinate hypothesis says that nonzero path actions stay
in the chosen target basis; no trace or moment formula is assumed. -/
theorem immCoefficientMatrix_second_trace {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (n : ℕ) (hn : 0 < n) (isV : (Fin n × Fin n × Fin n) → Bool)
    (source : I → (Fin n × Fin n × Fin n) →₀ ℕ)
    (hsource : Function.Injective source)
    (target : J → (Fin n × Fin n × Fin n) →₀ ℕ)
    (htarget : Function.Injective target)
    (shift : I → Fin (immPaths n hn).length → J)
    (hshift : ∀ i p, immPathAmplitude n hn isV (source i) p ≠ 0 →
      target (shift i p) = immPathOccupation n hn isV (source i) p) :
    let A := immCoefficientMatrix n isV source target
    let occupation := fun i => signedOccupation (source i)
    let eps := immPathSignedShift n hn isV
    let weight := fun i p => immPathAmplitude n hn isV (source i) p
    ((A.conjTranspose * A) ^ 2).trace.re =
      ∑ i, ∑ p, ∑ q, ∑ r, ∑ s,
        if eps p - eps q = eps r - eps s then
          weight i p * Function.extend occupation (fun k => weight k q) (fun _ => 0)
            (occupation i + eps p - eps q) * weight i r *
          Function.extend occupation (fun k => weight k s) (fun _ => 0)
            (occupation i + eps p - eps q) else 0 := by
  classical
  dsimp only
  rw [immCoefficientMatrix_eq_pathShiftMatrix n hn isV source target htarget shift hshift]
  apply complex_path_second_trace_eliminate_source
    (fun i => signedOccupation (source i)) (signedOccupation_injective.comp hsource)
    (fun j => signedOccupation (target j)) (signedOccupation_injective.comp htarget)
  intro i p hp
  rw [hshift i p hp]
  exact signedOccupation_immPathOccupation n hn isV (source i) p hp

theorem immFinitePathShift_val_of_amplitude_ne_zero
    (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ)
    (e0 : ImmTargetIndex n side a b) (d : ImmSourceIndex n side a b)
    (p : Fin (immPaths n hn).length)
    (hp : immPathAmplitude n hn (fun x => side x.1) d.1 p ≠ 0) :
    (immFinitePathShift n hn side a b e0 d p).1 =
      immPathOccupation n hn (fun x => side x.1) d.1 p := by
  simp only [immFinitePathShift, dite_eq_left hp]

/-- The finite normalized operator matrix is the indicated submatrix of its
ambient normalized monomial coefficients. -/
theorem immNormalizedMatrix_eq_immCoefficientMatrix
    (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ) :
    immNormalizedMatrix n side a b =
      immCoefficientMatrix n (fun x => side x.1)
        (fun d : ImmSourceIndex n side a b => d.1)
        (fun e : ImmTargetIndex n side a b => e.1) := by
  classical
  ext e d
  rw [immNormalizedMatrix_apply n hn side a b]
  exact (complexFockBasis_repr_mixedOperator_imm n hn (fun x => side x.1) d.1 e.1).symm

/-- Exact source-eliminated second trace of the genuine finite IMM operator.
This includes an empty target space: then every path amplitude vanishes.
There are no trace, closure, or nonempty-index assumptions in the statement. -/
theorem immNormalizedMatrix_second_trace
    (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ) :
    let A := immNormalizedMatrix n side a b
    let occupation := fun d : ImmSourceIndex n side a b => signedOccupation d.1
    let eps := immPathSignedShift n hn (fun x => side x.1)
    let weight := fun (d : ImmSourceIndex n side a b) p =>
      immPathAmplitude n hn (fun x => side x.1) d.1 p
    ((A.conjTranspose * A) ^ 2).trace.re =
      ∑ d, ∑ p, ∑ q, ∑ r, ∑ s,
        if eps p - eps q = eps r - eps s then
          weight d p * Function.extend occupation (fun k => weight k q) (fun _ => 0)
            (occupation d + eps p - eps q) * weight d r *
          Function.extend occupation (fun k => weight k s) (fun _ => 0)
            (occupation d + eps p - eps q) else 0 := by
  classical
  rcases isEmpty_or_nonempty (ImmTargetIndex n side a b) with h | h
  · let := h
    have hA : immNormalizedMatrix n side a b = 0 := Subsingleton.elim _ _
    have hz (d : ImmSourceIndex n side a b) (p : Fin (immPaths n hn).length) :
        immPathAmplitude n hn (fun x => side x.1) d.1 p = 0 := by
      by_contra hp
      exact isEmptyElim (⟨immPathOccupation n hn (fun x => side x.1) d.1 p,
        immPathOccupation_bidegree_of_amplitude_ne_zero n hn side a b d.1 d.2 p hp⟩ :
          ImmTargetIndex n side a b)
    simp [hA, hz]
  · obtain ⟨e0⟩ := h
    dsimp only
    rw [immNormalizedMatrix_eq_immCoefficientMatrix n hn side a b]
    exact immCoefficientMatrix_second_trace n hn (fun x => side x.1)
      _ Subtype.val_injective _ Subtype.val_injective
      (immFinitePathShift n hn side a b e0)
      (immFinitePathShift_val_of_amplitude_ne_zero n hn side a b e0)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmSecondLocalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The actual finite normalized IMM second trace is bounded by the sum
of the compatible local occupation-polynomial products. This has no
source-validity, moment, or nonempty-index assumptions. -/
theorem immNormalizedMatrix_second_trace_le_localPolynomial_sum
    (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ) :
    let A := immNormalizedMatrix n side a b
    let eps := immPathSignedShift n hn (fun x => side x.1)
    ((A.conjTranspose * A) ^ 2).trace.re ≤
      ∑ d : ImmSourceIndex n side a b, ∑ p, ∑ q, ∑ r, ∑ s,
        if eps p - eps q = eps r - eps s then
          ∏ t : Fin n, LocalMoments.localPolynomial (side t) (fun x => d.1 (t, x))
            (FockLayerProfile.immProfile n hn p t)
            (FockLayerProfile.immProfile n hn q t)
            (FockLayerProfile.immProfile n hn r t)
        else 0 := by
  classical
  dsimp only
  rw [immNormalizedMatrix_second_trace n hn side a b]
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro s hs
  split_ifs with hmatch
  · exact FockLayerProfile.imm_zeroExtended_amplitude_four_le_local_product
      n hn side (fun d : ImmSourceIndex n side a b => d.1)
      Subtype.val_injective d p q r s hmatch
  · exact le_rfl

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmCompatibleTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

private theorem totalImmProfile_get (n : ℕ) (hn : 0 < n)
    (p : Fin (immPaths n hn).length) :
    totalImmProfile n ((immPaths n hn).get p) = FockLayerProfile.immProfile n hn p := by
  simp only [totalImmProfile, dite_eq_left (immPaths_labels n hn _ (List.get_mem _ p)),
    FockLayerProfile.immProfile]

private theorem totalImmProfile_internal (d : ℕ) (p : Fin d → Fin (d + 1)) :
    totalImmProfile (d + 1) (immInternalPathEdges d p) = immInternalCoordinate d p := by
  funext t
  simp only [totalImmProfile, dite_eq_left (immInternalPathEdges_labels d p),
    edgeProfile_immInternalPathEdges]

/-- The actual second trace is bounded by the compatible endpoint-path local
occupation sum, with one source sum and no remaining representation hypotheses. -/
theorem immNormalizedMatrix_second_trace_le_compatible
    (d : ℕ) (side : Fin (d + 1) → Bool) (a b : ℕ) :
    let A := immNormalizedMatrix (d + 1) side a b
    ((A.conjTranspose * A) ^ 2).trace.re ≤
      ∑ M : ImmSourceIndex (d + 1) side a b,
        ∑ x : {x : Fin d → Pairings.Labels (Fin (d + 1)) // MomentPairing.Compatible 0 x},
          ∏ t : Fin (d + 1), LocalMoments.localPolynomial (side t)
            (fun y => M.1 (t, y)) (MomentPairing.layerLabels 0 x.1 t).p
              (MomentPairing.layerLabels 0 x.1 t).q
              (MomentPairing.layerLabels 0 x.1 t).r := by
  classical
  refine (immNormalizedMatrix_second_trace_le_localPolynomial_sum
    (d + 1) (Nat.succ_pos d) side a b).trans_eq ?_
  apply Finset.sum_congr rfl
  intro M hM
  have h := sum_four_immPaths_compatible_eq d side
    (fun P Q R _ => ∏ t : Fin (d + 1), LocalMoments.localPolynomial (side t)
      (fun y => M.1 (t, y)) (totalImmProfile (d + 1) P t)
        (totalImmProfile (d + 1) Q t) (totalImmProfile (d + 1) R t))
  simp only [totalImmProfile_get, totalImmProfile_internal] at h
  convert h using 1
  · rfl
  · apply Finset.sum_congr rfl
    intro x hx
    apply Finset.prod_congr rfl
    intro t ht
    rw [show x.1 = (fun i => ⟨(x.1 i).p, (x.1 i).q, (x.1 i).r, (x.1 i).s⟩) from rfl,
      layerLabels_immInternalCoordinate]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LocalMomentPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual geometric local table agrees with the canonical pairing
normalization, including coincident coordinates in the normal class. -/

noncomputable section
open scoped BigOperators

namespace Problem335.MomentPairing

open Pairings

theorem localGeometricMass_eq_moment {γ : Type*} [DecidableEq γ]
    (side : Bool) (A B : ℝ) (x : Labels γ) :
    LocalMoments.localGeometricMass side (if side then A else B) x.p x.q x.r =
      LocalMomentWeights.moment side (isDiagonal (classifyLayer x))
        (coincides x) A B := by
  classical
  cases side <;> by_cases hpq : x.p = x.q <;>
    simp [LocalMoments.localGeometricMass, LocalMoments.normalGeometricMass,
      LocalMoments.diagonalGeometricMass, LocalMomentWeights.moment,
      classifyLayer, isDiagonal, coincides, hpq]

/-- No compatibility assumption is needed for this algebraic identity: the
canonical class always chooses the normal branch precisely when `p=q`. -/
theorem prod_localGeometricMass_eq {γ : Type*} [DecidableEq γ] {L : ℕ}
    (side : Fin (L + 1) → Bool) (A B : ℝ)
    (endpoint : γ) (x : Fin L → Labels γ) :
    (∏ t, LocalMoments.localGeometricMass (side t) (if side t then A else B)
      (layerLabels endpoint x t).p (layerLabels endpoint x t).q
      (layerLabels endpoint x t).r) =
    pathGeometricMoment side A B endpoint (classifyWord endpoint x) x := by
  unfold pathGeometricMoment classifyWord
  apply Finset.prod_congr rfl
  intro t _
  exact localGeometricMass_eq_moment _ _ _ _

/-- Concrete input interface for occupation averaging: the geometric RHS is
the actual local polynomial table, rather than an assumed pairing weight. -/
theorem sum_sources_local_moments_le {ι γ : Type*} [Fintype ι]
    [Fintype γ] [DecidableEq γ] {L : ℕ}
    (side : Fin (L + 1) → Bool) {A B D : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hD : 0 ≤ D) (endpoint : γ)
    (C : ι → (Fin L → Labels γ) → ℝ)
    (hexpect : ∀ x, Compatible endpoint x →
      (∑ i, C i x) ≤ D *
        ∏ t, LocalMoments.localGeometricMass (side t) (if side t then A else B)
          (layerLabels endpoint x t).p (layerLabels endpoint x t).q
          (layerLabels endpoint x t).r) :
    (∑ i, ∑ x : {x : Fin L → Labels γ // Compatible endpoint x}, C i x.1) ≤
      D * pathMean side A B ^ 2 *
        ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
          pathWeight side (A / (A + 1)) (B / (B + 1)) endpoint τ x.1 := by
  apply sum_sources_compatible_le side hA hB hD endpoint C
  intro x hx
  simpa only [prod_localGeometricMass_eq] using hexpect x hx

end Problem335.MomentPairing

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PairingAverageCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplying a genuine normalized source average introduces exactly one
source-cardinality factor, including when the source is empty. -/
noncomputable section
open scoped BigOperators

namespace Problem335.MomentPairing
open Pairings

theorem sum_sources_local_moments_le_of_average {ι γ : Type*} [Fintype ι]
    [Fintype γ] [DecidableEq γ] {L : ℕ}
    (side : Fin (L + 1) → Bool) {A B : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (endpoint : γ)
    (C : ι → (Fin L → Labels γ) → ℝ)
    (haverage : ∀ x, Compatible endpoint x →
      (∑ i, C i x) / (Fintype.card ι : ℝ) ≤
        ∏ t, LocalMoments.localGeometricMass (side t) (if side t then A else B)
          (layerLabels endpoint x t).p (layerLabels endpoint x t).q
          (layerLabels endpoint x t).r) :
    (∑ i, ∑ x : {x : Fin L → Labels γ // Compatible endpoint x}, C i x.1) ≤
      (Fintype.card ι : ℝ) * pathMean side A B ^ 2 *
        ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
          pathWeight side (A / (A + 1)) (B / (B + 1)) endpoint τ x.1 := by
  classical
  apply sum_sources_local_moments_le side hA hB (by positivity) endpoint C
  intro x hx
  by_cases hcard : Fintype.card ι = 0
  · let : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    simp
  · have hpos : (0 : ℝ) < Fintype.card ι := by
      exact_mod_cast Nat.pos_of_ne_zero hcard
    simpa only [mul_comm] using (div_le_iff₀ hpos).mp (haverage x hx)

end Problem335.MomentPairing

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmSecondMomentParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
open Pairings MomentPairing

private theorem source_bound
    (L : ℕ) (side : Fin (L + 1) → Bool)
    [Nonempty {x : Fin (L + 1) × (Fin (L + 1) × Fin (L + 1)) // side x.1 = true}]
    [Nonempty {x : Fin (L + 1) × (Fin (L + 1) × Fin (L + 1)) // ¬ side x.1 = true}]
    (a b : ℕ) (ha : 0 < a) :
    (∑ M : ImmSourceIndex (L + 1) side a b,
      ∑ x : {x : Fin L → Labels (Fin (L + 1)) // Compatible 0 x},
        ∏ t : Fin (L + 1), LocalMoments.localPolynomial (side t)
          (fun y => M.1 (t, y)) (MomentPairing.layerLabels 0 x.1 t).p
            (MomentPairing.layerLabels 0 x.1 t).q (MomentPairing.layerLabels 0 x.1 t).r) ≤
      (Fintype.card (ImmSourceIndex (L + 1) side a b) : ℝ) *
        pathMean side (layerMeanV (Fin (L + 1)) side a)
          (layerMeanU (Fin (L + 1)) side b) ^ 2 *
        ∑ τ : Fin (L + 1) → Kind,
          ∑ x : RelaxedPaths (Fin (L + 1)) 0 τ,
            pathWeight side
              (layerMeanV (Fin (L + 1)) side a /
                (layerMeanV (Fin (L + 1)) side a + 1))
              (layerMeanU (Fin (L + 1)) side b /
                (layerMeanU (Fin (L + 1)) side b + 1)) 0 τ x.1 := by
  classical
  have hA : 0 < layerMeanV (Fin (L + 1)) side a := by
    unfold layerMeanV
    exact div_pos (by exact_mod_cast ha) (by exact_mod_cast Fintype.card_pos)
  have hB : 0 ≤ layerMeanU (Fin (L + 1)) side b := by
    unfold layerMeanU
    positivity
  apply sum_sources_local_moments_le_of_average
    (ι := ImmSourceIndex (L + 1) side a b) (γ := Fin (L + 1)) (L := L) side hA hB 0
    (fun M : ImmSourceIndex (L + 1) side a b => fun x =>
      ∏ t : Fin (L + 1), LocalMoments.localPolynomial (side t)
        (fun y => M.1 (t, y)) (MomentPairing.layerLabels 0 x t).p
          (MomentPairing.layerLabels 0 x t).q (MomentPairing.layerLabels 0 x t).r)
  intro x _
  simpa only [layerMeanV, layerMeanU] using
    LocalMoments.bidegree_average_layered_localProduct_le side a b Finset.univ
      (fun t => (MomentPairing.layerLabels 0 x t).p) (fun t => (MomentPairing.layerLabels 0 x t).q)
      (fun t => (MomentPairing.layerLabels 0 x t).r)

/-- The actual finite IMM second trace is bounded by the relaxed pairing sum,
with precisely one source dimension and the square of the path mean. -/
theorem immNormalizedMatrix_second_moment_le_relaxed
    (L : ℕ) (side : Fin (L + 1) → Bool)
    [Nonempty {x : Fin (L + 1) × (Fin (L + 1) × Fin (L + 1)) // side x.1 = true}]
    [Nonempty {x : Fin (L + 1) × (Fin (L + 1) × Fin (L + 1)) // ¬ side x.1 = true}]
    (a b : ℕ) (ha : 0 < a) :
    let A := immNormalizedMatrix (L + 1) side a b
    ((A.conjTranspose * A) ^ 2).trace.re ≤
      (Fintype.card (ImmSourceIndex (L + 1) side a b) : ℝ) *
        pathMean side (layerMeanV (Fin (L + 1)) side a)
          (layerMeanU (Fin (L + 1)) side b) ^ 2 *
        ∑ τ : Fin (L + 1) → Kind,
          ∑ x : RelaxedPaths (Fin (L + 1)) 0 τ,
            pathWeight side
              (layerMeanV (Fin (L + 1)) side a /
                (layerMeanV (Fin (L + 1)) side a + 1))
              (layerMeanU (Fin (L + 1)) side b /
                (layerMeanU (Fin (L + 1)) side b + 1)) 0 τ x.1 := by
  exact (immNormalizedMatrix_second_trace_le_compatible L side a b).trans
    (source_bound L side a b ha)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ConfiguredImmSecondMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335.LowerParameters
open MomentPairing

private theorem configured_layerMeanV {L : ℕ} (hn : 4 ≤ L + 1) :
    layerMeanV (Fin (L + 1)) (balancedLayer hn) (a (L + 1)) =
      (a (L + 1) : ℝ) / v (L + 1) := by
  unfold layerMeanV
  rw [balancedVariable_card_true hn]

private theorem configured_layerMeanU {L : ℕ} (hn : 4 ≤ L + 1) :
    layerMeanU (Fin (L + 1)) (balancedLayer hn) (b (L + 1)) =
      (b (L + 1) : ℝ) / u (L + 1) := by
  unfold layerMeanU
  simp only [Bool.not_eq_true]
  rw [balancedVariable_card_false hn]

private theorem v_fraction {n : ℕ} (hn : 4 ≤ n) :
    ((a n : ℝ) / v n) / ((a n : ℝ) / v n + 1) = alpha n := by
  have hv : (v n : ℝ) ≠ 0 := by exact_mod_cast (v_pos hn).ne'
  rw [alpha, div_add_one hv, div_div_div_cancel_right₀ hv]

private theorem u_fraction {n : ℕ} (hn : 4 ≤ n) :
    ((b n : ℝ) / u n) / ((b n : ℝ) / u n + 1) = beta n := by
  have hu : (u n : ℝ) ≠ 0 := by exact_mod_cast (u_pos hn).ne'
  rw [beta, div_add_one hu, div_div_div_cancel_right₀ hu]

/-- The complete actual second-trace estimate for the canonical parameters. -/
theorem configured_imm_second_moment_upper {n : ℕ} (hn : 16 ≤ n)
    (hbeta : beta n ≤ 2 / Real.sqrt (n : ℝ)) :
    let A := immNormalizedMatrix n (balancedLayer (show 4 ≤ n by omega)) (a n) (b n)
    ((A.conjTranspose * A) ^ 2).trace.re ≤
      rankDimension n * rankMomentScale n ^ 2 * Real.exp (10 * Real.sqrt (n : ℝ)) := by
  obtain ⟨L, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hn4 : 4 ≤ L + 1 := by omega
  let : Nonempty {x : Fin (L + 1) × (Fin (L + 1) × Fin (L + 1)) //
      balancedLayer hn4 x.1 = true} :=
    Fintype.card_pos_iff.mp (by rw [balancedVariable_card_true hn4]; exact v_pos hn4)
  let : Nonempty {x : Fin (L + 1) × (Fin (L + 1) × Fin (L + 1)) //
      ¬ balancedLayer hn4 x.1 = true} :=
    Fintype.card_pos_iff.mp (by
      simp only [Bool.not_eq_true]
      rw [balancedVariable_card_false hn4]
      exact u_pos hn4)
  have hraw := immNormalizedMatrix_second_moment_le_relaxed L
    (balancedLayer hn4) (a (L + 1)) (b (L + 1)) (a_pos hn4)
  dsimp only at hraw ⊢
  rw [configured_layerMeanV hn4, configured_layerMeanU hn4,
    v_fraction hn4, u_fraction hn4, card_immSourceIndex_eq_rankDimension hn4] at hraw
  apply configured_second_bound_of_path_bound hn hbeta _
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (sum_relaxed_pathWeight_balanced_le_exp hn (0 : Fin (L + 1)))
    (mul_nonneg (rankDimension_nonneg _) (sq_nonneg _)))

/-- A single eventual statement supplies the actual matrix premise required
by the final rank and circuit-size comparison. -/
theorem eventually_configured_imm_second_moment_upper :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ hn : 16 ≤ n,
      let A := immNormalizedMatrix n (balancedLayer (show 4 ≤ n by omega)) (a n) (b n)
      ((A.conjTranspose * A) ^ 2).trace.re ≤
        rankDimension n * rankMomentScale n ^ 2 * Real.exp (10 * Real.sqrt (n : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_second_moment_parameter_cutoff
  filter_upwards [Filter.eventually_ge_atTop N] with n hn hn16
  exact configured_imm_second_moment_upper hn16 (hN n hn).2.1

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CeilArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem335

theorem sqrt_le_ceilSqrt (n : ℕ) : Nat.sqrt n ≤ ceilSqrt n := by
  unfold ceilSqrt
  omega

theorem ceilSqrt_le_sqrt_add_one (n : ℕ) : ceilSqrt n ≤ Nat.sqrt n + 1 := by
  unfold ceilSqrt
  split <;> omega

theorem self_le_ceilSqrt_sq (n : ℕ) : n ≤ ceilSqrt n ^ 2 := by
  unfold ceilSqrt
  split
  · rename_i h
    simpa using h.ge
  · simpa [Nat.succ_eq_add_one] using (Nat.lt_succ_sqrt' n).le

theorem ceilSqrt_pos {n : ℕ} (hn : 0 < n) : 0 < ceilSqrt n :=
  lt_of_lt_of_le (Nat.sqrt_pos.mpr hn) (sqrt_le_ceilSqrt n)

theorem ceilSqrt_le_self (n : ℕ) : ceilSqrt n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  by_cases h : n = 1
  · subst n
    simp
  have hn' : 1 < n := by omega
  exact (ceilSqrt_le_sqrt_add_one n).trans (Nat.succ_le_of_lt (Nat.sqrt_lt_self hn'))

theorem two_le_ceilSqrt {n : ℕ} (hn : 2 ≤ n) : 2 ≤ ceilSqrt n := by
  have h := self_le_ceilSqrt_sq n
  by_contra hh
  have hh' : ceilSqrt n ≤ 1 := by omega
  have : ceilSqrt n ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left hh' 2
  omega

theorem ceilSqrt_cast_le_real_sqrt_add_one (n : ℕ) :
    (ceilSqrt n : ℝ) ≤ Real.sqrt (n : ℝ) + 1 := by
  have hnat : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' n
  have hceil : (ceilSqrt n : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by
    exact_mod_cast ceilSqrt_le_sqrt_add_one n
  linarith

theorem ceilDiv_le_iff {n t r : ℕ} (ht : 0 < t) :
    ceilDiv n t ≤ r ↔ n ≤ r * t := by
  unfold ceilDiv
  rw [Nat.div_le_iff_le_mul_add_pred ht]
  rw [Nat.mul_comm t r]
  omega

theorem ceilDiv_pos {n t : ℕ} (hn : 0 < n) (ht : 0 < t) :
    0 < ceilDiv n t := by
  by_contra h
  have hh : ceilDiv n t ≤ 0 := by omega
  have := (ceilDiv_le_iff ht).mp hh
  omega

theorem ceilDiv_ceilSqrt_le (n : ℕ) : ceilDiv n (ceilSqrt n) ≤ ceilSqrt n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ceilDiv]
  apply (ceilDiv_le_iff (ceilSqrt_pos hn)).mpr
  simpa [pow_two] using self_le_ceilSqrt_sq n

end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.UpperBoundArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem335

/-- The elementary gate-count estimate, before specializing the block parameters. -/
theorem gateCount_le_pow (n t r : ℕ) (hn : 3 ≤ n)
    (ht : 2 ≤ t) (hr : r ≤ t) (htn : t ≤ n) :
    2 * n ^ 3 + r * n ^ 2 + r * n ^ (t + 1) + n ^ (r - 1) + 1 ≤
      n ^ (t + 3) := by
  have hn0 : 0 < n := by omega
  have hrn : r ≤ n := hr.trans htn
  have hfirst : 2 * n ^ 3 + r * n ^ 2 ≤ 3 * n ^ 3 := by
    have h := Nat.mul_le_mul_right (n ^ 2) hrn
    nlinarith [pow_succ n 2]
  have hsecond : r * n ^ (t + 1) ≤ n ^ (t + 2) := by
    calc
      r * n ^ (t + 1) ≤ n * n ^ (t + 1) :=
        Nat.mul_le_mul_right _ hrn
      _ = n ^ (t + 2) := by simp [pow_add]; ring
  have hthird : n ^ (r - 1) ≤ n ^ (t - 1) :=
    Nat.pow_le_pow_right hn0 (Nat.sub_le_sub_right hr 1)
  have hsmall : 3 * n ^ 3 ≤ n ^ (t + 2) := by
    calc
      3 * n ^ 3 ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hn
      _ = n ^ 4 := by ring
      _ ≤ n ^ (t + 2) := Nat.pow_le_pow_right hn0 (by omega)
  have htail : n ^ (t - 1) + 1 ≤ n ^ (t + 2) := by
    have h := Nat.pow_lt_pow_right (by omega : 1 < n) (show t - 1 < t + 2 by omega)
    omega
  have htotal :
      2 * n ^ 3 + r * n ^ 2 + r * n ^ (t + 1) + n ^ (r - 1) + 1 ≤
        3 * n ^ (t + 2) := by omega
  calc
    _ ≤ 3 * n ^ (t + 2) := htotal
    _ ≤ n * n ^ (t + 2) := Nat.mul_le_mul_right _ hn
    _ = n ^ (t + 3) := by simp [pow_add]; ring

/-- Conversion of the integer block gate count into the advertised real-power bound. -/
theorem gateCount_le_rpow (n t r : ℕ) (hn : 3 ≤ n)
    (ht : 2 ≤ t) (hr : r ≤ t) (htn : t ≤ n)
    (htsqrt : (t : ℝ) ≤ Real.sqrt (n : ℝ) + 1) :
    ((2 * n ^ 3 + r * n ^ 2 + r * n ^ (t + 1) + n ^ (r - 1) + 1 : ℕ) : ℝ) ≤
      (n : ℝ) ^ (Real.sqrt (n : ℝ) + 4) := by
  calc
    _ ≤ ((n ^ (t + 3) : ℕ) : ℝ) := by
      exact_mod_cast gateCount_le_pow n t r hn ht hr htn
    _ = (n : ℝ) ^ ((t + 3 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_cast
    _ ≤ (n : ℝ) ^ (Real.sqrt (n : ℝ) + 4) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (show 1 ≤ n by omega)
      · push_cast
        linarith

/-- The exceptional smallest size in the upper-bound estimate. -/
theorem upperGateBound_two_le_rpow :
    (upperGateBound 2 : ℝ) ≤ (2 : ℝ) ^ (Real.sqrt 2 + 4) := by
  have hcount : upperGateBound 2 = 30 := by
    norm_num [upperGateBound, ceilSqrt, ceilDiv, Nat.sqrt_two]
  rw [hcount]
  calc
    (30 : ℝ) ≤ (2 : ℝ) ^ (5 : ℕ) := by norm_num
    _ = (2 : ℝ) ^ (5 : ℝ) := (Real.rpow_natCast 2 5).symm
    _ ≤ (2 : ℝ) ^ (Real.sqrt 2 + 4) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
      linarith

/-- The explicit gate bound is at most `n^(sqrt n + 4)`. -/
theorem upperGateBound_le_rpow (n : ℕ) (hn : 2 ≤ n) :
    (upperGateBound n : ℝ) ≤ (n : ℝ) ^ (Real.sqrt (n : ℝ) + 4) := by
  rcases eq_or_lt_of_le hn with rfl | hn
  · exact upperGateBound_two_le_rpow
  · exact gateCount_le_rpow n (ceilSqrt n) (ceilDiv n (ceilSqrt n))
      (by omega) (two_le_ceilSqrt (by omega)) (ceilDiv_ceilSqrt_le n)
      (ceilSqrt_le_self n) (ceilSqrt_cast_le_real_sqrt_add_one n)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.UpperConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

@[simp] theorem immUpperCircuit_outputDegree (K : Type*) [CommSemiring K]
    (n : ℕ) (hn : 0 < n) : (immUpperCircuit K n hn).outputDegree = n := by
  simp [immUpperCircuit]

theorem immUpperCircuit_size (K : Type*) [CommSemiring K]
    (n : ℕ) (hn : 0 < n) : circuitSize (immUpperCircuit K n hn) ≤ upperGateBound n := by
  have ht : 0 < ceilSqrt n := ceilSqrt_pos hn
  have hb : layerBlocks n (ceilSqrt n) ≠ [] := by
    intro h
    have hlen := layerBlocks_length (n := n) ht
    rw [h, List.length_nil] at hlen
    have hp := ceilDiv_pos hn ht
    omega
  have hne : ∀ b : Fin (layerBlocks n (ceilSqrt n)).length,
      (layerBlocks n (ceilSqrt n)).get b ≠ [] := by
    intro b
    exact layerBlocks_nonempty ht (List.get_mem ..)
  have hlower := BlockData.card_lower_le (layerBlocks n (ceilSqrt n))
    (ceilSqrt n) hn hne (layerBlocks_get_length_le ht)
  have hlen := layerBlocks_length (n := n) ht
  rw [immUpperCircuit, BlockData.circuit_size, BlockData.card_middle,
    BlockData.card_upper _ hb]
  calc
    _ ≤ 2 * n ^ 3 + (layerBlocks n (ceilSqrt n)).length * n ^ (ceilSqrt n + 1) +
        (layerBlocks n (ceilSqrt n)).length * n ^ 2 +
        n ^ ((layerBlocks n (ceilSqrt n)).length - 1) + 1 := by omega
    _ = upperGateBound n := by
      rw [hlen]
      simp only [upperGateBound]
      omega

@[simp] theorem immUpperCircuit_value (K : Type*) [CommSemiring K]
    (n : ℕ) (hn : 0 < n) : circuitValue (immUpperCircuit K n hn) = imm K n := by
  exact BlockData.circuit_value_eq_imm K hn (layerBlocks n (ceilSqrt n))
    (layerBlocks_flatten n (ceilSqrt n))

/-- A homogeneous depth-five circuit attaining the explicit block-expansion gate budget. -/
theorem exists_imm_circuit_le_upperGateBound (K : Type*) [CommSemiring K]
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ c : Depth5Circuit K n, circuitValue c = imm K n ∧ circuitSize c ≤ upperGateBound n := by
  have hn0 : 0 < n := by omega
  exact ⟨immUpperCircuit K n hn0, immUpperCircuit_value K n hn0,
    immUpperCircuit_size K n hn0⟩

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u

namespace Problem335

theorem complex_depth_five_lower_bound :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ c : Depth5Circuit ℂ n, circuitValue c = imm ℂ n → (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤ (circuitSize c : ℝ) := by
  exact complex_depth_five_lower_bound_of_eventual_second_trace 10
    LowerParameters.eventually_configured_imm_second_moment_upper

theorem characteristic_zero_depth_five_lower_bound :
    ∃ n0 : ℕ, ∀ (K : Type u) [Field K] [CharZero K], ∀ n : ℕ, n0 ≤ n → ∀ c : Depth5Circuit K n, circuitValue c = imm K n → (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤ (circuitSize c : ℝ) := by
  exact characteristic_zero_depth_five_lower_bound_of_complex complex_depth_five_lower_bound

theorem all_field_depth_five_upper_bound :
    ∀ (K : Type u) [Field K] (n : ℕ), 2 ≤ n → ∃ c : Depth5Circuit K n, circuitValue c = imm K n ∧ circuitSize c ≤ upperGateBound n ∧ (upperGateBound n : ℝ) ≤ (n : ℝ) ^ (Real.sqrt (n : ℝ) + 4) := by
  intro K _ n hn
  obtain ⟨c, hc, hs⟩ := exists_imm_circuit_le_upperGateBound K n hn
  exact ⟨c, hc, hs, upperGateBound_le_rpow n hn⟩

theorem main_oai :
    (∃ threshold : ℕ, ∀ size : ℕ, threshold ≤ size →
      ∀ circuit : Depth5Circuit ℂ size, circuitValue circuit = imm ℂ size →
        (size : ℝ) ^ (Real.sqrt (size : ℝ) / 400) ≤ (circuitSize circuit : ℝ)) ∧
    (∃ threshold : ℕ, ∀ (FieldType : Type u) [Field FieldType] [CharZero FieldType],
      ∀ size : ℕ, threshold ≤ size → ∀ circuit : Depth5Circuit FieldType size,
        circuitValue circuit = imm FieldType size →
          (size : ℝ) ^ (Real.sqrt (size : ℝ) / 400) ≤ (circuitSize circuit : ℝ)) ∧
    (∀ (FieldType : Type u) [Field FieldType] (size : ℕ), 2 ≤ size →
      ∃ circuit : Depth5Circuit FieldType size, circuitValue circuit = imm FieldType size ∧
        circuitSize circuit ≤ upperGateBound size ∧
        (upperGateBound size : ℝ) ≤ (size : ℝ) ^ (Real.sqrt (size : ℝ) + 4)) := by
  exact ⟨complex_depth_five_lower_bound,
    characteristic_zero_depth_five_lower_bound, all_field_depth_five_upper_bound⟩

end Problem335

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Problem335.main_oai.{u} := @OAI.Problem335.main_oai.{u}
