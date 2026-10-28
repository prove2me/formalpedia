-- Prove2me | solution 1 for MatrixAnalytic.SkipFree.stationary_embedded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:45:41.761384+00:00
-- url     : https://prove2.me/submissions/b39c6948-147b-4bae-83bd-7e52db75c470

import Mathlib
import Definitions.Def_MatrixAnalytic_SkipFree_Chain
import Definitions.Def_MatrixAnalytic_SkipFree_QBD
import Definitions.Def_MatrixAnalytic_SkipFree_Passage
import Definitions.Def_MatrixAnalytic_SkipFree_Models

open scoped ENNReal
open MatrixAnalytic.SkipFree

namespace S203SE

section Gen
set_option linter.unusedSectionVars false
variable {V : Type*} [Countable V] [DecidableEq V]

lemma stepPow_nonneg (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) :
    ∀ t x y, 0 ≤ stepPow P t x y := by
  intro t
  induction t with
  | zero => intro x y; simp only [stepPow]; split_ifs <;> norm_num
  | succ t ih =>
    intro x y; simp only [stepPow]
    exact tsum_nonneg fun z => mul_nonneg (ih x z) (hP z y)

lemma super_prop (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (m : V → ℝ) (hm0 : ∀ x, 0 ≤ m x)
    (hs : ∀ y, Summable fun x => m x * P x y) (hle : ∀ y, ∑' x, m x * P x y ≤ m y) :
    ∀ t x y, m x * stepPow P t x y ≤ m y := by
  intro t
  induction t with
  | zero => intro x y; simp only [stepPow]; split_ifs with h
            · subst h; simp
            · simpa using hm0 y
  | succ t ih =>
    intro x y; simp only [stepPow]
    by_cases hsum : Summable fun z => stepPow P t x z * P z y
    · rw [← tsum_mul_left]
      refine le_trans ?_ (hle y)
      refine (hsum.mul_left (m x)).tsum_le_tsum (fun z => ?_) (hs y)
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (ih x z) (hP z y)
    · rw [tsum_eq_zero_of_not_summable hsum]; simpa using hm0 y

lemma zero_prop (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hirr : IrreducibleC P)
    (m : V → ℝ) (hm0 : ∀ x, 0 ≤ m x)
    (hs : ∀ y, Summable fun x => m x * P x y) (hle : ∀ y, ∑' x, m x * P x y ≤ m y)
    (k : V) (hk : m k = 0) : ∀ x, m x = 0 := by
  intro x
  obtain ⟨t, ht⟩ := hirr x k
  have := super_prop P hP m hm0 hs hle t x k
  rw [hk] at this
  have h2 : m x * stepPow P t x k = 0 := le_antisymm this (mul_nonneg (hm0 x) ht.le)
  rcases mul_eq_zero.mp h2 with h | h
  · exact h
  · exact absurd h ht.ne'

lemma uniq (P : V → V → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (πt : V → ℝ) (hπt : IsStationaryC P πt) (μ : V → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ : ∀ y, HasSum (fun x => μ x * P x y) (μ y)) (k : V) (hk : μ k ≠ 0) :
    ∃ c : ℝ, ∀ y, πt y = c * μ y := by
  obtain ⟨hπ0, hπ1, hπ⟩ := hπt
  have hP0 := hP.1
  set a := πt k / μ k with ha
  have ha0 : 0 ≤ a := div_nonneg (hπ0 k) (hμ0 k)
  set ν : V → ℝ := fun x => min (πt x) (a * μ x) with hν
  have hν0 : ∀ x, 0 ≤ ν x := fun x => le_min (hπ0 x) (mul_nonneg ha0 (hμ0 x))
  have hνk : ν k = πt k := by
    simp only [hν, ha, div_mul_cancel₀ _ hk, min_self]
  have hνs : ∀ y, Summable fun x => ν x * P x y := fun y =>
    Summable.of_nonneg_of_le (fun x => mul_nonneg (hν0 x) (hP0 x y))
      (fun x => mul_le_mul_of_nonneg_right (min_le_left _ _) (hP0 x y)) (hπ y).summable
  have hνle : ∀ y, ∑' x, ν x * P x y ≤ ν y := by
    intro y
    refine le_min ?_ ?_
    · rw [← (hπ y).tsum_eq]
      exact (hνs y).tsum_le_tsum (fun x => mul_le_mul_of_nonneg_right (min_le_left _ _) (hP0 x y))
        (hπ y).summable
    · rw [← ((hμ y).mul_left a).tsum_eq]
      refine (hνs y).tsum_le_tsum (fun x => ?_) ((hμ y).mul_left a).summable
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (min_le_right _ _) (hP0 x y)
  have hνsum : Summable ν := Summable.of_nonneg_of_le hν0 (fun x => min_le_left _ _) hπ1.summable
  -- mass conservation
  have hrow : ∀ x, HasSum (fun y => ν x * P x y) (ν x) := fun x => by
    simpa using (hP.2 x).mul_left (ν x)
  have hprod : Summable (Function.uncurry fun x y => ν x * P x y) := by
    refine (summable_prod_of_nonneg (f := fun p : V × V => ν p.1 * P p.1 p.2)
      (fun p => mul_nonneg (hν0 p.1) (hP0 p.1 p.2))).mpr ⟨fun x => (hrow x).summable, ?_⟩
    exact hνsum.congr fun x => (hrow x).tsum_eq.symm
  have hmass : ∑' y, ∑' x, ν x * P x y = ∑' x, ν x := by
    rw [hprod.tsum_comm' (fun x => (hrow x).summable) hνs]
    exact tsum_congr fun x => (hrow x).tsum_eq
  have hνPs : Summable fun y => ∑' x, ν x * P x y :=
    Summable.of_nonneg_of_le (fun y => tsum_nonneg fun x => mul_nonneg (hν0 x) (hP0 x y)) hνle hνsum
  have hdiff : HasSum (fun y => ν y - ∑' x, ν x * P x y) 0 := by
    have := hνsum.hasSum.sub hνPs.hasSum
    rwa [hmass, sub_self] at this
  have hzero := (hasSum_zero_iff_of_nonneg (fun y => sub_nonneg.mpr (hνle y))).mp hdiff
  have hνinv : ∀ y, HasSum (fun x => ν x * P x y) (ν y) := fun y => by
    have := congrFun hzero y
    simp only [Pi.zero_apply, sub_eq_zero] at this
    rw [this]; exact (hνs y).hasSum
  -- πt - ν is invariant, zero at k
  have h1 : ∀ x, πt x - ν x = 0 := by
    refine zero_prop P hP0 hirr (fun x => πt x - ν x) (fun x => sub_nonneg.mpr (min_le_left _ _))
      (fun y => ?_) (fun y => ?_) k (by rw [hνk, sub_self])
    · exact ((hπ y).sub (hνinv y)).summable.congr fun x => by ring
    · rw [show (fun x => (πt x - ν x) * P x y) = fun x => πt x * P x y - ν x * P x y from
        funext fun x => by ring]
      rw [((hπ y).sub (hνinv y)).tsum_eq]
  have h2 : ∀ x, a * μ x - ν x = 0 := by
    refine zero_prop P hP0 hirr (fun x => a * μ x - ν x) (fun x => sub_nonneg.mpr (min_le_right _ _))
      (fun y => ?_) (fun y => ?_) k (by rw [hνk, ha, div_mul_cancel₀ _ hk, sub_self])
    · exact (((hμ y).mul_left a).sub (hνinv y)).summable.congr fun x => by ring
    · rw [show (fun x => (a * μ x - ν x) * P x y) = fun x => a * (μ x * P x y) - ν x * P x y from
        funext fun x => by ring]
      rw [(((hμ y).mul_left a).sub (hνinv y)).tsum_eq]
  exact ⟨a, fun y => by linarith [h1 y, h2 y]⟩

end Gen

section QBD
variable {ι : Type*} [DecidableEq ι] (D C : ℕ → ι → ι → ℝ)

lemma qbd_pos (x y : ℕ × (ℕ × ι)) (hx : x.2.1 ≠ 0) :
    mg1QBD D C x y = if x = (y.1 - 1, (y.2.1 + 1, y.2.2)) ∧ 1 ≤ y.1 then 1 else 0 := by
  obtain ⟨n, d, i⟩ := x
  obtain ⟨m, e, j⟩ := y
  simp only at hx
  simp only [mg1QBD, qbdP, augB, augA0, augA1, augA2, Prod.mk.injEq, hx, if_false]
  by_cases hij : i = j
  · subst hij; simp only [and_true, false_and, if_false]; split_ifs <;> first | rfl | (exfalso; omega)
  · simp only [hij, and_false, false_and, if_false]; split_ifs <;> rfl

lemma qbd_zero (n i m d j) :
    mg1QBD D C (n, (0, i)) (m, (d, j)) =
      if n = 0 then (if m = 0 then D d i j else 0)
      else (if m = n then C (d + 1) i j else if m + 1 = n ∧ d = 0 then C 0 i j else 0) := by
  simp only [mg1QBD, qbdP, augB, augA0, augA1, augA2, if_true, true_and]
  by_cases hn : n = 0
  · subst hn
    by_cases hm : m = 0
    · simp [hm]
    · simp [hm]
  · simp only [hn, if_false]
    by_cases h1 : m = n + 1
    · simp only [h1, if_true]; rw [if_neg (fun h => absurd h.1 (by omega)), if_neg (show ¬ n + 1 = n by omega), if_neg (show ¬(n + 1 + 1 = n ∧ d = 0) by omega)]
    · simp only [h1, if_false]
      by_cases h2 : m = n
      · simp [h2]
      · simp only [h2, if_false]
        by_cases h3 : m + 1 = n
        · by_cases hd : d = 0 <;> simp [h3, hd]
        · simp [h3]

variable (π : ℕ × (ℕ × ι) → ℝ)

lemma split (hπ : IsStationaryC (mg1QBD D C) π) (y : ℕ × (ℕ × ι)) :
    HasSum (fun p : ℕ × ι => π (p.1, (0, p.2)) * mg1QBD D C (p.1, (0, p.2)) y)
      (π y - if 1 ≤ y.1 then π (y.1 - 1, (y.2.1 + 1, y.2.2)) else 0) := by
  classical
  set y' : ℕ × (ℕ × ι) := (y.1 - 1, (y.2.1 + 1, y.2.2))
  have hH : HasSum (fun x => if x.2.1 = 0 then 0 else π x * mg1QBD D C x y)
      (if 1 ≤ y.1 then π y' else 0) := by
    have e : (fun x : ℕ × (ℕ × ι) => if x.2.1 = 0 then 0 else π x * mg1QBD D C x y) =
        fun x => if x = y' then (if 1 ≤ y.1 then π y' else 0) else 0 := by
      funext x
      by_cases hx : x.2.1 = 0
      · have : x ≠ y' := by rintro rfl; simp [y'] at hx
        simp [hx, this]
      · rw [if_neg hx, qbd_pos D C x y hx]
        by_cases hxy : x = y'
        · rw [hxy]; simp [y']
        · have : ¬ (x = (y.1 - 1, (y.2.1 + 1, y.2.2)) ∧ 1 ≤ y.1) := fun h => hxy h.1
          simp [hxy, this]
    rw [e]; exact hasSum_ite_eq _ _
  have hG : HasSum (fun x => if x.2.1 = 0 then π x * mg1QBD D C x y else 0)
      (π y - if 1 ≤ y.1 then π y' else 0) := by
    have := (hπ.2.2 y).sub hH
    refine this.congr_fun fun x => ?_
    split_ifs <;> simp
  rw [← (Function.Injective.hasSum_iff (g := fun p : ℕ × ι => (p.1, (0, p.2)))
    (fun p q h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 h.2.2)
    (fun x hx => ?_))] at hG
  · exact hG.congr_fun fun p => by simp
  · have : x.2.1 ≠ 0 := by
      intro h0; apply hx; exact ⟨(x.1, x.2.2), by obtain ⟨a, b, c⟩ := x; simp_all⟩
    simp [this]

lemma unroll (hπ : IsStationaryC (mg1QBD D C) π) : ∀ m d j,
    HasSum (fun p : ℕ × ι => π (p.1, (0, p.2)) *
      ∑ s ∈ Finset.range (m + 1), mg1QBD D C (p.1, (0, p.2)) (m - s, (d + s, j))) (π (m, (d, j))) := by
  intro m
  induction m with
  | zero =>
    intro d j
    simpa using split D C π hπ (0, (d, j))
  | succ m ih =>
    intro d j
    have h1 := split D C π hπ (m + 1, (d, j))
    have h2 := ih (d + 1) j
    simp only [show 1 ≤ m + 1 from by omega, if_true, Nat.add_sub_cancel] at h1
    have h3 := h1.add h2
    rw [sub_add_cancel] at h3
    refine h3.congr_fun fun p => ?_
    rw [← mul_add, Finset.sum_range_succ' _ (m + 1)]
    simp only [Nat.sub_zero, add_zero, Nat.add_sub_add_right]
    rw [add_comm]
    congr 2
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [show d + (s + 1) = d + 1 + s by omega]

lemma sum_eq (n : ℕ) (i : ι) (m : ℕ) (j : ι) :
    ∑ s ∈ Finset.range (m + 1), mg1QBD D C (n, (0, i)) (m - s, (0 + s, j)) =
      mg1P D C (n, i) (m, j) := by
  simp only [qbd_zero, zero_add, mg1P]
  by_cases hn : n = 0
  · subst hn
    simp only [if_true]
    rw [Finset.sum_eq_single m]
    · simp
    · intro s hs hsm
      rw [if_neg (by simp at hs; omega)]
    · intro h; simp at h
  · simp only [hn, if_false]
    by_cases h1 : n ≤ m
    · rw [Finset.sum_eq_single (m - n)]
      · rw [if_pos (by omega), if_pos (by omega), show m - n + 1 = m + 1 - n by omega]
      · intro s hs hsm
        rw [if_neg (by omega), if_neg (by omega)]
      · intro h; simp only [Finset.mem_range] at h; omega
    · by_cases h2 : n = m + 1
      · rw [Finset.sum_eq_single 0]
        · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), show m + 1 - n = 0 by omega]
        · intro s hs hsm
          rw [if_neg (by omega), if_neg (by omega)]
        · intro h; simp at h
      · rw [if_neg (by omega)]
        refine Finset.sum_eq_zero fun s hs => ?_
        rw [if_neg (by omega), if_neg (by omega)]

end QBD
end S203SE

open MatrixAnalytic.SkipFree

theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (D C : ℕ → ι → ι → ℝ) (πt : ℕ × ι → ℝ) (π : ℕ × (ℕ × ι) → ℝ)
    (hP : IsStochasticC (mg1P D C))
    (hirr : IrreducibleC (mg1P D C))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (mg1P D C) x)
    (hπt : IsStationaryC (mg1P D C) πt)
    (hπ : IsStationaryC (mg1QBD D C) π) :
    ∃ c : ℝ, ∀ (n : ℕ) (j : ι), πt (n, j) = c * π (n, (0, j)) := by
  have hU := S203SE.unroll D C π hπ
  have hinv : ∀ y : ℕ × ι, HasSum (fun x => π (x.1, (0, x.2)) * mg1P D C x y) (π (y.1, (0, y.2))) := by
    intro y
    refine (hU y.1 0 y.2).congr_fun fun p => ?_
    rw [S203SE.sum_eq]
  have hne : ∃ k : ℕ × ι, π (k.1, (0, k.2)) ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : ∀ z, π z = 0 := by
      rintro ⟨m, d, j⟩
      refine ((hU m d j).unique ?_)
      simp [h]
    have := hπ.2.1
    rw [show π = fun _ => 0 from funext h0] at this
    exact one_ne_zero (this.unique hasSum_zero)
  obtain ⟨k, hk⟩ := hne
  obtain ⟨c, hc⟩ := S203SE.uniq (mg1P D C) hP hirr πt hπt (fun x => π (x.1, (0, x.2)))
    (fun x => hπ.1 _) hinv k hk
  exact ⟨c, fun n j => hc (n, j)⟩
