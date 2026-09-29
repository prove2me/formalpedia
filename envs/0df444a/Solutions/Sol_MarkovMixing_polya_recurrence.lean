-- Prove2me | solution 1 for MarkovMixing.polya_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T09:07:11.497611+00:00
-- url     : https://prove2.me/submissions/8b5f7d97-cd15-4994-b867-3c39d1b30b92

import Definitions.Def_mm_countable
import Theorems.Thm_MarkovMixing_recurrence_dichotomy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Pólya's theorem (LPW §21.2)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

section Steps

variable {d : ℕ}

/-- The displacement of a single step: `±e_j`. -/
private def stepv (d : ℕ) (e : Fin d × Bool) : Fin d → ℤ :=
  fun i => if i = e.1 then (if e.2 then 1 else -1) else 0

private lemma stepv_inj (d : ℕ) : Function.Injective (stepv d) := by
  rintro ⟨j, b⟩ ⟨j', b'⟩ h
  have hj := congrFun h j
  simp only [stepv, if_pos rfl] at hj
  by_cases hjj : j = j'
  · subst hjj
    rw [if_pos rfl] at hj
    by_cases hb : b
    · rw [if_pos hb] at hj
      by_cases hb' : b'
      · rw [hb, hb']
      · rw [if_neg hb'] at hj; omega
    · rw [if_neg hb] at hj
      by_cases hb' : b'
      · rw [if_pos hb'] at hj; omega
      · simp only [Bool.not_eq_true] at hb hb'
        rw [hb, hb']
  · rw [if_neg hjj] at hj
    cases b <;> simp at hj

/-- The endpoint of a walk given its step sequence. -/
private def walkEnd (d : ℕ) {t : ℕ} (w : Fin t → Fin d × Bool) : Fin d → ℤ :=
  fun i => ∑ s : Fin t, stepv d (w s) i

private lemma srw_apply (d : ℕ) (x y : Fin d → ℤ) :
    srwZ d x y = if ∃ e : Fin d × Bool, y = x + stepv d e then ((2 * d : ℕ) : ℝ)⁻¹ else 0 := by
  have hiff : (∃ j : Fin d, (∀ i : Fin d, i ≠ j → y i = x i) ∧ (y j = x j + 1 ∨ y j = x j - 1))
      ↔ ∃ e : Fin d × Bool, y = x + stepv d e := by
    constructor
    · rintro ⟨j, hoff, hj⟩
      rcases hj with h | h
      · refine ⟨(j, true), ?_⟩
        funext i
        by_cases hij : i = j
        · subst hij
          simp only [Pi.add_apply, stepv, if_pos rfl, if_true]
          exact h
        · simp only [Pi.add_apply, stepv, if_neg hij, add_zero]
          exact hoff i hij
      · refine ⟨(j, false), ?_⟩
        funext i
        by_cases hij : i = j
        · subst hij
          simp only [Pi.add_apply, stepv]
          norm_num
          rw [h]
          ring
        · simp only [Pi.add_apply, stepv, if_neg hij, add_zero]
          exact hoff i hij
    · rintro ⟨⟨j, b⟩, rfl⟩
      refine ⟨j, ?_, ?_⟩
      · intro i hij
        simp only [Pi.add_apply, stepv, if_neg hij, add_zero]
      · simp only [Pi.add_apply, stepv, if_pos rfl]
        cases b
        · right; simp; ring
        · left; simp
  rw [srwZ]
  by_cases h : ∃ e : Fin d × Bool, y = x + stepv d e
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]

end Steps

/-! ### `stepPow` as a normalized count of step sequences -/

section Counting

variable {d : ℕ}

private lemma sum_div_const {ι : Type*} (s : Finset ι) (f : ι → ℝ) (c : ℝ) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c := by
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]

private def cnt (d : ℕ) (t : ℕ) (x y : Fin d → ℤ) : ℕ :=
  (Finset.univ.filter fun w : Fin t → Fin d × Bool => x + walkEnd d w = y).card

private lemma walkEnd_snoc (d t : ℕ) (w : Fin (t + 1) → Fin d × Bool) :
    walkEnd d w = walkEnd d (Fin.init w) + stepv d (w (Fin.last t)) := by
  funext j
  simp only [walkEnd, Pi.add_apply, Fin.init]
  exact Fin.sum_univ_castSucc (fun s : Fin (t + 1) => stepv d (w s) j)

private lemma cnt_succ (d t : ℕ) (x y : Fin d → ℤ) :
    cnt d (t + 1) x y = ∑ e : Fin d × Bool, cnt d t x (y - stepv d e) := by
  classical
  have hbij : cnt d (t + 1) x y
      = (Finset.univ.filter fun p : (Fin t → Fin d × Bool) × (Fin d × Bool) =>
          x + walkEnd d p.1 = y - stepv d p.2).card := by
    rw [cnt]
    refine Finset.card_nbij' (fun w => (Fin.init w, w (Fin.last t)))
      (fun p => Fin.snoc p.1 p.2) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hw ⊢
      rw [walkEnd_snoc] at hw
      have : x + walkEnd d (Fin.init w) + stepv d (w (Fin.last t)) = y := by
        rw [← hw]; abel
      rw [← this]; abel
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hp ⊢
      rw [walkEnd_snoc, Fin.init_snoc, Fin.snoc_last, ← add_assoc, hp]
      abel
    · intro w _
      exact Fin.snoc_init_self w
    · intro p _
      simp only [Fin.init_snoc, Fin.snoc_last]
  rw [hbij, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [cnt, Finset.card_filter]

private lemma cnt_zero (d : ℕ) (x y : Fin d → ℤ) :
    cnt d 0 x y = if x = y then 1 else 0 := by
  classical
  rw [cnt]
  have hw : ∀ w : Fin 0 → Fin d × Bool, walkEnd d w = 0 := by
    intro w; funext j; simp [walkEnd]
  by_cases h : x = y
  · rw [if_pos h]
    have : (Finset.univ.filter fun w : Fin 0 → Fin d × Bool => x + walkEnd d w = y)
        = Finset.univ := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true, hw w, add_zero]
      exact h
    rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero]
  · rw [if_neg h]
    refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_)
    intro w _
    rw [hw w, add_zero]
    exact h

private lemma srw_nonneg (d : ℕ) (x y : Fin d → ℤ) : 0 ≤ srwZ d x y := by
  rw [srw_apply]
  split_ifs
  · positivity
  · exact le_refl 0

private lemma stepPow_eq (d : ℕ) (hd : 0 < d) :
    ∀ (t : ℕ) (x y : Fin d → ℤ),
      stepPow (srwZ d) t x y = (cnt d t x y : ℝ) / ((2 * d : ℕ) : ℝ) ^ t := by
  classical
  have hden : ((2 * d : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  intro t
  induction t with
  | zero =>
      intro x y
      show (if y = x then (1:ℝ) else 0) = (cnt d 0 x y : ℝ) / ((2 * d : ℕ) : ℝ) ^ 0
      rw [cnt_zero, pow_zero, div_one]
      by_cases h : y = x
      · rw [if_pos h, if_pos h.symm]; norm_num
      · rw [if_neg h, if_neg (fun hc => h hc.symm)]; norm_num
  | succ t ih =>
      intro x y
      have hsupp : ∀ z : Fin d → ℤ,
          z ∉ Finset.univ.image (fun e : Fin d × Bool => y - stepv d e) →
          stepPow (srwZ d) t x z * srwZ d z y = 0 := by
        intro z hz
        rw [srw_apply, if_neg, mul_zero]
        rintro ⟨e, he⟩
        refine hz (Finset.mem_image.mpr ⟨e, Finset.mem_univ e, ?_⟩)
        rw [he]; abel
      have hts : ∑' z : Fin d → ℤ, stepPow (srwZ d) t x z * srwZ d z y
          = ∑ z ∈ Finset.univ.image (fun e : Fin d × Bool => y - stepv d e),
              stepPow (srwZ d) t x z * srwZ d z y :=
        tsum_eq_sum (fun z hz => hsupp z hz)
      have hinj : ∀ a ∈ (Finset.univ : Finset (Fin d × Bool)),
          ∀ b ∈ (Finset.univ : Finset (Fin d × Bool)),
          y - stepv d a = y - stepv d b → a = b := by
        intro a _ b _ h
        exact stepv_inj d (by linear_combination (norm := abel) -h)
      show (∑' z : Fin d → ℤ, stepPow (srwZ d) t x z * srwZ d z y) = _
      rw [hts, Finset.sum_image hinj]
      have hval : ∀ e : Fin d × Bool,
          stepPow (srwZ d) t x (y - stepv d e) * srwZ d (y - stepv d e) y
            = (cnt d t x (y - stepv d e) : ℝ) / ((2 * d : ℕ) : ℝ) ^ t
              * ((2 * d : ℕ) : ℝ)⁻¹ := by
        intro e
        rw [ih x (y - stepv d e), srw_apply, if_pos ⟨e, by abel⟩]
      rw [Finset.sum_congr rfl (fun e _ => hval e), ← Finset.sum_mul, cnt_succ]
      push_cast
      have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [← sum_div_const, pow_succ]
      field_simp

end Counting

/-! ### The walk is a stochastic irreducible chain -/

section Chain

variable {d : ℕ}

private lemma srw_stochastic (d : ℕ) (hd : 0 < d) : IsStochasticC (srwZ d) := by
  classical
  refine ⟨srw_nonneg d, fun x => ?_⟩
  have hzero : ∀ z ∉ Finset.univ.image (fun e : Fin d × Bool => x + stepv d e),
      srwZ d x z = 0 := by
    intro z hz
    rw [srw_apply, if_neg]
    rintro ⟨e, he⟩
    exact hz (Finset.mem_image.mpr ⟨e, Finset.mem_univ e, he.symm⟩)
  have h : HasSum (srwZ d x)
      (∑ z ∈ Finset.univ.image (fun e : Fin d × Bool => x + stepv d e), srwZ d x z) :=
    hasSum_sum_of_ne_finset_zero hzero
  have hval : ∑ z ∈ Finset.univ.image (fun e : Fin d × Bool => x + stepv d e), srwZ d x z = 1 := by
    rw [Finset.sum_image (fun a _ b _ hab => stepv_inj d (by
      have := congrArg (fun v => v - x) hab
      simpa using this))]
    have : ∀ e : Fin d × Bool, srwZ d x (x + stepv d e) = ((2 * d : ℕ) : ℝ)⁻¹ := by
      intro e
      rw [srw_apply, if_pos ⟨e, rfl⟩]
    rw [Finset.sum_congr rfl (fun e _ => this e), Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
    have hne : ((2 * d : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast
    field_simp
  rw [hval] at h
  exact h

private lemma cnt_pos_of_reach (d : ℕ) : ∀ (N : ℕ) (x y : Fin d → ℤ),
    (∑ i : Fin d, (y i - x i).natAbs) = N → ∃ t : ℕ, 0 < cnt d t x y := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      intro x y hN
      by_cases hxy : x = y
      · refine ⟨0, ?_⟩
        rw [cnt_zero, if_pos hxy]
        norm_num
      · have hex : ∃ j : Fin d, y j ≠ x j := by
          by_contra hc
          push_neg at hc
          exact hxy (funext fun i => (hc i).symm)
        obtain ⟨j, hj⟩ := hex
        set b : Bool := decide (x j < y j) with hb
        set e : Fin d × Bool := (j, b) with he
        set y' : Fin d → ℤ := y - stepv d e with hy'
        have hy'j : y' j = y j - (if b then 1 else -1) := by
          simp only [hy', he, Pi.sub_apply, stepv]
          norm_num
        have hy'i : ∀ i, i ≠ j → y' i = y i := by
          intro i hij
          simp only [hy', he, Pi.sub_apply, stepv, if_neg hij, sub_zero]
        have hdrop : (∑ i : Fin d, (y' i - x i).natAbs) < N := by
          rw [← hN]
          refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
          · by_cases hij : i = j
            · subst hij
              rw [hy'j]
              by_cases hlt : x i < y i
              · rw [if_pos (by simp [hb, hlt])]; omega
              · rw [if_neg (by simp [hb, hlt])]; omega
            · rw [hy'i i hij]
          · rw [hy'j]
            by_cases hlt : x j < y j
            · rw [if_pos (by simp [hb, hlt])]; omega
            · rw [if_neg (by simp [hb, hlt])]; omega
        obtain ⟨t, ht⟩ := ih _ hdrop x y' rfl
        refine ⟨t + 1, ?_⟩
        rw [cnt_succ]
        refine lt_of_lt_of_le ht ?_
        exact Finset.single_le_sum (f := fun e' : Fin d × Bool => cnt d t x (y - stepv d e'))
          (fun e' _ => Nat.zero_le _) (Finset.mem_univ e)

private lemma srw_irreducible (d : ℕ) (hd : 0 < d) : IrreducibleC (srwZ d) := by
  intro x y
  obtain ⟨t, ht⟩ := cnt_pos_of_reach d (∑ i : Fin d, (y i - x i).natAbs) x y rfl
  refine ⟨t, ?_⟩
  rw [stepPow_eq d hd t x y]
  have : (0:ℝ) < (cnt d t x y : ℝ) := by exact_mod_cast ht
  positivity

end Chain

/-! ### The one-dimensional balanced count -/

section OneDim

private def bal (n : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Fin n → Bool =>
    2 * (Finset.univ.filter fun s => σ s = true).card = n).card

private lemma card_fun_card_eq (n k : ℕ) :
    (Finset.univ.filter fun σ : Fin n → Bool =>
      (Finset.univ.filter fun s => σ s = true).card = k).card = n.choose k := by
  classical
  have hcard : ((Finset.univ : Finset (Fin n)).powersetCard k).card = n.choose k := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← hcard]
  refine Finset.card_nbij' (fun σ => Finset.univ.filter fun s => σ s = true)
    (fun A => fun s => decide (s ∈ A)) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hσ
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hσ⟩
  · intro A hA
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hA
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    rw [show (Finset.univ.filter fun s => (decide (s ∈ A)) = true) = A from by ext s; simp]
    exact hA.2
  · intro σ _; funext s; simp
  · intro A _; ext s; simp

private lemma bal_even (m : ℕ) : bal (2 * m) = (2 * m).choose m := by
  classical
  rw [bal, ← card_fun_card_eq (2 * m) m]
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

private lemma bal_odd (m : ℕ) : bal (2 * m + 1) = 0 := by
  classical
  rw [bal, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro σ _
  omega

private lemma cnt_one (n : ℕ) : cnt 1 n 0 0 = bal n := by
  classical
  rw [cnt, bal]
  refine Finset.card_nbij' (fun w => fun s => (w s).2) (fun σ => fun s => (0, σ s)) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hw ⊢
    have h0 := congrFun hw 0
    simp only [Pi.add_apply, Pi.zero_apply, walkEnd, zero_add] at h0
    have hstep : ∀ s : Fin n, stepv 1 (w s) 0 = if (w s).2 then (1:ℤ) else -1 := by
      intro s
      simp only [stepv]
      rw [if_pos (Subsingleton.elim _ _)]
    rw [Finset.sum_congr rfl (fun s _ => hstep s)] at h0
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s => (w s).2 = true)] at h0
    have h1 : ∑ s ∈ Finset.univ.filter (fun s : Fin n => (w s).2 = true),
        (if (w s).2 then (1:ℤ) else -1)
        = ((Finset.univ.filter fun s : Fin n => (w s).2 = true).card : ℤ) := by
      rw [Finset.sum_congr rfl (fun s hs => by
        rw [if_pos (Finset.mem_filter.mp hs).2]), Finset.sum_const, nsmul_eq_mul, mul_one]
    have h2 : ∑ s ∈ Finset.univ.filter (fun s : Fin n => ¬ ((w s).2 = true)),
        (if (w s).2 then (1:ℤ) else -1)
        = -((Finset.univ.filter fun s : Fin n => ¬ ((w s).2 = true)).card : ℤ) := by
      rw [Finset.sum_congr rfl (fun s hs => by
        rw [if_neg (Finset.mem_filter.mp hs).2]), Finset.sum_const, nsmul_eq_mul, mul_neg_one]
    have hsplit : (Finset.univ.filter fun s : Fin n => (w s).2 = true).card
        + (Finset.univ.filter fun s : Fin n => ¬ ((w s).2 = true)).card = n := by
      rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
    rw [h1, h2] at h0
    omega
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hσ ⊢
    funext j
    simp only [Pi.add_apply, Pi.zero_apply, walkEnd, zero_add]
    have hstep : ∀ s : Fin n, stepv 1 ((0 : Fin 1), σ s) j = if σ s then (1:ℤ) else -1 := by
      intro s
      simp only [stepv]
      rw [if_pos (Subsingleton.elim _ _)]
    rw [Finset.sum_congr rfl (fun s _ => hstep s)]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s => σ s = true)]
    have h1 : ∑ s ∈ Finset.univ.filter (fun s : Fin n => σ s = true), (if σ s then (1:ℤ) else -1)
        = ((Finset.univ.filter fun s : Fin n => σ s = true).card : ℤ) := by
      rw [Finset.sum_congr rfl (fun s hs => by
        rw [if_pos (Finset.mem_filter.mp hs).2]), Finset.sum_const, nsmul_eq_mul, mul_one]
    have h2 : ∑ s ∈ Finset.univ.filter (fun s : Fin n => ¬ (σ s = true)),
        (if σ s then (1:ℤ) else -1)
        = -((Finset.univ.filter fun s : Fin n => ¬ (σ s = true)).card : ℤ) := by
      rw [Finset.sum_congr rfl (fun s hs => by
        rw [if_neg (Finset.mem_filter.mp hs).2]), Finset.sum_const, nsmul_eq_mul, mul_neg_one]
    have hsplit : (Finset.univ.filter fun s : Fin n => σ s = true).card
        + (Finset.univ.filter fun s : Fin n => ¬ (σ s = true)).card = n := by
      rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
    rw [h1, h2]
    omega
  · intro w _
    funext s
    exact Prod.ext (Subsingleton.elim _ _) rfl
  · intro σ _
    funext s
    rfl

end OneDim

/-! ### Recurrence in dimension one -/

section DimOne

private lemma not_summable_inv_succ : ¬ Summable (fun m : ℕ => (1:ℝ) / (m + 1)) := by
  intro hcomp
  have hshift : Summable (fun n : ℕ => (1:ℝ) / n) := by
    rw [← summable_nat_add_iff 1]
    exact hcomp.congr (fun m => by push_cast; ring)
  exact Real.not_summable_one_div_natCast hshift

private lemma not_summable_odd_inv : ¬ Summable (fun m : ℕ => (1:ℝ) / (2 * m + 1)) := by
  intro h
  refine not_summable_inv_succ ?_
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) (h.mul_left 2)
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  linarith

private lemma srw1_diag (m : ℕ) :
    stepPow (srwZ 1) (2 * m) 0 0 = (((2 * m).choose m : ℕ) : ℝ) / 4 ^ m := by
  rw [stepPow_eq 1 (by norm_num) (2 * m) 0 0, cnt_one, bal_even]
  norm_num
  rw [show (2:ℝ) ^ (2 * m) = 4 ^ m from by rw [pow_mul]; norm_num]

private lemma central_lower (m : ℕ) : (4:ℝ) ^ m ≤ (2 * m + 1) * (((2 * m).choose m : ℕ) : ℝ) := by
  have h1 : ∑ i ∈ Finset.range (2 * m + 1), (2 * m).choose i = 2 ^ (2 * m) :=
    Nat.sum_range_choose (2 * m)
  have h2 : ∀ i ∈ Finset.range (2 * m + 1), (2 * m).choose i ≤ (2 * m).choose m := by
    intro i _
    have := Nat.choose_le_centralBinom i m
    rwa [Nat.centralBinom_eq_two_mul_choose] at this
  have h3 : (2:ℕ) ^ (2 * m) ≤ (2 * m + 1) * ((2 * m).choose m) := by
    rw [← h1]
    calc ∑ i ∈ Finset.range (2 * m + 1), (2 * m).choose i
        ≤ ∑ _i ∈ Finset.range (2 * m + 1), (2 * m).choose m := Finset.sum_le_sum h2
      _ = (2 * m + 1) * ((2 * m).choose m) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h4 : ((2:ℕ) ^ (2 * m) : ℝ) ≤ ((2 * m + 1) * ((2 * m).choose m) : ℕ) := by
    exact_mod_cast h3
  push_cast at h4
  calc (4:ℝ) ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
    _ ≤ (2 * m + 1) * (((2 * m).choose m : ℕ) : ℝ) := h4

private lemma srw1_lower (m : ℕ) : (1:ℝ) / (2 * m + 1) ≤ stepPow (srwZ 1) (2 * m) 0 0 := by
  rw [srw1_diag m, div_le_div_iff₀ (by positivity) (by positivity)]
  have := central_lower m
  linarith

private lemma srw1_not_summable : ¬ Summable (fun t : ℕ => stepPow (srwZ 1) t 0 0) := by
  intro h
  have hinj : Function.Injective (fun m : ℕ => 2 * m) := by
    intro a b hab
    simp only [] at hab
    omega
  have h2 : Summable (fun m : ℕ => stepPow (srwZ 1) (2 * m) 0 0) := h.comp_injective hinj
  exact not_summable_odd_inv
    (Summable.of_nonneg_of_le (fun m => by positivity) (fun m => srw1_lower m) h2)

end DimOne

/-! ### Recurrence in dimension two -/

section DimTwo

private def sgnSum {n : ℕ} (σ : Fin n → Bool) : ℤ := ∑ s, if σ s then (1:ℤ) else -1

private lemma sgnSum_eq {n : ℕ} (σ : Fin n → Bool) :
    sgnSum σ = 2 * ((Finset.univ.filter fun s => σ s = true).card : ℤ) - n := by
  classical
  rw [sgnSum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s => σ s = true)]
  have h1 : ∑ s ∈ Finset.univ.filter (fun s : Fin n => σ s = true), (if σ s then (1:ℤ) else -1)
      = ((Finset.univ.filter fun s : Fin n => σ s = true).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun s hs => by
      rw [if_pos (Finset.mem_filter.mp hs).2]), Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : ∑ s ∈ Finset.univ.filter (fun s : Fin n => ¬ (σ s = true)),
      (if σ s then (1:ℤ) else -1)
      = -((Finset.univ.filter fun s : Fin n => ¬ (σ s = true)).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun s hs => by
      rw [if_neg (Finset.mem_filter.mp hs).2]), Finset.sum_const, nsmul_eq_mul, mul_neg_one]
  have hsplit : (Finset.univ.filter fun s : Fin n => σ s = true).card
      + (Finset.univ.filter fun s : Fin n => ¬ (σ s = true)).card = n := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  rw [h1, h2]
  omega

private lemma bal_eq_sgn (n : ℕ) :
    bal n = (Finset.univ.filter fun σ : Fin n → Bool => sgnSum σ = 0).card := by
  classical
  rw [bal]
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, sgnSum_eq]
  omega

private lemma fin2_cases (j : Fin 2) : j = 0 ∨ j = 1 := by
  revert j
  decide

private lemma walk2_coord (n : ℕ) (w : Fin n → Fin 2 × Bool) (j : Fin 2) :
    walkEnd 2 w j = ∑ s : Fin n, (if j = (w s).1 then (if (w s).2 then (1:ℤ) else -1) else 0) :=
  Finset.sum_congr rfl fun s _ => by simp only [stepv]

private lemma sgn_first (n : ℕ) (w : Fin n → Fin 2 × Bool) :
    sgnSum (fun s => (w s).2) = walkEnd 2 w 0 + walkEnd 2 w 1 := by
  rw [walk2_coord, walk2_coord, ← Finset.sum_add_distrib, sgnSum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases fin2_cases (w s).1 with h | h
  · rw [h]
    try norm_num
  · rw [h]
    try norm_num

private lemma sgn_second (n : ℕ) (w : Fin n → Fin 2 × Bool) :
    sgnSum (fun s => if (w s).1 = 0 then (w s).2 else !(w s).2)
      = walkEnd 2 w 0 - walkEnd 2 w 1 := by
  rw [walk2_coord, walk2_coord, ← Finset.sum_sub_distrib, sgnSum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases fin2_cases (w s).1 with h | h <;> rw [h]
  · norm_num
  · rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
    norm_num
    cases hb : (w s).2 <;> norm_num

private lemma inv2_fst (n : ℕ) (p : (Fin n → Bool) × (Fin n → Bool)) :
    (fun s => ((if p.1 s = p.2 s then (0 : Fin 2) else 1, p.1 s) : Fin 2 × Bool).2) = p.1 := rfl

private lemma inv2_snd (n : ℕ) (p : (Fin n → Bool) × (Fin n → Bool)) :
    (fun s => if ((if p.1 s = p.2 s then (0 : Fin 2) else 1, p.1 s) : Fin 2 × Bool).1 = 0 then
        ((if p.1 s = p.2 s then (0 : Fin 2) else 1, p.1 s) : Fin 2 × Bool).2
      else !((if p.1 s = p.2 s then (0 : Fin 2) else 1, p.1 s) : Fin 2 × Bool).2) = p.2 := by
  funext s
  by_cases h : p.1 s = p.2 s
  · have h0 : (if p.1 s = p.2 s then (0 : Fin 2) else 1) = 0 := if_pos h
    rw [h0, if_pos rfl]
    exact h
  · have h1 : (if p.1 s = p.2 s then (0 : Fin 2) else 1) = 1 := if_neg h
    rw [h1, if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
    cases hb : p.1 s <;> cases hc : p.2 s <;> simp_all

private lemma cnt_two (n : ℕ) : cnt 2 n 0 0 = bal n * bal n := by
  classical
  have hprod : (Finset.univ.filter fun p : (Fin n → Bool) × (Fin n → Bool) =>
      sgnSum p.1 = 0 ∧ sgnSum p.2 = 0).card
      = (Finset.univ.filter fun σ : Fin n → Bool => sgnSum σ = 0).card
        * (Finset.univ.filter fun σ : Fin n → Bool => sgnSum σ = 0).card := by
    rw [← Finset.card_product, ← Finset.filter_product]
    rfl
  rw [bal_eq_sgn, ← hprod, cnt]
  refine Finset.card_nbij'
    (fun w => (fun s => (w s).2, fun s => if (w s).1 = 0 then (w s).2 else !(w s).2))
    (fun p => fun s => (if p.1 s = p.2 s then 0 else 1, p.1 s)) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hw ⊢
    have h0 : walkEnd 2 w 0 = 0 := by
      have := congrFun hw 0
      simpa using this
    have h1 : walkEnd 2 w 1 = 0 := by
      have := congrFun hw 1
      simpa using this
    exact ⟨by rw [sgn_first, h0, h1]; ring, by rw [sgn_second, h0, h1]; ring⟩
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨hp1, hp2⟩ := hp
    set w : Fin n → Fin 2 × Bool := fun s => (if p.1 s = p.2 s then 0 else 1, p.1 s) with hw
    have hs1 : sgnSum (fun s => (w s).2) = 0 := by rw [hw, inv2_fst]; exact hp1
    have hs2 : sgnSum (fun s => if (w s).1 = 0 then (w s).2 else !(w s).2) = 0 := by
      rw [hw, inv2_snd]; exact hp2
    rw [sgn_first] at hs1
    rw [sgn_second] at hs2
    funext j
    simp only [Pi.add_apply, Pi.zero_apply, zero_add]
    rcases fin2_cases j with h | h <;> rw [h] <;> omega
  · intro w _
    funext s
    rcases fin2_cases (w s).1 with h | h
    · rw [Prod.ext_iff]
      refine ⟨?_, rfl⟩
      show (if (w s).2 = (if (w s).1 = 0 then (w s).2 else !(w s).2) then (0:Fin 2) else 1)
        = (w s).1
      rw [h, if_pos rfl, if_pos rfl]
    · rw [Prod.ext_iff]
      refine ⟨?_, rfl⟩
      show (if (w s).2 = (if (w s).1 = 0 then (w s).2 else !(w s).2) then (0:Fin 2) else 1)
        = (w s).1
      have h3 : ¬ ((w s).2 = !(w s).2) := by cases hb : (w s).2 <;> simp
      rw [h, if_neg (by decide : ¬ ((1 : Fin 2) = 0)), if_neg h3]
  · intro p _
    rw [Prod.ext_iff]
    exact ⟨inv2_fst n p, inv2_snd n p⟩


end DimTwo

/-! ### Recurrence in dimension two, continued -/

section DimTwoBound

private def cbr (m : ℕ) : ℝ := (((2 * m).choose m : ℕ) : ℝ) / 4 ^ m

private lemma cbr_succ (m : ℕ) : cbr (m + 1) * (2 * (m:ℝ) + 2) = cbr m * (2 * m + 1) := by
  have h := Nat.succ_mul_centralBinom_succ m
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  have h' : ((m : ℝ) + 1) * (((2 * (m + 1)).choose (m + 1) : ℕ) : ℝ)
      = 2 * (2 * (m:ℝ) + 1) * (((2 * m).choose m : ℕ) : ℝ) := by exact_mod_cast h
  have h4 : (4:ℝ) ^ (m + 1) = 4 * 4 ^ m := by rw [pow_succ]; ring
  have hp : (0:ℝ) < 4 ^ m := by positivity
  rw [cbr, cbr, h4, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (2 * (4:ℝ) ^ m) * h'

private lemma cbr_pos (m : ℕ) : 0 < cbr m := by
  rw [cbr]
  have h1 : 0 < ((2 * m).choose m : ℕ) := Nat.choose_pos (by omega)
  have h2 : (0:ℝ) < (((2 * m).choose m : ℕ) : ℝ) := by exact_mod_cast h1
  positivity

private lemma cbr_sq_lower : ∀ m : ℕ, 1 ≤ m → (1:ℝ) / (4 * m) ≤ (cbr m) ^ 2 := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ k ih =>
      intro _
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        have h1 : cbr 1 = 1 / 2 := by
          rw [cbr]
          norm_num
        rw [h1]
        norm_num
      · have hprev := ih hk
        have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
        have hprev' : (1:ℝ) ≤ 4 * k * (cbr k) ^ 2 := by
          rw [div_le_iff₀ (by positivity)] at hprev
          linarith
        have hkey : ((k:ℝ) + 1) ≤ (cbr k) ^ 2 * (2 * (k:ℝ) + 1) ^ 2 := by
          nlinarith [hprev', hkR, sq_nonneg (cbr k)]
        have hsq : (cbr (k + 1)) ^ 2 * (2 * (k:ℝ) + 2) ^ 2
            = (cbr k) ^ 2 * (2 * (k:ℝ) + 1) ^ 2 := by
          rw [← mul_pow, ← mul_pow, cbr_succ k]
        rw [div_le_iff₀ (by positivity)]
        push_cast
        nlinarith [hkey, hsq, hkR, sq_nonneg (cbr (k + 1))]

private lemma srw2_diag (m : ℕ) : stepPow (srwZ 2) (2 * m) 0 0 = (cbr m) ^ 2 := by
  rw [stepPow_eq 2 (by norm_num) (2 * m) 0 0, cnt_two, bal_even, cbr]
  push_cast
  rw [div_pow, show ((4:ℝ) ^ m) ^ 2 = 4 ^ (2 * m) from by rw [← pow_mul]; congr 1; omega]
  ring

private lemma srw2_not_summable : ¬ Summable (fun t : ℕ => stepPow (srwZ 2) t 0 0) := by
  intro h
  have hinj : Function.Injective (fun m : ℕ => 2 * (m + 1)) := by
    intro a b hab
    simp only [] at hab
    omega
  have h2 : Summable (fun m : ℕ => stepPow (srwZ 2) (2 * (m + 1)) 0 0) := h.comp_injective hinj
  refine not_summable_inv_succ ?_
  have hle : ∀ m : ℕ, (1:ℝ) / (m + 1) ≤ 4 * stepPow (srwZ 2) (2 * (m + 1)) 0 0 := by
    intro m
    have := cbr_sq_lower (m + 1) (by omega)
    rw [srw2_diag (m + 1)]
    push_cast at this ⊢
    rw [div_le_iff₀ (by positivity)] at this ⊢
    nlinarith [this]
  exact Summable.of_nonneg_of_le (fun m => by positivity) hle (h2.mul_left 4)

end DimTwoBound

/-! ### The fibre bound in higher dimensions -/

section Fibres

private def balT (α : Type*) [Fintype α] [DecidableEq α] : ℕ :=
  (Finset.univ.filter fun σ : α → Bool => ∑ s : α, (if σ s then (1:ℤ) else -1) = 0).card

private lemma balT_fin (n : ℕ) : balT (Fin n) = bal n := by
  rw [balT, bal_eq_sgn]
  rfl

private lemma balT_eq (α : Type*) [Fintype α] [DecidableEq α] :
    balT α = bal (Fintype.card α) := by
  classical
  rw [← balT_fin]
  set e := Fintype.equivFin α with he
  rw [balT, balT]
  refine Finset.card_nbij' (fun σ => fun j => σ (e.symm j)) (fun τ => fun s => τ (e s)) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hσ ⊢
    rw [← hσ]
    exact (Equiv.sum_comp e.symm (fun s => if σ s then (1:ℤ) else -1))
  · intro τ hτ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hτ ⊢
    rw [← hτ]
    exact (Equiv.sum_comp e (fun j => if τ j then (1:ℤ) else -1))
  · intro σ _
    funext s
    show σ (e.symm (e s)) = σ s
    rw [Equiv.symm_apply_apply]
  · intro τ _
    funext j
    show τ (e (e.symm j)) = τ j
    rw [Equiv.apply_symm_apply]

private lemma walkEnd_fiber {d n : ℕ} (c : Fin n → Fin d) (σ : Fin n → Bool) (i : Fin d) :
    walkEnd d (fun s => (c s, σ s)) i
      = ∑ s : {s : Fin n // c s = i}, (if σ s.1 then (1:ℤ) else -1) := by
  classical
  rw [walkEnd]
  have hterm : ∀ s : Fin n, stepv d (c s, σ s) i
      = if c s = i then (if σ s then (1:ℤ) else -1) else 0 := by
    intro s
    simp only [stepv]
    by_cases h : i = c s
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hc => h hc.symm)]
  rw [Finset.sum_congr rfl (fun s _ => hterm s), ← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter fun s => c s = i)
    (fun x => by simp) (fun s => if σ s then (1:ℤ) else -1)

private lemma N_le {d n : ℕ} (hd : 0 < d) (c : Fin n → Fin d) :
    (Finset.univ.filter fun σ : Fin n → Bool =>
        ∀ i : Fin d, ∑ s : {s : Fin n // c s = i}, (if σ s.1 then (1:ℤ) else -1) = 0).card
      ≤ ∏ i : Fin d, balT {s : Fin n // c s = i} := by
  classical
  have hpi : (Fintype.piFinset fun i : Fin d =>
      (Finset.univ.filter fun τ : {s : Fin n // c s = i} → Bool =>
        ∑ s, (if τ s then (1:ℤ) else -1) = 0)).card
      = ∏ i : Fin d, balT {s : Fin n // c s = i} := by
    rw [Fintype.card_piFinset]
    rfl
  rw [← hpi]
  refine Finset.card_le_card_of_injOn
    (fun σ => fun i => fun s : {s : Fin n // c s = i} => σ s.1) ?_ ?_
  · intro σ hσ
    have hσ' : ∀ i : Fin d, ∑ s : {s : Fin n // c s = i}, (if σ s.1 then (1:ℤ) else -1) = 0 := by
      simpa using hσ
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hσ'
  · intro σ₁ _ σ₂ _ h
    funext s
    have := congrFun (congrFun h (c s)) ⟨s, rfl⟩
    exact this

end Fibres

/-! ### The normalised one-dimensional return probability -/

section RFun

private def rr (k : ℕ) : ℝ := (bal k : ℝ) / 2 ^ k

private lemma bal_le (k : ℕ) : bal k ≤ 2 ^ k := by
  classical
  have := Finset.card_filter_le (Finset.univ : Finset (Fin k → Bool))
    (fun σ => 2 * (Finset.univ.filter fun s => σ s = true).card = k)
  rw [bal]
  refine this.trans ?_
  rw [Finset.card_univ]
  simp [Fintype.card_fun]

private lemma rr_nonneg (k : ℕ) : 0 ≤ rr k := by
  rw [rr]; positivity

private lemma rr_le_one (k : ℕ) : rr k ≤ 1 := by
  rw [rr, div_le_one (by positivity)]
  have := bal_le k
  exact_mod_cast this

private lemma rr_even (m : ℕ) : rr (2 * m) = cbr m := by
  rw [rr, cbr, bal_even]
  congr 1
  rw [pow_mul]
  norm_num

private lemma rr_odd (m : ℕ) : rr (2 * m + 1) = 0 := by
  rw [rr, bal_odd]
  simp

private lemma cbr_sq_upper : ∀ m : ℕ, (cbr m) ^ 2 * (3 * m + 1) ≤ 1 := by
  intro m
  induction m with
  | zero =>
      have : cbr 0 = 1 := by rw [cbr]; norm_num
      rw [this]; norm_num
  | succ k ih =>
      have hs := cbr_succ k
      have hpos : (0:ℝ) < 2 * (k:ℝ) + 2 := by positivity
      have hval : cbr (k + 1) = cbr k * (2 * (k:ℝ) + 1) / (2 * k + 2) := by
        field_simp at hs ⊢
        linarith [hs]
      have hkey : (2 * (k:ℝ) + 1) ^ 2 * (3 * (k + 1) + 1) ≤ (2 * k + 2) ^ 2 * (3 * k + 1) := by
        nlinarith [sq_nonneg ((k:ℝ)), (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      have hcbrsq : (0:ℝ) ≤ (cbr k) ^ 2 := sq_nonneg _
      have hstep : (cbr (k+1)) ^ 2 * (3 * ((k:ℝ) + 1) + 1)
          = (cbr k) ^ 2 * ((2 * (k:ℝ) + 1) ^ 2 * (3 * (k + 1) + 1)) / (2 * k + 2) ^ 2 := by
        rw [hval]; field_simp; try ring
      have : (cbr (k+1)) ^ 2 * (3 * ((k:ℝ) + 1) + 1) ≤ (cbr k) ^ 2 * (3 * k + 1) := by
        rw [hstep, div_le_iff₀ (by positivity)]
        nlinarith [hcbrsq, hkey]
      push_cast
      linarith [ih, this]

private lemma rr_sq_le (k : ℕ) : (rr k) ^ 2 ≤ 2 / ((k : ℝ) + 1) := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hm' : k = 2 * m := by omega
    subst hm'
    rw [rr_even]
    have h := cbr_sq_upper m
    have h1 : (0:ℝ) < 3 * (m:ℝ) + 1 := by positivity
    have h2 : (cbr m) ^ 2 ≤ 1 / (3 * (m:ℝ) + 1) := by
      rw [le_div_iff₀ h1]; linarith
    refine h2.trans ?_
    rw [div_le_div_iff₀ h1 (by positivity)]
    push_cast
    linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  · subst hm
    rw [rr_odd]
    norm_num
    positivity

end RFun

/-! ### Decomposing a walk into its coordinate pattern -/

section Multinomial

private def kcnt {d n : ℕ} (c : Fin n → Fin d) (i : Fin d) : ℕ :=
  (Finset.univ.filter fun s => c s = i).card

private lemma kcnt_sum {d n : ℕ} (c : Fin n → Fin d) : ∑ i : Fin d, kcnt c i = n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (f := c) (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin d)))
    (fun x _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h.symm

private lemma balT_fiber {d n : ℕ} (c : Fin n → Fin d) (i : Fin d) :
    balT {s : Fin n // c s = i} = bal (kcnt c i) := by
  classical
  rw [balT_eq]
  congr 1
  rw [kcnt, Fintype.card_subtype]

private lemma cnt_le_sum {d n : ℕ} (hd : 0 < d) :
    cnt d n 0 0 ≤ ∑ c : Fin n → Fin d, ∏ i : Fin d, bal (kcnt c i) := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun w : Fin n → Fin d × Bool => (fun s => (w s).1))
    (s := (Finset.univ.filter fun w : Fin n → Fin d × Bool =>
      (0 : Fin d → ℤ) + walkEnd d w = 0))
    (t := (Finset.univ : Finset (Fin n → Fin d))) (fun x _ => Finset.mem_univ _)
  rw [cnt, hfib]
  refine Finset.sum_le_sum ?_
  intro c _
  refine le_trans ?_ (le_trans (N_le hd c) (le_of_eq (Finset.prod_congr rfl
    (fun i _ => balT_fiber c i))))
  refine Finset.card_le_card_of_injOn (fun w => fun s => (w s).2) ?_ ?_
  · intro w hw
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and,
      Finset.mem_coe, Finset.mem_filter] at hw ⊢
    obtain ⟨hw1, hw2⟩ := hw
    intro i
    have hwe : w = fun s => (c s, (w s).2) := by
      funext s
      have : (w s).1 = c s := congrFun hw2 s
      exact Prod.ext this rfl
    have := walkEnd_fiber c (fun s => (w s).2) i
    rw [← hwe] at this
    rw [← this]
    have : walkEnd d w = 0 := by rw [← hw1]; abel
    rw [this]
    rfl
  · intro w1 h1 w2 h2 h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at h1 h2
    funext s
    have e1 : (w1 s).1 = c s := congrFun h1.2 s
    have e2 : (w2 s).1 = c s := congrFun h2.2 s
    have e3 : (w1 s).2 = (w2 s).2 := congrFun h s
    exact Prod.ext (e1.trans e2.symm) e3

private lemma prod_bal_eq {d n : ℕ} (c : Fin n → Fin d) :
    (∏ i : Fin d, (bal (kcnt c i) : ℝ)) = (∏ i : Fin d, rr (kcnt c i)) * 2 ^ n := by
  have h1 : (∏ i : Fin d, rr (kcnt c i))
      = (∏ i : Fin d, (bal (kcnt c i) : ℝ)) / ∏ i : Fin d, (2:ℝ) ^ (kcnt c i) := by
    rw [← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl (fun i _ => rfl)
  have h2 : (∏ i : Fin d, (2:ℝ) ^ (kcnt c i)) = 2 ^ n := by
    rw [Finset.prod_pow_eq_pow_sum, kcnt_sum]
  rw [h1, h2]
  field_simp

private lemma stepPow_le_sum {d n : ℕ} (hd : 0 < d) :
    stepPow (srwZ d) n 0 0
      ≤ (∑ c : Fin n → Fin d, ∏ i : Fin d, rr (kcnt c i)) / (d:ℝ) ^ n := by
  classical
  rw [stepPow_eq d hd]
  have hdp : (0:ℝ) < (d:ℝ) ^ n := by
    have : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
    positivity
  have hnum : ((cnt d n 0 0 : ℕ) : ℝ)
      ≤ ∑ c : Fin n → Fin d, (∏ i : Fin d, rr (kcnt c i)) * 2 ^ n := by
    have := cnt_le_sum (d := d) (n := n) hd
    have h2 : ((cnt d n 0 0 : ℕ) : ℝ)
        ≤ ((∑ c : Fin n → Fin d, ∏ i : Fin d, bal (kcnt c i) : ℕ) : ℝ) := by
      exact_mod_cast this
    refine h2.trans (le_of_eq ?_)
    push_cast
    exact Finset.sum_congr rfl (fun c _ => prod_bal_eq c)
  rw [← Finset.sum_mul] at hnum
  have hcast : (((2 * d : ℕ) : ℝ)) ^ n = 2 ^ n * (d:ℝ) ^ n := by
    push_cast; rw [mul_pow]
  rw [hcast]
  rw [div_le_div_iff₀ (by positivity) hdp]
  have h2p : (0:ℝ) < 2 ^ n := by positivity
  nlinarith [hnum, hdp, h2p]

end Multinomial

/-! ### A Chernoff bound for the coordinate counts -/

section Chernoff

private lemma gen_id {d n : ℕ} (hd : 0 < d) (z : ℝ) (i0 : Fin d) :
    ∑ c : Fin n → Fin d, z ^ (kcnt c i0) = (z + ((d:ℝ) - 1)) ^ n := by
  classical
  have hterm : ∀ c : Fin n → Fin d,
      z ^ (kcnt c i0) = ∏ s : Fin n, (if c s = i0 then z else 1) := by
    intro c
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, kcnt]
  have hcol : ∀ _s : Fin n, (∑ i : Fin d, (if i = i0 then z else (1:ℝ)))
      = z + ((d:ℝ) - 1) := by
    intro _s
    have : ∀ i : Fin d, (if i = i0 then z else (1:ℝ)) = 1 + (if i = i0 then z - 1 else 0) := by
      intro i
      by_cases h : i = i0
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h]; ring
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib,
      Finset.sum_const, Finset.sum_ite_eq' Finset.univ i0 (fun _ => z - 1)]
    rw [if_pos (Finset.mem_univ i0), Finset.card_univ, Fintype.card_fin]
    simp
    ring
  have hprod := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin d)))
    (fun (_ : Fin n) (i : Fin d) => (if i = i0 then z else (1:ℝ)))
  rw [Finset.prod_congr rfl (fun s _ => hcol s), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hprod
  rw [Finset.sum_congr rfl (fun c _ => hterm c)]
  rw [hprod, Fintype.piFinset_univ]

private lemma bad_card {d n : ℕ} (hd : 0 < d) (i0 : Fin d) (m : ℕ) :
    (((Finset.univ.filter fun c : Fin n → Fin d => kcnt c i0 < m).card : ℕ) : ℝ)
      ≤ 2 ^ m * ((d:ℝ) - 1/2) ^ n := by
  classical
  set B := (Finset.univ.filter fun c : Fin n → Fin d => kcnt c i0 < m) with hB
  have hlow : ∀ c ∈ B, ((1:ℝ)/2) ^ m ≤ ((1:ℝ)/2) ^ (kcnt c i0) := by
    intro c hc
    rw [hB, Finset.mem_filter] at hc
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_of_lt hc.2)
  have h1 : (B.card : ℝ) * ((1:ℝ)/2) ^ m ≤ ∑ c ∈ B, ((1:ℝ)/2) ^ (kcnt c i0) := by
    have h := Finset.card_nsmul_le_sum B (fun c => ((1:ℝ)/2) ^ (kcnt c i0)) _ hlow
    simpa [nsmul_eq_mul] using h
  have h2 : ∑ c ∈ B, ((1:ℝ)/2) ^ (kcnt c i0)
      ≤ ∑ c : Fin n → Fin d, ((1:ℝ)/2) ^ (kcnt c i0) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro c _ _
    positivity
  have h3 := gen_id (d := d) (n := n) hd ((1:ℝ)/2) i0
  have h4 : ((1:ℝ)/2 + ((d:ℝ) - 1)) = (d:ℝ) - 1/2 := by ring
  rw [h4] at h3
  have h5 : (B.card : ℝ) * ((1:ℝ)/2) ^ m ≤ ((d:ℝ) - 1/2) ^ n := by
    rw [← h3]; exact h1.trans h2
  have hp : (0:ℝ) < ((1:ℝ)/2) ^ m := by positivity
  rw [← le_div_iff₀ hp] at h5
  refine h5.trans (le_of_eq ?_)
  rw [div_pow, one_pow]
  field_simp

end Chernoff

/-! ### The transience estimate in dimension at least three -/

section Transient

private lemma prod_le_sub {d : ℕ} (S : Finset (Fin d)) (f : Fin d → ℝ)
    (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1) :
    ∏ i : Fin d, f i ≤ ∏ i ∈ S, f i := by
  have h := Finset.prod_sdiff (f := f) (Finset.subset_univ S)
  rw [← h]
  have hc0 : 0 ≤ ∏ i ∈ Finset.univ \ S, f i := Finset.prod_nonneg (fun i _ => h0 i)
  have hc1 : ∏ i ∈ Finset.univ \ S, f i ≤ 1 :=
    Finset.prod_le_one (fun i _ => h0 i) (fun i _ => h1 i)
  have hs0 : 0 ≤ ∏ i ∈ S, f i := Finset.prod_nonneg (fun i _ => h0 i)
  nlinarith

private lemma sum_bound {d : ℕ} (hd : 3 ≤ d) (n : ℕ) :
    ∑ c : Fin n → Fin d, ∏ i : Fin d, rr (kcnt c i)
      ≤ (d:ℝ) ^ n * (Real.sqrt (4 * (d:ℝ) / ((n:ℝ) + 1))) ^ 3
        + 3 * (2 ^ (n / (2 * d)) * ((d:ℝ) - 1/2) ^ n) := by
  classical
  have hd0 : 0 < d := by omega
  set m := n / (2 * d) with hmdef
  set B := Real.sqrt (4 * (d:ℝ) / ((n:ℝ) + 1)) with hBdef
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  set i0 : Fin d := ⟨0, by omega⟩ with hi0
  set i1 : Fin d := ⟨1, by omega⟩ with hi1
  set i2 : Fin d := ⟨2, by omega⟩ with hi2
  set S : Finset (Fin d) := {i0, i1, i2} with hSdef
  have hScard : S.card = 3 := by
    refine Finset.card_eq_three.mpr ⟨i0, i1, i2, ?_, ?_, ?_, rfl⟩
    · rw [hi0, hi1]; simp [Fin.ext_iff]
    · rw [hi0, hi2]; simp [Fin.ext_iff]
    · rw [hi1, hi2]; simp [Fin.ext_iff]
  -- the key numeric comparison
  have hmn : n + 1 ≤ (m + 1) * (2 * d) := by
    have h3 : n < n / (2 * d) * (2 * d) + 2 * d :=
      Nat.lt_div_mul_add (show 0 < 2 * d by omega)
    rw [hmdef, add_mul, one_mul]
    omega
  have hmnR : ((n:ℝ) + 1) ≤ ((m:ℝ) + 1) * (2 * (d:ℝ)) := by
    have : ((n + 1 : ℕ) : ℝ) ≤ (((m + 1) * (2 * d) : ℕ) : ℝ) := by exact_mod_cast hmn
    push_cast at this
    linarith
  have hrrB : ∀ k : ℕ, m ≤ k → rr k ≤ B := by
    intro k hk
    have h1 : (rr k) ^ 2 ≤ 2 / ((k:ℝ) + 1) := rr_sq_le k
    have h2 : (2:ℝ) / ((k:ℝ) + 1) ≤ 2 / ((m:ℝ) + 1) := by
      have hkm : ((m:ℝ) + 1) ≤ ((k:ℝ) + 1) := by
        have : (m:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
        linarith
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hkm
    have h3 : (2:ℝ) / ((m:ℝ) + 1) ≤ 4 * (d:ℝ) / ((n:ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hmnR, (Nat.cast_nonneg m : (0:ℝ) ≤ m), (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
    have h4 : (rr k) ^ 2 ≤ 4 * (d:ℝ) / ((n:ℝ) + 1) := by linarith
    calc rr k = Real.sqrt ((rr k) ^ 2) := (Real.sqrt_sq (rr_nonneg k)).symm
      _ ≤ B := by rw [hBdef]; exact Real.sqrt_le_sqrt h4
  have hPle : ∀ c : Fin n → Fin d,
      ∏ i : Fin d, rr (kcnt c i) ≤ ∏ i ∈ S, rr (kcnt c i) :=
    fun c => prod_le_sub S _ (fun i => rr_nonneg _) (fun i => rr_le_one _)
  refine le_trans (Finset.sum_le_sum (fun c _ => hPle c)) ?_
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun c : Fin n → Fin d => ∀ i ∈ S, m ≤ kcnt c i)
    (fun c => ∏ i ∈ S, rr (kcnt c i))]
  refine add_le_add ?_ ?_
  · -- the good part
    have hgood : ∀ c ∈ Finset.univ.filter (fun c : Fin n → Fin d => ∀ i ∈ S, m ≤ kcnt c i),
        ∏ i ∈ S, rr (kcnt c i) ≤ B ^ 3 := by
      intro c hc
      rw [Finset.mem_filter] at hc
      calc ∏ i ∈ S, rr (kcnt c i) ≤ ∏ _i ∈ S, B :=
            Finset.prod_le_prod (fun i _ => rr_nonneg _) (fun i hi => hrrB _ (hc.2 i hi))
        _ = B ^ 3 := by rw [Finset.prod_const, hScard]
    refine le_trans (Finset.sum_le_sum hgood) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ.filter
        (fun c : Fin n → Fin d => ∀ i ∈ S, m ≤ kcnt c i)).card : ℝ) ≤ (d:ℝ) ^ n := by
      have h1 := Finset.card_filter_le (Finset.univ : Finset (Fin n → Fin d))
        (fun c => ∀ i ∈ S, m ≤ kcnt c i)
      have h2 : (Finset.univ : Finset (Fin n → Fin d)).card = d ^ n := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      rw [h2] at h1
      have : (((Finset.univ.filter
        (fun c : Fin n → Fin d => ∀ i ∈ S, m ≤ kcnt c i)).card : ℕ) : ℝ) ≤ ((d ^ n : ℕ) : ℝ) := by
        exact_mod_cast h1
      simpa using this
    have hB3 : 0 ≤ B ^ 3 := by positivity
    nlinarith
  · -- the bad part
    have hbad1 : ∀ c ∈ Finset.univ.filter
        (fun c : Fin n → Fin d => ¬ ∀ i ∈ S, m ≤ kcnt c i),
        ∏ i ∈ S, rr (kcnt c i) ≤ 1 :=
      fun c _ => Finset.prod_le_one (fun i _ => rr_nonneg _) (fun i _ => rr_le_one _)
    refine le_trans (Finset.sum_le_sum hbad1) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsub : (Finset.univ.filter (fun c : Fin n → Fin d => ¬ ∀ i ∈ S, m ≤ kcnt c i))
        ⊆ S.biUnion (fun i => Finset.univ.filter (fun c : Fin n → Fin d => kcnt c i < m)) := by
      intro c hc
      rw [Finset.mem_filter] at hc
      obtain ⟨i, hiS, hi⟩ : ∃ i ∈ S, ¬ (m ≤ kcnt c i) := by
        by_contra hcon
        push_neg at hcon
        exact hc.2 (fun i hi => hcon i hi)
      exact Finset.mem_biUnion.mpr ⟨i, hiS, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by omega⟩⟩
    have hcb : (Finset.univ.filter (fun c : Fin n → Fin d => ¬ ∀ i ∈ S, m ≤ kcnt c i)).card
        ≤ ∑ i ∈ S, (Finset.univ.filter (fun c : Fin n → Fin d => kcnt c i < m)).card :=
      le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
    have hcbR : (((Finset.univ.filter
        (fun c : Fin n → Fin d => ¬ ∀ i ∈ S, m ≤ kcnt c i)).card : ℕ) : ℝ)
        ≤ ∑ i ∈ S, (((Finset.univ.filter
          (fun c : Fin n → Fin d => kcnt c i < m)).card : ℕ) : ℝ) := by
      have : (((Finset.univ.filter
          (fun c : Fin n → Fin d => ¬ ∀ i ∈ S, m ≤ kcnt c i)).card : ℕ) : ℝ)
          ≤ ((∑ i ∈ S, (Finset.univ.filter
            (fun c : Fin n → Fin d => kcnt c i < m)).card : ℕ) : ℝ) := by exact_mod_cast hcb
      simpa using this
    refine hcbR.trans ?_
    have hterm : ∀ i ∈ S, (((Finset.univ.filter
        (fun c : Fin n → Fin d => kcnt c i < m)).card : ℕ) : ℝ)
        ≤ 2 ^ m * ((d:ℝ) - 1/2) ^ n := fun i _ => bad_card hd0 i m
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, hScard, nsmul_eq_mul]
    norm_num

end Transient

/-! ### Summability of the return probabilities for `d ≥ 3` -/

section Summable3

private lemma sqrt_cube {y : ℝ} (hy : 0 ≤ y) : (Real.sqrt y) ^ 3 = y ^ ((3:ℝ)/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (y ^ ((1:ℝ)/2)) 3, ← Real.rpow_mul hy]
  norm_num

private lemma rho_lt_one {d : ℕ} (hd : 3 ≤ d) :
    (2:ℝ) ^ ((1:ℝ)/(2*(d:ℝ))) * (1 - 1/(2*(d:ℝ))) < 1 := by
  have hdR : (3:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  set x : ℝ := 1/(2*(d:ℝ)) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : x ≤ 1/6 := by
    rw [hx, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h1 : (2:ℝ) ^ x = Real.exp (Real.log 2 * x) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
  have h2 : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have h3 : (0:ℝ) < Real.exp (Real.log 2 * x) := Real.exp_pos _
  have h4 : (2:ℝ) ^ x * (1 - x) ≤ Real.exp (Real.log 2 * x) * Real.exp (-x) := by
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (le_of_lt h3)
  have h5 : Real.exp (Real.log 2 * x) * Real.exp (-x) = Real.exp (x * (Real.log 2 - 1)) := by
    rw [← Real.exp_add]; ring_nf
  have h6 : Real.log 2 - 1 < 0 := by
    have := Real.log_two_lt_d9
    linarith
  have h7 : Real.exp (x * (Real.log 2 - 1)) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg hx0 h6
  linarith [h4, h5 ▸ h4]

private lemma stepPow_nonneg (d : ℕ) (hd : 0 < d) (t : ℕ) (x y : Fin d → ℤ) :
    0 ≤ stepPow (srwZ d) t x y := by
  rw [stepPow_eq d hd]
  positivity

private lemma main_bound {d : ℕ} (hd : 3 ≤ d) (n : ℕ) :
    stepPow (srwZ d) n 0 0
      ≤ (4*(d:ℝ)) ^ ((3:ℝ)/2) * (((n:ℝ)+1) ^ (-((3:ℝ)/2)))
        + 3 * ((2:ℝ) ^ ((1:ℝ)/(2*(d:ℝ))) * (1 - 1/(2*(d:ℝ)))) ^ n := by
  have hd0 : 0 < d := by omega
  have hdR : (3:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdp : (0:ℝ) < (d:ℝ) := by linarith
  have hdn : (0:ℝ) < (d:ℝ) ^ n := by positivity
  set m := n / (2 * d) with hmdef
  have hstep := stepPow_le_sum (d := d) (n := n) hd0
  have hsum := sum_bound hd n
  have hchain : stepPow (srwZ d) n 0 0
      ≤ ((d:ℝ) ^ n * (Real.sqrt (4 * (d:ℝ) / ((n:ℝ) + 1))) ^ 3
        + 3 * (2 ^ m * ((d:ℝ) - 1/2) ^ n)) / (d:ℝ) ^ n := by
    refine hstep.trans ?_
    exact div_le_div_of_nonneg_right hsum hdn.le
  have hsplit : ((d:ℝ) ^ n * (Real.sqrt (4 * (d:ℝ) / ((n:ℝ) + 1))) ^ 3
        + 3 * (2 ^ m * ((d:ℝ) - 1/2) ^ n)) / (d:ℝ) ^ n
      = (Real.sqrt (4 * (d:ℝ) / ((n:ℝ) + 1))) ^ 3
        + 3 * (2 ^ m * (1 - 1/(2*(d:ℝ))) ^ n) := by
    rw [add_div, mul_comm ((d:ℝ)^n), mul_div_assoc, div_self (ne_of_gt hdn), mul_one]
    congr 1
    rw [mul_div_assoc, mul_div_assoc]
    congr 2
    rw [← div_pow]
    congr 1
    field_simp
  rw [hsplit] at hchain
  refine hchain.trans (add_le_add ?_ ?_)
  · -- the polynomial term
    have hy : (0:ℝ) ≤ 4 * (d:ℝ) / ((n:ℝ) + 1) := by positivity
    rw [sqrt_cube hy, Real.div_rpow (by positivity) (by positivity),
      Real.rpow_neg (by positivity)]
    rw [div_eq_mul_inv]
  · -- the geometric term
    have hq : (0:ℝ) ≤ 1 - 1/(2*(d:ℝ)) := by
      rw [sub_nonneg, div_le_one (by linarith)]
      linarith
    have hpow : (2:ℝ) ^ m ≤ ((2:ℝ) ^ ((1:ℝ)/(2*(d:ℝ)))) ^ n := by
      have hmle : (m:ℝ) ≤ (n:ℝ) / (2*(d:ℝ)) := by
        have h1 : (m:ℝ) * (2*(d:ℝ)) ≤ (n:ℝ) := by
          have : m * (2 * d) ≤ n := Nat.div_mul_le_self n (2 * d)
          have h2 : ((m * (2*d) : ℕ) : ℝ) ≤ ((n:ℕ):ℝ) := by exact_mod_cast this
          push_cast at h2
          linarith
        rw [le_div_iff₀ (by linarith)]
        linarith
      have he : ((2:ℝ) ^ ((1:ℝ)/(2*(d:ℝ)))) ^ n = (2:ℝ) ^ ((n:ℝ)/(2*(d:ℝ))) := by
        rw [← Real.rpow_natCast ((2:ℝ) ^ ((1:ℝ)/(2*(d:ℝ)))) n, ← Real.rpow_mul (by norm_num)]
        congr 1
        field_simp
      rw [he, ← Real.rpow_natCast (2:ℝ) m]
      exact Real.rpow_le_rpow_left_iff (by norm_num) |>.mpr hmle
    have hqn : (0:ℝ) ≤ (1 - 1/(2*(d:ℝ))) ^ n := by positivity
    rw [mul_pow]
    have : (2:ℝ) ^ m * (1 - 1/(2*(d:ℝ))) ^ n
        ≤ ((2:ℝ) ^ ((1:ℝ)/(2*(d:ℝ)))) ^ n * (1 - 1/(2*(d:ℝ))) ^ n :=
      mul_le_mul_of_nonneg_right hpow hqn
    linarith

private lemma summable_step3 {d : ℕ} (hd : 3 ≤ d) :
    Summable (fun t : ℕ => stepPow (srwZ d) t 0 0) := by
  have hd0 : 0 < d := by omega
  have h1 : Summable (fun n : ℕ => ((n:ℝ)+1) ^ (-((3:ℝ)/2))) := by
    have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-((3:ℝ)/2))) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    have := (summable_nat_add_iff (f := fun n : ℕ => (n:ℝ) ^ (-((3:ℝ)/2))) 1).mpr hbase
    refine this.congr (fun n => ?_)
    push_cast
    ring_nf
  have h2 : Summable (fun n : ℕ =>
      3 * ((2:ℝ) ^ ((1:ℝ)/(2*(d:ℝ))) * (1 - 1/(2*(d:ℝ)))) ^ n) := by
    refine Summable.mul_left 3 ?_
    refine summable_geometric_of_lt_one ?_ (rho_lt_one hd)
    have hdR : (3:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have : (0:ℝ) ≤ 1 - 1/(2*(d:ℝ)) := by
      rw [sub_nonneg, div_le_one (by linarith)]
      linarith
    positivity
  have hmaj : Summable (fun n : ℕ =>
      (4*(d:ℝ)) ^ ((3:ℝ)/2) * (((n:ℝ)+1) ^ (-((3:ℝ)/2)))
        + 3 * ((2:ℝ) ^ ((1:ℝ)/(2*(d:ℝ))) * (1 - 1/(2*(d:ℝ)))) ^ n) :=
    (h1.mul_left _).add h2
  exact Summable.of_nonneg_of_le (fun n => stepPow_nonneg d hd0 n 0 0)
    (fun n => main_bound hd n) hmaj

end Summable3

end

end MarkovMixing

open MarkovMixing

/-- **Pólya's theorem** (LPW §21.2, Examples 21.8 and 21.9), the capstone of
Chapters 20–21: simple random walk on `ℤ^d` is recurrent in dimensions
`d ≤ 2` and transient in dimensions `d ≥ 3`. -/
theorem solution :
    (∀ d : ℕ, 1 ≤ d → d ≤ 2 → Recurrent (srwZ d) (fun _ => 0)) ∧
    (∀ d : ℕ, 3 ≤ d → ¬Recurrent (srwZ d) (fun _ => 0)) := by
  constructor
  · intro d h1 h2
    have hcase : d = 1 ∨ d = 2 := by omega
    rcases hcase with rfl | rfl
    · exact ((recurrence_dichotomy (srwZ 1) (srw_stochastic 1 one_pos)
        (srw_irreducible 1 one_pos) (fun _ => 0)).1).mpr srw1_not_summable
    · exact ((recurrence_dichotomy (srwZ 2) (srw_stochastic 2 (by norm_num))
        (srw_irreducible 2 (by norm_num)) (fun _ => 0)).1).mpr srw2_not_summable
  · intro d hd hrec
    have hd0 : 0 < d := by omega
    have h := ((recurrence_dichotomy (srwZ d) (srw_stochastic d hd0)
      (srw_irreducible d hd0) (fun _ => 0)).1).mp hrec
    exact h (summable_step3 hd)
