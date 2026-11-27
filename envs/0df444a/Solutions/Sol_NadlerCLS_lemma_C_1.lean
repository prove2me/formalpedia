-- Prove2me | solution 1 for NadlerCLS.lemma_C_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:20:42.244802+00:00
-- url     : https://prove2.me/submissions/0a698005-fd48-4a5e-ae7d-2f2ba4edaa85

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics
import Definitions.Def_NadlerCLS_l1
import Definitions.Def_NadlerCLS_kuhnInterp

set_option autoImplicit false

namespace NadlerCLS.KuhnAux

open NadlerCLS NetworkEquilibriumCLS.LinearNash

variable {n : ℕ}

/-! ### Ranks -/

noncomputable def rk (t : Fin n → ℝ) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun k : Fin n => k < i ∧ t i ≤ t k)).card +
    (Finset.univ.filter (fun k : Fin n => i < k ∧ t i < t k)).card

def prec (t : Fin n → ℝ) (k i : Fin n) : Prop := t i < t k ∨ (t i = t k ∧ k < i)

noncomputable instance (t : Fin n → ℝ) : DecidableRel (prec t) := by
  intro a b; unfold prec; infer_instance

lemma prec_iff (t : Fin n → ℝ) (k i : Fin n) :
    prec t k i ↔ (k < i ∧ t i ≤ t k) ∨ (i < k ∧ t i < t k) := by
  unfold prec
  rcases lt_trichotomy k i with h | h | h
  · constructor
    · rintro (h1 | ⟨h1, h2⟩)
      · exact Or.inl ⟨h, h1.le⟩
      · exact Or.inl ⟨h, h1.le⟩
    · rintro (⟨_, h2⟩ | ⟨h1, _⟩)
      · rcases h2.lt_or_eq with h3 | h3
        · exact Or.inl h3
        · exact Or.inr ⟨h3, h⟩
      · exact absurd (lt_trans h h1) (lt_irrefl _)
  · subst h
    simp
  · constructor
    · rintro (h1 | ⟨_, h2⟩)
      · exact Or.inr ⟨h, h1⟩
      · exact absurd (lt_trans h h2) (lt_irrefl _)
    · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · exact absurd (lt_trans h h1) (lt_irrefl _)
      · exact Or.inl h2

lemma rk_eq (t : Fin n → ℝ) (i : Fin n) :
    rk t i = (Finset.univ.filter (fun k => prec t k i)).card := by
  classical
  unfold rk
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext k
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, prec_iff]
  · rw [Finset.disjoint_filter]
    intro k _ h1 h2
    exact lt_asymm h1.1 h2.1

lemma prec_trans (t : Fin n → ℝ) {a b c : Fin n} (h1 : prec t a b) (h2 : prec t b c) :
    prec t a c := by
  unfold prec at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨by linarith, lt_trans h1' h2'⟩

lemma prec_irrefl (t : Fin n → ℝ) (a : Fin n) : ¬ prec t a a := by
  unfold prec; simp

lemma prec_total (t : Fin n → ℝ) {a b : Fin n} (h : a ≠ b) : prec t a b ∨ prec t b a := by
  unfold prec
  rcases lt_trichotomy (t a) (t b) with h1 | h1 | h1
  · right; left; exact h1
  · rcases lt_or_gt_of_ne h with h2 | h2
    · left; right; exact ⟨h1.symm, h2⟩
    · right; right; exact ⟨h1, h2⟩
  · left; left; exact h1

lemma rk_lt_of_prec (t : Fin n → ℝ) {a b : Fin n} (h : prec t a b) : rk t a < rk t b := by
  classical
  rw [rk_eq, rk_eq]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨a, by simp [h], by simp [prec_irrefl]⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact prec_trans t hk h

lemma rk_inj (t : Fin n → ℝ) : Function.Injective (rk t) := by
  intro a b hab
  by_contra h
  rcases prec_total t h with h1 | h1
  · have := rk_lt_of_prec t h1; omega
  · have := rk_lt_of_prec t h1; omega

lemma rk_lt (t : Fin n → ℝ) (i : Fin n) : rk t i < n := by
  classical
  rw [rk_eq]
  calc (Finset.univ.filter (fun k => prec t k i)).card < (Finset.univ : Finset (Fin n)).card := by
        apply Finset.card_lt_card
        rw [Finset.filter_ssubset]
        exact ⟨i, Finset.mem_univ _, prec_irrefl t i⟩
    _ = n := by simp

lemma rk_surj (t : Fin n → ℝ) (p : ℕ) (hp : p < n) : ∃ i, rk t i = p := by
  let f : Fin n → Fin n := fun i => ⟨rk t i, rk_lt t i⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply rk_inj t
    have := congrArg Fin.val hab
    simpa [f] using this
  obtain ⟨i, hi⟩ := Finite.injective_iff_surjective.mp hf ⟨p, hp⟩
  exact ⟨i, congrArg Fin.val hi⟩

lemma rk_anti (t : Fin n → ℝ) {i k : Fin n} (h : rk t i < rk t k) : t k ≤ t i := by
  by_contra h1
  push Not at h1
  have := rk_lt_of_prec t (Or.inl h1 : prec t k i)
  omega

/-! ### Sorted values -/

noncomputable def sT (t : Fin n → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 else ∑ i, if rk t i + 1 = j then t i else 0

lemma sT_rk (t : Fin n → ℝ) (i : Fin n) : sT t (rk t i + 1) = t i := by
  unfold sT
  rw [if_neg (by omega)]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    rw [if_neg]
    intro h
    exact hk (rk_inj t (by omega))
  · simp

lemma sT_big (t : Fin n → ℝ) (j : ℕ) (hj : n < j) : sT t j = 0 := by
  unfold sT
  rw [if_neg (by omega)]
  apply Finset.sum_eq_zero
  intro i _
  have := rk_lt t i
  rw [if_neg (by omega)]

lemma sT_le (t : Fin n → ℝ) (i : Fin n) (j : ℕ) (h1 : rk t i < j) (h2 : j ≤ n) :
    sT t j ≤ t i := by
  obtain ⟨k, hk⟩ := rk_surj t (j - 1) (by omega)
  have e : j = rk t k + 1 := by omega
  rw [e, sT_rk]
  rcases (show rk t i < rk t k ∨ rk t i = rk t k by omega) with h | h
  · exact rk_anti t h
  · rw [rk_inj t h]

lemma sT_ge (t : Fin n → ℝ) (i : Fin n) (j : ℕ) (h1 : j ≤ rk t i) :
    t i ≤ sT t (j + 1) := by
  have := rk_lt t i
  obtain ⟨k, hk⟩ := rk_surj t j (by omega)
  rw [← hk, sT_rk]
  rcases (show rk t k < rk t i ∨ rk t k = rk t i by omega) with h | h
  · exact rk_anti t h
  · rw [rk_inj t h]

lemma sT_bounds (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) (j : ℕ) :
    0 ≤ sT t j ∧ sT t j ≤ 1 := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp [sT]
  rcases (show j ≤ n ∨ n < j by omega) with h' | h'
  · obtain ⟨k, hk⟩ := rk_surj t (j - 1) (by omega)
    have e : j = rk t k + 1 := by omega
    rw [e, sT_rk]
    exact ht k
  · rw [sT_big t j h']
    norm_num

lemma sT_anti (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) (j : ℕ) :
    sT t (j + 1) ≤ sT t j := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    have := (sT_bounds t ht 1).2
    simpa [sT] using this
  rcases (show j < n ∨ n ≤ j by omega) with h' | h'
  · obtain ⟨a, ha⟩ := rk_surj t (j - 1) (by omega)
    obtain ⟨b, hb⟩ := rk_surj t j h'
    have e1 : j = rk t a + 1 := by omega
    have e2 : j + 1 = rk t b + 1 := by omega
    rw [e2, sT_rk, e1, sT_rk]
    exact rk_anti t (by omega)
  · rw [sT_big t (j + 1) (by omega)]
    exact (sT_bounds t ht j).1

lemma tel (f : ℕ → ℝ) (p : ℕ) (N : ℕ) :
    ∑ j ∈ Finset.range N, (if p < j then f j - f (j + 1) else 0) =
      if p < N then f (p + 1) - f N else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    rcases lt_trichotomy p N with h | h | h
    · rw [if_pos h, if_pos h, if_pos (by omega)]; ring
    · subst h; simp
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp


/-! ### Cells -/

lemma h_pos (m : ℕ) : 0 < kuhnH m := by unfold kuhnH; positivity

lemma x_eq (m : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    x i = kuhnCorner m x i + kuhnH m * kuhnT m x i := by
  have := h_pos m
  unfold kuhnT
  field_simp
  ring

lemma xs_eq (m : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    x i * 2 ^ m = (kuhnCell m x i : ℝ) + kuhnT m x i := by
  have := x_eq m x i
  unfold kuhnCorner kuhnH at this
  rw [this]
  field_simp

lemma cell_le (m : ℕ) (x : Fin n → ℝ) (i : Fin n) : kuhnCell m x i ≤ 2 ^ m - 1 := by
  unfold kuhnCell
  split_ifs <;> omega

lemma t_bounds (m : ℕ) (x : Fin n → ℝ) (i : Fin n) (hx : 0 ≤ x i ∧ x i ≤ 1) :
    0 ≤ kuhnT m x i ∧ kuhnT m x i ≤ 1 := by
  have e := xs_eq m x i
  have hp : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  unfold kuhnCell at e
  split_ifs at e with h
  · have : x i = 0 := le_antisymm h hx.1
    rw [this] at e
    simp at e
    rw [← e]; norm_num
  · push Not at h
    set N := ⌈x i * 2 ^ m⌉₊ with hN
    have h1 : x i * 2 ^ m ≤ N := Nat.le_ceil _
    have h2 : (N : ℝ) < x i * 2 ^ m + 1 := Nat.ceil_lt_add_one (by positivity)
    have h3 : 0 < N := Nat.ceil_pos.mpr (by positivity)
    have h4 : N ≤ 2 ^ m := by
      rw [hN, Nat.ceil_le]
      push_cast
      nlinarith [hx.2]
    have h5 : min (2 ^ m - 1) (N - 1) = N - 1 := by
      apply min_eq_right
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega
    rw [h5, Nat.cast_sub (by omega)] at e
    push_cast at e
    constructor <;> linarith

/-! ### Part (i) -/

lemma rank_eq (m : ℕ) (x : Fin n → ℝ) : kuhnRank m x = rk (kuhnT m x) := rfl
lemma sorted_eq (m : ℕ) (x : Fin n → ℝ) : kuhnSortedT m x = sT (kuhnT m x) := rfl

lemma ht (m : ℕ) (x : Fin n → ℝ) (hx : InCube x) : ∀ i, 0 ≤ kuhnT m x i ∧ kuhnT m x i ≤ 1 :=
  fun i => t_bounds m x i (hx i)

lemma weight_nonneg (m : ℕ) (x : Fin n → ℝ) (hx : InCube x) (j : Fin (n + 1)) :
    0 ≤ kuhnWeight m x j := by
  unfold kuhnWeight
  rw [sorted_eq]
  linarith [sT_anti _ (ht m x hx) j.val]

lemma weight_sum (m : ℕ) (x : Fin n → ℝ) : ∑ j, kuhnWeight m x j = 1 := by
  unfold kuhnWeight
  rw [sorted_eq, Fin.sum_univ_eq_sum_range (fun j => sT (kuhnT m x) j - sT (kuhnT m x) (j + 1)),
    Finset.sum_range_sub', sT_big _ (n + 1) (by omega)]
  simp [sT]

lemma vertex_grid (m : ℕ) (x : Fin n → ℝ) (j : Fin (n + 1)) (i : Fin n) :
    kuhnVertex m x j i =
      ((kuhnCell m x i + if kuhnRank m x i < j.val then 1 else 0 : ℕ) : ℝ) * kuhnH m := by
  unfold kuhnVertex kuhnCorner
  split_ifs <;> push_cast <;> ring

lemma vertex_cube (m : ℕ) (x : Fin n → ℝ) (j : Fin (n + 1)) : InCube (kuhnVertex m x j) := by
  intro i
  rw [vertex_grid]
  have h1 := cell_le m x i
  have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hc : (kuhnCell m x i + if kuhnRank m x i < j.val then 1 else 0 : ℕ) ≤ 2 ^ m := by
    split_ifs <;> omega
  have hc' : ((kuhnCell m x i + if kuhnRank m x i < j.val then 1 else 0 : ℕ) : ℝ) ≤ 2 ^ m := by
    exact_mod_cast hc
  have := h_pos m
  constructor
  · positivity
  · unfold kuhnH at *
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    exact hc'

lemma dist_le (m : ℕ) (x : Fin n → ℝ) (hx : InCube x) (j : Fin (n + 1)) :
    l1 x (kuhnVertex m x j) ≤ (n : ℝ) * kuhnH m := by
  unfold l1
  have hh := h_pos m
  calc ∑ i, |x i - kuhnVertex m x j i| ≤ ∑ _i : Fin n, kuhnH m := by
        apply Finset.sum_le_sum
        intro i _
        have e : x i - kuhnVertex m x j i =
            kuhnH m * (kuhnT m x i - if kuhnRank m x i < j.val then 1 else 0) := by
          rw [x_eq m x i]; unfold kuhnVertex; ring
        rw [e, abs_mul, abs_of_pos hh]
        have := ht m x hx i
        have : |kuhnT m x i - if kuhnRank m x i < j.val then 1 else 0| ≤ 1 := by
          rw [abs_le]; split_ifs <;> constructor <;> linarith
        nlinarith
    _ = (n : ℝ) * kuhnH m := by simp

lemma x_combo (m : ℕ) (x : Fin n → ℝ) : x = ∑ j, kuhnWeight m x j • kuhnVertex m x j := by
  funext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have e : ∀ j : Fin (n + 1), kuhnWeight m x j * kuhnVertex m x j i =
      kuhnCorner m x i * kuhnWeight m x j + kuhnH m *
        (if kuhnRank m x i < j.val then
          sT (kuhnT m x) j.val - sT (kuhnT m x) (j.val + 1) else 0) := by
    intro j
    unfold kuhnVertex kuhnWeight
    rw [sorted_eq]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, weight_sum,
    Fin.sum_univ_eq_sum_range (fun j => if kuhnRank m x i < j then
          sT (kuhnT m x) j - sT (kuhnT m x) (j + 1) else 0) (n + 1),
    tel, rank_eq, if_pos (by have := rk_lt (kuhnT m x) i; omega), sT_rk,
    sT_big _ (n + 1) (by omega)]
  rw [x_eq m x i]
  ring

lemma interp_apply {r : ℕ} (m : ℕ) (g : (Fin n → ℝ) → (Fin r → ℝ)) (x : Fin n → ℝ) (o : Fin r) :
    kuhnInterp m g x o = ∑ j, kuhnWeight m x j * g (kuhnVertex m x j) o := by
  unfold kuhnInterp
  rw [Finset.sum_apply]
  simp

lemma interp_cube {r : ℕ} (m : ℕ) (g : (Fin n → ℝ) → (Fin r → ℝ))
    (hg : ∀ v, InCube v → InCube (g v)) (x : Fin n → ℝ) (hx : InCube x) :
    InCube (kuhnInterp m g x) := by
  intro o
  rw [interp_apply]
  have hw := weight_nonneg m x hx
  have hv : ∀ j, 0 ≤ g (kuhnVertex m x j) o ∧ g (kuhnVertex m x j) o ≤ 1 :=
    fun j => hg _ (vertex_cube m x j) o
  constructor
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (hv j).1)
  · calc ∑ j, kuhnWeight m x j * g (kuhnVertex m x j) o ≤ ∑ j, kuhnWeight m x j :=
          Finset.sum_le_sum (fun j _ => mul_le_of_le_one_right (hw j) (hv j).2)
      _ = 1 := weight_sum m x


/-! ### Part (iii) -/

lemma l1_nonneg {k : ℕ} (a b : Fin k → ℝ) : 0 ≤ l1 a b :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma interp_err {r : ℕ} (m : ℕ) (g : (Fin n → ℝ) → (Fin r → ℝ)) (x : Fin n → ℝ)
    (hx : InCube x) :
    l1 (g x) (kuhnInterp m g x) ≤ ∑ j, kuhnWeight m x j * l1 (g x) (g (kuhnVertex m x j)) := by
  have hw := weight_nonneg m x hx
  unfold l1
  calc ∑ o, |g x o - kuhnInterp m g x o|
      ≤ ∑ o, ∑ j, kuhnWeight m x j * |g x o - g (kuhnVertex m x j) o| := by
        apply Finset.sum_le_sum
        intro o _
        have e : g x o - kuhnInterp m g x o =
            ∑ j, kuhnWeight m x j * (g x o - g (kuhnVertex m x j) o) := by
          rw [interp_apply]
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, weight_sum, one_mul]
        rw [e]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_of_nonneg (hw j)]
    _ = ∑ j, kuhnWeight m x j * ∑ o, |g x o - g (kuhnVertex m x j) o| := by
        rw [Finset.sum_comm]
        simp [Finset.mul_sum]

lemma part3 {r : ℕ} (m : ℕ) (g : (Fin n → ℝ) → (Fin r → ℝ)) (lam β : ℝ) (hβ : 0 < β)
    (x : Fin n → ℝ) (hx : InCube x)
    (H : ∀ j, l1 (g x) (g (kuhnVertex m x j)) ≤ lam * (l1 x (kuhnVertex m x j)) ^ β) :
    l1 (g x) (kuhnInterp m g x) ≤ lam * ((n : ℝ) * kuhnH m) ^ β := by
  have hw := weight_nonneg m x hx
  have hh := h_pos m
  have step : l1 (g x) (kuhnInterp m g x) ≤
      ∑ j, kuhnWeight m x j * (lam * (l1 x (kuhnVertex m x j)) ^ β) :=
    (interp_err m g x hx).trans
      (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (H j) (hw j)))
  rcases le_or_gt 0 lam with hl | hl
  · refine step.trans ?_
    calc ∑ j, kuhnWeight m x j * (lam * (l1 x (kuhnVertex m x j)) ^ β)
        ≤ ∑ j, kuhnWeight m x j * (lam * ((n : ℝ) * kuhnH m) ^ β) := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ (hw j)
          apply mul_le_mul_of_nonneg_left _ hl
          exact Real.rpow_le_rpow (l1_nonneg _ _) (dist_le m x hx j) hβ.le
      _ = lam * ((n : ℝ) * kuhnH m) ^ β := by
          rw [← Finset.sum_mul, weight_sum, one_mul]
  · have hz : ∀ j, l1 x (kuhnVertex m x j) = 0 := by
      intro j
      have h1 := H j
      have h2 := l1_nonneg (g x) (g (kuhnVertex m x j))
      have h3 : 0 ≤ (l1 x (kuhnVertex m x j)) ^ β := Real.rpow_nonneg (l1_nonneg _ _) _
      have h4 : (l1 x (kuhnVertex m x j)) ^ β = 0 := by nlinarith
      exact ((Real.rpow_eq_zero_iff_of_nonneg (l1_nonneg _ _)).mp h4).1
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine step.trans (le_of_eq ?_)
      simp [hz, Real.zero_rpow hβ.ne']
    · exfalso
      let i0 : Fin n := ⟨0, hn⟩
      have hle : ∀ j, |x i0 - kuhnVertex m x j i0| ≤ 0 := by
        intro j
        rw [← hz j]
        unfold l1
        exact Finset.single_le_sum (f := fun i => |x i - kuhnVertex m x j i|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ i0)
      have a0 := hle 0
      have a1 := hle (Fin.last n)
      have hr := rk_lt (kuhnT m x) i0
      unfold kuhnVertex at a0 a1
      rw [rank_eq] at a0 a1
      simp only [Fin.val_zero, Fin.val_last, Nat.not_lt_zero, if_false, if_pos hr] at a0 a1
      have b0 := abs_nonneg (x i0 - (kuhnCorner m x i0 + kuhnH m * 0))
      have b1 := abs_nonneg (x i0 - (kuhnCorner m x i0 + kuhnH m * 1))
      have c0 : x i0 - (kuhnCorner m x i0 + kuhnH m * 0) = 0 := abs_eq_zero.mp (le_antisymm a0 b0)
      have c1 : x i0 - (kuhnCorner m x i0 + kuhnH m * 1) = 0 := abs_eq_zero.mp (le_antisymm a1 b1)
      linarith


/-! ### Part (ii): integral representation -/

open MeasureTheory

lemma ae_ne (b : ℝ) : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ b := by
  filter_upwards [(Set.countable_singleton b).ae_notMem volume] with s hs
  simpa using hs

lemma piece (f : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b) (h : ∀ s, a < s → s < b → f s = c) :
    IntervalIntegrable f volume a b ∧ ∫ s in a..b, f s = (b - a) * c := by
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc a b → f s = c := by
    filter_upwards [ae_ne b] with s hs hmem
    rw [Set.uIoc_of_le hab] at hmem
    exact h s hmem.1 (lt_of_le_of_ne hmem.2 hs)
  constructor
  · rw [intervalIntegrable_iff]
    have hc : IntegrableOn (fun _ => c) (Set.uIoc a b) volume := by
      apply integrableOn_const
      · rw [Set.uIoc_of_le hab, Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top
      · exact enorm_ne_top
    exact hc.congr_fun_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hae.mono fun s hs hm => (hs hm).symm))
  · rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const, smul_eq_mul]

lemma ceil_int (u : ℝ) :
    IntervalIntegrable (fun s : ℝ => ((⌈u - s⌉ : ℤ) : ℝ)) volume 0 1 ∧
      ∫ s in (0 : ℝ)..1, ((⌈u - s⌉ : ℤ) : ℝ) = u := by
  set k := ⌊u⌋ with hk
  set f := Int.fract u with hf
  have hf0 : 0 ≤ f := Int.fract_nonneg u
  have hf1 : f < 1 := Int.fract_lt_one u
  have hu : u = k + f := by rw [hf, Int.fract]; ring
  have p1 := piece (fun s : ℝ => ((⌈u - s⌉ : ℤ) : ℝ)) 0 f ((k : ℝ) + 1) hf0 (by
    intro s h1 h2
    have : ⌈u - s⌉ = k + 1 := by
      rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
    simp only [this]; push_cast; ring)
  have p2 := piece (fun s : ℝ => ((⌈u - s⌉ : ℤ) : ℝ)) f 1 (k : ℝ) hf1.le (by
    intro s h1 h2
    have : ⌈u - s⌉ = k := by
      rw [Int.ceil_eq_iff]; constructor <;> linarith
    simp only [this])
  refine ⟨p1.1.trans p2.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals p1.1 p2.1, p1.2, p2.2, hu]
  ring

lemma ceil_diff (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => |((⌈a - s⌉ : ℤ) : ℝ) - ((⌈b - s⌉ : ℤ) : ℝ)|) volume 0 1 ∧
      ∫ s in (0 : ℝ)..1, |((⌈a - s⌉ : ℤ) : ℝ) - ((⌈b - s⌉ : ℤ) : ℝ)| = |a - b| := by
  have ha := ceil_int a
  have hb := ceil_int b
  rcases le_total a b with h | h
  · have e : (fun s : ℝ => |((⌈a - s⌉ : ℤ) : ℝ) - ((⌈b - s⌉ : ℤ) : ℝ)|) =
        fun s => ((⌈b - s⌉ : ℤ) : ℝ) - ((⌈a - s⌉ : ℤ) : ℝ) := by
      funext s
      have : ((⌈a - s⌉ : ℤ) : ℝ) ≤ ((⌈b - s⌉ : ℤ) : ℝ) := by
        exact_mod_cast Int.ceil_mono (by linarith)
      rw [abs_of_nonpos (by linarith)]; ring
    rw [e]
    refine ⟨hb.1.sub ha.1, ?_⟩
    rw [intervalIntegral.integral_sub hb.1 ha.1, ha.2, hb.2, abs_of_nonpos (by linarith)]
    ring
  · have e : (fun s : ℝ => |((⌈a - s⌉ : ℤ) : ℝ) - ((⌈b - s⌉ : ℤ) : ℝ)|) =
        fun s => ((⌈a - s⌉ : ℤ) : ℝ) - ((⌈b - s⌉ : ℤ) : ℝ) := by
      funext s
      have : ((⌈b - s⌉ : ℤ) : ℝ) ≤ ((⌈a - s⌉ : ℤ) : ℝ) := by
        exact_mod_cast Int.ceil_mono (by linarith)
      rw [abs_of_nonneg (by linarith)]
    rw [e]
    refine ⟨ha.1.sub hb.1, ?_⟩
    rw [intervalIntegral.integral_sub ha.1 hb.1, ha.2, hb.2, abs_of_nonneg (by linarith)]


/-- The canonical vertex at threshold `s`. -/
noncomputable def V (m : ℕ) (x : Fin n → ℝ) (s : ℝ) : Fin n → ℝ :=
  fun i => kuhnH m * ((⌈x i * 2 ^ m - s⌉ : ℤ) : ℝ)

lemma V_eq (m : ℕ) (x : Fin n → ℝ) (hx : InCube x) (j : Fin (n + 1)) (s : ℝ)
    (h1 : sT (kuhnT m x) (j.val + 1) < s) (h2 : s < sT (kuhnT m x) j.val) :
    V m x s = kuhnVertex m x j := by
  have hb := ht m x hx
  have hT := sT_bounds (kuhnT m x) hb
  have s0 : 0 < s := lt_of_le_of_lt (hT (j.val + 1)).1 h1
  have s1 : s < 1 := lt_of_lt_of_le h2 (hT j.val).2
  funext i
  unfold V kuhnVertex kuhnCorner
  rw [xs_eq, rank_eq]
  split_ifs with hr
  · have hle := sT_le (kuhnT m x) i j.val hr (by omega)
    have : ⌈(kuhnCell m x i : ℝ) + kuhnT m x i - s⌉ = (kuhnCell m x i : ℤ) + 1 := by
      rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith [(hb i).2]
    rw [this]; push_cast; ring
  · have hge := sT_ge (kuhnT m x) i j.val (by omega)
    have : ⌈(kuhnCell m x i : ℝ) + kuhnT m x i - s⌉ = (kuhnCell m x i : ℤ) := by
      rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith [(hb i).1]
    rw [this]; push_cast; ring

lemma interp_integral {r : ℕ} (m : ℕ) (g : (Fin n → ℝ) → (Fin r → ℝ)) (x : Fin n → ℝ)
    (hx : InCube x) (o : Fin r) :
    IntervalIntegrable (fun s => g (V m x s) o) volume 0 1 ∧
      ∫ s in (0 : ℝ)..1, g (V m x s) o = kuhnInterp m g x o := by
  have hb := ht m x hx
  set T := sT (kuhnT m x) with hTdef
  have hP : ∀ j : Fin (n + 1),
      IntervalIntegrable (fun s => g (V m x s) o) volume (T (j.val + 1)) (T j.val) ∧
      ∫ s in T (j.val + 1)..T j.val, g (V m x s) o =
        (T j.val - T (j.val + 1)) * g (kuhnVertex m x j) o := by
    intro j
    apply piece _ _ _ _ (sT_anti _ hb j.val)
    intro s h1 h2
    rw [V_eq m x hx j s h1 h2]
  have hT0 : T 0 = 1 := by simp [hTdef, sT]
  have hTn : T (n + 1) = 0 := sT_big _ _ (by omega)
  have hI : ∀ k < n + 1, IntervalIntegrable (fun s => g (V m x s) o) volume (T k) (T (k + 1)) :=
    fun k hk => (hP ⟨k, hk⟩).1.symm
  have hint := IntervalIntegrable.trans_iterate hI
  rw [hT0, hTn] at hint
  refine ⟨hint.symm, ?_⟩
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hI
  rw [hT0, hTn] at hsum
  rw [intervalIntegral.integral_symm 1 0, ← hsum, Finset.sum_range, interp_apply,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_symm, (hP j).2]
  unfold kuhnWeight
  rw [sorted_eq]
  ring

lemma V_cube (m : ℕ) (x : Fin n → ℝ) (hx : InCube x) (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    InCube (V m x s) := by
  intro i
  unfold V
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have hxi := hx i
  have c0 : (0 : ℤ) ≤ ⌈x i * 2 ^ m - s⌉ := by
    rw [Int.le_ceil_iff]; push_cast; nlinarith
  have c1 : ((⌈x i * 2 ^ m - s⌉ : ℤ) : ℝ) ≤ 2 ^ m := by
    have : ⌈x i * 2 ^ m - s⌉ ≤ (2 ^ m : ℤ) := by
      rw [Int.ceil_le]; push_cast; nlinarith
    exact_mod_cast this
  have c0' : (0 : ℝ) ≤ ((⌈x i * 2 ^ m - s⌉ : ℤ) : ℝ) := by exact_mod_cast c0
  unfold kuhnH
  constructor
  · positivity
  · rw [← div_eq_inv_mul, div_le_one hp]; exact c1

lemma pointwise {r : ℕ} (m : ℕ) (g : (Fin n → ℝ) → (Fin r → ℝ))
    (hg : ∀ v, InCube v → InCube (g v)) (x y : Fin n → ℝ) (hx : InCube x) (hy : InCube y)
    (o : Fin r) (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    |g (V m x s) o - g (V m y s) o| ≤
      ∑ i, |((⌈x i * 2 ^ m - s⌉ : ℤ) : ℝ) - ((⌈y i * 2 ^ m - s⌉ : ℤ) : ℝ)| := by
  have hsum0 : 0 ≤ ∑ i, |((⌈x i * 2 ^ m - s⌉ : ℤ) : ℝ) - ((⌈y i * 2 ^ m - s⌉ : ℤ) : ℝ)| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  by_cases hV : V m x s = V m y s
  · rw [hV, sub_self, abs_zero]; exact hsum0
  · obtain ⟨i, hi⟩ : ∃ i, V m x s i ≠ V m y s i := by
      by_contra hc; push Not at hc; exact hV (funext hc)
    have hne : ⌈x i * 2 ^ m - s⌉ ≠ ⌈y i * 2 ^ m - s⌉ := by
      intro he; apply hi; unfold V; rw [he]
    have h1i : (1 : ℝ) ≤ |((⌈x i * 2 ^ m - s⌉ : ℤ) : ℝ) - ((⌈y i * 2 ^ m - s⌉ : ℤ) : ℝ)| := by
      have := Int.one_le_abs (sub_ne_zero.mpr hne)
      exact_mod_cast this
    have hle := Finset.single_le_sum
      (f := fun i => |((⌈x i * 2 ^ m - s⌉ : ℤ) : ℝ) - ((⌈y i * 2 ^ m - s⌉ : ℤ) : ℝ)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have gx := hg _ (V_cube m x hx s h0 h1) o
    have gy := hg _ (V_cube m y hy s h0 h1) o
    have : |g (V m x s) o - g (V m y s) o| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    linarith

lemma part2 {r : ℕ} (m : ℕ) (g : (Fin n → ℝ) → (Fin r → ℝ))
    (hg : ∀ v, InCube v → InCube (g v)) (x y : Fin n → ℝ) (hx : InCube x) (hy : InCube y) :
    l1 (kuhnInterp m g x) (kuhnInterp m g y) ≤ (r : ℝ) / kuhnH m * l1 x y := by
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have key : ∀ o, |kuhnInterp m g x o - kuhnInterp m g y o| ≤ 2 ^ m * l1 x y := by
    intro o
    obtain ⟨ix, ex⟩ := interp_integral m g x hx o
    obtain ⟨iy, ey⟩ := interp_integral m g y hy o
    have hD : ∀ i ∈ (Finset.univ : Finset (Fin n)), IntervalIntegrable
        (fun s : ℝ => |((⌈x i * 2 ^ m - s⌉ : ℤ) : ℝ) - ((⌈y i * 2 ^ m - s⌉ : ℤ) : ℝ)|) volume 0 1 :=
      fun i _ => (ceil_diff _ _).1
    have hDi : IntervalIntegrable (fun s : ℝ =>
        ∑ i, |((⌈x i * 2 ^ m - s⌉ : ℤ) : ℝ) - ((⌈y i * 2 ^ m - s⌉ : ℤ) : ℝ)|) volume 0 1 := by
      have := IntervalIntegrable.sum Finset.univ hD
      rw [Finset.sum_fn] at this
      exact this
    rw [← ex, ← ey, ← intervalIntegral.integral_sub ix iy, ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ hDi).trans (le_of_eq ?_)
    · filter_upwards [ae_ne 1] with s hs hmem
      rw [Real.norm_eq_abs]
      exact pointwise m g hg x y hx hy o s hmem.1 (lt_of_le_of_ne hmem.2 hs)
    · rw [intervalIntegral.integral_finsetSum hD]
      unfold l1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [(ceil_diff _ _).2, ← sub_mul, abs_mul, abs_of_pos hp]
      ring
  unfold l1
  calc ∑ o, |kuhnInterp m g x o - kuhnInterp m g y o| ≤ ∑ _o : Fin r, 2 ^ m * l1 x y :=
        Finset.sum_le_sum (fun o _ => key o)
    _ = (r : ℝ) / kuhnH m * ∑ i, |x i - y i| := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        unfold kuhnH l1
        field_simp

end NadlerCLS.KuhnAux

open NadlerCLS NetworkEquilibriumCLS.LinearNash in
theorem solution (n r m : ℕ) (hm : 1 ≤ m) (g : (Fin n → ℝ) → (Fin r → ℝ))
    (hg : ∀ v, InCube v → InCube (g v)) :
    (∀ x : Fin n → ℝ, InCube x →
      (∀ j, 0 ≤ kuhnWeight m x j) ∧ ∑ j, kuhnWeight m x j = 1 ∧
      (∀ j i, ∃ c : ℕ, c ≤ 2 ^ m ∧ kuhnVertex m x j i = (c : ℝ) * kuhnH m) ∧
      (∀ j, l1 x (kuhnVertex m x j) ≤ (n : ℝ) * kuhnH m) ∧
      x = ∑ j, kuhnWeight m x j • kuhnVertex m x j ∧
      InCube (kuhnInterp m g x)) ∧
    (∀ x y : Fin n → ℝ, InCube x → InCube y →
      l1 (kuhnInterp m g x) (kuhnInterp m g y) ≤ (r : ℝ) / kuhnH m * l1 x y) ∧
    (∀ lam β : ℝ, 0 < β → β ≤ 1 → ∀ x : Fin n → ℝ, InCube x →
      (∀ j, l1 (g x) (g (kuhnVertex m x j)) ≤ lam * (l1 x (kuhnVertex m x j)) ^ β) →
      l1 (g x) (kuhnInterp m g x) ≤ lam * ((n : ℝ) * kuhnH m) ^ β) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    refine ⟨KuhnAux.weight_nonneg m x hx, KuhnAux.weight_sum m x, ?_,
      KuhnAux.dist_le m x hx, KuhnAux.x_combo m x, KuhnAux.interp_cube m g hg x hx⟩
    intro j i
    refine ⟨_, ?_, KuhnAux.vertex_grid m x j i⟩
    have h1 := KuhnAux.cell_le m x i
    have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    split_ifs <;> omega
  · intro x y hx hy
    exact KuhnAux.part2 m g hg x y hx hy
  · intro lam β hβ _ x hx H
    exact KuhnAux.part3 m g lam β hβ x hx H
