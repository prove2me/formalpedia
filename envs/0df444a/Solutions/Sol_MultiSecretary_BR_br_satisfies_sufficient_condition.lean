-- Prove2me | solution 1 for MultiSecretary.BR.br_satisfies_sufficient_condition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T02:02:15.196828+00:00
-- url     : https://prove2.me/submissions/1f7bf94e-bf02-4074-ad2c-6994fd814f76

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model
import Definitions.Def_MultiSecretary_BR_Policy

set_option autoImplicit false

namespace MultiSecretary.BR

open Finset

variable {m : ℕ} (I : Instance m)

/-! ### Expectation helpers -/

theorem cs_E_add {n : ℕ} (g h : (Fin n → Fin m) → ℝ) :
    I.E (fun x => g x + h x) = I.E g + I.E h := by
  unfold Instance.E; rw [← Finset.sum_add_distrib]; congr 1; ext x; ring

theorem cs_E_sub {n : ℕ} (g h : (Fin n → Fin m) → ℝ) :
    I.E (fun x => g x - h x) = I.E g - I.E h := by
  unfold Instance.E; rw [← Finset.sum_sub_distrib]; congr 1; ext x; ring

theorem cs_E_cmul {n : ℕ} (c : ℝ) (g : (Fin n → Fin m) → ℝ) :
    I.E (fun x => c * g x) = c * I.E g := by
  unfold Instance.E; rw [Finset.mul_sum]; congr 1; ext x; ring

theorem cs_E_sum {n : ℕ} {ι : Type} (s : Finset ι) (g : ι → (Fin n → Fin m) → ℝ) :
    I.E (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, I.E (g i) := by
  unfold Instance.E; simp_rw [Finset.mul_sum]; exact Finset.sum_comm

theorem cs_weight_nonneg {n : ℕ} (x : Fin n → Fin m) : 0 ≤ I.weight x := by
  unfold Instance.weight; exact Finset.prod_nonneg (fun t _ => (I.f_pos _).le)

theorem cs_E_mono {n : ℕ} (g h : (Fin n → Fin m) → ℝ) (hgh : ∀ x, g x ≤ h x) :
    I.E g ≤ I.E h := by
  unfold Instance.E
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hgh x) (cs_weight_nonneg I x))

theorem cs_E_prod {n : ℕ} (G : Fin n → Fin m → ℝ) :
    I.E (fun x => ∏ s, G s (x s)) = ∏ s, ∑ j, I.f j * G s j := by
  unfold Instance.E Instance.weight
  rw [Fintype.prod_sum]
  congr 1; ext x; rw [← Finset.prod_mul_distrib]

theorem cs_E_const {n : ℕ} (c : ℝ) : I.E (fun _ : Fin n → Fin m => c) = c := by
  have h := cs_E_prod I (n := n) (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one, I.f_sum] at h
  have h2 := cs_E_cmul I (n := n) c (fun _ => 1)
  simp only [mul_one] at h2
  rw [h2, h]; ring

theorem cs_weight_update {n : ℕ} (x : Fin n → Fin m) (v : Fin n) (w : Fin m) :
    I.weight x * I.f w = I.f (x v) * I.weight (Function.update x v w) := by
  unfold Instance.weight
  rw [← Finset.mul_prod_erase univ (fun t => I.f (x t)) (mem_univ v),
      ← Finset.mul_prod_erase univ (fun t => I.f (Function.update x v w t)) (mem_univ v)]
  have : ∏ t ∈ univ.erase v, I.f (Function.update x v w t) = ∏ t ∈ univ.erase v, I.f (x t) := by
    refine Finset.prod_congr rfl (fun t ht => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]
  rw [this, Function.update_self]; ring

/-- Tower property: integrate out coordinate `v`. -/
theorem cs_tower {n : ℕ} (v : Fin n) (G : (Fin n → Fin m) → ℝ) :
    I.E G = I.E (fun x => ∑ w, I.f w * G (Function.update x v w)) := by
  unfold Instance.E
  simp_rw [Finset.mul_sum]
  have h1 : ∀ x w, I.weight x * (I.f w * G (Function.update x v w)) =
      I.f (x v) * (I.weight (Function.update x v w) * G (Function.update x v w)) := by
    intro x w; rw [← mul_assoc, cs_weight_update I x v w]; ring
  simp_rw [h1]
  rw [← Fintype.sum_prod_type' (fun x w => I.f (x v) *
      (I.weight (Function.update x v w) * G (Function.update x v w)))]
  let e : (Fin n → Fin m) × Fin m ≃ (Fin n → Fin m) × Fin m :=
    { toFun := fun p => (Function.update p.1 v p.2, p.1 v)
      invFun := fun q => (Function.update q.1 v q.2, q.1 v)
      left_inv := fun p => by simp
      right_inv := fun q => by simp }
  have hE := Fintype.sum_equiv e (fun p : (Fin n → Fin m) × Fin m => I.f (p.1 v) *
      (I.weight (Function.update p.1 v p.2) * G (Function.update p.1 v p.2)))
    (fun q => I.f q.2 * (I.weight q.1 * G q.1)) (fun p => rfl)
  rw [hE]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul, I.f_sum, one_mul]

/-! ### Thresholds -/

theorem cs_f_ge (j : Fin m) : 2 * I.eps ≤ I.f j := by
  unfold Instance.eps
  have : univ.inf' ⟨I.top, mem_univ _⟩ I.f ≤ I.f j := Finset.inf'_le I.f (mem_univ j)
  linarith

theorem cs_eps_pos : 0 < I.eps := by
  unfold Instance.eps
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' (s := univ) ⟨I.top, mem_univ _⟩ I.f
  rw [hj]; linarith [I.f_pos j]

theorem cs_f_le_one (j : Fin m) : I.f j ≤ 1 := by
  rw [← I.f_sum]
  exact Finset.single_le_sum (fun i _ => (I.f_pos i).le) (mem_univ j)

theorem cs_eps_le : I.eps ≤ 1 / 2 := by
  have := cs_f_ge I I.top; have := cs_f_le_one I I.top; linarith

theorem cs_m_le (ε : ℝ) (hε : I.eps = ε) : (m : ℝ) * (2 * ε) ≤ 1 := by
  rw [← I.f_sum, ← hε]
  have : ∑ _j : Fin m, 2 * I.eps ≤ ∑ j, I.f j := Finset.sum_le_sum (fun j _ => cs_f_ge I j)
  simpa using this

theorem cs_surv_nonneg (j : Fin m) : 0 ≤ I.survival j := by
  unfold Instance.survival; exact Finset.sum_nonneg (fun i _ => (I.f_pos i).le)

theorem cs_surv_add (j : Fin m) :
    I.survival j + I.f j = ∑ i ∈ univ.filter (fun i => i ≤ j), I.f i := by
  unfold Instance.survival
  have : univ.filter (fun i : Fin m => i ≤ j) = insert j (univ.filter (fun i => i < j)) := by
    ext i; simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro h; rcases lt_or_eq_of_le h with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · exact le_of_eq h
      · exact le_of_lt h
  rw [this, Finset.sum_insert (by simp)]; ring

theorem cs_surv_add_le_one (j : Fin m) : I.survival j + I.f j ≤ 1 := by
  rw [cs_surv_add, ← I.f_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => (I.f_pos i).le)

theorem cs_surv_lt {i j : Fin m} (h : i < j) : I.survival i + I.f i ≤ I.survival j := by
  rw [cs_surv_add]
  unfold Instance.survival
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun l _ _ => (I.f_pos l).le)
  intro l; simp only [mem_filter, mem_univ, true_and]; intro hl; exact lt_of_le_of_lt hl h

theorem cs_T_le (j : Fin m) : I.T j ≤ I.survival j + I.f j / 2 := by
  unfold Instance.T
  split_ifs
  · linarith [cs_surv_nonneg I j, I.f_pos j]
  · exact le_rfl

theorem cs_T_eq (j : Fin m) (hj : j.val ≠ 0) : I.T j = I.survival j + I.f j / 2 := by
  unfold Instance.T; rw [if_neg hj]

theorem cs_T_zero (j : Fin m) (hj : j.val = 0) : I.T j = 0 := by
  unfold Instance.T; rw [if_pos hj]

theorem cs_T_nonneg (j : Fin m) : 0 ≤ I.T j := by
  unfold Instance.T
  split_ifs
  · exact le_rfl
  · linarith [cs_surv_nonneg I j, I.f_pos j]

theorem cs_T_le_one (j : Fin m) : I.T j + I.f j / 2 ≤ 1 := by
  linarith [cs_T_le I j, cs_surv_add_le_one I j]

theorem cs_T_gap {i j : Fin m} (h : i < j) : I.T i + I.f i / 2 + I.f j / 2 ≤ I.T j := by
  have hj : j.val ≠ 0 := by have : i.val < j.val := h; omega
  rw [cs_T_eq I j hj]
  linarith [cs_T_le I i, cs_surv_lt I h]

theorem cs_T_mono {i j : Fin m} (h : i ≤ j) : I.T i ≤ I.T j := by
  rcases lt_or_eq_of_le h with h | h
  · linarith [cs_T_gap I h, I.f_pos i, I.f_pos j]
  · rw [h]

theorem cs_T_lt {i j : Fin m} (h : i < j) : I.T i + 2 * I.eps ≤ I.T j := by
  linarith [cs_T_gap I h, cs_f_ge I i, cs_f_ge I j]

/-! ### BR index -/

theorem cs_brIndex_ge {r : ℝ} {j : Fin m} (hr : I.T j ≤ r) : j ≤ I.brIndex r := by
  unfold Instance.brIndex
  have hne : (univ.filter (fun j : Fin m => I.T j ≤ r)).Nonempty := ⟨j, by simp [hr]⟩
  rw [dif_pos hne]
  exact Finset.le_max' _ j (by simp [hr])

theorem cs_T_brIndex_le {r : ℝ} (hr : 0 ≤ r) : I.T (I.brIndex r) ≤ r := by
  unfold Instance.brIndex
  have h0 : I.T I.top ≤ r := by rw [cs_T_zero I I.top rfl]; exact hr
  have hne : (univ.filter (fun j : Fin m => I.T j ≤ r)).Nonempty := ⟨I.top, by simp [h0]⟩
  rw [dif_pos hne]
  have := Finset.max'_mem _ hne
  simp only [mem_filter, mem_univ, true_and] at this
  exact this

theorem cs_le_brIndex_iff {r : ℝ} (hr : 0 ≤ r) (j : Fin m) : j ≤ I.brIndex r ↔ I.T j ≤ r :=
  ⟨fun h => le_trans (cs_T_mono I h) (cs_T_brIndex_le I hr), fun h => cs_brIndex_ge I h⟩

/-! ### Budget -/

theorem cs_budget_zero {n k : ℕ} (x : Fin n → Fin m) : I.budget n k x 0 = k := rfl

theorem cs_budget_succ {n k : ℕ} (x : Fin n → Fin m) (t : ℕ) (h : t < n) :
    I.budget n k x (t + 1) =
      if 0 < I.budget n k x t ∧ x ⟨t, h⟩ ≤ I.brIndex (I.ratio n k x t) then
        I.budget n k x t - 1 else I.budget n k x t := by
  rw [Instance.budget, dif_pos h]; rfl

theorem cs_budget_succ_ge {n k : ℕ} (x : Fin n → Fin m) (t : ℕ) (h : ¬ t < n) :
    I.budget n k x (t + 1) = I.budget n k x t := by
  rw [Instance.budget, dif_neg h]

theorem cs_sel {n k : ℕ} (x : Fin n → Fin m) (t : Fin n) :
    I.brPolicy n k x t = true ↔
      0 < I.budget n k x t.val ∧ x t ≤ I.brIndex (I.ratio n k x t.val) := by
  unfold Instance.brPolicy; simp

theorem cs_budget_cast_succ {n k : ℕ} (x : Fin n → Fin m) (t : ℕ) (h : t < n) :
    (I.budget n k x (t + 1) : ℝ) =
      I.budget n k x t - (if I.brPolicy n k x ⟨t, h⟩ = true then 1 else 0) := by
  rw [cs_budget_succ I x t h]
  by_cases hc : 0 < I.budget n k x t ∧ x ⟨t, h⟩ ≤ I.brIndex (I.ratio n k x t)
  · have hs : I.brPolicy n k x ⟨t, h⟩ = true := (cs_sel I x ⟨t, h⟩).2 hc
    rw [if_pos hc, if_pos hs, Nat.cast_sub (Nat.succ_le_of_lt hc.1)]; push_cast; ring
  · have hs : ¬ I.brPolicy n k x ⟨t, h⟩ = true := fun h' => hc ((cs_sel I x ⟨t, h⟩).1 h')
    rw [if_neg hc, if_neg hs]; ring

theorem cs_budget_prefix {n k : ℕ} (x y : Fin n → Fin m) (t : ℕ)
    (hxy : ∀ s : Fin n, s.val < t → x s = y s) : I.budget n k x t = I.budget n k y t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (fun s hs => hxy s (by omega))
    by_cases h : t < n
    · have hr : I.ratio n k x t = I.ratio n k y t := by unfold Instance.ratio; rw [ih']
      rw [cs_budget_succ I x t h, cs_budget_succ I y t h, ih', hr, hxy ⟨t, h⟩ (by simp)]
    · rw [cs_budget_succ_ge I x t h, cs_budget_succ_ge I y t h, ih']

theorem cs_ratio_prefix {n k : ℕ} (x y : Fin n → Fin m) (t : ℕ)
    (hxy : ∀ s : Fin n, s.val < t → x s = y s) : I.ratio n k x t = I.ratio n k y t := by
  unfold Instance.ratio; rw [cs_budget_prefix I x y t hxy]

theorem cs_upd_agree {n : ℕ} (x : Fin n → Fin m) (v : Fin n) (w : Fin m) (t : ℕ)
    (ht : t ≤ v.val) : ∀ s : Fin n, s.val < t → Function.update x v w s = x s := by
  intro s hs
  have : s ≠ v := by intro h; rw [h] at hs; omega
  rw [Function.update_of_ne this]

theorem cs_budget_le_k {n k : ℕ} (x : Fin n → Fin m) (t : ℕ) : I.budget n k x t ≤ k := by
  induction t with
  | zero => exact le_of_eq rfl
  | succ t ih =>
    by_cases h : t < n
    · rw [cs_budget_succ I x t h]; split_ifs <;> omega
    · rw [cs_budget_succ_ge I x t h]; exact ih

theorem cs_budget_add_le {n k : ℕ} (hk : k ≤ n) (x : Fin n → Fin m) (t : ℕ) (ht : t ≤ n) :
    I.budget n k x t + t ≤ n := by
  induction t with
  | zero => show k + 0 ≤ n; omega
  | succ t ih =>
    have h : t < n := by omega
    have ih' := ih (by omega)
    rw [cs_budget_succ I x t h]
    split_ifs with hc
    · omega
    · by_contra hcon
      have hb : I.budget n k x t = n - t := by omega
      apply hc
      refine ⟨by omega, ?_⟩
      apply cs_brIndex_ge
      have hr : I.ratio n k x t = 1 := by
        unfold Instance.ratio
        rw [hb, Nat.cast_sub h.le]
        have : ((n:ℝ) - t) ≠ 0 := by
          have : (t:ℝ) < n := by exact_mod_cast h
          linarith
        exact div_self this
      rw [hr]; linarith [cs_T_le_one I (x ⟨t, h⟩), I.f_pos (x ⟨t, h⟩)]

theorem cs_ratio_nonneg {n k : ℕ} (x : Fin n → Fin m) (t : ℕ) (ht : t ≤ n) :
    0 ≤ I.ratio n k x t := by
  unfold Instance.ratio
  apply div_nonneg (Nat.cast_nonneg _)
  have : (t:ℝ) ≤ n := by exact_mod_cast ht
  linarith

theorem cs_ratio_le_one {n k : ℕ} (hk : k ≤ n) (x : Fin n → Fin m) (t : ℕ) (ht : t < n) :
    I.ratio n k x t ≤ 1 := by
  unfold Instance.ratio
  have h1 := cs_budget_add_le I hk x t ht.le
  have hpos : (0:ℝ) < n - t := by
    have : (t:ℝ) < n := by exact_mod_cast ht
    linarith
  rw [div_le_one hpos]
  have : ((I.budget n k x t + t : ℕ) : ℝ) ≤ n := by exact_mod_cast h1
  push_cast at this; linarith

theorem cs_budget_pos_of_ratio {n k : ℕ} (x : Fin n → Fin m) (t : ℕ)
    (h : 0 < I.ratio n k x t) : 0 < I.budget n k x t := by
  by_contra hb
  have : I.budget n k x t = 0 := by omega
  unfold Instance.ratio at h; rw [this] at h; simp at h

theorem cs_sel' {n k : ℕ} (x : Fin n → Fin m) (t : Fin n) :
    I.brPolicy n k x t = true ↔
      0 < I.budget n k x t.val ∧ I.T (x t) ≤ I.ratio n k x t.val := by
  rw [cs_sel, cs_le_brIndex_iff I (cs_ratio_nonneg I x t.val t.isLt.le)]

theorem cs_count {n k : ℕ} (x : Fin n → Fin m) (r : ℕ) (hr : r ≤ n) :
    ∑ t : Fin n, (if t.val < r ∧ I.brPolicy n k x t = true then (1:ℝ) else 0) =
      k - I.budget n k x r := by
  induction r with
  | zero => rw [cs_budget_zero]; simp
  | succ r ih =>
    have h : r < n := by omega
    have ih' := ih (by omega)
    have hpt : ∀ t : Fin n, (if t.val < r + 1 ∧ I.brPolicy n k x t = true then (1:ℝ) else 0) =
        (if t.val < r ∧ I.brPolicy n k x t = true then (1:ℝ) else 0) +
        (if t = ⟨r, h⟩ then (if I.brPolicy n k x t = true then (1:ℝ) else 0) else 0) := by
      intro t
      by_cases htr : t = ⟨r, h⟩
      · subst htr; simp
      · have : t.val ≠ r := fun h' => htr (Fin.ext h')
        by_cases hlt : t.val < r
        · simp [hlt, htr, show t.val < r + 1 by omega]
        · simp [hlt, htr, show ¬ t.val < r + 1 by omega]
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, ih', Fintype.sum_ite_eq', cs_budget_cast_succ I x r h]
    ring

theorem cs_online {n k : ℕ} : IsOnline (I.brPolicy n k) := by
  intro x y t hxy
  have hb := cs_budget_prefix I (k := k) x y t.val
    (fun s hs => hxy s (Fin.le_iff_val_le_val.mpr (le_of_lt hs)))
  have hr := cs_ratio_prefix I (k := k) x y t.val
    (fun s hs => hxy s (Fin.le_iff_val_le_val.mpr (le_of_lt hs)))
  unfold Instance.brPolicy
  rw [hb, hr, hxy t le_rfl]

theorem cs_feasible {n k : ℕ} : IsFeasible k (I.brPolicy n k) := by
  intro x
  have h := cs_count I (k := k) x n le_rfl
  have h2 : ∑ t : Fin n, (if t.val < n ∧ I.brPolicy n k x t = true then (1:ℝ) else 0) =
      ((univ.filter (fun t => I.brPolicy n k x t = true)).card : ℝ) := by
    rw [Finset.natCast_card_filter]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp [t.isLt]
  have : ((univ.filter (fun t => I.brPolicy n k x t = true)).card : ℝ) ≤ k := by
    rw [← h2, h]; linarith [(Nat.cast_nonneg (I.budget n k x n) : (0:ℝ) ≤ _)]
  exact_mod_cast this

theorem cs_mem_policies {n k : ℕ} : I.brPolicy n k ∈ policies n m k := by
  classical
  unfold policies
  convert (Finset.mem_filter (s := univ) (p := fun σ : (Fin n → Fin m) → Fin n → Bool =>
    IsOnline σ ∧ IsFeasible k σ) (a := I.brPolicy n k)).mpr
    ⟨mem_univ _, cs_online I, cs_feasible I⟩

/-! ### Stopping times -/

def csS0 (I : Instance m) (δ : ℝ) (n k : ℕ) (x : Fin n → Fin m) : Set ℕ :=
  {t : ℕ | (∃ j : Fin m, |I.ratio n k x t - I.T j| ≤ δ / 2) ∨ (n : ℝ) - 2 / δ - 1 ≤ t}

def csS (I : Instance m) (δ : ℝ) (n k : ℕ) (x : Fin n → Fin m) : Set ℕ :=
  {t : ℕ | I.tau0 δ n k x < t ∧
    ((∀ j, I.jTau0 δ n k x = some j → δ < |I.ratio n k x t - I.T j|) ∨ (n : ℝ) - 2 / δ - 1 ≤ t)}

theorem cs_tau0_def {n k : ℕ} (δ : ℝ) (x : Fin n → Fin m) :
    I.tau0 δ n k x = sInf (csS0 I δ n k x) := rfl

theorem cs_tau_def {n k : ℕ} (δ : ℝ) (x : Fin n → Fin m) :
    I.tau δ n k x = min n (sInf (csS I δ n k x)) := rfl

theorem cs_sInf_eq (Q : Set ℕ) (T : ℕ) (hT : T ∈ Q) (hmin : ∀ s < T, s ∉ Q) : sInf Q = T := by
  apply le_antisymm (Nat.sInf_le hT)
  by_contra h; push_neg at h
  exact hmin _ h (Nat.sInf_mem ⟨T, hT⟩)

theorem cs_S0_n {n k : ℕ} (δ : ℝ) (hδ : 0 < δ) (x : Fin n → Fin m) : n ∈ csS0 I δ n k x := by
  simp only [csS0, Set.mem_setOf_eq]
  right; have : 0 < 2 / δ := by positivity
  linarith

theorem cs_tau0_mem {n k : ℕ} (δ : ℝ) (hδ : 0 < δ) (x : Fin n → Fin m) :
    I.tau0 δ n k x ∈ csS0 I δ n k x := by
  rw [cs_tau0_def]; exact Nat.sInf_mem ⟨n, cs_S0_n I δ hδ x⟩

theorem cs_lt_tau0 {n k : ℕ} (δ : ℝ) (x : Fin n → Fin m) (t : ℕ) (ht : t < I.tau0 δ n k x) :
    (∀ j : Fin m, δ / 2 < |I.ratio n k x t - I.T j|) ∧ (t : ℝ) < (n : ℝ) - 2 / δ - 1 := by
  rw [cs_tau0_def] at ht
  have := Nat.notMem_of_lt_sInf ht
  simp only [csS0, Set.mem_setOf_eq, not_or, not_exists, not_le] at this
  exact this

theorem cs_S_nonempty {n k : ℕ} (δ : ℝ) (hδ : 0 < δ) (x : Fin n → Fin m) :
    (csS I δ n k x).Nonempty := by
  refine ⟨I.tau0 δ n k x + n + 1, ?_⟩
  simp only [csS, Set.mem_setOf_eq]
  refine ⟨by omega, Or.inr ?_⟩
  have : 0 < 2 / δ := by positivity
  push_cast; linarith [(Nat.cast_nonneg (I.tau0 δ n k x) : (0:ℝ) ≤ _)]

theorem cs_tau_le {n k : ℕ} (δ : ℝ) (x : Fin n → Fin m) : I.tau δ n k x ≤ n := by
  rw [cs_tau_def]; exact min_le_left _ _

theorem cs_lt_tau {n k : ℕ} (δ : ℝ) (x : Fin n → Fin m) (t : ℕ) (ht : t < I.tau δ n k x) :
    t ∉ csS I δ n k x := by
  rw [cs_tau_def] at ht
  exact Nat.notMem_of_lt_sInf (lt_of_lt_of_le ht (min_le_right _ _))

theorem cs_tau_lt_n {n k : ℕ} (δ : ℝ) (hδ : 0 < δ) (x : Fin n → Fin m)
    (h : I.tau δ n k x < n) : I.tau δ n k x ∈ csS I δ n k x := by
  have hs : sInf (csS I δ n k x) < n := by
    by_contra hc; push_neg at hc
    rw [cs_tau_def, min_eq_left hc] at h; exact lt_irrefl _ h
  rw [cs_tau_def, min_eq_right hs.le]
  exact Nat.sInf_mem (cs_S_nonempty I δ hδ x)

theorem cs_tau_stop {n k : ℕ} (δ : ℝ) (hδ : 0 < δ) (x y : Fin n → Fin m)
    (hxy : ∀ s : Fin n, s.val < I.tau δ n k x → x s = y s) :
    I.tau δ n k y = I.tau δ n k x := by
  by_cases hτ : n ≤ I.tau δ n k x
  · have : x = y := funext (fun s => hxy s (lt_of_lt_of_le s.isLt hτ))
    rw [this]
  push_neg at hτ
  have hTmem := cs_tau_lt_n I δ hδ x hτ
  have h0lt : I.tau0 δ n k x < I.tau δ n k x := by
    have h := hTmem; simp only [csS, Set.mem_setOf_eq] at h; exact h.1
  have hTmin : ∀ s < I.tau δ n k x, s ∉ csS I δ n k x := fun s hs => cs_lt_tau I δ x s hs
  have hr : ∀ t ≤ I.tau δ n k x, I.ratio n k y t = I.ratio n k x t := fun t ht =>
    (cs_ratio_prefix I x y t (fun s hs => hxy s (lt_of_lt_of_le hs ht))).symm
  have htau0 : I.tau0 δ n k y = I.tau0 δ n k x := by
    rw [cs_tau0_def I δ y]
    apply cs_sInf_eq
    · have hm := cs_tau0_mem I (k := k) δ hδ x
      simp only [csS0, Set.mem_setOf_eq] at hm ⊢
      rw [hr _ h0lt.le]; exact hm
    · intro s hs hm
      have := cs_lt_tau0 I δ x s hs
      simp only [csS0, Set.mem_setOf_eq] at hm
      rw [hr s (by omega)] at hm
      rcases hm with ⟨j, hj⟩ | hc
      · linarith [this.1 j]
      · linarith [this.2]
  have hj : I.jTau0 δ n k y = I.jTau0 δ n k x := by
    unfold Instance.jTau0
    simp only [htau0, hr _ h0lt.le]
  have hS : ∀ t ≤ I.tau δ n k x, (t ∈ csS I δ n k y ↔ t ∈ csS I δ n k x) := by
    intro t ht
    simp only [csS, Set.mem_setOf_eq, htau0, hj, hr t ht]
  have hSy : sInf (csS I δ n k y) = I.tau δ n k x := by
    apply cs_sInf_eq
    · exact (hS _ le_rfl).2 hTmem
    · intro s hs hm; exact hTmin s hs ((hS s hs.le).1 hm)
  rw [cs_tau_def I δ y, hSy]; exact min_eq_right hτ.le

/-! ### Ratio dynamics -/

theorem cs_jump {n k : ℕ} (hk : k ≤ n) (x : Fin n → Fin m) (δ : ℝ) (hδ : 0 < δ) (t : ℕ)
    (ht : (t:ℝ) ≤ n - 2 / δ - 1) : |I.ratio n k x (t+1) - I.ratio n k x t| ≤ δ / 2 := by
  have hδ2 : 0 < 2 / δ := by positivity
  have htn : t < n := by
    have : (t:ℝ) < n := by linarith
    exact_mod_cast this
  have h0 := cs_ratio_nonneg I (k := k) x t htn.le
  have h1 := cs_ratio_le_one I hk x t htn
  have hb := cs_budget_cast_succ I (k := k) x t htn
  have hN : (2/δ) ≤ (n:ℝ) - t - 1 := by linarith
  have hNpos : 0 < (n:ℝ) - t - 1 := by linarith
  have hne1 : (n:ℝ) - t ≠ 0 := by linarith
  have hne2 : (n:ℝ) - (t + 1) ≠ 0 := by linarith
  set s : ℝ := (if I.brPolicy n k x ⟨t, htn⟩ = true then 1 else 0) with hs
  have hs01 : s = 0 ∨ s = 1 := by rw [hs]; split_ifs <;> simp
  have key : I.ratio n k x (t+1) - I.ratio n k x t =
      (I.ratio n k x t - s) / ((n:ℝ) - t - 1) := by
    have e1 : I.ratio n k x (t+1) = ((I.budget n k x t : ℝ) - s) / ((n:ℝ) - (t + 1)) := by
      unfold Instance.ratio; rw [hb]; push_cast; ring
    have e2 : I.ratio n k x t = (I.budget n k x t : ℝ) / ((n:ℝ) - t) := rfl
    rw [e1, e2]
    have hne3 : (n:ℝ) - t - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
  have habs : |I.ratio n k x t - s| ≤ 1 := by
    rw [abs_le]; rcases hs01 with h | h <;> rw [h] <;> constructor <;> linarith
  have : 1 ≤ δ / 2 * ((n:ℝ) - t - 1) := by
    have := mul_le_mul_of_nonneg_left hN (by linarith : (0:ℝ) ≤ δ/2)
    rw [show δ / 2 * (2 / δ) = 1 by field_simp] at this
    linarith
  linarith

theorem cs_ratio_zero {n k : ℕ} (x : Fin n → Fin m) : I.ratio n k x 0 = (k : ℝ) / n := by
  unfold Instance.ratio; rw [cs_budget_zero]; simp

theorem cs_action_le {n k : ℕ} : I.T (I.actionIndex n k) ≤ (k : ℝ) / n := by
  unfold Instance.actionIndex
  split_ifs with h
  · have := Finset.max'_mem _ h
    simp only [mem_filter, mem_univ, true_and] at this
    linarith [cs_T_le I ((univ.filter (fun j : Fin m =>
      I.survival j + I.f j / 2 ≤ (k : ℝ) / n)).max' h)]
  · rw [cs_T_zero I I.top rfl]; positivity

theorem cs_action_next {n k : ℕ} (j : Fin m) (hj : I.actionIndex n k < j) :
    (k : ℝ) / n < I.T j := by
  have hj0 : j.val ≠ 0 := by
    have : (I.actionIndex n k).val < j.val := hj
    omega
  rw [cs_T_eq I j hj0]
  by_contra hc; push_neg at hc
  have hmem : j ∈ univ.filter (fun j : Fin m => I.survival j + I.f j / 2 ≤ (k : ℝ) / n) := by
    simp [hc]
  have hne : (univ.filter (fun j : Fin m => I.survival j + I.f j / 2 ≤ (k : ℝ) / n)).Nonempty :=
    ⟨j, hmem⟩
  have hle := Finset.le_max' _ j hmem
  unfold Instance.actionIndex at hj
  rw [dif_pos hne] at hj
  exact absurd hle (not_le.mpr hj)

theorem cs_interval {n k : ℕ} (hk : k ≤ n) (δ : ℝ) (hδ : 0 < δ) (x : Fin n → Fin m) :
    ∀ t, t ≤ I.tau0 δ n k x → t < n →
      I.T (I.actionIndex n k) ≤ I.ratio n k x t ∧
      ∀ j, I.actionIndex n k < j → I.ratio n k x t < I.T j := by
  intro t
  induction t with
  | zero =>
    intro _ _
    rw [cs_ratio_zero]
    exact ⟨cs_action_le I, fun j hj => cs_action_next I j hj⟩
  | succ t ih =>
    intro ht hn
    have htl : t < I.tau0 δ n k x := by omega
    obtain ⟨hfar, hc⟩ := cs_lt_tau0 I δ x t htl
    obtain ⟨h1, h2⟩ := ih (by omega) (by omega)
    have hjump := cs_jump I hk x δ hδ t hc.le
    rw [abs_le] at hjump
    refine ⟨?_, fun j hj => ?_⟩
    · have hf := hfar (I.actionIndex n k)
      rw [lt_abs] at hf
      rcases hf with h | h <;> linarith
    · have hf := hfar j
      rw [lt_abs] at hf
      have h2j := h2 j hj
      rcases hf with h | h <;> linarith

theorem cs_band {n k : ℕ} (hk : k ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδε : δ < I.eps)
    (x : Fin n → Fin m) :
    (∀ t, t < I.tau δ n k x → t < n →
        I.T (I.actionIndex n k) - δ ≤ I.ratio n k x t ∧
        ∀ j, I.actionIndex n k < j → I.ratio n k x t < I.T j) ∨
    (∀ t, t < I.tau δ n k x → t < n →
        I.T (I.actionIndex n k) ≤ I.ratio n k x t ∧ 0 < I.ratio n k x t ∧
        ∀ j : Fin m, (I.actionIndex n k).val + 1 < j.val → I.ratio n k x t < I.T j) := by
  have hINT := cs_interval I hk δ hδ x
  have heps := cs_eps_pos I
  have hafter : ∀ t, I.tau0 δ n k x < t → t < I.tau δ n k x →
      ¬ ((∀ j, I.jTau0 δ n k x = some j → δ < |I.ratio n k x t - I.T j|) ∨
        (n : ℝ) - 2 / δ - 1 ≤ t) := by
    intro t h1 h2 hc
    exact cs_lt_tau I δ x t h2 (by simp only [csS, Set.mem_setOf_eq]; exact ⟨h1, hc⟩)
  set j0 := I.actionIndex n k with hj0
  cases hJ : I.jTau0 δ n k x with
  | none =>
    left
    intro t ht hn
    have htle : t ≤ I.tau0 δ n k x := by
      by_contra hc; push_neg at hc
      exact hafter t hc ht (Or.inl (fun j hj => by rw [hJ] at hj; cases hj))
    obtain ⟨a, b⟩ := hINT t htle hn
    exact ⟨by linarith, b⟩
  | some j =>
    have hdef : (I.tau0 δ n k x : ℝ) < (n : ℝ) - 2 / δ - 1 ∧
        |I.ratio n k x (I.tau0 δ n k x) - I.T j| ≤ δ / 2 := by
      unfold Instance.jTau0 at hJ
      split_ifs at hJ with hc
      · refine ⟨hc.1, ?_⟩
        have hmem := Finset.min'_mem _ hc.2
        rw [Option.some_inj] at hJ
        rw [hJ] at hmem
        simp only [mem_filter, mem_univ, true_and] at hmem
        exact hmem
    obtain ⟨hτ0c, hτ0j⟩ := hdef
    have hτ0n : I.tau0 δ n k x < n := by
      have : (I.tau0 δ n k x : ℝ) < n := by linarith [show (0:ℝ) < 2 / δ by positivity]
      exact_mod_cast this
    obtain ⟨hA1, hA2⟩ := hINT _ le_rfl hτ0n
    have hband : ∀ t, I.tau0 δ n k x < t → t < I.tau δ n k x →
        |I.ratio n k x t - I.T j| ≤ δ := by
      intro t h1 h2
      have := hafter t h1 h2
      push_neg at this
      obtain ⟨⟨j', hj', hle⟩, _⟩ := this
      rw [hJ, Option.some_inj] at hj'
      rw [hj']; exact hle
    rw [abs_le] at hτ0j
    have hjge : j0 ≤ j := by
      by_contra hc; push_neg at hc
      have := cs_T_lt I hc
      linarith
    rcases lt_or_eq_of_le hjge with hlt | heq
    · have hjv : j.val = j0.val + 1 := by
        by_contra hne
        have hv : j0.val + 1 < j.val := by
          have : j0.val < j.val := hlt
          omega
        have hj1m : j0.val + 1 < m := by have := j.isLt; omega
        have h1 : j0 < (⟨j0.val + 1, hj1m⟩ : Fin m) := by
          show j0.val < j0.val + 1; omega
        have h2 : (⟨j0.val + 1, hj1m⟩ : Fin m) < j := by
          show j0.val + 1 < j.val; exact hv
        have := cs_T_lt I h2
        have := hA2 _ h1
        linarith
      right
      intro t ht hn
      have hTj : I.T j0 + 2 * I.eps ≤ I.T j := cs_T_lt I hlt
      have hT0 := cs_T_nonneg I j0
      rcases lt_trichotomy t (I.tau0 δ n k x) with h | h | h
      · obtain ⟨a, b⟩ := hINT t h.le hn
        have hfar := (cs_lt_tau0 I δ x t h).1 I.top
        rw [cs_T_zero I I.top rfl, sub_zero, abs_of_nonneg (cs_ratio_nonneg I x t hn.le)] at hfar
        refine ⟨a, by linarith, fun j' hj' => b j' ?_⟩
        show j0.val < j'.val; omega
      · subst h
        refine ⟨hA1, by linarith, fun j' hj' => hA2 j' ?_⟩
        show j0.val < j'.val; omega
      · have hb := hband t h ht
        rw [abs_le] at hb
        refine ⟨by linarith, by linarith, fun j' hj' => ?_⟩
        have hjj : j < j' := by show j.val < j'.val; omega
        have := cs_T_lt I hjj
        linarith
    · left
      intro t ht hn
      rcases le_or_gt t (I.tau0 δ n k x) with h | h
      · obtain ⟨a, b⟩ := hINT t h hn
        exact ⟨by linarith, b⟩
      · have hb := hband t h ht
        rw [abs_le, ← heq] at hb
        refine ⟨by linarith, fun j' hj' => ?_⟩
        have := cs_T_lt I hj'
        linarith

/-! ### Counting -/

theorem cs_fiber {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (S : Finset (Fin m))
    (x : Fin n → Fin m) :
    ∑ j ∈ S, ∑ t, (if P t ∧ x t = j then (1 : ℝ) else 0) =
      ∑ t, if P t ∧ x t ∈ S then (1:ℝ) else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  by_cases hP : P t
  · simp [hP]
  · simp [hP]

theorem cs_Z_cast {n : ℕ} (r : ℕ) (j : Fin m) (x : Fin n → Fin m) :
    (Z r j x : ℝ) = ∑ t, if t.val < r ∧ x t = j then (1 : ℝ) else 0 := by
  unfold Z; rw [Finset.natCast_card_filter]

theorem cs_on_cast {n : ℕ} (σ : (Fin n → Fin m) → Fin n → Bool) (r : ℕ) (j : Fin m)
    (x : Fin n → Fin m) :
    (onCount σ r j x : ℝ) =
      ∑ t, if (t.val < r ∧ σ x t = true) ∧ x t = j then (1 : ℝ) else 0 := by
  unfold onCount; rw [Finset.natCast_card_filter]; simp only [and_assoc]

theorem cs_cast_tsub (k b : ℕ) : ((k - b : ℕ) : ℝ) = max ((k : ℝ) - b) 0 := by
  rcases le_total b k with h | h
  · rw [Nat.cast_sub h, max_eq_left (by linarith [(Nat.cast_le (α := ℝ)).2 h])]
  · rw [Nat.sub_eq_zero_of_le h, max_eq_right (by linarith [(Nat.cast_le (α := ℝ)).2 h])]; simp

theorem cs_off_cast {n : ℕ} (k r : ℕ) (j : Fin m) (x : Fin n → Fin m) :
    (offCount k r j x : ℝ) =
      min (Z r j x : ℝ) (max ((k : ℝ) - ∑ i ∈ univ.filter (fun i => i < j), (Z r i x : ℝ)) 0) := by
  unfold offCount; rw [Nat.cast_min, cs_cast_tsub, Nat.cast_sum]

theorem cs_sumZ {n : ℕ} (r : ℕ) (j : Fin m) (x : Fin n → Fin m) :
    ∑ i ∈ univ.filter (fun i => i < j), (Z r i x : ℝ) =
      ∑ t, if t.val < r ∧ x t < j then (1 : ℝ) else 0 := by
  simp_rw [cs_Z_cast]
  rw [show (∑ i ∈ univ.filter (fun i => i < j), ∑ t : Fin n,
      (if t.val < r ∧ x t = i then (1:ℝ) else 0)) =
      ∑ t, if t.val < r ∧ x t ∈ univ.filter (fun i => i < j) then (1:ℝ) else 0 from
      cs_fiber (fun t : Fin n => t.val < r) _ x]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp

theorem cs_modes {n k : ℕ} (hk : k ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδε : δ < I.eps)
    (x : Fin n → Fin m) :
    (∀ t : Fin n, t.val < I.tau δ n k x →
      (x t < I.actionIndex n k → I.brPolicy n k x t = true) ∧
      (I.brPolicy n k x t = true → x t ≤ I.actionIndex n k)) ∨
    (∀ t : Fin n, t.val < I.tau δ n k x →
      (x t ≤ I.actionIndex n k → I.brPolicy n k x t = true) ∧
      (I.brPolicy n k x t = true → (x t).val ≤ (I.actionIndex n k).val + 1)) := by
  have heps := cs_eps_pos I
  rcases cs_band I hk δ hδ hδε x with hA | hB
  · left
    intro t ht
    obtain ⟨h1, h2⟩ := hA t.val ht t.isLt
    constructor
    · intro hlt
      have hg := cs_T_lt I hlt
      have hT := cs_T_nonneg I (x t)
      have hpos : 0 < I.ratio n k x t.val := by linarith
      exact (cs_sel' I x t).2 ⟨cs_budget_pos_of_ratio I x t.val hpos, by linarith⟩
    · intro hs
      have hs' := ((cs_sel' I x t).1 hs).2
      by_contra hc; push_neg at hc
      have := h2 (x t) hc
      linarith
  · right
    intro t ht
    obtain ⟨h1, h2, h3⟩ := hB t.val ht t.isLt
    constructor
    · intro hle
      have := cs_T_mono I hle
      exact (cs_sel' I x t).2 ⟨cs_budget_pos_of_ratio I x t.val h2, by linarith⟩
    · intro hs
      have hs' := ((cs_sel' I x t).1 hs).2
      by_contra hc; push_neg at hc
      have := h3 (x t) hc
      linarith

theorem cs_count_bound {n k : ℕ} (σ : (Fin n → Fin m) → Fin n → Bool) (x : Fin n → Fin m)
    (r : ℕ) (K : ℝ) (hK : 0 ≤ K) (j0 : Fin m)
    (htot : ∑ t : Fin n, (if t.val < r ∧ σ x t = true then (1:ℝ) else 0) = k - K)
    (hmode : (∀ t : Fin n, t.val < r → (x t < j0 → σ x t = true) ∧ (σ x t = true → x t ≤ j0)) ∨
      (∀ t : Fin n, t.val < r →
        (x t ≤ j0 → σ x t = true) ∧ (σ x t = true → (x t).val ≤ j0.val + 1))) :
    ((offCount k r j0 x : ℝ) ≤ (onCount σ r j0 x : ℝ) + K) ∧
    (∀ h : j0.val + 1 < m, (offCount k r ⟨j0.val + 1, h⟩ x : ℝ) ≤
      (onCount σ r ⟨j0.val + 1, h⟩ x : ℝ) + K) := by
  have hon0 := cs_on_cast σ r j0 x
  have hoff0 := cs_off_cast k r j0 x
  rw [cs_sumZ] at hoff0
  have hon_nonneg : ∀ j, (0:ℝ) ≤ onCount σ r j x := fun j => Nat.cast_nonneg _
  rcases hmode with hA | hB
  · have hdec : ∑ t : Fin n, (if t.val < r ∧ σ x t = true then (1:ℝ) else 0) =
        ∑ t : Fin n, (if t.val < r ∧ x t < j0 then (1:ℝ) else 0) +
        ∑ t : Fin n, (if (t.val < r ∧ σ x t = true) ∧ x t = j0 then (1:ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      by_cases htr : t.val < r
      · obtain ⟨a, b⟩ := hA t htr
        rcases lt_trichotomy (x t) j0 with h | h | h
        · have := a h; simp [htr, h, this, h.ne]
        · simp [htr, h]
        · have hs : σ x t ≠ true := fun hs => absurd (b hs) (not_le.mpr h)
          simp [htr, hs, not_lt.mpr h.le, h.ne']
      · simp [htr]
    rw [← hon0, htot] at hdec
    constructor
    · rw [hoff0]
      have e : (k:ℝ) - ∑ t : Fin n, (if t.val < r ∧ x t < j0 then (1:ℝ) else 0) =
          (onCount σ r j0 x : ℝ) + K := by linarith
      rw [e]
      calc _ ≤ max ((onCount σ r j0 x : ℝ) + K) 0 := min_le_right _ _
        _ = _ := max_eq_left (by linarith [hon_nonneg j0])
    · intro h
      have hoff1 := cs_off_cast k r ⟨j0.val + 1, h⟩ x
      rw [cs_sumZ] at hoff1
      have hle : ∑ t : Fin n, (if t.val < r ∧ x t < j0 then (1:ℝ) else 0) +
          (onCount σ r j0 x : ℝ) ≤
          ∑ t : Fin n, (if t.val < r ∧ x t < ⟨j0.val + 1, h⟩ then (1:ℝ) else 0) := by
        rw [hon0, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum; intro t _
        by_cases htr : t.val < r
        · rcases lt_trichotomy (x t) j0 with h' | h' | h'
          · have h1 : x t < ⟨j0.val + 1, h⟩ := by
              show (x t).val < j0.val + 1
              have : (x t).val < j0.val := h'
              omega
            simp [htr, h', h1, h'.ne]
          · have h1 : j0 < ⟨j0.val + 1, h⟩ := by
              show j0.val < j0.val + 1
              omega
            by_cases hs : σ x t = true <;> simp [htr, h', h1, hs]
          · have h1 : ¬ x t < ⟨j0.val + 1, h⟩ := by
              show ¬ (x t).val < j0.val + 1
              have : j0.val < (x t).val := h'
              omega
            simp [htr, h1, not_lt.mpr h'.le, h'.ne']
        · simp [htr]
      rw [hoff1]
      calc _ ≤ max ((k:ℝ) - ∑ t : Fin n,
              (if t.val < r ∧ x t < ⟨j0.val + 1, h⟩ then (1:ℝ) else 0)) 0 := min_le_right _ _
        _ ≤ max K 0 := max_le_max (by linarith) le_rfl
        _ = K := max_eq_left hK
        _ ≤ _ := by linarith [hon_nonneg ⟨j0.val + 1, h⟩]
  · constructor
    · have heq : (onCount σ r j0 x : ℝ) = (Z r j0 x : ℝ) := by
        rw [hon0, cs_Z_cast]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        by_cases htr : t.val < r
        · by_cases h' : x t = j0
          · have := (hB t htr).1 (le_of_eq h')
            simp [htr, h', this]
          · simp [htr, h']
        · simp [htr]
      rw [hoff0]
      calc _ ≤ (Z r j0 x : ℝ) := min_le_left _ _
        _ = (onCount σ r j0 x : ℝ) := heq.symm
        _ ≤ _ := by linarith
    · intro h
      have hon1 := cs_on_cast σ r ⟨j0.val + 1, h⟩ x
      have hoff1 := cs_off_cast k r ⟨j0.val + 1, h⟩ x
      rw [cs_sumZ] at hoff1
      have hdec : ∑ t : Fin n, (if t.val < r ∧ σ x t = true then (1:ℝ) else 0) =
          ∑ t : Fin n, (if t.val < r ∧ x t < ⟨j0.val + 1, h⟩ then (1:ℝ) else 0) +
          ∑ t : Fin n, (if (t.val < r ∧ σ x t = true) ∧ x t = ⟨j0.val + 1, h⟩
            then (1:ℝ) else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        by_cases htr : t.val < r
        · obtain ⟨a, b⟩ := hB t htr
          rcases lt_trichotomy (x t) ⟨j0.val + 1, h⟩ with h' | h' | h'
          · have hle : x t ≤ j0 := by
              show (x t).val ≤ j0.val
              have : (x t).val < j0.val + 1 := h'
              omega
            have := a hle
            simp [htr, h', this, h'.ne]
          · simp [htr, h']
          · have hs : σ x t ≠ true := by
              intro hs
              have := b hs
              have : j0.val + 1 < (x t).val := h'
              omega
            simp [htr, hs, not_lt.mpr h'.le, h'.ne']
        · simp [htr]
      rw [← hon1, htot] at hdec
      rw [hoff1]
      have e : (k:ℝ) - ∑ t : Fin n, (if t.val < r ∧ x t < ⟨j0.val + 1, h⟩ then (1:ℝ) else 0) =
          (onCount σ r ⟨j0.val + 1, h⟩ x : ℝ) + K := by linarith
      rw [e]
      calc _ ≤ max ((onCount σ r ⟨j0.val + 1, h⟩ x : ℝ) + K) 0 := min_le_right _ _
        _ = _ := max_eq_left (by linarith [hon_nonneg ⟨j0.val + 1, h⟩])

/-! ### Exponential supermartingale -/

theorem cs_expi {ι : Type} (s : Finset ι) (p Y : ι → ℝ) (hp : ∀ w ∈ s, 0 ≤ p w)
    (hsum : ∑ w ∈ s, p w = 1) (hY : ∀ w ∈ s, |Y w| ≤ 2) (η lam : ℝ) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1/2) (hl2 : lam ≤ η / 4) (hmean : ∑ w ∈ s, p w * Y w ≤ -η) :
    ∑ w ∈ s, p w * Real.exp (lam * Y w) ≤ 1 := by
  have hb : ∀ w ∈ s, p w * Real.exp (lam * Y w) ≤ p w * (1 + lam * Y w + 4 * lam ^ 2) := by
    intro w hw
    apply mul_le_mul_of_nonneg_left _ (hp w hw)
    have hYw := hY w hw
    have h1 : |lam * Y w| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hl0]
      calc lam * |Y w| ≤ (1/2) * 2 := mul_le_mul hl1 hYw (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have h2 := Real.abs_exp_sub_one_sub_id_le h1
    have hY2 : (Y w) ^ 2 ≤ 4 := by
      have h0 := abs_nonneg (Y w)
      nlinarith [sq_abs (Y w)]
    have h3 : (lam * Y w) ^ 2 ≤ 4 * lam ^ 2 := by
      rw [mul_pow]; nlinarith [sq_nonneg lam]
    have := (abs_le.mp h2).2
    linarith
  calc ∑ w ∈ s, p w * Real.exp (lam * Y w)
      ≤ ∑ w ∈ s, p w * (1 + lam * Y w + 4 * lam ^ 2) := Finset.sum_le_sum hb
    _ = (∑ w ∈ s, p w) * (1 + 4 * lam ^ 2) + lam * ∑ w ∈ s, p w * Y w := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun w _ => by ring)
    _ ≤ 1 := by
        rw [hsum]
        have : lam * ∑ w ∈ s, p w * Y w ≤ lam * (-η) := mul_le_mul_of_nonneg_left hmean hl0
        nlinarith [mul_nonneg hl0 (by linarith : (0:ℝ) ≤ η / 4 - lam)]

noncomputable def csD (I : Instance m) (n k : ℕ) (j : Fin m) (x : Fin n → Fin m) (v : ℕ) : ℝ :=
  (I.budget n k x v : ℝ) - ((n:ℝ) - v) * I.T j

noncomputable def csSel (I : Instance m) (n k : ℕ) (x : Fin n → Fin m) (v : Fin n) : ℝ :=
  if I.brPolicy n k x v = true then 1 else 0

def csG (I : Instance m) (δ : ℝ) (n k : ℕ) (j : Fin m) (u v : ℕ) (x : Fin n → Fin m) : Prop :=
  |I.ratio n k x u - I.T j| ≤ δ / 2 ∧
    ∀ s, u < s → s < v → δ / 2 < |I.ratio n k x s - I.T j| ∧ |I.ratio n k x s - I.T j| ≤ δ

open Classical in
noncomputable def csPhi (I : Instance m) (δ lam : ℝ) (n k : ℕ) (j : Fin m) (u v : ℕ)
    (x : Fin n → Fin m) : ℝ :=
  if csG I δ n k j u v x then Real.exp (lam * (|csD I n k j x v| - δ * ((n:ℝ) - v))) else 0

theorem cs_Phi_pos {n k : ℕ} (δ lam : ℝ) (j : Fin m) (u v : ℕ) (x : Fin n → Fin m)
    (h : csG I δ n k j u v x) :
    csPhi I δ lam n k j u v x = Real.exp (lam * (|csD I n k j x v| - δ * ((n:ℝ) - v))) := by
  unfold csPhi; rw [if_pos h]

theorem cs_Phi_neg {n k : ℕ} (δ lam : ℝ) (j : Fin m) (u v : ℕ) (x : Fin n → Fin m)
    (h : ¬ csG I δ n k j u v x) : csPhi I δ lam n k j u v x = 0 := by
  unfold csPhi; rw [if_neg h]

theorem cs_Phi_nonneg {n k : ℕ} (δ lam : ℝ) (j : Fin m) (u v : ℕ) (x : Fin n → Fin m) :
    0 ≤ csPhi I δ lam n k j u v x := by
  unfold csPhi; split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem cs_D_ratio {n k : ℕ} (j : Fin m) (x : Fin n → Fin m) (v : ℕ) (hv : v < n) :
    csD I n k j x v = ((n:ℝ) - v) * (I.ratio n k x v - I.T j) := by
  unfold csD Instance.ratio
  have hne : (n:ℝ) - v ≠ 0 := by
    have : (v:ℝ) < n := by exact_mod_cast hv
    linarith
  have h2 : ((n:ℝ) - v) * ((I.budget n k x v : ℝ) / ((n:ℝ) - v)) = I.budget n k x v := by
    field_simp
  rw [mul_sub, h2]

theorem cs_D_succ {n k : ℕ} (j : Fin m) (x : Fin n → Fin m) (v : ℕ) (hv : v < n) :
    csD I n k j x (v + 1) = csD I n k j x v + I.T j - csSel I n k x ⟨v, hv⟩ := by
  unfold csD csSel; rw [cs_budget_cast_succ I x v hv]; push_cast; ring

theorem cs_D_upd {n k : ℕ} (j : Fin m) (x : Fin n → Fin m) (v : ℕ) (hv : v < n) (w : Fin m) :
    csD I n k j (Function.update x ⟨v, hv⟩ w) v = csD I n k j x v := by
  unfold csD; rw [cs_budget_prefix I _ x v (cs_upd_agree x ⟨v, hv⟩ w v le_rfl)]

theorem cs_sel_upd {n k : ℕ} (x : Fin n → Fin m) (v : ℕ) (hv : v < n) (w : Fin m) :
    I.brPolicy n k (Function.update x ⟨v, hv⟩ w) ⟨v, hv⟩ = true ↔
      0 < I.budget n k x v ∧ I.T w ≤ I.ratio n k x v := by
  rw [cs_sel']
  have hag := cs_upd_agree x ⟨v, hv⟩ w v le_rfl
  have hb : I.budget n k (Function.update x ⟨v, hv⟩ w) v = I.budget n k x v :=
    cs_budget_prefix I _ x v hag
  have hr : I.ratio n k (Function.update x ⟨v, hv⟩ w) v = I.ratio n k x v :=
    cs_ratio_prefix I _ x v hag
  show 0 < I.budget n k (Function.update x ⟨v, hv⟩ w) v ∧
      I.T (Function.update x ⟨v, hv⟩ w ⟨v, hv⟩) ≤ I.ratio n k (Function.update x ⟨v, hv⟩ w) v ↔ _
  rw [hb, hr, Function.update_self]

theorem cs_step {n k : ℕ} (hk : k ≤ n) (δ lam : ℝ) (hδ : 0 < δ) (hδε : δ < I.eps)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1/2) (hl2 : lam ≤ (I.eps - δ) / 4) (j : Fin m) (u v : ℕ)
    (huv : u < v) (hvn : v < n) (hv1 : ((v + 1 : ℕ) : ℝ) ≤ (n:ℝ) - 2 / δ - 1)
    (x : Fin n → Fin m) :
    ∑ w, I.f w * csPhi I δ lam n k j u (v + 1) (Function.update x ⟨v, hvn⟩ w) ≤
      csPhi I δ lam n k j u v x := by
  have hr : ∀ w, ∀ s, s ≤ v →
      I.ratio n k (Function.update x ⟨v, hvn⟩ w) s = I.ratio n k x s :=
    fun w s hs => cs_ratio_prefix I _ x s (cs_upd_agree x ⟨v, hvn⟩ w s hs)
  have hGupd : ∀ w, csG I δ n k j u (v+1) (Function.update x ⟨v, hvn⟩ w) ↔
      csG I δ n k j u (v+1) x := by
    intro w
    unfold csG
    rw [hr w u huv.le]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun s hs1 hs2 => ?_⟩
      have := h2 s hs1 hs2
      rwa [hr w s (by omega)] at this
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun s hs1 hs2 => ?_⟩
      rw [hr w s (by omega)]; exact h2 s hs1 hs2
  by_cases hG : csG I δ n k j u (v+1) x
  swap
  · have h0 : ∀ w, csPhi I δ lam n k j u (v + 1) (Function.update x ⟨v, hvn⟩ w) = 0 :=
      fun w => cs_Phi_neg I δ lam j u (v+1) _ (fun h => hG ((hGupd w).1 h))
    simp only [h0, mul_zero, Finset.sum_const_zero]
    exact cs_Phi_nonneg I δ lam j u v x
  have hGv : csG I δ n k j u v x := ⟨hG.1, fun s h1 h2 => hG.2 s h1 (by omega)⟩
  have hband := hG.2 v huv (by omega)
  rw [cs_Phi_pos I δ lam j u v x hGv]
  have hPhiw : ∀ w, csPhi I δ lam n k j u (v + 1) (Function.update x ⟨v, hvn⟩ w) =
      Real.exp (lam * (|csD I n k j x v + I.T j -
        csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩| -
        δ * ((n:ℝ) - ((v + 1 : ℕ) : ℝ)))) := by
    intro w
    rw [cs_Phi_pos I δ lam j u (v+1) _ ((hGupd w).2 hG), cs_D_succ I j _ v hvn,
      cs_D_upd I j x v hvn w]
  have hδ2 : 0 < 2 / δ := by positivity
  have hnv : (2:ℝ)/δ + 2 ≤ (n:ℝ) - v := by push_cast at hv1; linarith
  have hDabs : |csD I n k j x v| = ((n:ℝ) - v) * |I.ratio n k x v - I.T j| := by
    rw [cs_D_ratio I j x v hvn, abs_mul, abs_of_nonneg (by linarith)]
  have hD1 : 1 ≤ |csD I n k j x v| := by
    rw [hDabs]
    have e1 : 1 ≤ ((n:ℝ) - v) * (δ / 2) := by
      have := mul_le_mul_of_nonneg_right hnv (by linarith : (0:ℝ) ≤ δ/2)
      have e : (2 / δ + 2) * (δ / 2) = 1 + δ := by
        rw [add_mul, div_mul_div_comm, mul_comm 2 δ, div_self (by positivity)]; ring
      linarith
    have := mul_le_mul_of_nonneg_left hband.1.le (by linarith : (0:ℝ) ≤ (n:ℝ) - v)
    linarith
  have heps := cs_eps_pos I
  have hepsle := cs_eps_le I
  have hT0 := cs_T_nonneg I j
  have hT1 : I.T j ≤ 1 := by linarith [cs_T_le_one I j, I.f_pos j]
  have hs01 : ∀ w, csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩ = 0 ∨
      csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩ = 1 := by
    intro w; unfold csSel; split_ifs <;> simp
  have hsU : ∀ w, 0 < I.budget n k x v → I.T w ≤ I.ratio n k x v →
      csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩ = 1 := by
    intro w h1 h2; unfold csSel; rw [if_pos ((cs_sel_upd I x v hvn w).2 ⟨h1, h2⟩)]
  have hsL : ∀ w, csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩ = 1 →
      I.T w ≤ I.ratio n k x v := by
    intro w h; unfold csSel at h; split_ifs at h with hc
    · exact ((cs_sel_upd I x v hvn w).1 hc).2
    · norm_num at h
  set A := lam * (|csD I n k j x v| - δ * ((n:ℝ) - v)) with hA
  have hfac : ∀ (Y : Fin m → ℝ), (∀ w, lam * (|csD I n k j x v + I.T j -
        csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩| -
        δ * ((n:ℝ) - ((v + 1 : ℕ) : ℝ))) = A + lam * Y w) →
      ∑ w, I.f w * Real.exp (lam * Y w) ≤ 1 →
      ∑ w, I.f w * csPhi I δ lam n k j u (v + 1) (Function.update x ⟨v, hvn⟩ w) ≤
        Real.exp A := by
    intro Y hY hsum
    calc ∑ w, I.f w * csPhi I δ lam n k j u (v + 1) (Function.update x ⟨v, hvn⟩ w)
        = ∑ w, Real.exp A * (I.f w * Real.exp (lam * Y w)) := by
          refine Finset.sum_congr rfl (fun w _ => ?_)
          rw [hPhiw w, hY w, Real.exp_add]; ring
      _ = Real.exp A * ∑ w, I.f w * Real.exp (lam * Y w) := by rw [Finset.mul_sum]
      _ ≤ Real.exp A * 1 := mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
      _ = Real.exp A := mul_one _
  have hDne : csD I n k j x v ≠ 0 := fun h => by rw [h, abs_zero] at hD1; linarith
  rcases lt_or_gt_of_ne hDne with hneg | hpos
  · -- below the threshold
    have hrlt : I.ratio n k x v < I.T j := by
      have hneg' := hneg
      rw [cs_D_ratio I j x v hvn] at hneg'
      by_contra hc; push_neg at hc
      have : 0 ≤ ((n:ℝ) - v) * (I.ratio n k x v - I.T j) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    have hj0 : j.val ≠ 0 := by
      intro h; rw [cs_T_zero I j h] at hrlt
      linarith [cs_ratio_nonneg I (k := k) x v hvn.le]
    have hDle : csD I n k j x v ≤ -1 := by
      rw [abs_of_neg hneg] at hD1; linarith
    apply hfac (fun w => csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩ - I.T j + δ)
    · intro w
      have habs : |csD I n k j x v + I.T j - csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩| =
          |csD I n k j x v| + (csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩ - I.T j) := by
        rw [abs_of_neg hneg, abs_of_nonpos]
        · ring
        · rcases hs01 w with h | h <;> rw [h] <;> linarith
      rw [habs, hA]; push_cast; ring
    · refine cs_expi univ I.f _ (fun w _ => (I.f_pos w).le) I.f_sum ?_ (I.eps - δ) lam
        hl0 hl1 hl2 ?_
      · intro w _
        rcases hs01 w with h | h <;> rw [h] <;> rw [abs_le] <;> constructor <;> linarith
      · have hle : ∀ w, csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩ ≤
            if w < j then 1 else 0 := by
          intro w
          rcases hs01 w with h | h
          · rw [h]; split_ifs <;> norm_num
          · have := hsL w h
            have hwj : w < j := by
              by_contra hc; push_neg at hc
              have := cs_T_mono I hc; linarith
            rw [h, if_pos hwj]
        have hsum : ∑ w, I.f w * (csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩ - I.T j + δ) =
            ∑ w, I.f w * csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩ +
              (∑ w, I.f w) * (δ - I.T j) := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun w _ => by ring)
        rw [hsum, I.f_sum]
        have h2 : ∑ w, I.f w * csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩ ≤
            I.survival j := by
          unfold Instance.survival
          rw [Finset.sum_filter]
          apply Finset.sum_le_sum; intro w _
          have hw := hle w
          have hf := I.f_pos w
          split_ifs at hw ⊢ with hwj
          · nlinarith
          · have h0 : csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩ = 0 := by
              rcases hs01 w with h | h
              · exact h
              · rw [h] at hw; norm_num at hw
            rw [h0]; simp
        have h3 := cs_T_eq I j hj0
        have h4 := cs_f_ge I j
        linarith
  · -- above the threshold
    have hrgt : I.T j < I.ratio n k x v := by
      have hpos' := hpos
      rw [cs_D_ratio I j x v hvn] at hpos'
      by_contra hc; push_neg at hc
      have : ((n:ℝ) - v) * (I.ratio n k x v - I.T j) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      linarith
    have hbpos : 0 < I.budget n k x v := cs_budget_pos_of_ratio I x v (by linarith)
    have hDge : 1 ≤ csD I n k j x v := by
      rw [abs_of_pos hpos] at hD1; exact hD1
    apply hfac (fun w => I.T j - csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩ + δ)
    · intro w
      have habs : |csD I n k j x v + I.T j - csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩| =
          |csD I n k j x v| + (I.T j - csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩) := by
        rw [abs_of_pos hpos, abs_of_nonneg]
        · ring
        · rcases hs01 w with h | h <;> rw [h] <;> linarith
      rw [habs, hA]; push_cast; ring
    · refine cs_expi univ I.f _ (fun w _ => (I.f_pos w).le) I.f_sum ?_ (I.eps - δ) lam
        hl0 hl1 hl2 ?_
      · intro w _
        rcases hs01 w with h | h <;> rw [h] <;> rw [abs_le] <;> constructor <;> linarith
      · have hge : ∀ w, (if w ≤ j then (1:ℝ) else 0) ≤
            csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩ := by
          intro w
          split_ifs with hwj
          · have := cs_T_mono I hwj
            rw [hsU w hbpos (by linarith)]
          · rcases hs01 w with h | h <;> rw [h] <;> norm_num
        have hsum : ∑ w, I.f w * (I.T j - csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩ + δ) =
            (∑ w, I.f w) * (I.T j + δ) -
              ∑ w, I.f w * csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩ := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun w _ => by ring)
        rw [hsum, I.f_sum]
        have h2 : I.survival j + I.f j ≤
            ∑ w, I.f w * csSel I n k (Function.update x ⟨v, hvn⟩ w) ⟨v, hvn⟩ := by
          rw [cs_surv_add, Finset.sum_filter]
          apply Finset.sum_le_sum; intro w _
          have hw := hge w
          have hf := I.f_pos w
          split_ifs at hw ⊢ with hwj
          · nlinarith
          · have := Nat.cast_nonneg (α := ℝ) 0
            rcases hs01 w with h | h <;> rw [h] <;> linarith
        have h3 := cs_T_le I j
        have h4 := cs_f_ge I j
        linarith

theorem cs_chain {n k : ℕ} (hk : k ≤ n) (δ lam : ℝ) (hδ : 0 < δ) (hδε : δ < I.eps)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1/2) (hl2 : lam ≤ (I.eps - δ) / 4) (j : Fin m) (u : ℕ) :
    ∀ v, u + 1 ≤ v → (v : ℝ) ≤ (n:ℝ) - 2 / δ - 1 →
      I.E (fun x => csPhi I δ lam n k j u v x) ≤
        Real.exp (lam * (1 + δ)) * Real.exp (-(lam * δ / 2) * ((n:ℝ) - u)) := by
  intro v huv
  induction v, huv using Nat.le_induction with
  | base =>
    intro hv
    have hδ2 : 0 < 2 / δ := by positivity
    have hun : u < n := by
      have : (u:ℝ) < n := by push_cast at hv; linarith
      exact_mod_cast this
    rw [← cs_E_const I (n := n) (Real.exp (lam * (1 + δ)) *
      Real.exp (-(lam * δ / 2) * ((n:ℝ) - u)))]
    apply cs_E_mono
    intro x
    by_cases hG : csG I δ n k j u (u + 1) x
    · rw [cs_Phi_pos I δ lam j u (u+1) x hG, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hT0 := cs_T_nonneg I j
      have hT1 : I.T j ≤ 1 := by linarith [cs_T_le_one I j, I.f_pos j]
      have hsel : csSel I n k x ⟨u, hun⟩ = 0 ∨ csSel I n k x ⟨u, hun⟩ = 1 := by
        unfold csSel; split_ifs <;> simp
      have h1 : |csD I n k j x (u+1)| ≤ |csD I n k j x u| + 1 := by
        rw [cs_D_succ I j x u hun]
        have : |I.T j - csSel I n k x ⟨u, hun⟩| ≤ 1 := by
          rcases hsel with h | h <;> rw [h] <;> rw [abs_le] <;> constructor <;> linarith
        calc |csD I n k j x u + I.T j - csSel I n k x ⟨u, hun⟩|
            = |csD I n k j x u + (I.T j - csSel I n k x ⟨u, hun⟩)| := by ring_nf
          _ ≤ |csD I n k j x u| + |I.T j - csSel I n k x ⟨u, hun⟩| := abs_add_le _ _
          _ ≤ _ := by linarith
      have h2 : |csD I n k j x u| ≤ ((n:ℝ) - u) * (δ / 2) := by
        have hnu : (0:ℝ) ≤ (n:ℝ) - u := by
          have : (u:ℝ) < n := by exact_mod_cast hun
          linarith
        rw [cs_D_ratio I j x u hun, abs_mul, abs_of_nonneg hnu]
        exact mul_le_mul_of_nonneg_left hG.1 hnu
      have h3 : |csD I n k j x (u+1)| ≤ ((n:ℝ) - u) * (δ / 2) + 1 := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 hl0
      push_cast
      nlinarith
    · rw [cs_Phi_neg I δ lam j u (u+1) x hG]; positivity
  | succ v hv ih =>
    intro hv1
    have hδ2 : 0 < 2 / δ := by positivity
    have hvc : (v:ℝ) ≤ (n:ℝ) - 2/δ - 1 := by push_cast at hv1; linarith
    have hvn : v < n := by
      have : (v:ℝ) < n := by linarith
      exact_mod_cast this
    refine le_trans ?_ (ih hvc)
    rw [cs_tower I ⟨v, hvn⟩]
    apply cs_E_mono
    intro x
    exact cs_step I hk δ lam hδ hδε hl0 hl1 hl2 j u v (by omega) hvn hv1 x

/-! ### Exit indicators and the bound on `E[n - τ]` -/

open Classical in
noncomputable def csInd (I : Instance m) (δ : ℝ) (n k : ℕ) (j : Fin m) (u t : ℕ)
    (x : Fin n → Fin m) : ℝ :=
  if csG I δ n k j u t x ∧ δ < |I.ratio n k x t - I.T j| ∧ (t:ℝ) ≤ (n:ℝ) - 2 / δ - 1
  then 1 else 0

theorem cs_Ind_nonneg {n k : ℕ} (δ : ℝ) (j : Fin m) (u t : ℕ) (x : Fin n → Fin m) :
    0 ≤ csInd I δ n k j u t x := by
  unfold csInd; split_ifs <;> norm_num

theorem cs_Ind_le_Phi {n k : ℕ} (δ lam : ℝ) (hδ : 0 < δ) (hl0 : 0 ≤ lam) (j : Fin m)
    (u t : ℕ) (x : Fin n → Fin m) : csInd I δ n k j u t x ≤ csPhi I δ lam n k j u t x := by
  unfold csInd
  split_ifs with h
  · obtain ⟨hG, hdev, htc⟩ := h
    rw [cs_Phi_pos I δ lam j u t x hG]
    have hδ2 : 0 < 2 / δ := by positivity
    have htn : t < n := by
      have : (t:ℝ) < n := by linarith
      exact_mod_cast this
    have hnt : (0:ℝ) ≤ (n:ℝ) - t := by linarith
    rw [cs_D_ratio I j x t htn, abs_mul, abs_of_nonneg hnt]
    apply Real.one_le_exp
    apply mul_nonneg hl0
    have := mul_le_mul_of_nonneg_left hdev.le hnt
    linarith
  · exact cs_Phi_nonneg I δ lam j u t x

theorem cs_Ind_E {n k : ℕ} (hk : k ≤ n) (δ lam : ℝ) (hδ : 0 < δ) (hδε : δ < I.eps)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1/2) (hl2 : lam ≤ (I.eps - δ) / 4) (j : Fin m) (u t : ℕ)
    (hut : u < t) :
    I.E (fun x => csInd I δ n k j u t x) ≤
      Real.exp (lam * (1 + δ)) * Real.exp (-(lam * δ / 2) * ((n:ℝ) - u)) := by
  by_cases htc : (t:ℝ) ≤ (n:ℝ) - 2 / δ - 1
  · calc I.E (fun x => csInd I δ n k j u t x)
        ≤ I.E (fun x => csPhi I δ lam n k j u t x) :=
          cs_E_mono I _ _ (fun x => cs_Ind_le_Phi I δ lam hδ hl0 j u t x)
      _ ≤ _ := cs_chain I hk δ lam hδ hδε hl0 hl1 hl2 j u t hut htc
  · have h0 : ∀ x : Fin n → Fin m, csInd I δ n k j u t x = 0 := fun x => by
      unfold csInd; rw [if_neg (fun h => htc h.2.2)]
    simp_rw [h0]
    rw [cs_E_const]
    positivity

theorem cs_pathwise {n k : ℕ} (δ : ℝ) (hδ : 0 < δ) (x : Fin n → Fin m) :
    (n:ℝ) - I.tau δ n k x ≤ 2 / δ + 2 + ∑ t ∈ range n, ∑ u ∈ range t, ∑ j : Fin m,
      ((n:ℝ) - t) * csInd I δ n k j u t x := by
  have hδ2 : 0 < 2 / δ := by positivity
  have hterm : ∀ t ∈ range n, ∀ u ∈ range t, ∀ j : Fin m,
      0 ≤ ((n:ℝ) - t) * csInd I δ n k j u t x := by
    intro t ht u _ j
    have : (t:ℝ) < n := by exact_mod_cast (mem_range.mp ht)
    exact mul_nonneg (by linarith) (cs_Ind_nonneg I δ j u t x)
  have hS : 0 ≤ ∑ t ∈ range n, ∑ u ∈ range t, ∑ j : Fin m,
      ((n:ℝ) - t) * csInd I δ n k j u t x :=
    Finset.sum_nonneg (fun t ht => Finset.sum_nonneg (fun u hu =>
      Finset.sum_nonneg (fun j _ => hterm t ht u hu j)))
  by_cases h1 : (n:ℝ) - 2 / δ - 1 ≤ (I.tau δ n k x : ℝ)
  · linarith
  push_neg at h1
  have hτlt : I.tau δ n k x < n := by
    have : (I.tau δ n k x : ℝ) < n := by linarith
    exact_mod_cast this
  have hmem := cs_tau_lt_n I δ hδ x hτlt
  simp only [csS, Set.mem_setOf_eq] at hmem
  obtain ⟨h0lt, hdev⟩ := hmem
  have hdev' : ∀ j, I.jTau0 δ n k x = some j →
      δ < |I.ratio n k x (I.tau δ n k x) - I.T j| := by
    rcases hdev with h | h
    · exact h
    · exact absurd h (not_le.mpr h1)
  have h0c : (I.tau0 δ n k x : ℝ) < (n:ℝ) - 2 / δ - 1 := by
    have : (I.tau0 δ n k x : ℝ) < I.tau δ n k x := by exact_mod_cast h0lt
    linarith
  have h0mem := cs_tau0_mem I (k := k) δ hδ x
  simp only [csS0, Set.mem_setOf_eq] at h0mem
  have hne : (univ.filter (fun j : Fin m =>
      |I.ratio n k x (I.tau0 δ n k x) - I.T j| ≤ δ / 2)).Nonempty := by
    rcases h0mem with ⟨j, hj⟩ | h
    · exact ⟨j, by simp [hj]⟩
    · exact absurd h (not_le.mpr h0c)
  obtain ⟨j, hjdef⟩ : ∃ j, j = (univ.filter (fun j : Fin m =>
      |I.ratio n k x (I.tau0 δ n k x) - I.T j| ≤ δ / 2)).min' hne := ⟨_, rfl⟩
  have hJ : I.jTau0 δ n k x = some j := by
    unfold Instance.jTau0; rw [dif_pos ⟨h0c, hne⟩, hjdef]
  have hj0 : |I.ratio n k x (I.tau0 δ n k x) - I.T j| ≤ δ / 2 := by
    have := Finset.min'_mem _ hne
    rw [← hjdef] at this
    simp only [mem_filter, mem_univ, true_and] at this; exact this
  have hdevj := hdev' j hJ
  have hin : ∀ s, I.tau0 δ n k x < s → s < I.tau δ n k x →
      |I.ratio n k x s - I.T j| ≤ δ := by
    intro s h1' h2'
    have hns := cs_lt_tau I δ x s h2'
    simp only [csS, Set.mem_setOf_eq] at hns
    push_neg at hns
    obtain ⟨⟨j', hj', hle⟩, _⟩ := hns h1'
    rw [hJ, Option.some_inj] at hj'
    rw [hj']; exact hle
  obtain ⟨U, hU⟩ : ∃ U, U = (range (I.tau δ n k x)).filter (fun s =>
      I.tau0 δ n k x ≤ s ∧ |I.ratio n k x s - I.T j| ≤ δ / 2) := ⟨_, rfl⟩
  have hUne : U.Nonempty := ⟨I.tau0 δ n k x, by
    rw [hU, mem_filter, mem_range]; exact ⟨h0lt, le_rfl, hj0⟩⟩
  obtain ⟨u, hudef⟩ : ∃ u, u = U.max' hUne := ⟨_, rfl⟩
  have hu := Finset.max'_mem U hUne
  rw [← hudef, hU, mem_filter, mem_range] at hu
  obtain ⟨hut, h0u, hu2⟩ := hu
  have hG : csG I δ n k j u (I.tau δ n k x) x := by
    refine ⟨hu2, fun s hs1 hs2 => ⟨?_, hin s (by omega) hs2⟩⟩
    by_contra hc; push_neg at hc
    have hsU : s ∈ U := by
      rw [hU, mem_filter, mem_range]; exact ⟨hs2, by omega, hc⟩
    have : s ≤ u := by rw [hudef]; exact Finset.le_max' U s hsU
    omega
  have hInd : csInd I δ n k j u (I.tau δ n k x) x = 1 := by
    unfold csInd; rw [if_pos ⟨hG, hdevj, h1.le⟩]
  have hsingle : ((n:ℝ) - I.tau δ n k x) * csInd I δ n k j u (I.tau δ n k x) x ≤
      ∑ t ∈ range n, ∑ u ∈ range t, ∑ j : Fin m, ((n:ℝ) - t) * csInd I δ n k j u t x := by
    calc ((n:ℝ) - I.tau δ n k x) * csInd I δ n k j u (I.tau δ n k x) x
        ≤ ∑ j' : Fin m, ((n:ℝ) - I.tau δ n k x) * csInd I δ n k j' u (I.tau δ n k x) x :=
          Finset.single_le_sum (f := fun j' =>
            ((n:ℝ) - I.tau δ n k x) * csInd I δ n k j' u (I.tau δ n k x) x)
            (fun j' _ => hterm _ (mem_range.mpr hτlt) u (mem_range.mpr hut) j') (mem_univ j)
      _ ≤ ∑ u' ∈ range (I.tau δ n k x), ∑ j' : Fin m,
            ((n:ℝ) - I.tau δ n k x) * csInd I δ n k j' u' (I.tau δ n k x) x :=
          Finset.single_le_sum (f := fun u' => ∑ j' : Fin m,
            ((n:ℝ) - I.tau δ n k x) * csInd I δ n k j' u' (I.tau δ n k x) x)
            (fun u' hu' => Finset.sum_nonneg (fun j' _ => hterm _ (mem_range.mpr hτlt) u' hu' j'))
            (mem_range.mpr hut)
      _ ≤ _ := Finset.single_le_sum (f := fun t => ∑ u' ∈ range t, ∑ j' : Fin m,
            ((n:ℝ) - t) * csInd I δ n k j' u' t x)
            (fun t ht => Finset.sum_nonneg (fun u' hu' =>
              Finset.sum_nonneg (fun j' _ => hterm t ht u' hu' j'))) (mem_range.mpr hτlt)
  rw [hInd, mul_one] at hsingle
  linarith

theorem cs_geom_inner (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (t : ℕ) :
    ∑ u ∈ range t, q ^ (t - u) ≤ (1 - q)⁻¹ := by
  calc ∑ u ∈ range t, q ^ (t - u) ≤ ∑ u ∈ range t, q ^ (t - 1 - u) := by
        apply Finset.sum_le_sum; intro u hu
        have := mem_range.mp hu
        exact pow_le_pow_of_le_one hq0 hq1.le (by omega)
    _ = ∑ i ∈ range t, q ^ i := Finset.sum_range_reflect (fun i => q ^ i) t
    _ ≤ ∑' i : ℕ, q ^ i :=
        (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun i _ => pow_nonneg hq0 i)
    _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1

theorem cs_double_sum (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hs : Summable (fun i : ℕ => ((i:ℝ) + 1) * q ^ i)) (n : ℕ) :
    ∑ t ∈ range n, ∑ u ∈ range t, ((n:ℝ) - t) * q ^ (n - u) ≤
      (∑' i : ℕ, ((i:ℝ) + 1) * q ^ i) * (1 - q)⁻¹ := by
  have hG : 0 ≤ (1 - q)⁻¹ := inv_nonneg.mpr (by linarith)
  calc ∑ t ∈ range n, ∑ u ∈ range t, ((n:ℝ) - t) * q ^ (n - u)
      = ∑ t ∈ range n, ((n:ℝ) - t) * q ^ (n - t) * ∑ u ∈ range t, q ^ (t - u) := by
        refine Finset.sum_congr rfl (fun t ht => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun u hu => ?_)
        have htn := mem_range.mp ht
        have hut := mem_range.mp hu
        rw [show n - u = (n - t) + (t - u) by omega, pow_add]; ring
    _ ≤ ∑ t ∈ range n, ((n:ℝ) - t) * q ^ (n - t) * (1 - q)⁻¹ := by
        apply Finset.sum_le_sum; intro t ht
        have htn : (t:ℝ) < n := by exact_mod_cast mem_range.mp ht
        apply mul_le_mul_of_nonneg_left (cs_geom_inner q hq0 hq1 t)
        exact mul_nonneg (by linarith) (pow_nonneg hq0 _)
    _ = (∑ t ∈ range n, ((n:ℝ) - t) * q ^ (n - t)) * (1 - q)⁻¹ := by rw [Finset.sum_mul]
    _ ≤ (∑' i : ℕ, ((i:ℝ) + 1) * q ^ i) * (1 - q)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ hG
        calc ∑ t ∈ range n, ((n:ℝ) - t) * q ^ (n - t)
            ≤ ∑ t ∈ range n, (((n - 1 - t : ℕ) : ℝ) + 1) * q ^ (n - 1 - t) := by
              apply Finset.sum_le_sum; intro t ht
              have htn := mem_range.mp ht
              have hc : ((n - 1 - t : ℕ) : ℝ) + 1 + t = n := by
                have h : n - 1 - t + 1 + t = n := by omega
                exact_mod_cast h
              have hp : q ^ (n - t) ≤ q ^ (n - 1 - t) :=
                pow_le_pow_of_le_one hq0 hq1.le (by omega)
              rw [show (n:ℝ) - t = ((n - 1 - t : ℕ) : ℝ) + 1 by linarith]
              exact mul_le_mul_of_nonneg_left hp (by positivity)
          _ = ∑ i ∈ range n, ((i : ℝ) + 1) * q ^ i :=
              Finset.sum_range_reflect (fun i => ((i : ℝ) + 1) * q ^ i) n
          _ ≤ _ := hs.sum_le_tsum _ (fun i _ => by positivity)

theorem cs_main_bound (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (m : ℕ) (I : Instance m), I.eps = ε → ∀ n k : ℕ, k ≤ n →
      I.E (fun x : Fin n → Fin m => (n : ℝ) - I.tau δ n k x) ≤ M := by
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = min (1/2 : ℝ) ((ε - δ) / 4) := ⟨_, rfl⟩
  have hlpos : 0 < lam := by rw [hlam]; exact lt_min (by norm_num) (by linarith)
  have hl1 : lam ≤ 1/2 := by rw [hlam]; exact min_le_left _ _
  have hl2 : lam ≤ (ε - δ) / 4 := by rw [hlam]; exact min_le_right _ _
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.exp (-(lam * δ / 2)) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact (Real.exp_pos _).le
  have hq1 : q < 1 := by
    have : 0 < lam * δ := mul_pos hlpos hδ
    rw [hq]
    calc Real.exp (-(lam * δ / 2)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  obtain ⟨B0, hB0⟩ : ∃ B0 : ℝ, B0 = Real.exp (lam * (1 + δ)) := ⟨_, rfl⟩
  have hB0nn : 0 ≤ B0 := by rw [hB0]; exact (Real.exp_pos _).le
  have hsum1 : Summable (fun i : ℕ => ((i:ℝ) + 1) * q ^ i) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
    have h2 := summable_geometric_of_lt_one hq0 hq1
    exact (h1.add h2).congr (fun i => by simp only [Pi.add_apply, pow_one]; ring)
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = ∑' i : ℕ, ((i:ℝ) + 1) * q ^ i := ⟨_, rfl⟩
  have hK1nn : 0 ≤ K1 := by rw [hK1]; exact tsum_nonneg (fun i => by positivity)
  have hG1nn : 0 ≤ (1 - q)⁻¹ := inv_nonneg.mpr (by linarith)
  have hexpq : ∀ n u : ℕ, u ≤ n →
      Real.exp (-(lam * δ / 2) * ((n:ℝ) - u)) = q ^ (n - u) := by
    intro n u hu
    rw [hq, ← Real.exp_nat_mul, Nat.cast_sub hu]
    congr 1; ring
  refine ⟨2 / δ + 2 + (1 / (2 * ε)) * (B0 * (K1 * (1 - q)⁻¹)), by positivity, ?_⟩
  intro m I hI n k hk
  have hδε' : δ < I.eps := by rw [hI]; exact hδε
  have hl2' : lam ≤ (I.eps - δ) / 4 := by rw [hI]; exact hl2
  have hm : (m:ℝ) ≤ 1 / (2 * ε) := by
    have := cs_m_le I ε hI
    rw [le_div_iff₀ (by positivity)]; linarith
  have hEind : ∀ t ∈ range n, ∀ u ∈ range t, ∀ j : Fin m,
      ((n:ℝ) - t) * I.E (fun x => csInd I δ n k j u t x) ≤ ((n:ℝ) - t) * (B0 * q ^ (n - u)) := by
    intro t ht u hu j
    have htn := mem_range.mp ht
    have hut := mem_range.mp hu
    apply mul_le_mul_of_nonneg_left _ (by
      have : (t:ℝ) < n := by exact_mod_cast htn
      linarith)
    have := cs_Ind_E I hk δ lam hδ hδε' hlpos.le hl1 hl2' j u t hut
    rw [hexpq n u (by omega), ← hB0] at this
    exact this
  calc I.E (fun x => (n:ℝ) - I.tau δ n k x)
      ≤ I.E (fun x => 2 / δ + 2 + ∑ t ∈ range n, ∑ u ∈ range t, ∑ j : Fin m,
          ((n:ℝ) - t) * csInd I δ n k j u t x) :=
        cs_E_mono I _ _ (fun x => cs_pathwise I δ hδ x)
    _ = 2 / δ + 2 + ∑ t ∈ range n, ∑ u ∈ range t, ∑ j : Fin m,
          ((n:ℝ) - t) * I.E (fun x => csInd I δ n k j u t x) := by
        rw [cs_E_add, cs_E_const, cs_E_sum]
        congr 1
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [cs_E_sum]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [cs_E_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [cs_E_cmul]
    _ ≤ 2 / δ + 2 + ∑ t ∈ range n, ∑ u ∈ range t,
          (1 / (2 * ε)) * (B0 * (((n:ℝ) - t) * q ^ (n - u))) := by
        refine add_le_add le_rfl ?_
        apply Finset.sum_le_sum; intro t ht
        apply Finset.sum_le_sum; intro u hu
        have htn : (t:ℝ) < n := by exact_mod_cast mem_range.mp ht
        calc ∑ j : Fin m, ((n:ℝ) - t) * I.E (fun x => csInd I δ n k j u t x)
            ≤ ∑ _j : Fin m, ((n:ℝ) - t) * (B0 * q ^ (n - u)) :=
              Finset.sum_le_sum (fun j _ => hEind t ht u hu j)
          _ = (m:ℝ) * (((n:ℝ) - t) * (B0 * q ^ (n - u))) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ ≤ (1 / (2 * ε)) * (((n:ℝ) - t) * (B0 * q ^ (n - u))) := by
              apply mul_le_mul_of_nonneg_right hm
              exact mul_nonneg (by linarith) (mul_nonneg hB0nn (pow_nonneg hq0 _))
          _ = (1 / (2 * ε)) * (B0 * (((n:ℝ) - t) * q ^ (n - u))) := by ring
    _ = 2 / δ + 2 + (1 / (2 * ε)) * (B0 * ∑ t ∈ range n, ∑ u ∈ range t,
          ((n:ℝ) - t) * q ^ (n - u)) := by
        congr 1
        simp_rw [Finset.mul_sum]
    _ ≤ 2 / δ + 2 + (1 / (2 * ε)) * (B0 * (K1 * (1 - q)⁻¹)) := by
        have := cs_double_sum q hq0 hq1 hsum1 n
        rw [← hK1] at this
        gcongr

end MultiSecretary.BR

open MultiSecretary.BR Finset in
theorem solution (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ < ε) :
    ∃ M : ℝ, ∀ (m : ℕ) (I : Instance m), I.eps = ε → ∀ n k : ℕ, k ≤ n →
      I.brPolicy n k ∈ policies n m k ∧
      (∀ x, I.tau δ n k x ≤ n) ∧
      (∀ x y : Fin n → Fin m, (∀ s : Fin n, s.val < I.tau δ n k x → x s = y s) →
        I.tau δ n k y = I.tau δ n k x) ∧
      (∑ j ∈ univ.filter (fun j => j < I.actionIndex n k),
          I.E (fun x => (onCount (I.brPolicy n k) (I.tau δ n k x) j x : ℝ)) =
        ∑ j ∈ univ.filter (fun j => j < I.actionIndex n k),
          I.E (fun x => (Z (I.tau δ n k x) j x : ℝ))) ∧
      (I.E (fun x => (offCount k (I.tau δ n k x) (I.actionIndex n k) x : ℝ)) - M ≤
        I.E (fun x => (onCount (I.brPolicy n k) (I.tau δ n k x) (I.actionIndex n k) x : ℝ))) ∧
      (∀ h : (I.actionIndex n k).val + 1 < m,
        I.E (fun x => (offCount k (I.tau δ n k x) ⟨(I.actionIndex n k).val + 1, h⟩ x : ℝ)) - M ≤
        I.E (fun x =>
          (onCount (I.brPolicy n k) (I.tau δ n k x) ⟨(I.actionIndex n k).val + 1, h⟩ x : ℝ))) ∧
      ((n : ℝ) - M ≤ I.E (fun x : Fin n → Fin m => (I.tau δ n k x : ℝ))) := by
  obtain ⟨M, _, hM⟩ := cs_main_bound ε δ hε hδ hδε
  refine ⟨M, fun m I hI n k hk => ?_⟩
  have hδε' : δ < I.eps := by rw [hI]; exact hδε
  have hEτ := hM m I hI n k hk
  have hK : ∀ x : Fin n → Fin m,
      (I.budget n k x (I.tau δ n k x) : ℝ) ≤ (n:ℝ) - I.tau δ n k x := by
    intro x
    have h := cs_budget_add_le I hk x _ (cs_tau_le I (k := k) δ x)
    have : ((I.budget n k x (I.tau δ n k x) + I.tau δ n k x : ℕ) : ℝ) ≤ n := by exact_mod_cast h
    push_cast at this; linarith
  have hcounts := fun x : Fin n → Fin m => cs_count_bound (k := k) (I.brPolicy n k) x
    (I.tau δ n k x) (I.budget n k x (I.tau δ n k x)) (Nat.cast_nonneg _) (I.actionIndex n k)
    (cs_count I (k := k) x _ (cs_tau_le I (k := k) δ x)) (cs_modes I hk δ hδ hδε' x)
  refine ⟨cs_mem_policies I, fun x => cs_tau_le I δ x,
    fun x y hxy => cs_tau_stop I δ hδ x y hxy, ?_, ?_, ?_, ?_⟩
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [mem_filter, mem_univ, true_and] at hj
    congr 1; funext x
    have hacc : ∀ t : Fin n, t.val < I.tau δ n k x → x t < I.actionIndex n k →
        I.brPolicy n k x t = true := by
      intro t ht hlt
      rcases cs_modes I hk δ hδ hδε' x with hA | hB
      · exact (hA t ht).1 hlt
      · exact (hB t ht).1 hlt.le
    rw [cs_on_cast, cs_Z_cast]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases h1 : t.val < I.tau δ n k x
    · by_cases h2 : x t = j
      · have := hacc t h1 (by rw [h2]; exact hj)
        simp [h1, h2, this]
      · simp [h1, h2]
    · simp [h1]
  · have h1 : I.E (fun x => (offCount k (I.tau δ n k x) (I.actionIndex n k) x : ℝ)) ≤
        I.E (fun x => (onCount (I.brPolicy n k) (I.tau δ n k x) (I.actionIndex n k) x : ℝ) +
          ((n:ℝ) - I.tau δ n k x)) :=
      cs_E_mono I _ _ (fun x => le_trans (hcounts x).1 (by linarith [hK x]))
    rw [cs_E_add] at h1
    linarith
  · intro h
    have h1 : I.E (fun x => (offCount k (I.tau δ n k x) ⟨(I.actionIndex n k).val + 1, h⟩ x : ℝ)) ≤
        I.E (fun x => (onCount (I.brPolicy n k) (I.tau δ n k x)
          ⟨(I.actionIndex n k).val + 1, h⟩ x : ℝ) + ((n:ℝ) - I.tau δ n k x)) :=
      cs_E_mono I _ _ (fun x => le_trans ((hcounts x).2 h) (by linarith [hK x]))
    rw [cs_E_add] at h1
    linarith
  · have : I.E (fun x : Fin n → Fin m => (n:ℝ) - I.tau δ n k x) =
        n - I.E (fun x : Fin n → Fin m => (I.tau δ n k x : ℝ)) := by
      rw [cs_E_sub, cs_E_const]
    linarith
