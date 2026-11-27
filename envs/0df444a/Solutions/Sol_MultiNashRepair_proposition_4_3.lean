-- Prove2me | solution 1 for MultiNashRepair.proposition_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:22:57.718517+00:00
-- url     : https://prove2.me/submissions/917ef1c7-b9a1-42e7-a7b7-f6a9e74e4460

import Mathlib
import Definitions.Def_NashAmplification_Filtering_Model
import Definitions.Def_MultiNashRepair_IDRH
import Theorems.Thm_MultiNashRepair_controls_5_7
import Theorems.Thm_MultiNashRepair_lemma_5_11
import Theorems.Thm_MultiNashRepair_lemma_5_1
import Theorems.Thm_MultiNashRepair_lemma_5_3
import Theorems.Thm_MultiNashRepair_lemma_5_5
import Theorems.Thm_MultiNashRepair_lemma_5_6
import Theorems.Thm_MultiNashRepair_lemma_5_12

open NashAmplification.Filtering (Mixed Utility Tuple BoundedGame)
open Finset
open MultiNashRepair



theorem MNR51_pp_update {m : ℕ} {n : Fin m → ℕ} (y : Mixed n) (j : Fin m)
    (w : Fin (n j) → ℝ) (s : Tuple n) :
    AGT.profileProb (Function.update y j w) s = w (s j) * ∏ k ∈ univ.erase j, y k (s k) := by
  unfold AGT.profileProb
  rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (ne_of_mem_erase hk)]

theorem MNR51_sum_pp {m : ℕ} {n : Fin m → ℕ} (y : Mixed n) (hy : AGT.IsMixedProfile y) :
    ∑ s : Tuple n, AGT.profileProb y s = 1 := by
  unfold AGT.profileProb
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one (fun j _ => (hy j).2)

theorem MNR51_xp_apply {m : ℕ} {n : Fin m → ℕ} (x : Mixed n) (η : ℝ)
    (z : (j : Fin m) → Fin (n j) → ℝ) (j : Fin m) (c : Fin (n j)) :
    descentProfile x η z j c = (1 - η * ∑ b, z j b) * x j c + η * z j c := by
  simp only [descentProfile, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  congr 1
  simp [ePure, DGPNash.WellSupported.pureStrategy]

theorem MNR51_xp_mixed {m : ℕ} {n : Fin m → ℕ} (x : Mixed n) (hx : AGT.IsMixedProfile x)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (z : (j : Fin m) → Fin (n j) → ℝ) (hz : LPFeasible z) :
    AGT.IsMixedProfile (descentProfile x η z) := by
  intro j
  have hZj : ∑ b, z j b ≤ 1 := by
    have h1 : ∑ b, z j b ≤ ∑ k, ∑ b, z k b :=
      Finset.single_le_sum (f := fun k => ∑ b, z k b)
        (fun k _ => Finset.sum_nonneg (fun b _ => hz.1 k b)) (mem_univ j)
    linarith [hz.2]
  have hZj0 : 0 ≤ ∑ b, z j b := Finset.sum_nonneg (fun b _ => hz.1 j b)
  have hc : 0 ≤ 1 - η * ∑ b, z j b := by nlinarith only [hZj, hZj0, hη0, hη1]
  constructor
  · intro c
    rw [MNR51_xp_apply]
    exact add_nonneg (mul_nonneg hc ((hx j).1 c)) (mul_nonneg hη0 (hz.1 j c))
  · simp only [MNR51_xp_apply, Finset.sum_add_distrib, ← Finset.mul_sum, (hx j).2]
    ring

theorem MNR51_ePure_lottery {m : ℕ} {n : Fin m → ℕ} {j : Fin m} (b : Fin (n j)) :
    AGT.IsLottery (ePure b) := by
  constructor
  · intro c; simp only [ePure, DGPNash.WellSupported.pureStrategy]; split_ifs <;> norm_num
  · simp [ePure, DGPNash.WellSupported.pureStrategy]

theorem MNR51_update_mixed {m : ℕ} {n : Fin m → ℕ} (x : Mixed n) (hx : AGT.IsMixedProfile x)
    (j : Fin m) (y : Fin (n j) → ℝ) (hy : AGT.IsLottery y) :
    AGT.IsMixedProfile (Function.update x j y) := by
  intro k
  by_cases hk : k = j
  · subst hk; simpa using hy
  · simpa [Function.update_of_ne hk] using hx k

theorem MNR51_cfac {m : ℕ} {n : Fin m → ℕ} (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (z : (j : Fin m) → Fin (n j) → ℝ) (hz : LPFeasible z) (j : Fin m) :
    0 ≤ 1 - η * ∑ b, z j b ∧ 1 - η * ∑ b, z j b ≤ 1 := by
  have hZj : ∑ b, z j b ≤ 1 := by
    have h1 : ∑ b, z j b ≤ ∑ k, ∑ b, z k b :=
      Finset.single_le_sum (f := fun k => ∑ b, z k b)
        (fun k _ => Finset.sum_nonneg (fun b _ => hz.1 k b)) (mem_univ j)
    linarith [hz.2]
  have hZj0 : 0 ≤ ∑ b, z j b := Finset.sum_nonneg (fun b _ => hz.1 j b)
  constructor
  · nlinarith only [hZj, hZj0, hη0, hη1]
  · nlinarith only [hZj0, hη0]

theorem MNR51_ep_bounds {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (hu : BoundedGame u)
    (x : Mixed n) (hx : AGT.IsMixedProfile x) (i : Fin m) :
    0 ≤ AGT.expectedPayoff u x i ∧ AGT.expectedPayoff u x i ≤ 1 := by
  have hp : ∀ s : Tuple n, 0 ≤ AGT.profileProb x s := fun s =>
    Finset.prod_nonneg (fun j _ => (hx j).1 (s j))
  unfold AGT.expectedPayoff
  constructor
  · exact Finset.sum_nonneg (fun s _ => mul_nonneg (hp s) (hu i s).1)
  · calc ∑ s, AGT.profileProb x s * u i s ≤ ∑ s, AGT.profileProb x s * 1 :=
          Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hu i s).2 (hp s))
      _ = 1 := by simp [MNR51_sum_pp x hx]

theorem MNR51_deficitMix_nonneg {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (hu : BoundedGame u)
    (x : Mixed n) (hx : AGT.IsMixedProfile x) (i : Fin m) (b : Fin (n i) → ℝ)
    (hb : AGT.IsLottery b) : 0 ≤ deficitMix u x i b := by
  unfold deficitMix
  have h1 := (MNR51_ep_bounds u hu _ (MNR51_update_mixed x hx i b hb) i).2
  have h2 := (MNR51_ep_bounds u hu x hx i).1
  linarith

theorem MNR53_list_fsum {m : ℕ} {n : Fin m → ℕ} {ι : Type*} (S : Finset ι) (gs : List (Gen n))
    (f : ι → Gen n → ℝ) :
    ∑ i ∈ S, (gs.map (f i)).sum = (gs.map fun g => ∑ i ∈ S, f i g).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

theorem MNR53_list_le {m : ℕ} {n : Fin m → ℕ} (gs : List (Gen n)) (f g : Gen n → ℝ)
    (h : ∀ x ∈ gs, f x ≤ g x) : (gs.map f).sum ≤ (gs.map g).sum := by
  induction gs with
  | nil => simp
  | cons a gs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (List.mem_cons_self ..)) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem MNR53_list_nonneg {m : ℕ} {n : Fin m → ℕ} (gs : List (Gen n)) (f : Gen n → ℝ)
    (h : ∀ x ∈ gs, 0 ≤ f x) : 0 ≤ (gs.map f).sum := by
  have := MNR53_list_le gs (fun _ => 0) f h
  simpa using this

theorem MNR53_list_mul {m : ℕ} {n : Fin m → ℕ} (gs : List (Gen n)) (c : ℝ) (f : Gen n → ℝ) :
    (gs.map fun g => c * f g).sum = c * (gs.map f).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem MNR53_list_sub {m : ℕ} {n : Fin m → ℕ} (gs : List (Gen n)) (f g : Gen n → ℝ) :
    (gs.map fun x => f x - g x).sum = (gs.map f).sum - (gs.map g).sum := by
  induction gs with
  | nil => simp
  | cons a gs ih => simp only [List.map_cons, List.sum_cons, ih]; ring



theorem MNRQ_cast (q : ℚ) : IsRat (q : ℝ) := ⟨q, rfl⟩
theorem MNRQ_nat (k : ℕ) : IsRat (k : ℝ) := ⟨k, by push_cast; rfl⟩
theorem MNRQ_add {a b : ℝ} (ha : IsRat a) (hb : IsRat b) : IsRat (a + b) := by
  obtain ⟨p, rfl⟩ := ha; obtain ⟨q, rfl⟩ := hb; exact ⟨p + q, by push_cast; ring⟩
theorem MNRQ_sub {a b : ℝ} (ha : IsRat a) (hb : IsRat b) : IsRat (a - b) := by
  obtain ⟨p, rfl⟩ := ha; obtain ⟨q, rfl⟩ := hb; exact ⟨p - q, by push_cast; ring⟩
theorem MNRQ_mul {a b : ℝ} (ha : IsRat a) (hb : IsRat b) : IsRat (a * b) := by
  obtain ⟨p, rfl⟩ := ha; obtain ⟨q, rfl⟩ := hb; exact ⟨p * q, by push_cast; ring⟩
theorem MNRQ_div {a b : ℝ} (ha : IsRat a) (hb : IsRat b) : IsRat (a / b) := by
  obtain ⟨p, rfl⟩ := ha; obtain ⟨q, rfl⟩ := hb; exact ⟨p / q, by push_cast; ring⟩
theorem MNRQ_pow {a : ℝ} (ha : IsRat a) (k : ℕ) : IsRat (a ^ k) := by
  obtain ⟨p, rfl⟩ := ha; exact ⟨p ^ k, by push_cast; ring⟩
theorem MNRQ_max {a b : ℝ} (ha : IsRat a) (hb : IsRat b) : IsRat (max a b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; exact ha
theorem MNRQ_one : IsRat (1 : ℝ) := ⟨1, by norm_num⟩
theorem MNRQ_zero : IsRat (0 : ℝ) := ⟨0, by norm_num⟩
theorem MNRQ_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ S, IsRat (f i)) :
    IsRat (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [MNRQ_zero]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact MNRQ_add (hf a (Finset.mem_insert_self a S)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
theorem MNRQ_prod {ι : Type*} (S : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ S, IsRat (f i)) :
    IsRat (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [MNRQ_one]
  | insert a S ha ih =>
    rw [Finset.prod_insert ha]
    exact MNRQ_mul (hf a (Finset.mem_insert_self a S)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
theorem MNRQ_iSup {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (hf : ∀ i, IsRat (f i)) :
    IsRat (⨆ i, f i) := by
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := f)
  rw [← hj]; exact hf j

theorem MNRQ_ep {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (hu : ∀ i a, IsRat (u i a)) (x : Mixed n)
    (hx : ∀ i a, IsRat (x i a)) (i : Fin m) : IsRat (AGT.expectedPayoff u x i) := by
  unfold AGT.expectedPayoff AGT.profileProb
  exact MNRQ_sum _ _ (fun s _ => MNRQ_mul (MNRQ_prod _ _ (fun j _ => hx j (s j))) (hu i s))

theorem MNRQ_ePure {m : ℕ} {n : Fin m → ℕ} {j : Fin m} (a c : Fin (n j)) : IsRat (ePure a c) := by
  simp only [ePure, DGPNash.WellSupported.pureStrategy]; split_ifs
  · exact MNRQ_one
  · exact MNRQ_zero

theorem MNRQ_update {m : ℕ} {n : Fin m → ℕ} (x : Mixed n) (hx : ∀ i a, IsRat (x i a)) (j : Fin m)
    (y : Fin (n j) → ℝ) (hy : ∀ a, IsRat (y a)) : ∀ i a, IsRat (Function.update x j y i a) := by
  intro i a
  by_cases h : i = j
  · subst h; simp only [Function.update_self]; exact hy a
  · rw [Function.update_of_ne h]; exact hx i a

theorem MNRQ_Reg {m : ℕ} {n : Fin m → ℕ} (hm : 1 ≤ m) (hn : ∀ i, 0 < n i) (u : Utility n)
    (hu : ∀ i a, IsRat (u i a)) (x : Mixed n) (hx : ∀ i a, IsRat (x i a)) :
    (∀ i a, IsRat (gain u x i a)) ∧ (∀ i, IsRat (qi u x i)) ∧ IsRat (Reg u x) ∧ IsRat (scaled u x) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hg : ∀ i a, IsRat (gain u x i a) := fun i a =>
    MNRQ_sub (MNRQ_ep u hu _ (MNRQ_update x hx i _ (fun c => MNRQ_ePure a c)) i) (MNRQ_ep u hu x hx i)
  have hr : ∀ i, IsRat (regret u x i) := fun i => by
    haveI : Nonempty (Fin (n i)) := ⟨⟨0, hn i⟩⟩
    exact MNRQ_iSup _ (hg i)
  have hR : IsRat (Reg u x) := MNRQ_iSup _ hr
  exact ⟨hg, fun i => MNRQ_sub MNRQ_one (hr i), hR, MNRQ_mul (MNRQ_nat m) (MNRQ_sub MNRQ_one hR)⟩


theorem MNR54_filter_succ {m : ℕ} (k : ℕ) (hk : k < m) :
    (univ.filter (fun j : Fin m => j.val < k + 1))
      = insert ⟨k, hk⟩ (univ.filter (fun j : Fin m => j.val < k)) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · right; exact h'
    · left; exact Fin.ext h'
  · rintro (h | h)
    · rw [h]; exact Nat.lt_succ_self k
    · exact Nat.lt_succ_of_lt h

theorem MNR54_filter_lt {m : ℕ} (i : Fin m) :
    univ.filter (fun j : Fin m => j < i) = univ.filter (fun j : Fin m => j.val < i.val) := by
  ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Fin.lt_def

theorem MNR54_filter_le {m : ℕ} (i : Fin m) :
    univ.filter (fun j : Fin m => j ≤ i) = univ.filter (fun j : Fin m => j.val < i.val + 1) := by
  ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fin.le_def, Nat.lt_succ_iff]

theorem MNR54_filter_all {m : ℕ} :
    univ.filter (fun j : Fin m => j.val < m) = univ := by
  ext j; simp [j.isLt]

/-- Telescoping for the reverse sweep: `Π_{j<k} (1 - p_j) = 1 - Σ_{j<k} δ_j`. -/
theorem MNR54_rev_tele {m : ℕ} (δ : Fin m → ℝ) (hδ0 : ∀ i, 0 ≤ δ i) (ρ : ℝ) (hρ : 0 < ρ)
    (hδ1 : ∑ i, δ i = 1 - ρ) :
    ∀ k ≤ m, ∏ j ∈ univ.filter (fun j : Fin m => j.val < k), (1 - revProb δ j)
      = 1 - ∑ j ∈ univ.filter (fun j : Fin m => j.val < k), δ j := by
  have hpos : ∀ S : Finset (Fin m), 0 < 1 - ∑ j ∈ S, δ j := by
    intro S
    have : ∑ j ∈ S, δ j ≤ ∑ j, δ j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun j _ _ => hδ0 j)
    linarith
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [MNR54_filter_succ k hk, Finset.prod_insert (by simp), Finset.sum_insert (by simp),
      ih (Nat.le_of_succ_le hk)]
    have hp : revProb δ ⟨k, hk⟩ = δ ⟨k, hk⟩ / (1 - ∑ j ∈ univ.filter (fun j : Fin m => j.val < k), δ j) := by
      unfold revProb; rw [MNR54_filter_lt]
    rw [hp]
    have := hpos (univ.filter (fun j : Fin m => j.val < k))
    field_simp; ring

/-- Telescoping for the forward sweep: `Π_{j<k} (1 - θ_j) = 1 / (1 + Σ_{j<k} e_j)`. -/
theorem MNR54_fwd_tele {m : ℕ} (e : Fin m → ℝ) (he : ∀ i, 0 ≤ e i) :
    ∀ k ≤ m, ∏ j ∈ univ.filter (fun j : Fin m => j.val < k), (1 - fwdProb e j)
      = 1 / (1 + ∑ j ∈ univ.filter (fun j : Fin m => j.val < k), e j) := by
  have hpos : ∀ S : Finset (Fin m), 0 < 1 + ∑ j ∈ S, e j := fun S => by
    have := Finset.sum_nonneg (fun j (_ : j ∈ S) => he j); linarith
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [MNR54_filter_succ k hk, Finset.prod_insert (by simp), Finset.sum_insert (by simp),
      ih (Nat.le_of_succ_le hk)]
    have hp : fwdProb e ⟨k, hk⟩ = e ⟨k, hk⟩ / (1 + (e ⟨k, hk⟩ + ∑ j ∈ univ.filter (fun j : Fin m => j.val < k), e j)) := by
      unfold fwdProb
      rw [MNR54_filter_le]
      simp only [Fin.val_mk]
      rw [MNR54_filter_succ k hk, Finset.sum_insert (by simp)]
    rw [hp]
    have h1 := hpos (univ.filter (fun j : Fin m => j.val < k))
    have h2 : 0 < 1 + (e ⟨k, hk⟩ + ∑ j ∈ univ.filter (fun j : Fin m => j.val < k), e j) := by
      linarith [he ⟨k, hk⟩]
    field_simp; ring


theorem MNR54_pp_self {m : ℕ} {n : Fin m → ℕ} (x : Mixed n) (i : Fin m) (s : Tuple n) :
    AGT.profileProb x s = x i (s i) * ∏ k ∈ univ.erase i, x k (s k) := by
  have := MNR51_pp_update x i (x i) s
  rwa [Function.update_eq_self] at this

theorem MNR54_pp_update2 {m : ℕ} {n : Fin m → ℕ} (x : Mixed n) (i j : Fin m) (hij : i ≠ j)
    (v : Fin (n i) → ℝ) (w : Fin (n j) → ℝ) (s : Tuple n) :
    AGT.profileProb (Function.update (Function.update x i v) j w) s
      = v (s i) * w (s j) * ∏ l ∈ (univ.erase i).erase j, x l (s l) := by
  rw [MNR51_pp_update]
  have hi : i ∈ univ.erase j := Finset.mem_erase.mpr ⟨hij, mem_univ i⟩
  rw [← Finset.mul_prod_erase _ _ hi]
  rw [Function.update_self, Finset.erase_right_comm]
  have : ∏ l ∈ (univ.erase i).erase j, Function.update x i v l (s l) = ∏ l ∈ (univ.erase i).erase j, x l (s l) := by
    apply Finset.prod_congr rfl; intro l hl
    rw [Function.update_of_ne (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl))]
  rw [this]; ring

theorem MNR54_actY_apply {m : ℕ} {n : Fin m → ℕ} (x b : Mixed n) (t : ℝ) (γ : Fin m → ℝ)
    (k : Fin m) (c : Fin (n k)) :
    actY x b t γ k c = (1 - t * γ k) * x k c + t * γ k * b k c := by
  simp [actY]

theorem MNR54_rev_apply {m : ℕ} {n : Fin m → ℕ} (y : Mixed n) (δ : Fin m → ℝ)
    (arev : (i : Fin m) → Fin (n i)) (k : Fin m) (c : Fin (n k)) :
    revSweep y δ arev k c = (1 - revProb δ k) * y k c + revProb δ k * ePure (arev k) c := by
  simp [revSweep]

theorem MNR54_ePure_nonneg {m : ℕ} {n : Fin m → ℕ} {j : Fin m} (a c : Fin (n j)) :
    0 ≤ (ePure a) c := (MNR51_ePure_lottery a).1 c


theorem MNR54_rev_facts {m : ℕ} (δ : Fin m → ℝ) (hδ0 : ∀ i, 0 ≤ δ i) (ρ : ℝ) (hρ : 0 < ρ)
    (hδ1 : ∑ i, δ i = 1 - ρ) :
    (∀ k, 0 ≤ revProb δ k ∧ revProb δ k < 1) ∧
    (∀ k, 0 ≤ δ k / (1 - ∑ j ∈ univ.filter (· ≤ k), δ j)) ∧
    (∀ k, (1 - revProb δ k) * (δ k / (1 - ∑ j ∈ univ.filter (· ≤ k), δ j)) = revProb δ k) ∧
    (∏ k, (1 - revProb δ k) = ρ) ∧
    (∀ i, revProb δ i * ∏ j ∈ univ.filter (· < i), (1 - revProb δ j) = δ i) := by
  have hle : ∀ S : Finset (Fin m), ∑ j ∈ S, δ j ≤ 1 - ρ := fun S => by
    rw [← hδ1]; exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun j _ _ => hδ0 j)
  -- P_{k-1} - δ_k = P_k ≥ ρ
  have hsplit : ∀ k : Fin m, ∑ j ∈ univ.filter (· ≤ k), δ j = δ k + ∑ j ∈ univ.filter (· < k), δ j := by
    intro k
    have : univ.filter (· ≤ k) = insert k (univ.filter (· < k)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h; rcases lt_or_eq_of_le h with h' | h'
        · right; exact h'
        · left; exact h'
      · rintro (h | h)
        · rw [h]
        · exact le_of_lt h
    rw [this, Finset.sum_insert (by simp)]
  have hPk : ∀ k : Fin m, ρ ≤ 1 - ∑ j ∈ univ.filter (· ≤ k), δ j := fun k => by linarith [hle (univ.filter (· ≤ k))]
  have hPk1 : ∀ k : Fin m, ρ + δ k ≤ 1 - ∑ j ∈ univ.filter (· < k), δ j := fun k => by
    have := hPk k; rw [hsplit k] at this; linarith
  have hp : ∀ k, revProb δ k = δ k / (1 - ∑ j ∈ univ.filter (· < k), δ j) := fun k => rfl
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, ?_, fun i => ?_⟩
  · have h1 := hPk1 k
    have hden : 0 < 1 - ∑ j ∈ univ.filter (· < k), δ j := by linarith [hδ0 k]
    rw [hp]
    constructor
    · exact div_nonneg (hδ0 k) hden.le
    · rw [div_lt_one hden]; linarith
  · exact div_nonneg (hδ0 k) (by linarith [hPk k])
  · have h1 := hPk1 k
    have hden : 0 < 1 - ∑ j ∈ univ.filter (· < k), δ j := by linarith [hδ0 k]
    have hden2 : 0 < 1 - ∑ j ∈ univ.filter (· ≤ k), δ j := by linarith [hPk k]
    rw [hsplit k] at hden2
    rw [hp, hsplit k]
    field_simp
    ring
  · have := MNR54_rev_tele δ hδ0 ρ hρ hδ1 m le_rfl
    rw [MNR54_filter_all] at this
    rw [this, hδ1]; ring
  · have := MNR54_rev_tele δ hδ0 ρ hρ hδ1 i.val (le_of_lt i.isLt)
    rw [← MNR54_filter_lt] at this
    rw [this, hp]
    have h1 := hPk1 i
    have hden : 0 < 1 - ∑ j ∈ univ.filter (· < i), δ j := by linarith [hδ0 i]
    field_simp


theorem MNR54_xt_mixed {m : ℕ} {n : Fin m → ℕ} (x b : Mixed n) (hx : AGT.IsMixedProfile x)
    (hb : AGT.IsMixedProfile b) (γ : Fin m → ℝ) (t : ℝ) (htγ : ∀ i, 0 ≤ t * γ i ∧ t * γ i < 1)
    (δ : Fin m → ℝ) (hδ0 : ∀ i, 0 ≤ δ i) (ρ : ℝ) (hρ : 0 < ρ) (hδ1 : ∑ i, δ i = 1 - ρ)
    (arev : (i : Fin m) → Fin (n i)) :
    AGT.IsMixedProfile (actY x b t γ) ∧ AGT.IsMixedProfile (revSweep (actY x b t γ) δ arev) := by
  obtain ⟨hp01, -, -, -, -⟩ := MNR54_rev_facts δ hδ0 ρ hρ hδ1
  have hy : AGT.IsMixedProfile (actY x b t γ) := by
    intro k
    refine ⟨fun c => ?_, ?_⟩
    · rw [MNR54_actY_apply]
      exact add_nonneg (mul_nonneg (by linarith [(htγ k).2]) ((hx k).1 c)) (mul_nonneg (htγ k).1 ((hb k).1 c))
    · simp only [MNR54_actY_apply, Finset.sum_add_distrib, ← Finset.mul_sum, (hx k).2, (hb k).2]; ring
  refine ⟨hy, fun k => ⟨fun c => ?_, ?_⟩⟩
  · rw [MNR54_rev_apply]
    exact add_nonneg (mul_nonneg (by linarith [(hp01 k).2]) ((hy k).1 c))
      (mul_nonneg (hp01 k).1 (MNR54_ePure_nonneg _ c))
  · simp only [MNR54_rev_apply, Finset.sum_add_distrib, ← Finset.mul_sum, (hy k).2,
      (MNR51_ePure_lottery (arev k)).2]; ring

theorem MNR54_list_add {m : ℕ} {n : Fin m → ℕ} (gs : List (Gen n)) (f g : Gen n → ℝ) :
    (gs.map fun x => f x + g x).sum = (gs.map f).sum + (gs.map g).sum := by
  induction gs with
  | nil => simp
  | cons a gs ih => simp only [List.map_cons, List.sum_cons, ih]; ring


theorem MNR54_fwd_facts {m : ℕ} (e : Fin m → ℝ) (he : ∀ i, 0 ≤ e i) :
    (∀ k, 0 ≤ fwdProb e k ∧ fwdProb e k < 1) ∧
    (∏ k, (1 - fwdProb e k) = 1 / (1 + ∑ k, e k)) ∧
    (∀ i, fwdProb e i * ∏ k ∈ univ.filter (fun k => ¬ k ≤ i), (1 - fwdProb e k)
        = e i / (1 + ∑ k, e k)) := by
  have hpos : ∀ S : Finset (Fin m), 0 < 1 + ∑ j ∈ S, e j := fun S => by
    have := Finset.sum_nonneg (fun j (_ : j ∈ S) => he j); linarith
  have hθ : ∀ k, fwdProb e k = e k / (1 + ∑ j ∈ univ.filter (· ≤ k), e j) := fun k => rfl
  have hall : ∏ k, (1 - fwdProb e k) = 1 / (1 + ∑ k, e k) := by
    have := MNR54_fwd_tele e he m le_rfl
    rw [MNR54_filter_all] at this; exact this
  refine ⟨fun k => ?_, hall, fun i => ?_⟩
  · rw [hθ]
    have h1 : e k ≤ ∑ j ∈ univ.filter (· ≤ k), e j :=
      Finset.single_le_sum (f := e) (fun j _ => he j) (by simp)
    have h2 := hpos (univ.filter (· ≤ k))
    exact ⟨div_nonneg (he k) h2.le, by rw [div_lt_one h2]; linarith⟩
  · have hle : ∏ k ∈ univ.filter (· ≤ i), (1 - fwdProb e k) = 1 / (1 + ∑ j ∈ univ.filter (· ≤ i), e j) := by
      have := MNR54_fwd_tele e he (i.val + 1) i.isLt
      rw [← MNR54_filter_le] at this; exact this
    have hsplit := Finset.prod_filter_mul_prod_filter_not univ (fun k : Fin m => k ≤ i)
      (fun k => 1 - fwdProb e k)
    rw [hall, hle] at hsplit
    have h2 := hpos (univ.filter (· ≤ i))
    have h3 := hpos univ
    have hR : ∏ k ∈ univ.filter (fun k => ¬ k ≤ i), (1 - fwdProb e k)
        = (1 + ∑ j ∈ univ.filter (· ≤ i), e j) / (1 + ∑ k, e k) := by
      field_simp at hsplit ⊢; linarith
    rw [hR, hθ]; field_simp

theorem MNR54_fwd_apply {m : ℕ} {n : Fin m → ℕ} (xt : Mixed n) (e : Fin m → ℝ)
    (acor : (i : Fin m) → Fin (n i)) (k : Fin m) (c : Fin (n k)) :
    fwdSweep xt e acor k c = (1 - fwdProb e k) * xt k c + fwdProb e k * ePure (acor k) c := by
  simp [fwdSweep]


set_option maxHeartbeats 16000000 in
theorem MNR512_repair {σ : ℚ} (ctrl : Controls σ) {m : ℕ} {n : Fin m → ℕ} (hm : ctrl.m0 ≤ m)
    (hn : ∀ i, 0 < n i) (u : Utility n) (hu : BoundedGame u) (s : State n)
    (hx : AGT.IsMixedProfile s.x) (hterm : ¬ Terminal σ u s)
    (hgens : ∀ g ∈ s.gens, GenLegal g)
    (hI1 : ∀ i, s.h i = (s.gens.map fun g => g.A * g.t * g.γ i).sum)
    (hH : s.H = ∑ i, s.h i)
    (hI2 : (∀ i, 0 ≤ s.h i) ∧ s.H ≤ ctrl.knobs.L0 ∧
      ∀ i, (m : ℝ) * s.h i - s.H ≤ ctrl.knobs.R0 * s.H)
    (hI3 : ColumnBound u s.gens 9) (hI4 : CertLaw s.x s.gens)
    (hfail : ¬ Passes ctrl u s)
    (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ) (arev : (i : Fin m) → Fin (n i))
    (hw : DualOptimal u s.x ctrl.η w α) :
    let k := ctrl.knobs
    RepairLegal k u s w arev ∧ AGT.IsMixedProfile (bdev w) ∧ (∀ i, rGamma k s w i < 3 / m) ∧
    (∀ (j : Fin m) (y : Fin (n j) → ℝ), AGT.IsLottery y →
      ∑ i ∈ univ.erase j, rGamma k s w i * deficitMix u (Function.update s.x j y) i (bdev w i) < 9 / m) ∧
    ((∀ i, 0 ≤ (k.c • (s.h + k.t • rGamma k s w)) i) ∧
      ∑ i, (k.c • (s.h + k.t • rGamma k s w)) i = k.c * (s.H + k.t) ∧
      k.c * (s.H + k.t) ≤ k.L0 ∧
      ∀ i, (m : ℝ) * (k.c • (s.h + k.t • rGamma k s w)) i - k.c * (s.H + k.t) ≤ k.R0 * (k.c * (s.H + k.t))) := by
  intro k
  -- scalar constants
  have hdq : (0:ℚ) < ctrl.d := ctrl.d_pos
  have hd : (0:ℝ) < ctrl.d := by exact_mod_cast hdq
  have huq : ctrl.u = 1/2 * min (1/144) (ctrl.d/100) := rfl
  have hηq : ctrl.η = 1/2 * min (1/4) (ctrl.d/24) := rfl
  have hu0q : (0:ℚ) < ctrl.u := by
    rw [huq]; have := lt_min (by norm_num : (0:ℚ) < 1/144) (by positivity : (0:ℚ) < ctrl.d/100)
    linarith
  have hu1q : ctrl.u ≤ 1/288 := by
    rw [huq]; have := min_le_left (1/144 : ℚ) (ctrl.d/100); linarith
  have hudq : ctrl.u ≤ ctrl.d/200 := by
    rw [huq]; have := min_le_right (1/144 : ℚ) (ctrl.d/100); linarith
  have hη0q : (0:ℚ) < ctrl.η := by
    rw [hηq]; have := lt_min (by norm_num : (0:ℚ) < 1/4) (by positivity : (0:ℚ) < ctrl.d/24); linarith
  have hη1q : ctrl.η ≤ 1/8 := by rw [hηq]; have := min_le_left (1/4 : ℚ) (ctrl.d/24); linarith
  have hu0 : (0:ℝ) < ctrl.u := by exact_mod_cast hu0q
  have hu1 : (ctrl.u:ℝ) ≤ 1/288 := by
    have := (Rat.cast_le (K := ℝ)).mpr hu1q; push_cast at this; exact this
  have hud : (ctrl.u:ℝ) ≤ ctrl.d/200 := by exact_mod_cast hudq
  have hη0 : (0:ℝ) < ctrl.η := by exact_mod_cast hη0q
  have hη1 : (ctrl.η:ℝ) < 1 := by
    have := (Rat.cast_le (K := ℝ)).mpr hη1q; push_cast at this; linarith
  have hf1 : (7/12:ℝ) ≤ ctrl.f0 := by
    have := (Rat.cast_le (K := ℝ)).mpr ctrl.f0_ge; push_cast at this; exact this
  have hf2 : (ctrl.f0:ℝ) ≤ 3/5 := by
    have := (Rat.cast_le (K := ℝ)).mpr ctrl.f0_le; push_cast at this; exact this
  have hF0 : (0:ℝ) < ctrl.f0 := by linarith
  have hm0 : (ctrl.m0:ℝ) ≤ m := by exact_mod_cast hm
  have hmu2 : 1000 / (ctrl.u:ℝ)^2 ≤ m := by
    have h1 := ctrl.m0_ge_u
    have e : ((uOf ctrl.d : ℚ) : ℝ) = ctrl.u := rfl
    rw [e] at h1; linarith
  have hmpos : (0:ℝ) < m := lt_of_lt_of_le (by positivity) hmu2
  have hm1 : 1 ≤ m := by
    have : (0:ℝ) < m := hmpos
    exact_mod_cast (show (0:ℕ) < m by exact_mod_cast this)
  have hinvm : 1 / (m:ℝ) ≤ (ctrl.u:ℝ)^2 / 1000 := by
    rw [div_le_div_iff₀ hmpos (by norm_num)]
    have := (div_le_iff₀ (by positivity : (0:ℝ) < (ctrl.u:ℝ)^2)).mp hmu2
    linarith
  have hm66 : 66 / (ctrl.d:ℝ) ≤ m := le_trans ctrl.m0_ge_d hm0
  -- controls
  have hC := MultiNashRepair.controls_5_7 (ctrl.f0:ℝ) (ctrl.u:ℝ) hf1 hf2 hu0 (by linarith)
  dsimp only at hC
  have hR0pos : 0 < k.R0 := hC.1.1
  have hR0lt : k.R0 < 1 := hC.1.2.1
  have hQ1 : 1 < k.Q := hC.1.2.2.1
  have hQ2 : k.Q < 2 := hC.1.2.2.2.1
  have hau1 : k.au < 1 := hC.1.2.2.2.2.2.1
  have hL0f : k.L0 < ctrl.f0 := hC.1.2.2.2.2.2.2.1
  have hQL0 : k.Q * k.L0 < k.c := hC.1.2.2.2.2.2.2.2
  have hSuB : ∀ H : ℝ, 0 ≤ H → H ≤ k.L0 → k.Su H ≤ 1 + k.L0 + k.R0 ∧ 1 + k.L0 + k.R0 < 13 / 5 :=
    fun H h0 h1 => ⟨(hC.2 H h0 h1).2.2.1, (hC.2 H h0 h1).2.2.2⟩
  have hc : k.c = 1 - ctrl.u + (ctrl.u:ℝ)^2/2 - (ctrl.u:ℝ)^3 := rfl
  have ht : k.t = ctrl.f0 * ctrl.u := rfl
  have hcpos : 0 < k.c := by rw [hc]; nlinarith only [hu0, hu1]
  have hc1 : k.c < 1 := by rw [hc]; nlinarith only [hu0, hu1]
  have htpos : 0 < k.t := by rw [ht]; positivity
  have htu : k.t ≤ 3/5 * ctrl.u := by rw [ht]; nlinarith only [hf2, hu0]
  have hu0' : 0 < 1 + k.u0 := by
    have : k.u0 = (ctrl.u:ℝ) - (ctrl.u:ℝ)^2 := rfl
    rw [this]; nlinarith only [hu0, hu1]
  have hβdef : k.beta = k.c * k.t * (1 + k.u0) := rfl
  have hβpos : 0 < k.beta := by rw [hβdef]; positivity
  have hν : k.nu = k.Q * k.beta := by
    have : k.Q = k.nu / k.beta := rfl
    rw [this]; field_simp
  have hρ : 1 - k.rho = k.beta * k.R0 := by
    have : k.R0 = (1 - k.rho) / k.beta := rfl
    rw [this]; field_simp
  have hG0 : k.G0 = 1 + k.R0 := rfl
  have hrho_def : k.rho = 1 - (1 - ctrl.f0) * ctrl.u + (1 - (ctrl.f0:ℝ))^2 * (ctrl.u:ℝ)^2 / 2 := rfl
  have ha : 0 ≤ (1 - (ctrl.f0:ℝ)) * ctrl.u := mul_nonneg (by linarith) hu0.le
  have hb : (1 - (ctrl.f0:ℝ)) * ctrl.u ≤ ctrl.u := by nlinarith only [mul_pos hF0 hu0]
  have hrho1 : k.rho ≤ 1 := by
    rw [hrho_def]
    have := mul_le_mul_of_nonneg_left (le_trans hb (by linarith : (ctrl.u:ℝ) ≤ 1)) ha
    nlinarith only [this, ha]
  have hrho34 : 3/4 ≤ k.rho := by
    rw [hrho_def]; nlinarith only [hb, ha, hu1, sq_nonneg ((1 - (ctrl.f0:ℝ)) * ctrl.u)]
  have h1rho : 1 - k.rho ≤ ctrl.u := by
    rw [hrho_def]; nlinarith only [hb, sq_nonneg ((1 - (ctrl.f0:ℝ)) * ctrl.u)]
  have hβu : k.beta ≤ 17/26 * ctrl.u := by
    rw [hβdef, ht]
    have : k.u0 = (ctrl.u:ℝ) - (ctrl.u:ℝ)^2 := rfl
    rw [this]
    have h1 : k.c * (1 + ((ctrl.u:ℝ) - ctrl.u^2)) ≤ 17/16 := by
      rw [hc]
      have h3 : (ctrl.u:ℝ)^2 ≤ 1 := by nlinarith only [hu0, hu1]
      nlinarith only [hu0, hu1, h3, pow_pos hu0 3, pow_pos hu0 4, pow_pos hu0 5, mul_pos hu0 hu0]
    have h2 : 0 ≤ (ctrl.f0:ℝ) * ctrl.u := by positivity
    nlinarith only [mul_le_mul_of_nonneg_left h1 h2, hf2, hu0]
  -- memory
  have hh0 := hI2.1
  have hHnn : 0 ≤ s.H := by rw [hH]; exact Finset.sum_nonneg (fun i _ => hh0 i)
  have hHL := hI2.2.1
  have hH1 : s.H < 1 := by linarith
  -- G0 lower bound and μ
  have h511' := MultiNashRepair.lemma_5_11 (ctrl.f0:ℝ) (ctrl.u:ℝ) hf1 hf2 hu0 (by linarith)
  dsimp only at h511'
  have hG0lo : 1/(ctrl.f0:ℝ) - 32 * ctrl.u ≤ k.G0 := by
    have h := h511'.2.2 0 le_rfl (le_trans hHnn hHL : (0:ℝ) ≤ k.L0)
    rw [h511'.1] at h
    have e : Kf (ctrl.f0) 0 = 1/(ctrl.f0:ℝ) := by
      unfold Kf; rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    rw [e] at h
    have h2 : |k.G0 - 1/(ctrl.f0:ℝ)| ≤ 32 * ctrl.u := h
    linarith [(abs_le.mp h2).1]
  have hQH : 0 < 1 + k.Q * s.H := by nlinarith only [hQ1, hHnn]
  have hSuG : k.G0 ≤ k.Su s.H := by
    have hS : k.Su s.H = 1 + s.H + k.R0 * (1 + s.H) / (1 + k.Q * s.H) := rfl
    rw [hS, hG0]
    have : k.R0 * (1 + s.H) / (1 + k.Q * s.H) ≥ k.R0 - k.au * s.H := by
      rw [ge_iff_le, le_div_iff₀ hQH]
      have hau : k.au = k.R0 * (k.Q - 1) := rfl
      rw [hau]
      nlinarith only [mul_nonneg (mul_nonneg hR0pos.le (by linarith : (0:ℝ) ≤ k.Q - 1)) (mul_nonneg hHnn (mul_nonneg (by linarith : (0:ℝ) ≤ k.Q) hHnn)), hR0pos, hHnn]
    nlinarith only [this, hau1, hHnn]
  set ς := scaled u s.x with hςdef
  have hςσ : ς < (σ:ℝ) := lt_of_not_ge hterm
  have hfinv := ctrl.f0_inv
  set μ := ctrl.mu ς s.H with hμdef
  have hμeq : μ = k.Su s.H - ς - ctrl.d := rfl
  have hμpos : 0 < μ := by rw [hμeq]; linarith
  have hςμ : ς + μ < 3 := by rw [hμeq]; have := (hSuB s.H hHnn hHL); linarith
  -- Lemma 5.1 (b)
  obtain ⟨hlam, hbm, hF, hlamF, h512⟩ :=
    (MultiNashRepair.lemma_5_1 hm1 hn u hu s.x hx ctrl.η μ hη0 hη1 hμpos).2 hfail w α hw
  -- Lemma 5.3
  have hmh : ∀ i, (m:ℝ) * s.h i ≤ ∑ j, s.h j + k.R0 * s.H := by
    intro i; have := hI2.2.2 i; rw [← hH]; linarith
  have h53 := MultiNashRepair.lemma_5_3 hm1 hn u hu s.x hx (lam w) (bdev w) hlam hbm μ hF s.gens
    hgens hI4 9 (by norm_num) hI3 s.h hI1 hh0 (k.R0 * s.H)
    (mul_nonneg hR0pos.le hHnn) hmh
  dsimp only at h53
  obtain ⟨ϑ, hϑ0, hϑ1, hϑ⟩ := h53
  rw [← hH] at hϑ1 hϑ
  -- the floor condition (5.26)
  haveI : Nonempty (Fin m) := ⟨⟨0, hm1⟩⟩
  set r := (⨆ i, (m:ℝ) * lam w i) - 1 with hr
  set Hψ := ∑ i, lam w i * ((m:ℝ) * s.h i - s.H) with hHψ
  have hπ : ∀ i, (m:ℝ) * lam w i ≤ 1 + r := fun i => by
    rw [hr]; linarith [le_ciSup (f := fun i => (m:ℝ) * lam w i) (Set.finite_range _).bddAbove i]
  have hr3 : 1 + r < 3 := by
    have hb : ∀ i, (m:ℝ) * lam w i < 3 := fun i => by
      have h1 := hlamF i
      have h2 := hF i (bdev w i) (hbm i)
      have k1 : (m:ℝ) * lam w i ≤ (m:ℝ) * Fcol u s.x w i (bdev w i) := mul_le_mul_of_nonneg_left h1 hmpos.le
      have k2 : (m:ℝ) * Fcol u s.x w i (bdev w i) < ς + μ := by
        rw [lt_div_iff₀ hmpos] at h2; linarith
      linarith
    obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i => (m:ℝ) * lam w i)
    have : (⨆ i, (m:ℝ) * lam w i) < 3 := by rw [← hj]; exact hb j
    rw [hr]; linarith
  have hr0 : 0 ≤ 1 + r := le_trans (mul_nonneg hmpos.le (hlam.1 ⟨0, hm1⟩)) (hπ ⟨0, hm1⟩)
  have hϑ11 : ϑ ≤ 11 / m := by
    refine le_trans hϑ1 (div_le_div_of_nonneg_right ?_ hmpos.le)
    nlinarith only [hHnn, hH1, hR0lt, mul_le_mul_of_nonneg_left hR0lt.le hHnn]
  have hrHψ : r + Hψ ≤ k.Cu s.H - ctrl.d / 2 := by
    have hSu : k.Su s.H = 1 + s.H + k.Cu s.H := rfl
    have h1 : (1 + r) * ϑ ≤ 3 * (11 / m) := mul_le_mul hr3.le hϑ11 hϑ0 (by norm_num)
    have h2 : 3 * (11 / (m:ℝ)) ≤ ctrl.d / 2 := by
      rw [div_le_iff₀ hd] at hm66
      rw [show 3 * (11 / (m:ℝ)) = 33 / m by ring, div_le_iff₀ hmpos]; linarith
    rw [hμeq, hSu] at hϑ
    nlinarith only [hϑ, h1, h2]
  have hHψr : Hψ ≤ r * s.H := by
    have e : Hψ = ∑ i, ((m:ℝ) * lam w i) * s.h i - s.H := by
      rw [hHψ]
      have e1 : ∑ i, lam w i * ((m:ℝ) * s.h i - s.H) = ∑ i, ((m:ℝ) * lam w i * s.h i - lam w i * s.H) :=
        Finset.sum_congr rfl (fun i _ => by ring)
      rw [e1, Finset.sum_sub_distrib, ← Finset.sum_mul, hlam.2, one_mul]
    rw [e]
    have : ∑ i, ((m:ℝ) * lam w i) * s.h i ≤ ∑ i, (1 + r) * s.h i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hπ i) (hh0 i))
    rw [← Finset.mul_sum, ← hH] at this
    linarith
  have h526 : r + k.Q * Hψ ≤ k.R0 := by
    have hCu : k.Cu s.H * (1 + k.Q * s.H) = k.R0 * (1 + s.H) := by
      have : k.Cu s.H = k.R0 * (1 + s.H) / (1 + k.Q * s.H) := rfl
      rw [this]; field_simp
    have key : (r + k.Q * Hψ) * (1 + s.H) ≤ k.R0 * (1 + s.H) := by
      have k1 : (r + k.Q * Hψ) * (1 + s.H) = (1 + k.Q * s.H) * (r + Hψ) - (k.Q - 1) * (r * s.H - Hψ) := by ring
      have k2 : 0 ≤ (k.Q - 1) * (r * s.H - Hψ) := mul_nonneg (by linarith) (by linarith)
      have k3 : (1 + k.Q * s.H) * (r + Hψ) ≤ (1 + k.Q * s.H) * (k.Cu s.H - ctrl.d / 2) :=
        mul_le_mul_of_nonneg_left hrHψ hQH.le
      have k4 : 0 ≤ (1 + k.Q * s.H) * (ctrl.d / 2) := mul_nonneg hQH.le (by linarith)
      nlinarith only [k1, k2, k3, k4, hCu]
    exact le_of_mul_le_mul_right key (by linarith)
  -- Lemma 5.5
  have h55 := MultiNashRepair.lemma_5_5 ctrl hm hn u hu s.x hx (lam w) (bdev w) hlam hbm s.h hh0
    (by rw [← hH]; exact hHL) (by intro i; rw [← hH]; exact hI2.2.2 i) (by rw [← hH]; exact hF)
    (by rw [← hH]; exact h526)
  dsimp only at h55
  rw [← hH] at h55
  have hγlot : AGT.IsLottery (rGamma k s w) := h55.1.1
  have hγ3 : ∀ i, rGamma k s w i < 3 / m := h55.1.2.1
  have hγl : ∀ i, rGamma k s w i ≤ 3 * lam w i := h55.1.2.2.1
  have hδeq : ∀ i, k.beta / m * (k.G0 - k.Q * ((m:ℝ) * s.h i - s.H) - m * rGamma k s w i)
      = rDelta k s w i := fun i => h55.2.1.2.2 i
  have hδ0 : ∀ i, 0 ≤ rDelta k s w i := fun i => by rw [← hδeq i]; exact h55.2.1.1 i
  have hδ1 : ∑ i, rDelta k s w i = 1 - k.rho := by
    rw [← h55.2.1.2.1]; apply Finset.sum_congr rfl; intro i _; exact (hδeq i).symm
  have hcol : ∀ (j : Fin m) (y : Fin (n j) → ℝ), AGT.IsLottery y →
      ∑ i ∈ univ.erase j, rGamma k s w i * deficitMix u (Function.update s.x j y) i (bdev w i) < 9 / m :=
    h55.2.2.2.2
  -- conclusions
  have hγ0 : ∀ i, 0 ≤ rGamma k s w i := hγlot.1
  have h3m : 3 / (m:ℝ) ≤ 3 * (ctrl.u:ℝ)^2 / 1000 := by
    have := mul_le_mul_of_nonneg_left hinvm (by norm_num : (0:ℝ) ≤ 3)
    rw [show 3 * (1 / (m:ℝ)) = 3 / m by ring] at this; linarith
  have htγ : ∀ i, 0 ≤ k.t * rGamma k s w i ∧ k.t * rGamma k s w i < 1 := fun i => by
    have h1 := mul_le_mul_of_nonneg_left (le_trans (hγ3 i).le h3m) htpos.le
    have hu2 : (ctrl.u:ℝ)^2 ≤ 1 := by nlinarith only [hu0, hu1]
    refine ⟨mul_nonneg htpos.le (hγ0 i), ?_⟩
    nlinarith only [h1, htu, hu1, hu0, hu2]
  have hρpos : 0 < k.rho := by linarith
  have hP : ∀ i, k.rho ≤ 1 - ∑ j ∈ univ.filter (· ≤ i), rDelta k s w j := fun i => by
    have : ∑ j ∈ univ.filter (· ≤ i), rDelta k s w j ≤ ∑ j, rDelta k s w j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => hδ0 j)
    linarith
  obtain ⟨hym, hxtm⟩ := MNR54_xt_mixed s.x (bdev w) hx hbm (rGamma k s w) k.t htγ (rDelta k s w) hδ0
    k.rho hρpos hδ1 arev
  have hτ : rTau s w ≤ k.R0 * s.H := by
    show ∑ i, lam w i * ((m:ℝ) * s.h i - s.H) ≤ _
    calc ∑ i, lam w i * ((m:ℝ) * s.h i - s.H) ≤ ∑ i, lam w i * (k.R0 * s.H) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hI2.2.2 i) (hlam.1 i))
      _ = k.R0 * s.H := by rw [← Finset.sum_mul, hlam.2, one_mul]
  have hZ : 0 < k.G0 - k.Q * rTau s w := by
    have hQH' : k.Q * s.H ≤ k.c := by
      have := mul_le_mul_of_nonneg_left hHL (by linarith : (0:ℝ) ≤ k.Q); linarith
    have k1 := mul_le_mul_of_nonneg_left hτ (by linarith : (0:ℝ) ≤ k.Q)
    have k2 : k.Q * (k.R0 * s.H) ≤ k.R0 * k.c := by nlinarith only [mul_le_mul_of_nonneg_left hQH' hR0pos.le]
    have k3 : k.R0 * k.c ≤ k.R0 := by nlinarith only [hR0pos, hc1]
    rw [hG0]; linarith
  have hE0 : ∀ i, 0 ≤ rE k u s w arev i := fun i => le_max_left _ _
  obtain ⟨hfw01, -, -⟩ := MNR54_fwd_facts (rE k u s w arev) hE0
  refine ⟨⟨hZ, hγlot, htγ, hδ0, hδ1, hρpos, hP, hfw01, hym, hxtm⟩, hbm, hγ3, hcol, ?_⟩
  exact h55.2.2.1


theorem MNRQ_knobs {σ : ℚ} (ctrl : Controls σ) :
    IsRat ctrl.knobs.c ∧ IsRat ctrl.knobs.t ∧ IsRat ctrl.knobs.rho ∧ IsRat ctrl.knobs.beta ∧
    IsRat ctrl.knobs.nu ∧ IsRat ctrl.knobs.G0 ∧ IsRat ctrl.knobs.Q ∧ IsRat ctrl.knobs.R0 := by
  have hf : IsRat ctrl.knobs.f0 := ⟨ctrl.f0, rfl⟩
  have hu : IsRat ctrl.knobs.u := ⟨ctrl.u, rfl⟩
  have hc : IsRat ctrl.knobs.c := by
    show IsRat (1 - ctrl.knobs.u + ctrl.knobs.u ^ 2 / 2 - ctrl.knobs.u ^ 3)
    exact MNRQ_sub (MNRQ_add (MNRQ_sub MNRQ_one hu) (MNRQ_div (MNRQ_pow hu 2) ⟨2, by norm_num⟩)) (MNRQ_pow hu 3)
  have ht : IsRat ctrl.knobs.t := MNRQ_mul hf hu
  have hrho : IsRat ctrl.knobs.rho := by
    show IsRat (1 - (1 - ctrl.knobs.f0) * ctrl.knobs.u + (1 - ctrl.knobs.f0) ^ 2 * ctrl.knobs.u ^ 2 / 2)
    exact MNRQ_add (MNRQ_sub MNRQ_one (MNRQ_mul (MNRQ_sub MNRQ_one hf) hu))
      (MNRQ_div (MNRQ_mul (MNRQ_pow (MNRQ_sub MNRQ_one hf) 2) (MNRQ_pow hu 2)) ⟨2, by norm_num⟩)
  have hu0 : IsRat ctrl.knobs.u0 := MNRQ_sub hu (MNRQ_pow hu 2)
  have hβ : IsRat ctrl.knobs.beta := MNRQ_mul (MNRQ_mul hc ht) (MNRQ_add MNRQ_one hu0)
  have hν : IsRat ctrl.knobs.nu := MNRQ_mul hc hu0
  have hR0 : IsRat ctrl.knobs.R0 := MNRQ_div (MNRQ_sub MNRQ_one hrho) hβ
  exact ⟨hc, ht, hrho, hβ, hν, MNRQ_add MNRQ_one hR0, MNRQ_div hν hβ, hR0⟩

theorem MNRQ_lam {m : ℕ} {n : Fin m → ℕ} (w : (i : Fin m) → Fin (n i) → ℝ)
    (hw : ∀ i a, IsRat (w i a)) (i : Fin m) : IsRat (lam w i) :=
  MNRQ_sum _ _ (fun a _ => hw i a)

theorem MNRQ_bdev {m : ℕ} {n : Fin m → ℕ} (w : (i : Fin m) → Fin (n i) → ℝ)
    (hw : ∀ i a, IsRat (w i a)) : ∀ i a, IsRat (bdev w i a) := by
  intro i a
  unfold bdev
  split_ifs
  · exact MNRQ_div (hw i a) (MNRQ_lam w hw i)
  · dsimp only; split_ifs
    · exact MNRQ_one
    · exact MNRQ_zero

theorem MNRQ_gamma {σ : ℚ} (ctrl : Controls σ) {m : ℕ} {n : Fin m → ℕ} (s : State n)
    (w : (i : Fin m) → Fin (n i) → ℝ) (hw : ∀ i a, IsRat (w i a)) (hh : ∀ i, IsRat (s.h i))
    (hH : IsRat s.H) : (∀ i, IsRat (rGamma ctrl.knobs s w i)) ∧ (∀ i, IsRat (rDelta ctrl.knobs s w i)) := by
  obtain ⟨hc, ht, hrho, hβ, hν, hG0, hQ, hR0⟩ := MNRQ_knobs ctrl
  have hv : ∀ i, IsRat (rV s i) := fun i => MNRQ_sub (MNRQ_mul (MNRQ_nat m) (hh i)) hH
  have hτ : IsRat (rTau s w) := MNRQ_sum _ _ (fun i _ => MNRQ_mul (MNRQ_lam w hw i) (hv i))
  have hγ : ∀ i, IsRat (rGamma ctrl.knobs s w i) := fun i =>
    MNRQ_div (MNRQ_mul (MNRQ_lam w hw i) (MNRQ_sub hG0 (MNRQ_mul hQ (hv i)))) (MNRQ_sub hG0 (MNRQ_mul hQ hτ))
  refine ⟨hγ, fun i => ?_⟩
  have hD : IsRat (ctrl.knobs.Dsh s.H) := MNRQ_mul hβ (MNRQ_add hG0 (MNRQ_mul hQ hH))
  exact MNRQ_sub (MNRQ_sub (MNRQ_div hD (MNRQ_nat m)) (MNRQ_mul hβ (hγ i))) (MNRQ_mul hν (hh i))

theorem MNRQ_repair_x {σ : ℚ} (ctrl : Controls σ) {m : ℕ} {n : Fin m → ℕ} (hm : 1 ≤ m)
    (hn : ∀ i, 0 < n i) (u : Utility n) (hu : ∀ i a, IsRat (u i a)) (s : State n)
    (hx : ∀ i a, IsRat (s.x i a)) (w : (i : Fin m) → Fin (n i) → ℝ) (hw : ∀ i a, IsRat (w i a))
    (hh : ∀ i, IsRat (s.h i)) (hH : IsRat s.H) (arev acor : (i : Fin m) → Fin (n i)) :
    ∀ i a, IsRat ((repairState ctrl.knobs u s w arev acor).x i a) := by
  obtain ⟨hc, ht, hrho, hβ, hν, hG0, hQ, hR0⟩ := MNRQ_knobs ctrl
  obtain ⟨hγ, hδ⟩ := MNRQ_gamma ctrl s w hw hh hH
  have hy : ∀ i a, IsRat (rY ctrl.knobs s w i a) := fun i a => by
    show IsRat (actY s.x (bdev w) ctrl.knobs.t (rGamma ctrl.knobs s w) i a)
    rw [MNR54_actY_apply]
    exact MNRQ_add (MNRQ_mul (MNRQ_sub MNRQ_one (MNRQ_mul ht (hγ i))) (hx i a))
      (MNRQ_mul (MNRQ_mul ht (hγ i)) (MNRQ_bdev w hw i a))
  have hp : ∀ i, IsRat (revProb (rDelta ctrl.knobs s w) i) := fun i =>
    MNRQ_div (hδ i) (MNRQ_sub MNRQ_one (MNRQ_sum _ _ (fun j _ => hδ j)))
  have hxt : ∀ i a, IsRat (rXt ctrl.knobs s w arev i a) := fun i a => by
    show IsRat (revSweep (rY ctrl.knobs s w) (rDelta ctrl.knobs s w) arev i a)
    rw [MNR54_rev_apply]
    exact MNRQ_add (MNRQ_mul (MNRQ_sub MNRQ_one (hp i)) (hy i a)) (MNRQ_mul (hp i) (MNRQ_ePure _ a))
  obtain ⟨-, hqi, -, hsc⟩ := MNRQ_Reg hm hn u hu s.x hx
  obtain ⟨-, hqit, -, -⟩ := MNRQ_Reg hm hn u hu _ hxt
  have hCraw : IsRat (rCraw ctrl.knobs s w) :=
    MNRQ_mul hrho (MNRQ_prod _ _ (fun i _ => MNRQ_sub MNRQ_one (MNRQ_mul ht (hγ i))))
  have hD : IsRat (ctrl.knobs.Dsh s.H) := MNRQ_mul hβ (MNRQ_add hG0 (MNRQ_mul hQ hH))
  have he : ∀ i, IsRat (rE ctrl.knobs u s w arev i) := fun i =>
    MNRQ_max MNRQ_zero (MNRQ_sub (MNRQ_div (MNRQ_add (MNRQ_mul hCraw hsc) hD) (MNRQ_nat m)) (hqit i))
  have hθ : ∀ i, IsRat (fwdProb (rE ctrl.knobs u s w arev) i) := fun i =>
    MNRQ_div (he i) (MNRQ_add MNRQ_one (MNRQ_sum _ _ (fun j _ => he j)))
  intro i a
  show IsRat (fwdSweep (rXt ctrl.knobs s w arev) (rE ctrl.knobs u s w arev) acor i a)
  rw [MNR54_fwd_apply]
  exact MNRQ_add (MNRQ_mul (MNRQ_sub MNRQ_one (hθ i)) (hxt i a)) (MNRQ_mul (hθ i) (MNRQ_ePure _ a))

theorem MNRQ_descent_x {m : ℕ} {n : Fin m → ℕ} (x : Mixed n) (hx : ∀ i a, IsRat (x i a))
    (η : ℝ) (hη : IsRat η) (z : (j : Fin m) → Fin (n j) → ℝ) (hz : ∀ j b, IsRat (z j b)) :
    (∀ i a, IsRat (descentProfile x η z i a)) ∧ IsRat (descentFactor η z) := by
  constructor
  · intro i a; rw [MNR51_xp_apply]
    exact MNRQ_add (MNRQ_mul (MNRQ_sub MNRQ_one (MNRQ_mul hη (MNRQ_sum _ _ (fun b _ => hz i b)))) (hx i a))
      (MNRQ_mul hη (hz i a))
  · exact MNRQ_prod _ _ (fun j _ => MNRQ_sub MNRQ_one (MNRQ_mul hη (MNRQ_sum _ _ (fun b _ => hz j b))))


theorem MNR51_cert_scale {m : ℕ} {n : Fin m → ℕ} (gs : List (Gen n)) (P : ℝ) (f : Gen n → ℝ)
    (hf : ∀ g : Gen n, f { g with A := P * g.A } = P * f g) :
    ((gs.map fun g => { g with A := P * g.A }).map f).sum = P * (gs.map f).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp only [List.map_cons, List.sum_cons, ih, hf]; ring

theorem MNRQ_list {m : ℕ} {n : Fin m → ℕ} (gs : List (Gen n)) (f : Gen n → ℝ)
    (hf : ∀ g ∈ gs, IsRat (f g)) : IsRat (gs.map f).sum := by
  induction gs with
  | nil => simp [MNRQ_zero]
  | cons g gs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact MNRQ_add (hf g (List.mem_cons_self ..)) (ih (fun x hx => hf x (List.mem_cons_of_mem _ hx)))


section MNR43V
open Matrix

/-- A real solution of an injective rational linear system is rational. -/
theorem MNR43_rat_solution {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C] [DecidableEq R]
    (L : Matrix R C ℚ) (b : R → ℚ) (v : C → ℝ)
    (hinj : ∀ d : C → ℝ, (L.map (Rat.castHom ℝ)) *ᵥ d = 0 → d = 0)
    (hv : (L.map (Rat.castHom ℝ)) *ᵥ v = fun r => (b r : ℝ)) :
    ∃ q : C → ℚ, ∀ c, v c = (q c : ℝ) := by
  have hinjQ : LinearMap.ker (Matrix.mulVecLin L) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h1 : (L.map (Rat.castHom ℝ)) *ᵥ (fun c => (x c : ℝ)) = 0 := by
      funext r
      have h3 : (L *ᵥ x) r = 0 := by
        have : L *ᵥ x = 0 := hx
        rw [this]; rfl
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, Rat.coe_castHom] at h3 ⊢
      have := congrArg (fun q : ℚ => (q : ℝ)) h3
      simpa using this
    have := hinj _ h1
    funext c
    have := congrFun this c
    simpa using this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin L) hinjQ
  set G := LinearMap.toMatrix' g with hG
  have hGL : G * L = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext; intro x
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hG,
      LinearMap.toMatrix'_mulVec]
    have := congrArg (fun f => f x) hg
    simpa using this
  refine ⟨G *ᵥ b, fun c => ?_⟩
  have hGLR : (G.map (Rat.castHom ℝ)) * (L.map (Rat.castHom ℝ)) = 1 := by
    rw [← Matrix.map_mul, hGL, Matrix.map_one _ (by simp) (by simp)]
  have : v = (G.map (Rat.castHom ℝ)) *ᵥ ((L.map (Rat.castHom ℝ)) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hGLR, Matrix.one_mulVec]
  rw [this, hv]
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply]

theorem MNR43_vertex {K C : Type*} [Fintype K] [Fintype C] [DecidableEq K] [DecidableEq C]
    (G : Matrix K C ℚ) (S : C → ℚ) (o : C → ℝ) (V : ℝ)
    (hub : ∀ v : C → ℝ, (∀ k, 0 ≤ ((G.map (Rat.castHom ℝ)) *ᵥ v) k) →
      (fun c => (S c : ℝ)) ⬝ᵥ v = 1 → o ⬝ᵥ v ≤ V)
    (hex : ∃ v : C → ℝ, (∀ k, 0 ≤ ((G.map (Rat.castHom ℝ)) *ᵥ v) k) ∧
      (fun c => (S c : ℝ)) ⬝ᵥ v = 1 ∧ o ⬝ᵥ v = V)
    (hdir : ∀ d : C → ℝ, (fun c => (S c : ℝ)) ⬝ᵥ d = 0 → o ⬝ᵥ d = 0 → d ≠ 0 →
      ∃ k, ((G.map (Rat.castHom ℝ)) *ᵥ d) k < 0) :
    ∃ v : C → ℝ, (∀ k, 0 ≤ ((G.map (Rat.castHom ℝ)) *ᵥ v) k) ∧
      (fun c => (S c : ℝ)) ⬝ᵥ v = 1 ∧ o ⬝ᵥ v = V ∧ ∃ q : C → ℚ, ∀ c, v c = (q c : ℝ) := by
  classical
  set GR := G.map (Rat.castHom ℝ) with hGR
  set SR : C → ℝ := fun c => (S c : ℝ) with hSR
  let Opt : (C → ℝ) → Prop := fun v => (∀ k, 0 ≤ (GR *ᵥ v) k) ∧ SR ⬝ᵥ v = 1 ∧ o ⬝ᵥ v = V
  let tight : (C → ℝ) → Finset K := fun v => univ.filter (fun k => (GR *ᵥ v) k = 0)
  -- choose an optimal point with the most tight constraints
  let Pk : ℕ → Prop := fun j => ∃ v, Opt v ∧ j ≤ (tight v).card
  have hP0 : Pk 0 := by obtain ⟨v, hv⟩ := hex; exact ⟨v, hv, Nat.zero_le _⟩
  set jmax := Nat.findGreatest Pk (Fintype.card K) with hjmax
  have hPj : Pk jmax := Nat.findGreatest_spec (P := Pk) (Nat.zero_le _) hP0
  obtain ⟨v, hvopt, hvj⟩ := hPj
  have hmax : ∀ w, Opt w → (tight w).card ≤ (tight v).card := by
    intro w hw
    have h1 : (tight w).card ≤ jmax := by
      apply Nat.le_findGreatest (Finset.card_le_univ _) ⟨w, hw, le_rfl⟩
    linarith
  obtain ⟨hvG, hvS, hvo⟩ := hvopt
  -- moving along a direction that keeps tight constraints tight
  have hmove : ∀ d : C → ℝ, (∀ k ∈ tight v, (GR *ᵥ d) k = 0) →
      ∃ t : ℝ, 0 < t ∧ ∀ k, 0 ≤ (GR *ᵥ (v + t • d)) k := by
    intro d hd
    have hlin : ∀ (t : ℝ) k, (GR *ᵥ (v + t • d)) k = (GR *ᵥ v) k + t * (GR *ᵥ d) k := by
      intro t k; rw [Matrix.mulVec_add, Matrix.mulVec_smul]; simp
    set Neg := univ.filter (fun k => (GR *ᵥ d) k < 0) with hNeg
    by_cases hne : Neg.Nonempty
    · obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image Neg (fun k => (GR *ᵥ v) k / (-(GR *ᵥ d) k)) hne
      have hpos : ∀ k ∈ Neg, 0 < (GR *ᵥ v) k := by
        intro k hk
        have hk' : (GR *ᵥ d) k < 0 := (Finset.mem_filter.mp hk).2
        rcases (hvG k).lt_or_eq with h | h
        · exact h
        · exfalso
          have : k ∈ tight v := Finset.mem_filter.mpr ⟨mem_univ _, h.symm⟩
          linarith [hd k this]
      have hk0' : (GR *ᵥ d) k0 < 0 := (Finset.mem_filter.mp hk0).2
      refine ⟨(GR *ᵥ v) k0 / (-(GR *ᵥ d) k0), div_pos (hpos k0 hk0) (by linarith), fun k => ?_⟩
      rw [hlin]
      by_cases hk : k ∈ Neg
      · have hk' : (GR *ᵥ d) k < 0 := (Finset.mem_filter.mp hk).2
        have := hmin k hk
        rw [div_le_div_iff₀ (by linarith : (0:ℝ) < -(GR *ᵥ d) k0) (by linarith : (0:ℝ) < -(GR *ᵥ d) k)] at this
        have h2 : (GR *ᵥ v) k0 / -(GR *ᵥ d) k0 * (GR *ᵥ d) k ≥ -(GR *ᵥ v) k := by
          have e : (GR *ᵥ v) k0 / -(GR *ᵥ d) k0 * (GR *ᵥ d) k
              = (GR *ᵥ v) k0 * (GR *ᵥ d) k / -(GR *ᵥ d) k0 := by ring
          rw [e, ge_iff_le, le_div_iff₀ (by linarith : (0:ℝ) < -(GR *ᵥ d) k0)]
          linarith
        linarith
      · have : 0 ≤ (GR *ᵥ d) k := by
          by_contra h; push Not at h; exact hk (Finset.mem_filter.mpr ⟨mem_univ _, h⟩)
        have := mul_nonneg (div_pos (hpos k0 hk0) (by linarith : (0:ℝ) < -(GR *ᵥ d) k0)).le this
        linarith [hvG k]
    · refine ⟨(1:ℝ), one_pos, fun k => ?_⟩
      rw [hlin]
      have : 0 ≤ (GR *ᵥ d) k := by
        by_contra h; push Not at h
        exact hne ⟨k, Finset.mem_filter.mpr ⟨mem_univ _, h⟩⟩
      linarith [hvG k]
  -- injectivity of the tight system
  have hinj : ∀ d : C → ℝ, (∀ k ∈ tight v, (GR *ᵥ d) k = 0) → SR ⬝ᵥ d = 0 → d = 0 := by
    intro d hd hS
    by_contra hne
    have hlin : ∀ (t : ℝ) (w : C → ℝ), o ⬝ᵥ (v + t • w) = o ⬝ᵥ v + t * (o ⬝ᵥ w) := by
      intro t w; rw [dotProduct_add, dotProduct_smul]; simp
    have hlinS : ∀ (t : ℝ) (w : C → ℝ), SR ⬝ᵥ (v + t • w) = SR ⬝ᵥ v + t * (SR ⬝ᵥ w) := by
      intro t w; rw [dotProduct_add, dotProduct_smul]; simp
    -- the objective is flat along d
    have hod : o ⬝ᵥ d = 0 := by
      by_contra hod
      set s : ℝ := if 0 < o ⬝ᵥ d then 1 else -1 with hs
      have hsd : 0 < o ⬝ᵥ (s • d) := by
        rw [dotProduct_smul]; simp only [hs, smul_eq_mul]
        split_ifs with h
        · linarith
        · have : o ⬝ᵥ d < 0 := lt_of_le_of_ne (not_lt.mp h) hod
          linarith
      have hd' : ∀ k ∈ tight v, (GR *ᵥ (s • d)) k = 0 := by
        intro k hk; rw [Matrix.mulVec_smul]; simp [hd k hk]
      obtain ⟨t, ht, hfeas⟩ := hmove (s • d) hd'
      have hS' : SR ⬝ᵥ (v + t • (s • d)) = 1 := by
        rw [hlinS, dotProduct_smul, hS]; simp [hvS]
      have := hub (v + t • (s • d)) hfeas hS'
      rw [hlin, hvo] at this
      nlinarith only [this, ht, hsd]
    obtain ⟨k1, hk1⟩ := hdir d hS hod hne
    -- move maximally along d
    set Neg := univ.filter (fun k => (GR *ᵥ d) k < 0) with hNeg
    have hne' : Neg.Nonempty := ⟨k1, Finset.mem_filter.mpr ⟨mem_univ _, hk1⟩⟩
    obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image Neg (fun k => (GR *ᵥ v) k / (-(GR *ᵥ d) k)) hne'
    have hk0' : (GR *ᵥ d) k0 < 0 := (Finset.mem_filter.mp hk0).2
    have hpos : ∀ k ∈ Neg, 0 < (GR *ᵥ v) k := by
      intro k hk
      have hk' : (GR *ᵥ d) k < 0 := (Finset.mem_filter.mp hk).2
      rcases (hvG k).lt_or_eq with h | h
      · exact h
      · exfalso
        have : k ∈ tight v := Finset.mem_filter.mpr ⟨mem_univ _, h.symm⟩
        linarith [hd k this]
    set t := (GR *ᵥ v) k0 / (-(GR *ᵥ d) k0) with ht
    have htpos : 0 < t := div_pos (hpos k0 hk0) (by linarith)
    have hlinG : ∀ k, (GR *ᵥ (v + t • d)) k = (GR *ᵥ v) k + t * (GR *ᵥ d) k := by
      intro k; rw [Matrix.mulVec_add, Matrix.mulVec_smul]; simp
    have hfeas : ∀ k, 0 ≤ (GR *ᵥ (v + t • d)) k := by
      intro k
      rw [hlinG]
      by_cases hk : k ∈ Neg
      · have hk' : (GR *ᵥ d) k < 0 := (Finset.mem_filter.mp hk).2
        have := hmin k hk
        rw [div_le_div_iff₀ (by linarith : (0:ℝ) < -(GR *ᵥ d) k0) (by linarith : (0:ℝ) < -(GR *ᵥ d) k)] at this
        have h2 : t * (GR *ᵥ d) k ≥ -(GR *ᵥ v) k := by
          have e : t * (GR *ᵥ d) k = (GR *ᵥ v) k0 * (GR *ᵥ d) k / -(GR *ᵥ d) k0 := by rw [ht]; ring
          rw [e, ge_iff_le, le_div_iff₀ (by linarith : (0:ℝ) < -(GR *ᵥ d) k0)]
          linarith
        linarith
      · have : 0 ≤ (GR *ᵥ d) k := by
          by_contra h; push Not at h; exact hk (Finset.mem_filter.mpr ⟨mem_univ _, h⟩)
        nlinarith only [this, htpos, hvG k]
    have hopt' : Opt (v + t • d) := ⟨hfeas, by rw [hlinS, hS]; simp [hvS], by rw [hlin, hod]; simp [hvo]⟩
    have hsub : tight v ⊆ tight (v + t • d) := by
      intro k hk
      have hk2 := (Finset.mem_filter.mp hk).2
      exact Finset.mem_filter.mpr ⟨mem_univ _, by rw [hlinG, hk2, hd k hk]; ring⟩
    have hk0t : k0 ∈ tight (v + t • d) := by
      refine Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩
      have hne0 : (GR *ᵥ d) k0 ≠ 0 := ne_of_lt hk0'
      rw [hlinG, ht]; field_simp; ring
    have hk0n : k0 ∉ tight v := by
      intro h; linarith [hd k0 h]
    have hlt : (tight v).card < (tight (v + t • d)).card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hk0n (h ▸ hk0t)⟩)
    have := hmax _ hopt'
    omega
  -- the tight system as a rational matrix
  let T := tight v
  let L : Matrix (T ⊕ Unit) C ℚ := fun r c => match r with
    | Sum.inl k => G k.1 c
    | Sum.inr _ => S c
  let b : (T ⊕ Unit) → ℚ := fun r => match r with
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  have hrow : ∀ (d : C → ℝ) (r : T ⊕ Unit), ((L.map (Rat.castHom ℝ)) *ᵥ d) r =
      match r with
      | Sum.inl k => (GR *ᵥ d) k.1
      | Sum.inr _ => SR ⬝ᵥ d := by
    intro d r
    rcases r with k | u
    · simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, GR]; rfl
    · simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, SR]; rfl
  obtain ⟨q, hq⟩ := MNR43_rat_solution L b v (by
      intro d hd
      apply hinj d
      · intro k hk
        have := congrFun hd (Sum.inl ⟨k, hk⟩)
        rw [hrow] at this; simpa using this
      · have := congrFun hd (Sum.inr ())
        rw [hrow] at this; simpa using this) (by
      funext r
      rw [hrow]
      rcases r with k | u
      · simp only [b]; push_cast; exact (Finset.mem_filter.mp k.2).2
      · simp only [b]; push_cast; exact hvS)
  exact ⟨v, hvG, hvS, hvo, q, hq⟩
end MNR43V


theorem MNR43_pp_congr {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (x x' : Mixed n) (i : Fin m)
    (h : ∀ j, j ≠ i → x j = x' j) (a : Fin (n i)) :
    DGPNash.NashMap.purePayoff u x i a = DGPNash.NashMap.purePayoff u x' i a := by
  unfold DGPNash.NashMap.purePayoff
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · rw [Function.update_of_ne hj, Function.update_of_ne hj, h j hj]

theorem MNR43_br_exists {m : ℕ} {n : Fin m → ℕ} (hn : ∀ i, 0 < n i) (u : Utility n)
    (r : Fin m → ℕ) (hr : ∀ i, r i ≤ m)
    (F : ((i : Fin m) → Fin (n i)) → Fin m → Mixed n)
    (hF : ∀ A A' i, (∀ j, r j < r i → A j = A' j) → ∀ j, j ≠ i → F A i j = F A' i j) :
    ∃ A : (i : Fin m) → Fin (n i), ∀ i a,
      DGPNash.NashMap.purePayoff u (F A i) i a ≤ DGPNash.NashMap.purePayoff u (F A i) i (A i) := by
  classical
  suffices H : ∀ K : ℕ, ∃ A : (i : Fin m) → Fin (n i), ∀ i, r i < K → ∀ a,
      DGPNash.NashMap.purePayoff u (F A i) i a ≤ DGPNash.NashMap.purePayoff u (F A i) i (A i) by
    obtain ⟨A, hA⟩ := H (m + 1)
    exact ⟨A, fun i => hA i (by have := hr i; omega)⟩
  intro K
  induction K with
  | zero => exact ⟨fun i => ⟨0, hn i⟩, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ K ih =>
    obtain ⟨A, hA⟩ := ih
    have hmax : ∀ i, ∃ b : Fin (n i), ∀ a,
        DGPNash.NashMap.purePayoff u (F A i) i a ≤ DGPNash.NashMap.purePayoff u (F A i) i b := by
      intro i
      obtain ⟨b, -, hb⟩ := Finset.exists_max_image univ
        (fun a => DGPNash.NashMap.purePayoff u (F A i) i a) ⟨⟨0, hn i⟩, mem_univ _⟩
      exact ⟨b, fun a => hb a (mem_univ a)⟩
    choose g hg using hmax
    refine ⟨fun i => if r i = K then g i else A i, fun i hi a => ?_⟩
    have hagree : ∀ j, j ≠ i → F (fun i => if r i = K then g i else A i) i j = F A i j := by
      apply hF
      intro j hj
      have : r j ≠ K := by omega
      simp [this]
    rw [MNR43_pp_congr u _ _ i hagree, MNR43_pp_congr u _ _ i hagree]
    by_cases hK : r i = K
    · simp only [hK, if_true]; exact hg i a
    · simp only [hK, if_false]; exact hA i (by omega) a

theorem MNR43_rev_exists {m : ℕ} {n : Fin m → ℕ} (hn : ∀ i, 0 < n i) (u : Utility n)
    (y : Mixed n) (δ : Fin m → ℝ) : ∃ arev, IsRevBR u y δ arev := by
  obtain ⟨A, hA⟩ := MNR43_br_exists hn u (fun i => m - i.val) (fun i => by omega)
    (fun A i => fun j => if j < i then y j else revSweep y δ A j) (by
      intro A A' i hAA j hji
      show (if j < i then _ else _) = (if j < i then _ else _)
      split_ifs with h
      · rfl
      · have hlt : i < j := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hji)
        have : A j = A' j := hAA j (by
          have := j.isLt; have : i.val < j.val := hlt; omega)
        unfold revSweep; rw [this])
  exact ⟨A, hA⟩

theorem MNR43_fwd_exists {m : ℕ} {n : Fin m → ℕ} (hn : ∀ i, 0 < n i) (u : Utility n)
    (xt : Mixed n) (e : Fin m → ℝ) : ∃ acor, IsFwdBR u xt e acor := by
  obtain ⟨A, hA⟩ := MNR43_br_exists hn u (fun i => i.val) (fun i => by have := i.isLt; omega)
    (fun A i => fun j => if j < i then fwdSweep xt e A j else xt j) (by
      intro A A' i hAA j hji
      show (if j < i then _ else _) = (if j < i then _ else _)
      split_ifs with h
      · have : A j = A' j := hAA j h
        unfold fwdSweep; rw [this]
      · rfl)
  exact ⟨A, hA⟩

theorem MNR43_affine {ι : Type*} [Fintype ι] (S : Set (ι → ℝ)) (hS : Convex ℝ S) (K : ℝ)
    (c : ι → ℝ) :
    ConvexOn ℝ S (fun z => K + ∑ i, z i * c i) ∧ ConcaveOn ℝ S (fun z => K + ∑ i, z i * c i) := by
  have key : ∀ (z z' : ι → ℝ) (a b : ℝ), a + b = 1 →
      K + ∑ i, (a • z + b • z') i * c i = a • (K + ∑ i, z i * c i) + b • (K + ∑ i, z' i * c i) := by
    intro z z' a b hab
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_assoc,
      ← Finset.mul_sum]
    linear_combination (-K) * hab
  exact ⟨⟨hS, fun z _ z' _ a b _ _ hab => (key z z' a b hab).le⟩,
    ⟨hS, fun z _ z' _ a b _ _ hab => (key z z' a b hab).ge⟩⟩

theorem MNR43_minimax {P Q : Type*} [Fintype P] [Fintype Q] [Nonempty P] [Nonempty Q]
    [DecidableEq P] [DecidableEq Q] (g : P → ℝ) (C : Q → P → ℝ) :
    ∃ (w : P → ℝ) (α : ℝ), (∀ p, 0 ≤ w p) ∧ ∑ p, w p = 1 ∧ 0 ≤ α ∧
      (∀ q, 0 ≤ α + ∑ p, w p * C q p) ∧
      ∃ z : Q → ℝ, (∀ q, 0 ≤ z q) ∧ ∑ q, z q ≤ 1 ∧
        ∀ p, g p + ∑ q, z q * C q p ≤ ∑ p, w p * g p - α := by
  classical
  let f : (Q → ℝ) → (P → ℝ) → ℝ := fun z w => ∑ p, w p * (g p + ∑ q, z q * C q p)
  have hswap : ∀ z w, f z w = (∑ p, w p * g p) + ∑ q, z q * (∑ p, w p * C q p) := by
    intro z w
    simp only [f, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by ring
  have hswap2 : ∀ z w, f z w = 0 + ∑ p, w p * (g p + ∑ q, z q * C q p) := by
    intro z w; simp [f]
  let X : Set (Q → ℝ) := {z | (∀ q, 0 ≤ z q) ∧ ∑ q, z q ≤ 1}
  let Y : Set (P → ℝ) := stdSimplex ℝ P
  have hXc : Convex ℝ X := by
    intro z hz z' hz' a b ha hb hab
    refine ⟨fun q => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hz.1 q)) (mul_nonneg hb (hz'.1 q))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
      nlinarith [hz.2, hz'.2]
  have hXk : IsCompact X := by
    have hsub : X ⊆ Set.univ.pi (fun _ : Q => Set.Icc (0:ℝ) 1) := by
      intro z hz q _
      refine ⟨hz.1 q, le_trans ?_ hz.2⟩
      exact Finset.single_le_sum (fun q _ => hz.1 q) (mem_univ q)
    refine (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset ?_ hsub
    have h1 : IsClosed {z : Q → ℝ | ∀ q, 0 ≤ z q} := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun q => isClosed_le continuous_const (continuous_apply q)
    have h2 : IsClosed {z : Q → ℝ | ∑ q, z q ≤ 1} :=
      isClosed_le (continuous_finsetSum _ fun q _ => continuous_apply q) continuous_const
    exact h1.inter h2
  obtain ⟨p0⟩ := ‹Nonempty P›
  have hXne : X.Nonempty := ⟨0, fun q => le_rfl, by simp⟩
  have hYne : Y.Nonempty := ⟨fun p => if p = p0 then 1 else 0, fun p => by dsimp only; split_ifs <;> norm_num,
    by simp⟩
  have hcontz : ∀ w, Continuous fun z => f z w := by
    intro w
    have : (fun z => f z w) = fun z => (∑ p, w p * g p) + ∑ q, z q * (∑ p, w p * C q p) := by
      funext z; exact hswap z w
    rw [this]
    exact continuous_const.add (continuous_finsetSum _ fun q _ => (continuous_apply q).mul continuous_const)
  have hcontw : ∀ z, Continuous fun w => f z w := by
    intro z
    exact continuous_finsetSum _ fun p _ => (continuous_apply p).mul continuous_const
  obtain ⟨zs, hzs, ws, hws, hsad⟩ := Sion.exists_isSaddlePointOn (f := f) hXne hXc hXk
    (fun w _ => (hcontz w).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun w _ => by
      have : (fun z => f z w) = fun z => (∑ p, w p * g p) + ∑ q, z q * (∑ p, w p * C q p) := by
        funext z; exact hswap z w
      rw [this]; exact (MNR43_affine X hXc _ _).1.quasiconvexOn)
    (convex_stdSimplex ℝ P) hYne (isCompact_stdSimplex ℝ P)
    (fun z _ => (hcontw z).upperSemicontinuous.upperSemicontinuousOn _)
    (fun z _ => by
      have : (fun w => f z w) = fun w => 0 + ∑ p, w p * (g p + ∑ q, z q * C q p) := by
        funext w; exact hswap2 z w
      rw [this]; exact (MNR43_affine Y (convex_stdSimplex ℝ P) _ _).2.quasiconcaveOn)
  -- dual multiplier
  let c : Q → ℝ := fun q => ∑ p, ws p * C q p
  obtain ⟨q0, -, hq0⟩ := Finset.exists_max_image univ (fun q => -c q) univ_nonempty
  refine ⟨ws, max 0 (-c q0), hws.1, hws.2, le_max_left _ _, fun q => ?_, zs, hzs.1, hzs.2, fun p => ?_⟩
  · have := hq0 q (mem_univ q); have := le_max_right 0 (-c q0); show 0 ≤ _ + c q; linarith
  · have hep : (fun p' => if p' = p then (1:ℝ) else 0) ∈ Y :=
      ⟨fun p' => by dsimp only; split_ifs <;> norm_num, by simp⟩
    have hle : ∀ z ∈ X, g p + ∑ q, zs q * C q p ≤ f z ws := by
      intro z hz
      have := hsad z hz _ hep
      simpa [f] using this
    rcases le_or_gt (-c q0) 0 with h | h
    · rw [max_eq_left h]
      have h0 := hle 0 ⟨fun q => le_rfl, by simp⟩
      rw [hswap] at h0; simpa using h0
    · rw [max_eq_right h.le]
      have hz1 : (fun q => if q = q0 then (1:ℝ) else 0) ∈ X :=
        ⟨fun q => by dsimp only; split_ifs <;> norm_num, by simp⟩
      have h0 := hle _ hz1
      rw [hswap] at h0; simpa [c] using h0



theorem MNR43_swap {m : ℕ} {n : Fin m → ℕ}
    (F : (i : Fin m) → Fin (n i) → (j : Fin m) → Fin (n j) → ℝ) :
    ∑ i, ∑ a, ∑ j, ∑ b, F i a j b = ∑ j, ∑ b, ∑ i, ∑ a, F i a j b := by
  have L : ∑ i, ∑ a, ∑ j, ∑ b, F i a j b =
      ∑ p : (Σ i, Fin (n i)), ∑ q : (Σ j, Fin (n j)), F p.1 p.2 q.1 q.2 := by
    rw [Fintype.sum_sigma]
    refine sum_congr rfl fun i _ => sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_sigma]
  have R : ∑ j, ∑ b, ∑ i, ∑ a, F i a j b =
      ∑ q : (Σ j, Fin (n j)), ∑ p : (Σ i, Fin (n i)), F p.1 p.2 q.1 q.2 := by
    rw [Fintype.sum_sigma]
    refine sum_congr rfl fun i _ => sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_sigma]
  rw [L, R, Finset.sum_comm]

theorem MNR43_weak {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (x : Mixed n) (η : ℝ)
    (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ) (hw : DualFeasible u x η w α)
    (z : (j : Fin m) → Fin (n j) → ℝ) (hz : LPFeasible z) :
    dualObj u x w α ≤ lpObj u x η z := by
  obtain ⟨hw0, hw1, hα0, hα⟩ := hw
  obtain ⟨hz0, hz1⟩ := hz
  have hT : ∀ i a, gain u x i a + η * ∑ j, ∑ b, z j b * repl u x j b i a ≤ lpObj u x η z :=
    fun i a => le_ciSup (f := fun p : (Σ i : Fin m, Fin (n i)) =>
      gain u x p.1 p.2 + η * ∑ j, ∑ b, z j b * repl u x j b p.1 p.2)
      (Set.finite_range _).bddAbove ⟨i, a⟩
  -- Σ w (g + η Σ z B) ≤ lpObj
  have h1 : ∑ i, ∑ a, w i a * (gain u x i a + η * ∑ j, ∑ b, z j b * repl u x j b i a) ≤
      lpObj u x η z := by
    calc _ ≤ ∑ i, ∑ a, w i a * lpObj u x η z :=
          sum_le_sum fun i _ => sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hT i a) (hw0 i a)
      _ = lpObj u x η z := by
          rw [show ∑ i, ∑ a, w i a * lpObj u x η z = (∑ i, ∑ a, w i a) * lpObj u x η z by
            rw [Finset.sum_mul]; exact sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm,
            hw1, one_mul]
  -- swap
  have h2 : ∑ i, ∑ a, w i a * (gain u x i a + η * ∑ j, ∑ b, z j b * repl u x j b i a) =
      dualObj u x w α + α + ∑ j, ∑ b, z j b * (η * ∑ i, ∑ a, w i a * repl u x j b i a) := by
    unfold dualObj
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    have := MNR43_swap (fun i a j b => w i a * (η * (z j b * repl u x j b i a)))
    rw [this]
    have e2 : ∑ j, ∑ b, ∑ i, ∑ a, w i a * (η * (z j b * repl u x j b i a)) =
        ∑ j, ∑ b, ∑ i, ∑ a, z j b * (η * (w i a * repl u x j b i a)) :=
      sum_congr rfl fun j _ => sum_congr rfl fun b _ => sum_congr rfl fun i _ =>
        sum_congr rfl fun a _ => by ring
    rw [e2]; ring
  have h3 : -α ≤ ∑ j, ∑ b, z j b * (η * ∑ i, ∑ a, w i a * repl u x j b i a) := by
    have hA : ∑ j, ∑ b, z j b * (-α) ≤ ∑ j, ∑ b, z j b * (η * ∑ i, ∑ a, w i a * repl u x j b i a) :=
      sum_le_sum fun j _ => sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_left (by linarith [hα j b]) (hz0 j b)
    have hB : ∑ j, ∑ b, z j b * (-α) = -α * ∑ j, ∑ b, z j b := by
      simp only [Finset.mul_sum]; exact sum_congr rfl fun j _ => sum_congr rfl fun b _ => by ring
    have hC : α * ∑ j, ∑ b, z j b ≤ α * 1 := mul_le_mul_of_nonneg_left hz1 hα0
    linarith
  linarith

theorem MNR43_le_value {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (x : Mixed n) (η : ℝ)
    (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ) (hw : DualFeasible u x η w α) :
    dualObj u x w α ≤ lpValue u x η := by
  unfold lpValue
  refine le_csInf ⟨lpObj u x η 0, 0, ⟨fun _ _ => le_rfl, by simp⟩, rfl⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  exact MNR43_weak u x η w α hw z hz

theorem MNR43_value_eq {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (x : Mixed n) (η : ℝ)
    (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ) (hw : DualFeasible u x η w α)
    (z : (j : Fin m) → Fin (n j) → ℝ) (hz : LPFeasible z) (hle : lpObj u x η z ≤ dualObj u x w α) :
    DualOptimal u x η w α := by
  refine ⟨hw, le_antisymm (MNR43_le_value u x η w α hw) ?_⟩
  unfold lpValue
  have hbdd : BddBelow (lpObj u x η '' {z | LPFeasible z}) := by
    refine ⟨dualObj u x w α, ?_⟩
    rintro _ ⟨z', hz', rfl⟩
    exact MNR43_weak u x η w α hw z' hz'
  exact (csInf_le hbdd ⟨z, hz, rfl⟩).trans hle

theorem MNR43_strong {m : ℕ} {n : Fin m → ℕ} (hm : 1 ≤ m) (hn : ∀ i, 0 < n i)
    (u : Utility n) (x : Mixed n) (η : ℝ) :
    ∃ (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ), DualOptimal u x η w α := by
  classical
  haveI : Nonempty (Σ i : Fin m, Fin (n i)) := ⟨⟨⟨0, hm⟩, ⟨0, hn _⟩⟩⟩
  obtain ⟨w', α, hw0, hw1, hα0, hαq, z', hz0, hz1, hb⟩ := MNR43_minimax
    (P := Σ i : Fin m, Fin (n i)) (Q := Σ j : Fin m, Fin (n j))
    (fun p => gain u x p.1 p.2) (fun q p => η * repl u x q.1 q.2 p.1 p.2)
  have hconv : ∀ (F : (Σ i : Fin m, Fin (n i)) → ℝ), ∑ p, F p = ∑ i, ∑ a, F ⟨i, a⟩ :=
    fun F => Fintype.sum_sigma F
  have hw : DualFeasible u x η (fun i a => w' ⟨i, a⟩) α := by
    refine ⟨fun i a => hw0 _, by rw [← hw1, hconv], hα0, fun j b => ?_⟩
    have := hαq ⟨j, b⟩
    rw [hconv] at this
    simp only [Finset.mul_sum] at this ⊢
    convert this using 3 with i _ a _
    exact sum_congr rfl fun a _ => by ring
  refine ⟨_, α, MNR43_value_eq u x η _ α hw (fun j b => z' ⟨j, b⟩)
    ⟨fun j b => hz0 _, by rw [← hconv]; exact hz1⟩ ?_⟩
  unfold lpObj
  refine ciSup_le fun p => ?_
  have := hb p
  rw [hconv, hconv] at this
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq rfl))
  congr 1
  rw [Finset.mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact sum_congr rfl fun b _ => by ring

open Matrix in
theorem MNR43_rat_dual {m : ℕ} {n : Fin m → ℕ} (hm : 1 ≤ m) (hn : ∀ i, 0 < n i)
    (u : Utility n) (x : Mixed n) (η : ℝ)
    (hB : ∀ (j : Fin m) (b : Fin (n j)) (i : Fin m) (a : Fin (n i)), IsRat (η * repl u x j b i a)) :
    ∃ (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ), DualOptimal u x η w α ∧ ∀ i a, IsRat (w i a) := by
  classical
  choose Bq hBq using fun (q : Σ i : Fin m, Fin (n i)) (p : Σ i : Fin m, Fin (n i)) =>
    hB q.1 q.2 p.1 p.2
  have hconv : ∀ (F : (Σ i : Fin m, Fin (n i)) → ℝ), ∑ p, F p = ∑ i, ∑ a, F ⟨i, a⟩ :=
    fun F => Fintype.sum_sigma F
  let G : Matrix ((Σ i : Fin m, Fin (n i)) ⊕ Option (Σ i : Fin m, Fin (n i)))
      ((Σ i : Fin m, Fin (n i)) ⊕ Unit) ℚ := fun k c =>
    match k, c with
    | Sum.inl p, Sum.inl p' => if p = p' then 1 else 0
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr none, Sum.inl _ => 0
    | Sum.inr none, Sum.inr _ => 1
    | Sum.inr (some q), Sum.inl p => Bq q p
    | Sum.inr (some _), Sum.inr _ => 1
  let S : (Σ i : Fin m, Fin (n i)) ⊕ Unit → ℚ := fun c =>
    match c with
    | Sum.inl _ => 1
    | Sum.inr _ => 0
  let o : (Σ i : Fin m, Fin (n i)) ⊕ Unit → ℝ := fun c =>
    match c with
    | Sum.inl p => gain u x p.1 p.2
    | Sum.inr _ => -1
  have hG1 : ∀ p p', G (Sum.inl p) (Sum.inl p') = if p = p' then 1 else 0 := fun _ _ => rfl
  have hG2 : ∀ p, G (Sum.inl p) (Sum.inr ()) = 0 := fun _ => rfl
  have hG3 : ∀ p, G (Sum.inr none) (Sum.inl p) = 0 := fun _ => rfl
  have hG4 : G (Sum.inr none) (Sum.inr ()) = 1 := rfl
  have hG5 : ∀ q p, G (Sum.inr (some q)) (Sum.inl p) = Bq q p := fun _ _ => rfl
  have hG6 : ∀ q, G (Sum.inr (some q)) (Sum.inr ()) = 1 := fun _ => rfl
  clear_value G
  have hrow1 : ∀ v p, ((G.map (Rat.castHom ℝ)) *ᵥ v) (Sum.inl p) = v (Sum.inl p) := by
    intro v p
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.map_apply, hG1, hG2, hG3, hG4, apply_ite, ite_mul]
  have hrow2 : ∀ v, ((G.map (Rat.castHom ℝ)) *ᵥ v) (Sum.inr none) = v (Sum.inr ()) := by
    intro v
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.map_apply, hG1, hG2, hG3, hG4, apply_ite, ite_mul]
  have hrow3 : ∀ v q, ((G.map (Rat.castHom ℝ)) *ᵥ v) (Sum.inr (some q)) =
      ∑ p, (η * repl u x q.1 q.2 p.1 p.2) * v (Sum.inl p) + v (Sum.inr ()) := by
    intro v q
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.map_apply, hG5, hG6, hBq]
  have hS : ∀ v, (fun c => (S c : ℝ)) ⬝ᵥ v = ∑ p, v (Sum.inl p) := by
    intro v; simp [dotProduct, Fintype.sum_sum_type, S]
  have ho : ∀ v, o ⬝ᵥ v = ∑ p, gain u x p.1 p.2 * v (Sum.inl p) - v (Sum.inr ()) := by
    intro v; simp [dotProduct, Fintype.sum_sum_type, o]; ring
  -- from a vector to a dual pair
  have hfeas : ∀ v, (∀ k, 0 ≤ ((G.map (Rat.castHom ℝ)) *ᵥ v) k) →
      (fun c => (S c : ℝ)) ⬝ᵥ v = 1 →
      DualFeasible u x η (fun i a => v (Sum.inl ⟨i, a⟩)) (v (Sum.inr ())) ∧
      o ⬝ᵥ v = dualObj u x (fun i a => v (Sum.inl ⟨i, a⟩)) (v (Sum.inr ())) := by
    intro v hk hs
    refine ⟨⟨fun i a => by have := hk (Sum.inl ⟨i, a⟩); rwa [hrow1] at this, ?_, ?_, ?_⟩, ?_⟩
    · rw [hS, hconv] at hs; exact hs
    · have := hk (Sum.inr none); rwa [hrow2] at this
    · intro j b
      have := hk (Sum.inr (some ⟨j, b⟩))
      rw [hrow3, hconv] at this
      rw [Finset.mul_sum]
      refine le_of_le_of_eq this ?_
      rw [add_comm]; congr 1
      refine sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact sum_congr rfl fun a _ => by ring
    · rw [ho, hconv]; unfold dualObj
      congr 1
      exact sum_congr rfl fun i _ => sum_congr rfl fun a _ => by ring
  -- vertex
  obtain ⟨v, hvk, hvs, hvo, qv, hqv⟩ := MNR43_vertex G S o (lpValue u x η)
    (fun v hk hs => by
      obtain ⟨hf, he⟩ := hfeas v hk hs
      rw [he]; exact MNR43_le_value u x η _ _ hf)
    (by
      obtain ⟨w, α, hwf, hwo⟩ := MNR43_strong hm hn u x η
      refine ⟨Sum.elim (fun p => w p.1 p.2) (fun _ => α), fun k => ?_, ?_, ?_⟩
      · rcases k with p | (_ | q)
        · rw [hrow1]; exact hwf.1 _ _
        · rw [hrow2]; exact hwf.2.2.1
        · rw [hrow3]
          have := hwf.2.2.2 q.1 q.2
          refine le_of_le_of_eq this ?_
          simp only [Sum.elim_inl, Sum.elim_inr]
          rw [hconv, Finset.mul_sum, add_comm]; congr 1
          refine sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact sum_congr rfl fun a _ => by ring
      · rw [hS, hconv]; exact hwf.2.1
      · rw [ho, hconv, ← hwo]; simp only [Sum.elim_inl, Sum.elim_inr]; unfold dualObj
        congr 1; exact sum_congr rfl fun i _ => sum_congr rfl fun a _ => by ring)
    (by
      intro d hsd hod hd0
      by_contra hcon
      push_neg at hcon
      have hd1 : ∀ p, 0 ≤ d (Sum.inl p) := fun p => by have := hcon (Sum.inl p); rwa [hrow1] at this
      rw [hS] at hsd
      have hz : ∀ p, d (Sum.inl p) = 0 :=
        fun p => (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => hd1 p)).mp hsd p (mem_univ p)
      rw [ho] at hod
      simp only [hz, mul_zero, Finset.sum_const_zero, zero_sub, neg_eq_zero] at hod
      apply hd0
      funext c
      rcases c with p | ⟨⟩
      · exact hz p
      · exact hod)
  obtain ⟨hf, he⟩ := hfeas v hvk hvs
  refine ⟨_, _, ⟨hf, by rw [← he, hvo]⟩, fun i a => ⟨qv (Sum.inl ⟨i, a⟩), (hqv _).symm⟩⟩


set_option maxHeartbeats 8000000 in
theorem solution {σ : ℚ} (ctrl : Controls σ) {m : ℕ} {n : Fin m → ℕ}
    (hm : ctrl.m0 ≤ m) (hn : ∀ i, 0 < n i) (u : Utility n) (hu : BoundedGame u)
    {kk : ℕ} {s : State n} (hs : Reach ctrl u kk s) (hterm : ¬ Terminal σ u s)
    (hfail : ¬ Passes ctrl u s) :
    ((∀ i a, IsRat (u i a)) → ∃ s' : State n, RepairStep ctrl u s s') ∧
    ∀ (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ) (arev acor : (i : Fin m) → Fin (n i)),
      DualOptimal u s.x ctrl.η w α →
      IsRevBR u (rY ctrl.knobs s w) (rDelta ctrl.knobs s w) arev →
      IsFwdBR u (rXt ctrl.knobs s w arev) (rE ctrl.knobs u s w arev) acor →
      let k := ctrl.knobs
      let E := rEtot k u s w arev
      let s' := repairState k u s w arev acor
      RepairLegal k u s w arev ∧ AGT.IsMixedProfile s'.x ∧
        k.c * scaled u s.x + k.Dsh s.H - E ≤ scaled u s'.x ∧
        0 ≤ E ∧ E ≤ 120 * (ctrl.u : ℝ) / m ∧
        s'.h = k.c • (s.h + k.t • rGamma k s w) ∧ s'.H = k.c * (s.H + k.t) ∧
        s'.H ≤ k.L0 ∧ ∀ i, (m : ℝ) * s'.h i - s'.H ≤ k.R0 * s'.H := by
  have hm1 : 1 ≤ m := by
    have hdq : (0:ℚ) < ctrl.d := ctrl.d_pos
    have hd : (0:ℝ) < ctrl.d := by exact_mod_cast hdq
    have h1 := ctrl.m0_ge_d
    have : (0:ℝ) < 66 / (ctrl.d:ℝ) := by positivity
    have h2 : (ctrl.m0:ℝ) ≤ m := by exact_mod_cast hm
    have : (0:ℝ) < m := by linarith
    exact_mod_cast (show (0:ℕ) < m by exact_mod_cast this)
  have h512 := MultiNashRepair.lemma_5_12 ctrl hm hn u hu hs
  dsimp only at h512
  obtain ⟨⟨hx, hxr, hg, hI1, hH⟩, ⟨hh0, -, hHL, hv⟩, hI3, hI4, -, -, -⟩ := h512
  refine ⟨fun hur => ?_, ?_⟩
  · -- existence of a repair step
    have hxq := hxr hur
    have hB : ∀ (j : Fin m) (b : Fin (n j)) (i : Fin m) (a : Fin (n i)),
        IsRat ((ctrl.η : ℝ) * repl u s.x j b i a) := by
      intro j b i a
      refine MNRQ_mul (MNRQ_cast _) ?_
      unfold repl
      exact MNRQ_sub ((MNRQ_Reg hm1 hn u hur _
        (MNRQ_update s.x hxq j _ (fun c => MNRQ_ePure b c))).1 i a)
        ((MNRQ_Reg hm1 hn u hur s.x hxq).1 i a)
    obtain ⟨w, α, hw, hwr⟩ := MNR43_rat_dual hm1 hn u s.x ctrl.η hB
    obtain ⟨arev, hrev⟩ := MNR43_rev_exists hn u (rY ctrl.knobs s w) (rDelta ctrl.knobs s w)
    obtain ⟨acor, hfwd⟩ := MNR43_fwd_exists hn u (rXt ctrl.knobs s w arev)
      (rE ctrl.knobs u s w arev)
    exact ⟨_, hfail, w, α, arev, acor, hw, hwr, hrev, hfwd, rfl⟩
  · intro w α arev acor hw hrev hfwd
    have hL1 := MNR512_repair ctrl hm hn u hu s hx hterm (fun g hgm => (hg g hgm).1) hI1 hH
      ⟨hh0, hHL, hv⟩ hI3 hI4 hfail w α arev hw
    dsimp only at hL1
    obtain ⟨hRL, -, -, -, hh'⟩ := hL1
    have hRL' := hRL
    obtain ⟨-, -, -, -, -, -, -, hfw01, -, hxtm⟩ := hRL'
    have h56 := MultiNashRepair.lemma_5_6 ctrl hm hn u hu s hx hterm
      (fun g hgm => ⟨(hg g hgm).1, (hg g hgm).2.2.1, (hg g hgm).2.2.2⟩) hI1 hH ⟨hh0, hHL, hv⟩ hI3 hI4
      hfail w α arev acor hw hrev hfwd
    dsimp only at h56
    obtain ⟨hE0, hE1, -, -, hsc⟩ := h56
    dsimp only
    refine ⟨hRL, ?_, hsc, hE0, hE1, rfl, rfl, hh'.2.2.1, hh'.2.2.2⟩
    intro j
    show AGT.IsLottery (fwdSweep (rXt ctrl.knobs s w arev) (rE ctrl.knobs u s w arev) acor j)
    refine ⟨fun c => ?_, ?_⟩
    · rw [MNR54_fwd_apply]
      exact add_nonneg (mul_nonneg (by linarith [(hfw01 j).2]) ((hxtm j).1 c))
        (mul_nonneg (hfw01 j).1 (MNR54_ePure_nonneg (acor j) c))
    · simp only [MNR54_fwd_apply, Finset.sum_add_distrib, ← Finset.mul_sum, (hxtm j).2,
        (MNR51_ePure_lottery (acor j)).2]; ring
