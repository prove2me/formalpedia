-- Prove2me | solution 1 for MultiNashRepair.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:13:47.739483+00:00
-- url     : https://prove2.me/submissions/2976bc84-73e1-4c94-8afb-7d37978c5d81

import Mathlib
import Definitions.Def_NashAmplification_Filtering_Model
import Definitions.Def_MultiNashRepair_IDRH
import Theorems.Thm_MultiNashRepair_controls_5_7
import Theorems.Thm_MultiNashRepair_lemma_5_11
import Theorems.Thm_MultiNashRepair_lemma_5_1
import Theorems.Thm_MultiNashRepair_lemma_5_3
import Theorems.Thm_MultiNashRepair_lemma_5_4
import Theorems.Thm_MultiNashRepair_lemma_5_5

open NashAmplification.Filtering (Mixed Utility Tuple BoundedGame)
open Finset
open MultiNashRepair
theorem MNR51_sum_pp {m : ℕ} {n : Fin m → ℕ} (y : Mixed n) (hy : AGT.IsMixedProfile y) :
    ∑ s : Tuple n, AGT.profileProb y s = 1 := by
  unfold AGT.profileProb
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one (fun j _ => (hy j).2)

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

theorem MNR56_prod_lb {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1) :
    1 - ∑ i ∈ S, a i + ((∑ i ∈ S, a i) ^ 2 - ∑ i ∈ S, a i ^ 2) / 2 - (∑ i ∈ S, a i) ^ 3 / 6
      ≤ ∏ i ∈ S, (1 - a i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert b S hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb, Finset.sum_insert hb]
    set T := ∑ i ∈ S, a i with hT
    set Q := ∑ i ∈ S, a i ^ 2 with hQ
    have hT0 : 0 ≤ T := Finset.sum_nonneg (fun i _ => h0 i)
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun i _ => sq_nonneg (a i))
    have hc : 0 ≤ 1 - a b := by linarith [h1 b]
    have k := mul_le_mul_of_nonneg_left ih hc
    have hb0 := h0 b
    nlinarith only [k, mul_nonneg hb0 hQ0, mul_nonneg hb0 (pow_nonneg hT0 3),
      mul_nonneg hT0 (sq_nonneg (a b)), pow_nonneg hb0 3]

theorem MNR56_swap {m : ℕ} (f : Fin m → Fin m → ℝ) :
    ∑ i, ∑ j ∈ univ.erase i, f i j = ∑ j, ∑ i ∈ univ.erase j, f i j := by
  have e1 : ∀ i, ∑ j ∈ univ.erase i, f i j = ∑ j, f i j - f i i := fun i => by
    rw [Finset.sum_erase_eq_sub (mem_univ i)]
  have e2 : ∀ j, ∑ i ∈ univ.erase j, f i j = ∑ i, f i j - f j j := fun j => by
    rw [Finset.sum_erase_eq_sub (mem_univ j)]
  simp only [e1, e2, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

theorem MNR56_cur_err {m : ℕ} (C t u M : ℝ) (α ω γ d0 : Fin m → ℝ) (dB dE : Fin m → Fin m → ℝ)
    (hM : 0 < M) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (ht0 : 0 ≤ t) (hu0 : 0 ≤ u)
    (hα0 : ∀ i, 0 ≤ α i) (hαγ : ∀ i, α i ≤ 2 * t * γ i) (hγ0 : ∀ i, 0 ≤ γ i)
    (hγ1 : ∑ i, γ i = 1) (hγm : ∀ i, γ i ≤ 3 / M)
    (hω0 : ∀ i, 0 ≤ ω i) (hωm : ∀ i, ω i ≤ 3 * u / M) (hωs : ∑ i, ω i ≤ 2 * u)
    (hd0 : ∀ i, 0 ≤ d0 i) (hdB : ∀ i j, 0 ≤ dB i j) (hdE : ∀ i j, 0 ≤ dE i j)
    (hc0 : ∑ i, γ i * d0 i ≤ 9 / M) (hcB : ∀ j, ∑ i ∈ univ.erase j, γ i * dB i j ≤ 9 / M)
    (hcE : ∀ j, ∑ i ∈ univ.erase j, γ i * dE i j ≤ 9 / M) :
    ∑ i, C * α i * (d0 i + α i + ω i + ∑ j ∈ univ.erase i, α j * dB i j
      + ∑ j ∈ univ.erase i, ω j * dE i j) ≤ (18 * t + 48 * t ^ 2 + 42 * t * u) / M := by
  have hαs : ∑ i, α i ≤ 2 * t := by
    calc ∑ i, α i ≤ ∑ i, 2 * t * γ i := Finset.sum_le_sum (fun i _ => hαγ i)
      _ = 2 * t := by rw [← Finset.mul_sum, hγ1, mul_one]
  have hαm : ∀ i, α i ≤ 6 * t / M := fun i => by
    have := mul_le_mul_of_nonneg_left (hγm i) (by linarith : (0:ℝ) ≤ 2 * t)
    calc α i ≤ 2 * t * γ i := hαγ i
      _ ≤ 2 * t * (3 / M) := this
      _ = 6 * t / M := by ring
  -- the five pieces
  have p1 : ∑ i, α i * d0 i ≤ 2 * t * (9 / M) := by
    calc ∑ i, α i * d0 i ≤ ∑ i, 2 * t * (γ i * d0 i) := Finset.sum_le_sum (fun i _ => by
          have := mul_le_mul_of_nonneg_right (hαγ i) (hd0 i); linarith)
      _ = 2 * t * ∑ i, γ i * d0 i := by rw [Finset.mul_sum]
      _ ≤ 2 * t * (9 / M) := mul_le_mul_of_nonneg_left hc0 (by linarith)
  have p2 : ∑ i, α i * α i ≤ 6 * t / M * (2 * t) := by
    calc ∑ i, α i * α i ≤ ∑ i, 6 * t / M * α i := Finset.sum_le_sum (fun i _ =>
          by have := mul_le_mul_of_nonneg_right (hαm i) (hα0 i); linarith)
      _ = 6 * t / M * ∑ i, α i := by rw [Finset.mul_sum]
      _ ≤ 6 * t / M * (2 * t) := mul_le_mul_of_nonneg_left hαs (by positivity)
  have p3 : ∑ i, α i * ω i ≤ 3 * u / M * (2 * t) := by
    calc ∑ i, α i * ω i ≤ ∑ i, 3 * u / M * α i := Finset.sum_le_sum (fun i _ =>
          by have := mul_le_mul_of_nonneg_left (hωm i) (hα0 i); linarith)
      _ = 3 * u / M * ∑ i, α i := by rw [Finset.mul_sum]
      _ ≤ 3 * u / M * (2 * t) := mul_le_mul_of_nonneg_left hαs (by positivity)
  have p4 : ∑ i, α i * ∑ j ∈ univ.erase i, α j * dB i j ≤ 2 * t * (2 * t * (9 / M)) := by
    have e : ∑ i, α i * ∑ j ∈ univ.erase i, α j * dB i j
        = ∑ j, α j * ∑ i ∈ univ.erase j, α i * dB i j := by
      simp only [Finset.mul_sum]
      rw [MNR56_swap (fun i j => α i * (α j * dB i j))]
      apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring
    rw [e]
    have hin : ∀ j, ∑ i ∈ univ.erase j, α i * dB i j ≤ 2 * t * (9 / M) := fun j => by
      calc ∑ i ∈ univ.erase j, α i * dB i j ≤ ∑ i ∈ univ.erase j, 2 * t * (γ i * dB i j) :=
            Finset.sum_le_sum (fun i _ => by
              have := mul_le_mul_of_nonneg_right (hαγ i) (hdB i j); linarith)
        _ = 2 * t * ∑ i ∈ univ.erase j, γ i * dB i j := by rw [Finset.mul_sum]
        _ ≤ 2 * t * (9 / M) := mul_le_mul_of_nonneg_left (hcB j) (by linarith)
    calc ∑ j, α j * ∑ i ∈ univ.erase j, α i * dB i j ≤ ∑ j, α j * (2 * t * (9 / M)) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hin j) (hα0 j))
      _ = (∑ j, α j) * (2 * t * (9 / M)) := by rw [Finset.sum_mul]
      _ ≤ 2 * t * (2 * t * (9 / M)) := mul_le_mul_of_nonneg_right hαs (by positivity)
  have p5 : ∑ i, α i * ∑ j ∈ univ.erase i, ω j * dE i j ≤ 2 * u * (2 * t * (9 / M)) := by
    have e : ∑ i, α i * ∑ j ∈ univ.erase i, ω j * dE i j
        = ∑ j, ω j * ∑ i ∈ univ.erase j, α i * dE i j := by
      simp only [Finset.mul_sum]
      rw [MNR56_swap (fun i j => α i * (ω j * dE i j))]
      apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring
    rw [e]
    have hin : ∀ j, ∑ i ∈ univ.erase j, α i * dE i j ≤ 2 * t * (9 / M) := fun j => by
      calc ∑ i ∈ univ.erase j, α i * dE i j ≤ ∑ i ∈ univ.erase j, 2 * t * (γ i * dE i j) :=
            Finset.sum_le_sum (fun i _ => by
              have := mul_le_mul_of_nonneg_right (hαγ i) (hdE i j); linarith)
        _ = 2 * t * ∑ i ∈ univ.erase j, γ i * dE i j := by rw [Finset.mul_sum]
        _ ≤ 2 * t * (9 / M) := mul_le_mul_of_nonneg_left (hcE j) (by linarith)
    calc ∑ j, ω j * ∑ i ∈ univ.erase j, α i * dE i j ≤ ∑ j, ω j * (2 * t * (9 / M)) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hin j) (hω0 j))
      _ = (∑ j, ω j) * (2 * t * (9 / M)) := by rw [Finset.sum_mul]
      _ ≤ 2 * u * (2 * t * (9 / M)) := mul_le_mul_of_nonneg_right hωs (by positivity)
  -- combine
  have hX : ∀ i, 0 ≤ d0 i + α i + ω i + ∑ j ∈ univ.erase i, α j * dB i j
      + ∑ j ∈ univ.erase i, ω j * dE i j := fun i => by
    have h1 : 0 ≤ ∑ j ∈ univ.erase i, α j * dB i j := Finset.sum_nonneg (fun j _ => mul_nonneg (hα0 j) (hdB i j))
    have h2 : 0 ≤ ∑ j ∈ univ.erase i, ω j * dE i j := Finset.sum_nonneg (fun j _ => mul_nonneg (hω0 j) (hdE i j))
    linarith [hd0 i, hα0 i, hω0 i]
  have hle : ∑ i, C * α i * (d0 i + α i + ω i + ∑ j ∈ univ.erase i, α j * dB i j
      + ∑ j ∈ univ.erase i, ω j * dE i j) ≤ ∑ i, α i * (d0 i + α i + ω i + ∑ j ∈ univ.erase i, α j * dB i j
      + ∑ j ∈ univ.erase i, ω j * dE i j) := Finset.sum_le_sum (fun i _ => by
        have := mul_le_mul_of_nonneg_right hC1 (mul_nonneg (hα0 i) (hX i)); nlinarith only [this])
  have hsplit : ∑ i, α i * (d0 i + α i + ω i + ∑ j ∈ univ.erase i, α j * dB i j
      + ∑ j ∈ univ.erase i, ω j * dE i j) = ∑ i, α i * d0 i + ∑ i, α i * α i + ∑ i, α i * ω i
        + ∑ i, α i * ∑ j ∈ univ.erase i, α j * dB i j + ∑ i, α i * ∑ j ∈ univ.erase i, ω j * dE i j := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [hsplit] at hle
  have e : (18 * t + 48 * t ^ 2 + 42 * t * u) / M = 2 * t * (9 / M) + 6 * t / M * (2 * t)
      + 3 * u / M * (2 * t) + 2 * t * (2 * t * (9 / M)) + 2 * u * (2 * t * (9 / M)) := by
    field_simp; ring
  rw [e]; linarith

theorem MNR56_gen_err {m : ℕ} (t u M : ℝ) (α ω o γ' : Fin m → ℝ) (cB cE : Fin m → Fin m → ℝ)
    (hM : 0 < M) (ht0 : 0 ≤ t) (hu0 : 0 ≤ u)
    (hα0 : ∀ i, 0 ≤ α i) (hαm : ∀ i, α i ≤ 6 * t / M) (hαs : ∑ i, α i ≤ 2 * t)
    (hω0 : ∀ i, 0 ≤ ω i) (hωm : ∀ i, ω i ≤ 3 * u / M) (hωs : ∑ i, ω i ≤ 2 * u)
    (ho0 : ∀ i, 0 ≤ o i) (hoγ : ∀ i, o i ≤ 2 * t * γ' i) (hγ'0 : ∀ i, 0 ≤ γ' i) (hγ'1 : ∑ i, γ' i = 1)
    (hcB0 : ∀ i j, 0 ≤ cB i j) (hcE0 : ∀ i j, 0 ≤ cE i j)
    (hcB : ∀ j, ∑ i ∈ univ.erase j, γ' i * cB i j ≤ 9 / M)
    (hcE : ∀ j, ∑ i ∈ univ.erase j, γ' i * cE i j ≤ 9 / M) :
    ∑ i, o i * (α i + ω i + ∑ j ∈ univ.erase i, α j * cB i j + ∑ j ∈ univ.erase i, ω j * cE i j)
      ≤ t * (48 * t + 42 * u) / M := by
  have hos : ∑ i, o i ≤ 2 * t := by
    calc ∑ i, o i ≤ ∑ i, 2 * t * γ' i := Finset.sum_le_sum (fun i _ => hoγ i)
      _ = 2 * t := by rw [← Finset.mul_sum, hγ'1, mul_one]
  have p1 : ∑ i, o i * (α i + ω i) ≤ (6 * t / M + 3 * u / M) * (2 * t) := by
    calc ∑ i, o i * (α i + ω i) ≤ ∑ i, (6 * t / M + 3 * u / M) * o i := Finset.sum_le_sum (fun i _ => by
          have := mul_le_mul_of_nonneg_left (add_le_add (hαm i) (hωm i)) (ho0 i); linarith)
      _ = (6 * t / M + 3 * u / M) * ∑ i, o i := by rw [Finset.mul_sum]
      _ ≤ (6 * t / M + 3 * u / M) * (2 * t) := mul_le_mul_of_nonneg_left hos (by positivity)
  have hin : ∀ (c : Fin m → Fin m → ℝ), (∀ i j, 0 ≤ c i j) →
      (∀ j, ∑ i ∈ univ.erase j, γ' i * c i j ≤ 9 / M) →
      ∀ j, ∑ i ∈ univ.erase j, o i * c i j ≤ 2 * t * (9 / M) := fun c hc0 hc j => by
    calc ∑ i ∈ univ.erase j, o i * c i j ≤ ∑ i ∈ univ.erase j, 2 * t * (γ' i * c i j) :=
          Finset.sum_le_sum (fun i _ => by
            have := mul_le_mul_of_nonneg_right (hoγ i) (hc0 i j); linarith)
      _ = 2 * t * ∑ i ∈ univ.erase j, γ' i * c i j := by rw [Finset.mul_sum]
      _ ≤ 2 * t * (9 / M) := mul_le_mul_of_nonneg_left (hc j) (by linarith)
  have p2 : ∑ i, o i * ∑ j ∈ univ.erase i, α j * cB i j ≤ 2 * t * (2 * t * (9 / M)) := by
    have e : ∑ i, o i * ∑ j ∈ univ.erase i, α j * cB i j = ∑ j, α j * ∑ i ∈ univ.erase j, o i * cB i j := by
      simp only [Finset.mul_sum]
      rw [MNR56_swap (fun i j => o i * (α j * cB i j))]
      apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring
    rw [e]
    calc ∑ j, α j * ∑ i ∈ univ.erase j, o i * cB i j ≤ ∑ j, α j * (2 * t * (9 / M)) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hin cB hcB0 hcB j) (hα0 j))
      _ = (∑ j, α j) * (2 * t * (9 / M)) := by rw [Finset.sum_mul]
      _ ≤ 2 * t * (2 * t * (9 / M)) := mul_le_mul_of_nonneg_right hαs (by positivity)
  have p3 : ∑ i, o i * ∑ j ∈ univ.erase i, ω j * cE i j ≤ 2 * u * (2 * t * (9 / M)) := by
    have e : ∑ i, o i * ∑ j ∈ univ.erase i, ω j * cE i j = ∑ j, ω j * ∑ i ∈ univ.erase j, o i * cE i j := by
      simp only [Finset.mul_sum]
      rw [MNR56_swap (fun i j => o i * (ω j * cE i j))]
      apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring
    rw [e]
    calc ∑ j, ω j * ∑ i ∈ univ.erase j, o i * cE i j ≤ ∑ j, ω j * (2 * t * (9 / M)) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hin cE hcE0 hcE j) (hω0 j))
      _ = (∑ j, ω j) * (2 * t * (9 / M)) := by rw [Finset.sum_mul]
      _ ≤ 2 * u * (2 * t * (9 / M)) := mul_le_mul_of_nonneg_right hωs (by positivity)
  have hsplit : ∑ i, o i * (α i + ω i + ∑ j ∈ univ.erase i, α j * cB i j + ∑ j ∈ univ.erase i, ω j * cE i j)
      = ∑ i, o i * (α i + ω i) + ∑ i, o i * ∑ j ∈ univ.erase i, α j * cB i j
        + ∑ i, o i * ∑ j ∈ univ.erase i, ω j * cE i j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hsplit]
  have e : t * (48 * t + 42 * u) / M = (6 * t / M + 3 * u / M) * (2 * t) + 2 * t * (2 * t * (9 / M))
      + 2 * u * (2 * t * (9 / M)) := by field_simp; ring
  rw [e]; linarith

theorem MNR56_poly (f u : ℝ) (hf1 : 7 / 12 ≤ f) (hf2 : f ≤ 3 / 5) (hu0 : 0 < u) (hu1 : u ≤ 1 / 288) :
    21 / 25 * u ^ 3 ≤ (1 - (1 - f) * u + (1 - f) ^ 2 * u ^ 2 / 2)
      * (1 - f * u + (f * u) ^ 2 / 2 - (f * u) ^ 3 / 6) - (1 - u + u ^ 2 / 2 - u ^ 3) := by
  have key : (1 - (1 - f) * u + (1 - f) ^ 2 * u ^ 2 / 2)
      * (1 - f * u + (f * u) ^ 2 / 2 - (f * u) ^ 3 / 6) - (1 - u + u ^ 2 / 2 - u ^ 3)
      = u ^ 3 * ((1 - f / 2 + f ^ 2 / 2 - f ^ 3 / 6) + u * (f ^ 4 / 12 - f ^ 3 / 3 + f ^ 2 / 4)
          + u ^ 2 * (-f ^ 5 / 12 + f ^ 4 / 6 - f ^ 3 / 12)) := by ring
  rw [key]
  have hA : 211 / 250 ≤ 1 - f / 2 + f ^ 2 / 2 - f ^ 3 / 6 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hf2) (sub_nonneg.mpr hf1), mul_nonneg (mul_nonneg (sub_nonneg.mpr hf2) (sub_nonneg.mpr hf1)) (by linarith : (0:ℝ) ≤ f)]
  have hB : 0 ≤ f ^ 4 / 12 - f ^ 3 / 3 + f ^ 2 / 4 := by
    have : f ^ 4 / 12 - f ^ 3 / 3 + f ^ 2 / 4 = f ^ 2 * ((f - 2) ^ 2 - 1) / 12 := by ring
    rw [this]; apply div_nonneg _ (by norm_num); apply mul_nonneg (sq_nonneg f); nlinarith
  have hC : -1 / 10 ≤ -f ^ 5 / 12 + f ^ 4 / 6 - f ^ 3 / 12 := by
    have h0 : 0 ≤ f := by linarith
    nlinarith [pow_nonneg h0 3, pow_nonneg h0 4, pow_nonneg h0 5]
  have hu2 : u ^ 2 ≤ 1 / 288 ^ 2 := by nlinarith
  have : 21 / 25 ≤ (1 - f / 2 + f ^ 2 / 2 - f ^ 3 / 6) + u * (f ^ 4 / 12 - f ^ 3 / 3 + f ^ 2 / 4)
      + u ^ 2 * (-f ^ 5 / 12 + f ^ 4 / 6 - f ^ 3 / 12) := by
    have := mul_nonneg hu0.le hB
    have := mul_le_mul_of_nonneg_left hC (sq_nonneg u)
    nlinarith
  have hu3 : 0 ≤ u ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hu3]

set_option maxHeartbeats 16000000 in
theorem solution {σ : ℚ} (ctrl : Controls σ) {m : ℕ} {n : Fin m → ℕ} (hm : ctrl.m0 ≤ m)
    (hn : ∀ i, 0 < n i) (u : Utility n) (hu : BoundedGame u) (s : State n)
    (hx : AGT.IsMixedProfile s.x) (hterm : ¬ Terminal σ u s)
    (hgens : ∀ g ∈ s.gens, GenLegal g ∧ g.t = ctrl.knobs.t ∧ ∀ i, g.γ i < 3 / m)
    (hI1 : ∀ i, s.h i = (s.gens.map fun g => g.A * g.t * g.γ i).sum)
    (hH : s.H = ∑ i, s.h i)
    (hI2 : (∀ i, 0 ≤ s.h i) ∧ s.H ≤ ctrl.knobs.L0 ∧
      ∀ i, (m : ℝ) * s.h i - s.H ≤ ctrl.knobs.R0 * s.H)
    (hI3 : ColumnBound u s.gens 9) (hI4 : CertLaw s.x s.gens)
    (hfail : ¬ Passes ctrl u s)
    (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ) (arev acor : (i : Fin m) → Fin (n i))
    (hw : DualOptimal u s.x ctrl.η w α)
    (hrev : IsRevBR u (rY ctrl.knobs s w) (rDelta ctrl.knobs s w) arev)
    (hfwd : IsFwdBR u (rXt ctrl.knobs s w arev) (rE ctrl.knobs u s w arev) acor) :
    let k := ctrl.knobs
    let E := rEtot k u s w arev
    let s' := repairState k u s w arev acor
    0 ≤ E ∧ E ≤ 120 * (ctrl.u : ℝ) / m ∧ k.c ≤ rCraw k s w / (1 + E) ∧
      CertLaw s'.x s'.gens ∧ k.c * scaled u s.x + k.Dsh s.H - E ≤ scaled u s'.x := by
  intro k E s'
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
    (fun g hg => (hgens g hg).1) hI4 9 (by norm_num) hI3 s.h hI1 hh0 (k.R0 * s.H)
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
  -- Lemma 5.4
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
  have hνnn : 0 ≤ k.nu := by rw [hν]; exact mul_nonneg (by linarith) hβpos.le
  have hgsL : ∀ g ∈ s.gens, GenLegal g := fun g hg => (hgens g hg).1
  have h54 := MultiNashRepair.lemma_5_4 hm1 hn u hu s.x hx (bdev w) hbm (rGamma k s w) hγlot k.t
    k.rho k.beta k.nu k.c htγ hρpos hβpos.le hνnn hcpos (rDelta k s w) hδ0 hδ1 s.gens hgsL hI4 s.h hI1
    arev acor hrev
  dsimp only at h54
  obtain ⟨hP1, hP2⟩ := h54
  have hDeq : 1 - k.rho + k.beta + k.nu * ∑ i, s.h i = k.Dsh s.H := by
    rw [← hH]
    show _ = k.beta * (k.G0 + k.Q * s.H)
    rw [hG0, hν]; linear_combination hρ
  rw [hDeq] at hP2
  -- notation
  set γ := rGamma k s w with hγdef
  set δ := rDelta k s w with hδdef
  set Craw := k.rho * ∏ i, (1 - k.t * γ i) with hCraw
  have hu2 : (ctrl.u:ℝ)^2 ≤ 1 := by nlinarith only [hu0, hu1]
  have hγ1 : ∑ i, γ i = 1 := hγlot.2
  have htγh : ∀ i, k.t * γ i ≤ 1 / 2 := fun i => by
    have h1 := mul_le_mul_of_nonneg_left (le_trans (hγ3 i).le h3m) htpos.le
    nlinarith only [h1, htu, hu1, hu0, hu2]
  have hαle : ∀ i, k.t * γ i / (1 - k.t * γ i) ≤ 2 * k.t * γ i := fun i => by
    rw [div_le_iff₀ (by linarith [htγh i])]; nlinarith only [htγh i, (htγ i).1]
  have hαge : ∀ i, k.t * γ i ≤ k.t * γ i / (1 - k.t * γ i) := fun i => by
    rw [le_div_iff₀ (by linarith [htγh i])]; nlinarith only [htγh i, (htγ i).1]
  have hα0 : ∀ i, 0 ≤ k.t * γ i / (1 - k.t * γ i) := fun i => le_trans (htγ i).1 (hαge i)
  -- reverse-sweep denominators
  have hP : ∀ i, k.rho ≤ 1 - ∑ j ∈ univ.filter (· ≤ i), δ j := fun i => by
    have : ∑ j ∈ univ.filter (· ≤ i), δ j ≤ ∑ j, δ j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => hδ0 j)
    linarith
  have hP1' : ∀ i, 1 - ∑ j ∈ univ.filter (· ≤ i), δ j ≤ 1 := fun i => by
    have := Finset.sum_nonneg (fun j (_ : j ∈ univ.filter (· ≤ i)) => hδ0 j); linarith
  have hω0 : ∀ i, 0 ≤ δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j) := fun i =>
    div_nonneg (hδ0 i) (by linarith [hP i])
  have hωge : ∀ i, δ i ≤ δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j) := fun i => by
    rw [le_div_iff₀ (by linarith [hP i])]; nlinarith only [hδ0 i, hP1' i]
  have hωle : ∀ i, δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j) ≤ δ i / k.rho := fun i =>
    div_le_div_of_nonneg_left (hδ0 i) hρpos (hP i)
  have hDsh : k.Dsh s.H ≤ 2 * ctrl.u := by
    show k.beta * (k.G0 + k.Q * s.H) ≤ _
    have hQH' : k.Q * s.H ≤ k.c := by
      have := mul_le_mul_of_nonneg_left hHL (by linarith : (0:ℝ) ≤ k.Q); linarith
    have h1 : k.G0 + k.Q * s.H ≤ 3 := by rw [hG0]; linarith
    have h2 : 0 ≤ k.G0 + k.Q * s.H := by rw [hG0]; nlinarith only [hR0pos, hQ1, hHnn]
    nlinarith only [mul_le_mul hβu h1 h2 (by positivity), hu0]
  have hDsh0 : 0 ≤ k.Dsh s.H := by
    show 0 ≤ k.beta * (k.G0 + k.Q * s.H)
    apply mul_nonneg hβpos.le; rw [hG0]; nlinarith only [hR0pos, hQ1, hHnn]
  have hδle : ∀ i, δ i ≤ k.Dsh s.H / m := fun i => by
    have e : δ i = k.Dsh s.H / m - k.beta * γ i - k.nu * s.h i := rfl
    rw [e]; nlinarith only [mul_nonneg hβpos.le (hγ0 i), mul_nonneg hνnn (hh0 i)]
  have hωm : ∀ i, δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j) ≤ 3 * ctrl.u / m := fun i => by
    refine le_trans (hωle i) ?_
    rw [div_le_iff₀ hρpos]
    have h1 := hδle i
    have h2 : k.Dsh s.H / m ≤ 2 * ctrl.u / m := div_le_div_of_nonneg_right hDsh hmpos.le
    have h3 : 0 ≤ 3 * (ctrl.u:ℝ) / m := by positivity
    have h4 : 3 * (ctrl.u:ℝ) / m * (3 / 4) ≤ 3 * (ctrl.u:ℝ) / m * k.rho := mul_le_mul_of_nonneg_left hrho34 h3
    have h5 : 2 * (ctrl.u:ℝ) / m ≤ 3 * (ctrl.u:ℝ) / m * (3 / 4) := by
      rw [show 3 * (ctrl.u:ℝ) / m * (3 / 4) = 9 / 4 * ctrl.u / m by ring]
      exact div_le_div_of_nonneg_right (by nlinarith only [hu0]) hmpos.le
    linarith
  have hωs : ∑ i, δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j) ≤ 2 * ctrl.u := by
    calc ∑ i, δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j) ≤ ∑ i, δ i / k.rho :=
          Finset.sum_le_sum (fun i _ => hωle i)
      _ = (1 - k.rho) / k.rho := by rw [← Finset.sum_div, hδ1]
      _ ≤ 2 * ctrl.u := by rw [div_le_iff₀ hρpos]; nlinarith only [h1rho, hrho34, hu0]
  -- C_raw lower bound
  have hprod := MNR56_prod_lb univ (fun i => k.t * γ i) (fun i => (htγ i).1) (fun i => (htγ i).2.le)
  have hS : ∑ i, k.t * γ i = k.t := by rw [← Finset.mul_sum, hγ1, mul_one]
  have hQs : ∑ i, (k.t * γ i) ^ 2 ≤ 3 * k.t ^ 2 / m := by
    calc ∑ i, (k.t * γ i) ^ 2 ≤ ∑ i, k.t ^ 2 * (3 / m) * γ i := Finset.sum_le_sum (fun i _ => by
          have := mul_le_mul_of_nonneg_left (hγ3 i).le (mul_nonneg (sq_nonneg k.t) (hγ0 i))
          nlinarith only [this])
      _ = 3 * k.t ^ 2 / m := by rw [← Finset.mul_sum, hγ1]; ring
  rw [hS] at hprod
  have hpoly := MNR56_poly (ctrl.f0:ℝ) (ctrl.u:ℝ) hf1 hf2 hu0 hu1
  rw [← hrho_def, ← ht, ← hc] at hpoly
  have hCrawlo : k.c + 21 / 25 * (ctrl.u:ℝ) ^ 3 - 3 * k.t ^ 2 / (2 * m) ≤ Craw := by
    rw [hCraw]
    have k1 := mul_le_mul_of_nonneg_left hprod hρpos.le
    have k2 : k.rho * ((k.t ^ 2 - ∑ i, (k.t * γ i) ^ 2) / 2) ≥ k.rho * ((k.t ^ 2 - 3 * k.t ^ 2 / m) / 2) := by
      apply mul_le_mul_of_nonneg_left _ hρpos.le; linarith
    have k3 : k.rho * (3 * k.t ^ 2 / m / 2) ≤ 3 * k.t ^ 2 / (2 * m) := by
      rw [show 3 * k.t ^ 2 / (2 * (m:ℝ)) = 1 * (3 * k.t ^ 2 / m / 2) by field_simp]
      exact mul_le_mul_of_nonneg_right hrho1 (by positivity)
    nlinarith only [k1, k2, k3, hpoly]
  have hsmall : 3 * k.t ^ 2 / (2 * m) ≤ 3 / 2000 * (ctrl.u:ℝ) ^ 4 := by
    have ht2 : k.t ^ 2 ≤ (ctrl.u:ℝ) ^ 2 := by nlinarith only [htu, htpos, hu0]
    have : 3 * k.t ^ 2 / (2 * (m:ℝ)) = 3 / 2 * k.t ^ 2 * (1 / m) := by field_simp
    rw [this]
    have := mul_le_mul ht2 hinvm (by positivity) (sq_nonneg _)
    nlinarith only [this]
  have hu4 : (ctrl.u:ℝ) ^ 4 ≤ (ctrl.u:ℝ) ^ 3 := by nlinarith only [hu0, hu1, pow_pos hu0 3]
  have hCrawc : k.c + 4 / 5 * (ctrl.u:ℝ) ^ 3 ≤ Craw := by nlinarith only [hCrawlo, hsmall, hu4, pow_pos hu0 3]
  have hfac : ∀ i, 0 ≤ 1 - k.t * γ i ∧ 1 - k.t * γ i ≤ 1 := fun i =>
    ⟨by linarith [(htγ i).2], by linarith [(htγ i).1]⟩
  have hCraw1 : Craw ≤ 1 := by
    rw [hCraw]
    have h1 : ∏ i, (1 - k.t * γ i) ≤ 1 := Finset.prod_le_one (fun i _ => (hfac i).1) (fun i _ => (hfac i).2)
    have h2 : 0 ≤ ∏ i, (1 - k.t * γ i) := Finset.prod_nonneg (fun i _ => (hfac i).1)
    nlinarith only [h1, h2, hrho1, hρpos]
  have hCraw0 : 0 ≤ Craw := by linarith [hcpos, pow_pos hu0 3]
  -- event memory
  set Sev := ∑ i, (k.t * γ i / (1 - k.t * γ i) + δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j)) with hSev
  have hSevlo : k.u0 ≤ Sev := by
    have h1 : k.t ≤ ∑ i, k.t * γ i / (1 - k.t * γ i) := by
      calc k.t = ∑ i, k.t * γ i := hS.symm
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hαge i)
    have h2 : 1 - k.rho ≤ ∑ i, δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j) := by
      rw [← hδ1]; exact Finset.sum_le_sum (fun i _ => hωge i)
    have e : Sev = ∑ i, k.t * γ i / (1 - k.t * γ i) + ∑ i, δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j) :=
      Finset.sum_add_distrib
    have hu0d : k.u0 = (ctrl.u:ℝ) - (ctrl.u:ℝ)^2 := rfl
    rw [e, hu0d]
    have : k.t + (1 - k.rho) ≥ (ctrl.u:ℝ) - (ctrl.u:ℝ)^2 := by
      rw [ht, hrho_def]; nlinarith only [hb, sq_nonneg ((1 - (ctrl.f0:ℝ)) * ctrl.u), ha]
    linarith
  have hu00 : 0 ≤ k.u0 := by
    have : k.u0 = (ctrl.u:ℝ) - (ctrl.u:ℝ)^2 := rfl
    rw [this]; nlinarith only [hu0, hu1]
  have hβle : k.beta ≤ Craw * k.t * (1 + Sev) := by
    rw [hβdef]
    have k1 : k.c * k.t ≤ Craw * k.t := mul_le_mul_of_nonneg_right (by linarith [pow_pos hu0 3]) htpos.le
    have k2 := mul_le_mul k1 (by linarith : 1 + k.u0 ≤ 1 + Sev) (by linarith) (mul_nonneg hCraw0 htpos.le)
    linarith
  have hνle : k.nu ≤ Craw * Sev := by
    have : k.nu = k.c * k.u0 := rfl
    rw [this]
    exact mul_le_mul (by linarith [pow_pos hu0 3]) hSevlo hu00 hCraw0
  obtain ⟨hEle, hsc, hP3⟩ := hP2 hβle hνle (fun i => rfl) hfwd
  -- the error bound
  have hd0nn : ∀ i, 0 ≤ deficitMix u s.x i (bdev w i) := fun i =>
    MNR51_deficitMix_nonneg u hu s.x hx i _ (hbm i)
  have hdnn : ∀ i j (y : Fin (n j) → ℝ), AGT.IsLottery y →
      0 ≤ deficitMix u (Function.update s.x j y) i (bdev w i) := fun i j y hy =>
    MNR51_deficitMix_nonneg u hu _ (MNR51_update_mixed s.x hx j y hy) i _ (hbm i)
  have hγd0 : ∑ i, γ i * deficitMix u s.x i (bdev w i) ≤ 9 / m := by
    have k1 : ∑ i, γ i * deficitMix u s.x i (bdev w i) ≤ 3 * ∑ i, lam w i * deficitMix u s.x i (bdev w i) := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun i _ => by
        have := mul_le_mul_of_nonneg_right (hγl i) (hd0nn i); linarith)
    have k2 : ς + ctrl.η * μ ≤ 3 := by
      have : ctrl.η * μ ≤ μ := by nlinarith only [hη1, hμpos, hη0]
      linarith
    have k3 : (ς + ctrl.η * μ) / m ≤ 3 / m := div_le_div_of_nonneg_right k2 hmpos.le
    rw [show (9:ℝ) / m = 3 * (3 / m) by ring]
    linarith
  have hcur := MNR56_cur_err Craw k.t ctrl.u m (fun i => k.t * γ i / (1 - k.t * γ i))
    (fun i => δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j)) γ (fun i => deficitMix u s.x i (bdev w i))
    (fun i j => deficitMix u (Function.update s.x j (bdev w j)) i (bdev w i))
    (fun i j => deficitMix u (Function.update s.x j (ePure (arev j))) i (bdev w i))
    hmpos hCraw0 hCraw1 htpos.le hu0.le hα0 hαle hγ0 hγ1 (fun i => (hγ3 i).le) hω0 hωm hωs
    hd0nn (fun i j => hdnn i j _ (hbm j)) (fun i j => hdnn i j _ (MNR51_ePure_lottery _))
    hγd0 (fun j => (hcol j _ (hbm j)).le) (fun j => (hcol j _ (MNR51_ePure_lottery _)).le)
  -- the historical error
  have hαm : ∀ i, k.t * γ i / (1 - k.t * γ i) ≤ 6 * k.t / m := fun i => by
    have := mul_le_mul_of_nonneg_left (hγ3 i).le (by linarith : (0:ℝ) ≤ 2 * k.t)
    calc k.t * γ i / (1 - k.t * γ i) ≤ 2 * k.t * γ i := hαle i
      _ ≤ 2 * k.t * (3 / m) := this
      _ = 6 * k.t / m := by ring
  have hαs : ∑ i, k.t * γ i / (1 - k.t * γ i) ≤ 2 * k.t := by
    calc ∑ i, k.t * γ i / (1 - k.t * γ i) ≤ ∑ i, 2 * k.t * γ i := Finset.sum_le_sum (fun i _ => hαle i)
      _ = 2 * k.t := by rw [← Finset.mul_sum, hγ1, mul_one]
  have hgen : ∀ g ∈ s.gens, Craw * g.A * ∑ i, g.odds i * (k.t * γ i / (1 - k.t * γ i)
        + δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j)
        + ∑ j ∈ univ.erase i, k.t * γ j / (1 - k.t * γ j) * Gen.col u g i j (bdev w j)
        + ∑ j ∈ univ.erase i, δ j / (1 - ∑ l ∈ univ.filter (· ≤ j), δ l) * Gen.col u g i j (ePure (arev j)))
      ≤ g.A * k.t * ((48 * k.t + 42 * ctrl.u) / m) := by
    intro g hg
    obtain ⟨⟨hbase, hdev, hγg, htγg, hA⟩, hgt, hg3⟩ := hgens g hg
    have hoγ : ∀ i, g.odds i ≤ 2 * k.t * g.γ i := fun i => by
      unfold Gen.odds; rw [hgt]
      have h1 : k.t * g.γ i ≤ 1 / 2 := by
        have := mul_le_mul_of_nonneg_left (le_trans (hg3 i).le h3m) htpos.le
        nlinarith only [this, htu, hu1, hu0, hu2]
      have h0 : 0 ≤ k.t * g.γ i := by rw [← hgt]; exact (htγg i).1
      rw [div_le_iff₀ (by linarith)]; nlinarith only [h1, h0]
    have ho0 : ∀ i, 0 ≤ g.odds i := fun i => div_nonneg (htγg i).1 (by linarith [(htγg i).2])
    have hcolnn : ∀ i j (y : Fin (n j) → ℝ), AGT.IsLottery y → 0 ≤ Gen.col u g i j y := fun i j y hy =>
      MNR51_deficitMix_nonneg u hu _ (MNR51_update_mixed _ hbase j y hy) i _ (hdev i)
    have hge := MNR56_gen_err k.t ctrl.u m (fun i => k.t * γ i / (1 - k.t * γ i))
      (fun i => δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j)) g.odds g.γ
      (fun i j => Gen.col u g i j (bdev w j)) (fun i j => Gen.col u g i j (ePure (arev j)))
      hmpos htpos.le hu0.le hα0 hαm hαs hω0 hωm hωs ho0 hoγ hγg.1 hγg.2
      (fun i j => hcolnn i j _ (hbm j)) (fun i j => hcolnn i j _ (MNR51_ePure_lottery _))
      (fun j => hI3 g hg j _ (hbm j)) (fun j => hI3 g hg j _ (MNR51_ePure_lottery _))
    have hX0 : 0 ≤ ∑ i, g.odds i * (k.t * γ i / (1 - k.t * γ i)
        + δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j)
        + ∑ j ∈ univ.erase i, k.t * γ j / (1 - k.t * γ j) * Gen.col u g i j (bdev w j)
        + ∑ j ∈ univ.erase i, δ j / (1 - ∑ l ∈ univ.filter (· ≤ j), δ l) * Gen.col u g i j (ePure (arev j))) := by
      apply Finset.sum_nonneg; intro i _
      apply mul_nonneg (ho0 i)
      have h2 : 0 ≤ ∑ j ∈ univ.erase i, k.t * γ j / (1 - k.t * γ j) * Gen.col u g i j (bdev w j) :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (hα0 j) (hcolnn i j _ (hbm j)))
      have h3 : 0 ≤ ∑ j ∈ univ.erase i, δ j / (1 - ∑ l ∈ univ.filter (· ≤ j), δ l) * Gen.col u g i j (ePure (arev j)) :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (hω0 j) (hcolnn i j _ (MNR51_ePure_lottery _)))
      linarith [hα0 i, hω0 i]
    have k1 : Craw * g.A * (∑ i, g.odds i * (k.t * γ i / (1 - k.t * γ i)
        + δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j)
        + ∑ j ∈ univ.erase i, k.t * γ j / (1 - k.t * γ j) * Gen.col u g i j (bdev w j)
        + ∑ j ∈ univ.erase i, δ j / (1 - ∑ l ∈ univ.filter (· ≤ j), δ l) * Gen.col u g i j (ePure (arev j))))
        ≤ 1 * g.A * (k.t * (48 * k.t + 42 * ctrl.u) / m) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hCraw1 hA) hge hX0 (by positivity)
    have e : 1 * g.A * (k.t * (48 * k.t + 42 * ctrl.u) / m) = g.A * k.t * ((48 * k.t + 42 * ctrl.u) / m) := by ring
    linarith
  have hHsum : (s.gens.map fun g => g.A * k.t).sum = s.H := by
    rw [hH]; simp only [hI1]
    rw [MNR53_list_fsum]
    congr 1; apply List.map_congr_left; intro g hg
    obtain ⟨⟨-, -, hγg, -, -⟩, hgt, -⟩ := hgens g hg
    rw [← Finset.mul_sum, hγg.2, mul_one, hgt]
  have hold : ∑ i, (s.gens.map (fun g => Craw * g.A * g.odds i *
          (k.t * γ i / (1 - k.t * γ i) + δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j)
            + ∑ j ∈ univ.erase i, k.t * γ j / (1 - k.t * γ j) * Gen.col u g i j (bdev w j)
            + ∑ j ∈ univ.erase i, δ j / (1 - ∑ l ∈ univ.filter (· ≤ j), δ l) * Gen.col u g i j (ePure (arev j))))).sum
      ≤ (48 * k.t + 42 * ctrl.u) / m * s.H := by
    rw [MNR53_list_fsum]
    have e : ∀ g : Gen n, ∑ i, Craw * g.A * g.odds i *
          (k.t * γ i / (1 - k.t * γ i) + δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j)
            + ∑ j ∈ univ.erase i, k.t * γ j / (1 - k.t * γ j) * Gen.col u g i j (bdev w j)
            + ∑ j ∈ univ.erase i, δ j / (1 - ∑ l ∈ univ.filter (· ≤ j), δ l) * Gen.col u g i j (ePure (arev j)))
        = Craw * g.A * ∑ i, g.odds i * (k.t * γ i / (1 - k.t * γ i)
            + δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j)
            + ∑ j ∈ univ.erase i, k.t * γ j / (1 - k.t * γ j) * Gen.col u g i j (bdev w j)
            + ∑ j ∈ univ.erase i, δ j / (1 - ∑ l ∈ univ.filter (· ≤ j), δ l) * Gen.col u g i j (ePure (arev j))) := by
      intro g; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [List.map_congr_left (fun g _ => e g)]
    refine le_trans (MNR53_list_le _ _ _ hgen) ?_
    rw [show (fun g : Gen n => g.A * k.t * ((48 * k.t + 42 * ctrl.u) / m))
        = (fun g : Gen n => (48 * k.t + 42 * ctrl.u) / m * (g.A * k.t)) by funext g; ring,
      MNR53_list_mul, hHsum]
  rw [Finset.sum_add_distrib] at hEle
  have hEb : E ≤ 120 * (ctrl.u:ℝ) / m := by
    have h1 : (18 * k.t + 48 * k.t ^ 2 + 42 * k.t * ctrl.u) / m + (48 * k.t + 42 * ctrl.u) / m * s.H
        ≤ 120 * ctrl.u / m := by
      have hH' : (48 * k.t + 42 * ctrl.u) / m * s.H ≤ (48 * k.t + 42 * ctrl.u) / m :=
        by nlinarith only [hH1, hHnn, show (0:ℝ) ≤ (48 * k.t + 42 * ctrl.u) / m by positivity]
      have h2 : (18 * k.t + 48 * k.t ^ 2 + 42 * k.t * ctrl.u) / m + (48 * k.t + 42 * ctrl.u) / m
          = (66 * k.t + 48 * k.t ^ 2 + 42 * k.t * ctrl.u + 42 * ctrl.u) / m := by ring
      have h3 : 66 * k.t + 48 * k.t ^ 2 + 42 * k.t * ctrl.u + 42 * ctrl.u ≤ 120 * ctrl.u := by
        nlinarith only [htu, htpos, hu0, hu1]
      have h4 := div_le_div_of_nonneg_right h3 hmpos.le
      linarith
    show rEtot k u s w arev ≤ _
    exact le_trans hEle (by linarith [hcur, hold])
  have hE0 : 0 ≤ E := Finset.sum_nonneg (fun i _ => le_max_left _ _)
  -- retention
  have hret : k.c ≤ Craw / (1 + E) := by
    rw [le_div_iff₀ (by linarith)]
    have h1 : 120 * (ctrl.u:ℝ) / m ≤ 3 / 25 * (ctrl.u:ℝ) ^ 3 := by
      rw [show 120 * (ctrl.u:ℝ) / m = 120 * ctrl.u * (1 / m) by ring]
      have := mul_le_mul_of_nonneg_left hinvm (by positivity : (0:ℝ) ≤ 120 * ctrl.u)
      nlinarith only [this]
    have h2 : k.c * E ≤ E := by nlinarith only [hE0, hc1]
    nlinarith only [hCrawc, h1, h2, hEb, pow_pos hu0 3]
  obtain ⟨hcert', hfinal⟩ := hP3 hret
  refine ⟨hE0, hEb, hret, hcert', ?_⟩
  have hDE : k.Dsh s.H * E ≤ E := by nlinarith only [hDsh, hE0, hu1, hDsh0]
  have hfinal' : k.c * ς + k.Dsh s.H - k.Dsh s.H * E ≤ scaled u s'.x := hfinal
  linarith
