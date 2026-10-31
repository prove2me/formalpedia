-- Prove2me | solution 1 for LiquidDemocracy.Upward.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T11:40:44.377455+00:00
-- url     : https://prove2.me/submissions/c4cc82e6-bdfc-45ec-bb40-1f3d7c301fe6

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Setting
import Theorems.Thm_LiquidDemocracy_Upward_eq_14

open MeasureTheory Filter Topology Asymptotics LiquidDemocracy.Upward
open scoped Classical

/-! ### Finite-sum facts about `voteProb` -/

noncomputable def LD1_w {n : ℕ} (c : Fin n → ℝ) (i : Fin n) (b : Bool) : ℝ :=
  if b then c i else 1 - c i

theorem LD1_voteProb_eq {n : ℕ} (c : Fin n → ℝ) (E : (Fin n → Bool) → Prop) :
    voteProb c E = ∑ v, if E v then ∏ i, LD1_w c i (v i) else 0 := by
  unfold voteProb LD1_w
  rw [Finset.sum_filter]

theorem LD1_prod_nonneg {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1)
    (v : Fin n → Bool) : 0 ≤ ∏ i, LD1_w c i (v i) := by
  apply Finset.prod_nonneg
  intro i _
  unfold LD1_w
  have := hc i
  split_ifs <;> simp only [Set.mem_Icc] at this <;> linarith

/-- Product formula: `∑_v ∏_k h_k(v_k) = ∏_k ∑_b h_k(b)`. -/
theorem LD1_sum_prod {n : ℕ} (h : Fin n → Bool → ℝ) :
    ∑ v : Fin n → Bool, ∏ k, h k (v k) = ∏ k, ∑ b, h k b :=
  (Fintype.prod_sum h).symm

theorem LD1_total {n : ℕ} (c : Fin n → ℝ) : ∑ v : Fin n → Bool, ∏ i, LD1_w c i (v i) = 1 := by
  rw [LD1_sum_prod]
  simp [LD1_w]

theorem LD1_vp_mono {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1)
    (E F : (Fin n → Bool) → Prop) (h : ∀ v, E v → F v) : voteProb c E ≤ voteProb c F := by
  rw [LD1_voteProb_eq, LD1_voteProb_eq]
  apply Finset.sum_le_sum
  intro v _
  have := LD1_prod_nonneg c hc v
  by_cases hE : E v
  · rw [if_pos hE, if_pos (h v hE)]
  · rw [if_neg hE]; split_ifs <;> linarith

theorem LD1_vp_union {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1)
    (E F : (Fin n → Bool) → Prop) :
    voteProb c (fun v => E v ∨ F v) ≤ voteProb c E + voteProb c F := by
  rw [LD1_voteProb_eq, LD1_voteProb_eq, LD1_voteProb_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  have := LD1_prod_nonneg c hc v
  by_cases hE : E v <;> by_cases hF : F v <;> simp [hE, hF] <;> linarith

theorem LD1_vp_compl {n : ℕ} (c : Fin n → ℝ) (E : (Fin n → Bool) → Prop) :
    voteProb c E + voteProb c (fun v => ¬ E v) = 1 := by
  rw [LD1_voteProb_eq, LD1_voteProb_eq, ← Finset.sum_add_distrib, ← LD1_total c]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hE : E v <;> simp [hE]

/-! ### Second moment of a linear statistic -/

noncomputable def LD1_y {n : ℕ} (c : Fin n → ℝ) (i : Fin n) (b : Bool) : ℝ :=
  (if b then 1 else 0) - c i

theorem LD1_cross {n : ℕ} (c : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    ∑ v : Fin n → Bool, (∏ k, LD1_w c k (v k)) * (LD1_y c i (v i) * LD1_y c j (v j)) = 0 := by
  have hrw : ∀ v : Fin n → Bool, (∏ k, LD1_w c k (v k)) * (LD1_y c i (v i) * LD1_y c j (v j)) =
      ∏ k, (LD1_w c k (v k) * (if k = i then LD1_y c i (v k) else 1) *
        (if k = j then LD1_y c j (v k) else 1)) := by
    intro v
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i,
      Finset.prod_ite_eq' Finset.univ j]
    simp only [Finset.mem_univ, if_true]
    ring
  simp_rw [hrw]
  rw [LD1_sum_prod (fun k b => LD1_w c k b * (if k = i then LD1_y c i b else 1) *
    (if k = j then LD1_y c j b else 1))]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [LD1_w, LD1_y, hij]
  ring

theorem LD1_diag {n : ℕ} (c : Fin n → ℝ) (i : Fin n) :
    ∑ v : Fin n → Bool, (∏ k, LD1_w c k (v k)) * (LD1_y c i (v i) * LD1_y c i (v i)) =
      c i * (1 - c i) := by
  have hrw : ∀ v : Fin n → Bool, (∏ k, LD1_w c k (v k)) * (LD1_y c i (v i) * LD1_y c i (v i)) =
      ∏ k, (LD1_w c k (v k) * (if k = i then LD1_y c i (v k) * LD1_y c i (v k) else 1)) := by
    intro v
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i]
    simp
  simp_rw [hrw]
  rw [LD1_sum_prod (fun k b => LD1_w c k b *
    (if k = i then LD1_y c i b * LD1_y c i b else 1))]
  rw [Finset.prod_eq_single i]
  · simp [LD1_w, LD1_y]; ring
  · intro k _ hk
    simp [LD1_w, LD1_y, hk]
  · simp

theorem LD1_second_moment {n : ℕ} (c : Fin n → ℝ) (a : Fin n → ℝ) :
    ∑ v : Fin n → Bool, (∏ k, LD1_w c k (v k)) * (∑ i, a i * LD1_y c i (v i)) ^ 2 =
      ∑ i, a i ^ 2 * (c i * (1 - c i)) := by
  have hexp : ∀ v : Fin n → Bool, (∏ k, LD1_w c k (v k)) * (∑ i, a i * LD1_y c i (v i)) ^ 2 =
      ∑ i, ∑ j, a i * a j * ((∏ k, LD1_w c k (v k)) * (LD1_y c i (v i) * LD1_y c j (v j))) := by
    intro v
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single i]
  · rw [← Finset.mul_sum, LD1_diag]; ring
  · intro j _ hji
    rw [← Finset.mul_sum, LD1_cross c i j (Ne.symm hji), mul_zero]
  · simp

/-- Chebyshev for a linear statistic of the votes. -/
theorem LD1_cheb {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1) (a : Fin n → ℝ)
    (β : ℝ) (hβ : 0 < β) :
    voteProb c (fun v => β ≤ |∑ i, a i * (if v i then 1 else 0) - ∑ i, a i * c i|) ≤
      (∑ i, a i ^ 2 * (c i * (1 - c i))) / β ^ 2 := by
  rw [← LD1_second_moment c a, LD1_voteProb_eq, Finset.sum_div]
  apply Finset.sum_le_sum
  intro v _
  have hP := LD1_prod_nonneg c hc v
  have hlin : ∑ i, a i * LD1_y c i (v i) =
      ∑ i, a i * (if v i then 1 else 0) - ∑ i, a i * c i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    simp only [LD1_y]; ring
  rw [hlin]
  split_ifs with hE
  · rw [le_div_iff₀ (by positivity)]
    have h2 : β ^ 2 ≤ (∑ i, a i * (if v i then 1 else 0) - ∑ i, a i * c i) ^ 2 := by
      have := sq_le_sq' (by linarith [abs_nonneg (∑ i, a i * (if v i then (1:ℝ) else 0) -
        ∑ i, a i * c i), neg_abs_le (∑ i, a i * (if v i then (1:ℝ) else 0) - ∑ i, a i * c i)])
        hE
      rw [sq_abs] at this
      linarith [sq_abs (∑ i, a i * (if v i then (1:ℝ) else 0) - ∑ i, a i * c i)]
    nlinarith
  · positivity

theorem LD1_var_le {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1)
    (a : Fin n → ℝ) : ∑ i, a i ^ 2 * (c i * (1 - c i)) ≤ (∑ i, a i ^ 2) / 4 := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  have h := hc i
  simp only [Set.mem_Icc] at h
  nlinarith [sq_nonneg (c i - 1 / 2), sq_nonneg (a i)]

/-! ### Deterministic core of Lemma 1 -/

theorem LD1_XD_eq {n : ℕ} (v : Fin n → Bool) :
    XD v = ∑ i, (1 : ℝ) * (if v i then 1 else 0) := by
  unfold XD
  rw [Finset.card_filter]
  push_cast
  simp

theorem LD1_sum_weight_le {n : ℕ} (g : DelegGraph n) : ∑ i, (weight g i : ℝ) ≤ n := by
  have h1 : ∀ i, (weight g i : ℝ) ≤ ((Finset.univ.filter fun j => root g j = i).card : ℝ) := by
    intro i
    unfold weight
    split_ifs <;> simp
  calc ∑ i, (weight g i : ℝ) ≤ ∑ i, ((Finset.univ.filter fun j => root g j = i).card : ℝ) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = ((Finset.univ : Finset (Fin n)).card : ℝ) := by
        rw [Finset.card_eq_sum_card_fiberwise (f := root g) (t := Finset.univ)
          (fun x _ => Finset.mem_univ _)]
        push_cast
        rfl
    _ = n := by simp

theorem LD1_sum_sq_weight_le {n : ℕ} (g : DelegGraph n) (C : ℕ) (hC : maxWeight g ≤ C) :
    ∑ i, (weight g i : ℝ) ^ 2 ≤ C * n := by
  have hw : ∀ i, (weight g i : ℝ) ≤ C := by
    intro i
    have : weight g i ≤ maxWeight g := Finset.le_sup (f := weight g) (Finset.mem_univ i)
    exact_mod_cast this.trans hC
  calc ∑ i, (weight g i : ℝ) ^ 2 ≤ ∑ i, (C : ℝ) * weight g i := by
        apply Finset.sum_le_sum; intro i _
        rw [sq]; exact mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _)
    _ = C * ∑ i, (weight g i : ℝ) := by rw [Finset.mul_sum]
    _ ≤ C * n := mul_le_mul_of_nonneg_left (LD1_sum_weight_le g) (Nat.cast_nonneg _)

theorem LD1_dev_D {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1) (β : ℝ)
    (hβ : 0 < β) :
    voteProb c (fun v => β ≤ |XD v - ∑ i, c i|) ≤ (n / 4) / β ^ 2 := by
  have h := LD1_cheb c hc (fun _ => 1) β hβ
  simp only [one_mul] at h
  have hv := LD1_var_le c hc (fun _ => 1)
  simp only [one_pow, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hv
  calc voteProb c (fun v => β ≤ |XD v - ∑ i, c i|)
      = voteProb c (fun v => β ≤ |∑ i, (if v i then (1 : ℝ) else 0) - ∑ i, c i|) := by
        congr 1; ext v; rw [LD1_XD_eq]; simp
    _ ≤ (∑ i, (c i * (1 - c i))) / β ^ 2 := by simpa using h
    _ ≤ (n / 4) / β ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        simpa using hv

theorem LD1_dev_F {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1) (g : DelegGraph n)
    (C : ℕ) (hC : maxWeight g ≤ C) (β : ℝ) (hβ : 0 < β) :
    voteProb c (fun v => β ≤ |XF g v - ∑ i, (weight g i : ℝ) * c i|) ≤ (C * n / 4) / β ^ 2 := by
  have h := LD1_cheb c hc (fun i => (weight g i : ℝ)) β hβ
  have hv := LD1_var_le c hc (fun i => (weight g i : ℝ))
  have hs := LD1_sum_sq_weight_le g C hC
  calc voteProb c (fun v => β ≤ |XF g v - ∑ i, (weight g i : ℝ) * c i|)
      ≤ (∑ i, (weight g i : ℝ) ^ 2 * (c i * (1 - c i))) / β ^ 2 := h
    _ ≤ (C * n / 4) / β ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith

/-- (11) and (12) imply `gain ≥ −(1 + C)/(4α²n)`. -/
theorem LD1_dnh_det {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1)
    (g : DelegGraph n) (C : ℕ) (hC : maxWeight g ≤ C) (α : ℝ) (hα : 0 < α)
    (h12 : 2 * α * n ≤ ∑ i, (weight g i : ℝ) * c i - ∑ i, c i) :
    -((1 + C) / (4 * α ^ 2 * n)) ≤ gain c g := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hβ : 0 < α * n := by positivity
  have h14 := eq_14 n c hc g
  have hsub : voteProb c (fun v => XF g v < XD v) ≤
      voteProb c (fun v => α * n ≤ |XD v - ∑ i, c i| ∨
        α * n ≤ |XF g v - ∑ i, (weight g i : ℝ) * c i|) := by
    apply LD1_vp_mono c hc
    intro v hv
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have a1 := (abs_lt.mp h1).2
    have a2 := (abs_lt.mp h2).1
    linarith
  have hu := LD1_vp_union c hc (fun v => α * n ≤ |XD v - ∑ i, c i|)
    (fun v => α * n ≤ |XF g v - ∑ i, (weight g i : ℝ) * c i|)
  have hD := LD1_dev_D c hc (α * n) hβ
  have hF := LD1_dev_F c hc g C hC (α * n) hβ
  have heq : (n / 4) / (α * n) ^ 2 + (C * n / 4) / (α * n) ^ 2 = (1 + C) / (4 * α ^ 2 * n) := by
    field_simp
  linarith

/-- (11) and (3) imply `gain ≥ 1 − (1 + C)/(4α²n)`. -/
theorem LD1_pg_det {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1)
    (g : DelegGraph n) (C : ℕ) (hC : maxWeight g ≤ C) (α : ℝ) (hα : 0 < α)
    (h3a : ∑ i, c i + α * n ≤ (n : ℝ) / 2)
    (h3b : (n : ℝ) / 2 ≤ ∑ i, (weight g i : ℝ) * c i - α * n) :
    1 - (1 + C) / (4 * α ^ 2 * n) ≤ gain c g := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hβ : 0 < α * n := by positivity
  have hD := LD1_dev_D c hc (α * n) hβ
  have hF := LD1_dev_F c hc g C hC (α * n) hβ
  have hD' : voteProb c (fun v => (n : ℝ) / 2 < XD v) ≤
      voteProb c (fun v => α * n ≤ |XD v - ∑ i, c i|) := by
    apply LD1_vp_mono c hc
    intro v hv
    rw [le_abs]; left; linarith
  have hF' : voteProb c (fun v => ¬ ((n : ℝ) / 2 < XF g v)) ≤
      voteProb c (fun v => α * n ≤ |XF g v - ∑ i, (weight g i : ℝ) * c i|) := by
    apply LD1_vp_mono c hc
    intro v hv
    push Not at hv
    rw [le_abs]; right; linarith
  have hcomp := LD1_vp_compl c (fun v => (n : ℝ) / 2 < XF g v)
  have heq : (n / 4) / (α * n) ^ 2 + (C * n / 4) / (α * n) ^ 2 = (1 + C) / (4 * α ^ 2 * n) := by
    field_simp
  unfold gain
  linarith

/-! ### The instance law is a probability measure, concentrated on `[0,1]^n` -/

theorem LD1_choice_nonneg (M : Model) {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ x ∈ Set.Icc (0 : ℝ) 1, M.q x ∈ Set.Icc (0 : ℝ) 1)
    (hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ M.φ x y) (i j : Fin n) :
    0 ≤ choiceProb M c i j := by
  unfold choiceProb
  have hS : 0 ≤ ∑ k ∈ Finset.univ.filter (· ≠ i), M.φ (c i) (c k) :=
    Finset.sum_nonneg fun k _ => hφ _ (hc i) _ (hc k)
  have hqi := hq _ (hc i)
  simp only [Set.mem_Icc] at hqi
  split_ifs
  · norm_num
  · norm_num
  · linarith
  · exact div_nonneg (mul_nonneg hqi.1 (hφ _ (hc i) _ (hc j))) hS

theorem LD1_choice_sum (M : Model) {n : ℕ} (c : Fin n → ℝ) (i : Fin n) :
    ∑ j, choiceProb M c i j = 1 := by
  unfold choiceProb
  set S := ∑ k ∈ Finset.univ.filter (· ≠ i), M.φ (c i) (c k) with hS
  by_cases h0 : S = 0
  · simp [h0]
  · simp only [h0, if_false]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl]
    have : ∑ x ∈ Finset.univ.erase i, (if x = i then 1 - M.q (c i)
        else M.q (c i) * M.φ (c i) (c x) / S) =
        ∑ x ∈ Finset.univ.erase i, M.q (c i) * M.φ (c i) (c x) / S := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [if_neg (Finset.ne_of_mem_erase hx)]
    rw [this, ← Finset.sum_div, ← Finset.mul_sum]
    have he : Finset.univ.erase i = Finset.univ.filter (· ≠ i) := by
      ext x; simp
    rw [he, ← hS]
    field_simp
    ring

theorem LD1_density_sum (M : Model) {n : ℕ} (c : Fin n → ℝ) :
    ∑ g : DelegGraph n, ∏ i, choiceProb M c i (g i) = 1 := by
  rw [← Fintype.prod_sum (fun i j => choiceProb M c i j)]
  exact Finset.prod_eq_one fun i _ => LD1_choice_sum M c i

theorem LD1_meas_choice (M : Model) (hqm : Measurable M.q)
    (hφm : Measurable (Function.uncurry M.φ)) {n : ℕ} (i j : Fin n) :
    Measurable fun c : Fin n → ℝ => choiceProb M c i j := by
  have hφk : ∀ k : Fin n, Measurable fun c : Fin n → ℝ => M.φ (c i) (c k) := by
    intro k
    change Measurable (Function.uncurry M.φ ∘ fun c : Fin n → ℝ => (c i, c k))
    exact hφm.comp (by fun_prop)
  have hS : Measurable fun c : Fin n → ℝ => ∑ k ∈ Finset.univ.filter (· ≠ i), M.φ (c i) (c k) :=
    Finset.measurable_sum _ fun k _ => hφk k
  have hqi : Measurable fun c : Fin n → ℝ => M.q (c i) := hqm.comp (measurable_pi_apply i)
  unfold choiceProb
  refine Measurable.ite (measurableSet_eq_fun hS measurable_const) measurable_const ?_
  split_ifs
  · exact measurable_const.sub hqi
  · exact (hqi.mul (hφk j)).div hS

theorem LD1_box_null (D : Measure ℝ) [IsProbabilityMeasure D] (hD : D (Set.Icc 0 1)ᶜ = 0)
    (n : ℕ) : (Measure.pi fun _ : Fin n => D) {c | ¬ ∀ i, c i ∈ Set.Icc (0 : ℝ) 1} = 0 := by
  have : {c : Fin n → ℝ | ¬ ∀ i, c i ∈ Set.Icc (0 : ℝ) 1} =
      ⋃ i, (Function.eval i) ⁻¹' (Set.Icc 0 1)ᶜ := by
    ext c; simp
  rw [this, measure_iUnion_null_iff]
  intro i
  exact Measure.pi_eval_preimage_null _ hD

theorem LD1_box_meas (n : ℕ) : MeasurableSet {c : Fin n → ℝ | ¬ ∀ i, c i ∈ Set.Icc (0 : ℝ) 1} := by
  have : {c : Fin n → ℝ | ¬ ∀ i, c i ∈ Set.Icc (0 : ℝ) 1} =
      ⋃ i, (Function.eval i) ⁻¹' (Set.Icc 0 1)ᶜ := by
    ext c; simp
  rw [this]
  exact MeasurableSet.iUnion fun i => (measurable_pi_apply i) measurableSet_Icc.compl

theorem LD1_law_box (D : Measure ℝ) [IsProbabilityMeasure D] (hD : D (Set.Icc 0 1)ᶜ = 0)
    (M : Model) (n : ℕ) :
    ∀ᵐ ω ∂instanceLaw D M n, ∀ i, ω.1 i ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_iff]
  unfold instanceLaw
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro g _
  have hmeas : MeasurableSet {ω : (Fin n → ℝ) × DelegGraph n | ¬ ∀ i, ω.1 i ∈ Set.Icc (0 : ℝ) 1} :=
    measurable_fst (LD1_box_meas n)
  rw [Measure.map_apply (by fun_prop) hmeas]
  apply withDensity_absolutelyContinuous
  exact LD1_box_null D hD n

theorem LD1_law_prob (D : Measure ℝ) [IsProbabilityMeasure D] (hD : D (Set.Icc 0 1)ᶜ = 0)
    (M : Model) (hq : ∀ x ∈ Set.Icc (0 : ℝ) 1, M.q x ∈ Set.Icc (0 : ℝ) 1)
    (hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ M.φ x y)
    (hqm : Measurable M.q) (hφm : Measurable (Function.uncurry M.φ)) (n : ℕ) :
    IsProbabilityMeasure (instanceLaw D M n) := by
  constructor
  unfold instanceLaw
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  have hdens : ∀ g : DelegGraph n, Measurable fun c : Fin n → ℝ =>
      ENNReal.ofReal (∏ i, choiceProb M c i (g i)) := by
    intro g
    exact ENNReal.measurable_ofReal.comp
      (Finset.measurable_prod _ fun i _ => LD1_meas_choice M hqm hφm i (g i))
  have hterm : ∀ g : DelegGraph n, (((Measure.pi fun _ : Fin n => D).withDensity
      (fun c => ENNReal.ofReal (∏ i, choiceProb M c i (g i)))).map (fun c => (c, g))) Set.univ =
      ∫⁻ c, ENNReal.ofReal (∏ i, choiceProb M c i (g i)) ∂(Measure.pi fun _ : Fin n => D) := by
    intro g
    rw [Measure.map_apply (by fun_prop : Measurable fun c : Fin n → ℝ => (c, g)) MeasurableSet.univ,
      Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [← lintegral_finsetSum _ fun g _ => hdens g]
  have hae : ∀ᵐ c ∂(Measure.pi fun _ : Fin n => D),
      ∑ g : DelegGraph n, ENNReal.ofReal (∏ i, choiceProb M c i (g i)) = 1 := by
    have h0 := LD1_box_null D hD n
    have : ∀ᵐ c ∂(Measure.pi fun _ : Fin n => D), ∀ i, c i ∈ Set.Icc (0 : ℝ) 1 := by
      rw [ae_iff]; exact h0
    filter_upwards [this] with c hc
    rw [← ENNReal.ofReal_sum_of_nonneg (fun g _ => Finset.prod_nonneg fun i _ =>
      LD1_choice_nonneg M c hc hq hφ i (g i)), LD1_density_sum, ENNReal.ofReal_one]
  rw [lintegral_congr_ae hae]
  simp

/-! ### Assembly -/

theorem LD1_lower {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (A B G : Set X) (Q : X → Prop) (hBm : MeasurableSet B) (hQ : ∀ᵐ ω ∂μ, Q ω)
    (h : ∀ ω, Q ω → ω ∈ A → ω ∈ B → ω ∈ G) : μ.real A + μ.real B - 1 ≤ μ.real G := by
  have h1 : μ.real A ≤ μ.real (A ∩ B) + μ.real Bᶜ := by
    calc μ.real A ≤ μ.real ((A ∩ B) ∪ Bᶜ) := by
          apply measureReal_mono _ (measure_ne_top _ _)
          intro ω hω
          by_cases hb : ω ∈ B
          · left; exact ⟨hω, hb⟩
          · right; exact hb
      _ ≤ μ.real (A ∩ B) + μ.real Bᶜ := measureReal_union_le _ _
  have h2 : μ.real Bᶜ = 1 - μ.real B := probReal_compl_eq_one_sub hBm
  have h3 : μ.real (A ∩ B) ≤ μ.real G := by
    rw [measureReal_def, measureReal_def]
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hQ] with ω hω hAB
    exact h ω hω hAB.1 hAB.2
  linarith

theorem LD1_rate (C : ℕ → ℕ) (hCo : (fun n => (C n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    (α : ℝ) (hα : 0 < α) :
    Tendsto (fun n : ℕ => (1 + C n) / (4 * α ^ 2 * n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (C n : ℝ) / n) atTop (𝓝 0) := hCo.tendsto_div_nhds_zero
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h3 := (h2.add h1).div_const (4 * α ^ 2)
  rw [add_zero, zero_div] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn' : (n : ℝ) ≠ 0 := by linarith
  field_simp

theorem LD1_meas_lin (n : ℕ) (f : DelegGraph n → (Fin n → ℝ) → ℝ)
    (hf : ∀ g, Measurable (f g)) :
    Measurable fun ω : (Fin n → ℝ) × DelegGraph n => f ω.2 ω.1 :=
  measurable_from_prod_countable_left fun g => hf g

theorem solution (M : Model) (𝔇 : Set (Measure ℝ))
    (h𝔇 : ∀ D ∈ 𝔇, IsProbabilityMeasure D ∧ D (Set.Icc 0 1)ᶜ = 0)
    (hq : ∀ x ∈ Set.Icc (0 : ℝ) 1, M.q x ∈ Set.Icc (0 : ℝ) 1)
    (hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ M.φ x y)
    (hqm : Measurable M.q) (hφm : Measurable (Function.uncurry M.φ))
    (h12 : ∀ D ∈ 𝔇, ∃ α ∈ Set.Ioo (0 : ℝ) 1, ∃ C : ℕ → ℕ,
      (fun n => (C n : ℝ)) =o[atTop] (fun n => (n : ℝ)) ∧
      Tendsto (fun n => (instanceLaw D M n).real {ω | maxWeight ω.2 ≤ C n}) atTop (𝓝 1) ∧
      Tendsto (fun n => (instanceLaw D M n).real
        {ω | 2 * α * n ≤ ∑ i, (weight ω.2 i : ℝ) * ω.1 i - ∑ i, ω.1 i}) atTop (𝓝 1)) :
    ProbDNH M 𝔇 ∧
      ((∃ D ∈ 𝔇, ∃ α ∈ Set.Ioo (0 : ℝ) 1, Tendsto (fun n => (instanceLaw D M n).real
          {ω | ∑ i, ω.1 i + α * n ≤ (n : ℝ) / 2 ∧
            (n : ℝ) / 2 ≤ ∑ i, (weight ω.2 i : ℝ) * ω.1 i - α * n}) atTop (𝓝 1)) →
        ProbPG M 𝔇) := by
  constructor
  · intro D hD ε hε δ hδ
    obtain ⟨hP, hS⟩ := h𝔇 D hD
    have hprob := LD1_law_prob D hS M hq hφ hqm hφm
    obtain ⟨α, hα, C, hCo, h1, h2⟩ := h12 D hD
    have hr := LD1_rate C hCo α hα.1
    have hsum := (h1.add h2).sub_const 1
    norm_num at hsum
    have ev1 := hsum.eventually (lt_mem_nhds (show 1 - δ < 1 by linarith))
    have ev2 := hr.eventually (Iic_mem_nhds hε)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (ev1.and (ev2.and (eventually_ge_atTop 1)))
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨hlt, hle, hn1⟩ := hN n hn
    refine lt_of_lt_of_le hlt ?_
    apply LD1_lower (instanceLaw D M n) _ _ _ (fun ω => ∀ i, ω.1 i ∈ Set.Icc (0 : ℝ) 1)
    · apply measurableSet_le measurable_const
      apply LD1_meas_lin n (fun g c => ∑ i, (weight g i : ℝ) * c i - ∑ i, c i)
      intro g; fun_prop
    · exact LD1_law_box D hS M n
    · intro ω hbox hA hB
      simp only [Set.mem_setOf_eq] at hA hB ⊢
      have := LD1_dnh_det hn1 ω.1 hbox ω.2 (C n) hA α hα.1 hB
      linarith
  · rintro ⟨D, hD, α, hα, h3⟩
    refine ⟨D, hD, ?_⟩
    intro ε hε δ hδ
    obtain ⟨hP, hS⟩ := h𝔇 D hD
    have hprob := LD1_law_prob D hS M hq hφ hqm hφm
    obtain ⟨α', _, C, hCo, h1, _⟩ := h12 D hD
    have hr := LD1_rate C hCo α hα.1
    have hsum := (h1.add h3).sub_const 1
    norm_num at hsum
    have ev1 := hsum.eventually (lt_mem_nhds (show 1 - δ < 1 by linarith))
    have ev2 := hr.eventually (Iic_mem_nhds hε)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (ev1.and (ev2.and (eventually_ge_atTop 1)))
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨hlt, hle, hn1⟩ := hN n hn
    refine lt_of_lt_of_le hlt ?_
    apply LD1_lower (instanceLaw D M n) _ _ _ (fun ω => ∀ i, ω.1 i ∈ Set.Icc (0 : ℝ) 1)
    · rw [Set.setOf_and]
      apply MeasurableSet.inter
      · exact measurableSet_le (LD1_meas_lin n (fun g c => ∑ i, c i + α * n)
          (fun g => by fun_prop)) measurable_const
      · exact measurableSet_le measurable_const
          (LD1_meas_lin n (fun g c => ∑ i, (weight g i : ℝ) * c i - α * n)
          (fun g => by fun_prop))
    · exact LD1_law_box D hS M n
    · intro ω hbox hA hB
      simp only [Set.mem_setOf_eq] at hA hB ⊢
      have := LD1_pg_det hn1 ω.1 hbox ω.2 (C n) hA α hα.1 hB.1 hB.2
      linarith
