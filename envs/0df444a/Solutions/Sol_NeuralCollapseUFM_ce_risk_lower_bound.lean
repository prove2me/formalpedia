-- Prove2me | solution 1 for NeuralCollapseUFM.ce_risk_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T17:37:31.107124+00:00
-- url     : https://prove2.me/submissions/7b9c87dc-7531-456f-aa4c-7f82767b04b4

import Mathlib
import Definitions.Def_NeuralCollapseUFM_Basic

open Matrix Filter Topology

namespace NeuralCollapseUFM

section A
open Finset
theorem cl_main {K : ℕ} (hK : 2 ≤ K) (z : Fin K → ℝ) (k : Fin K) (c1 : ℝ)
    (hc1 : 0 < c1) :
    1 / (1 + c1) * ((∑ i, z i) - K * z k) / ((K : ℝ) - 1) + cTwo K c1 ≤ ceLoss z k ∧
    (ceLoss z k = 1 / (1 + c1) * ((∑ i, z i) - K * z k) / ((K : ℝ) - 1) + cTwo K c1 ↔
      (∀ i j, i ≠ k → j ≠ k → z i = z j) ∧
        c1 = (((K : ℝ) - 1) * Real.exp (((∑ i, z i) - K * z k) / ((K : ℝ) - 1)))⁻¹) := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK1 : (0 : ℝ) < (K : ℝ) - 1 := by linarith
  set t := univ.erase k with ht
  have hct : (t.card : ℝ) = (K : ℝ) - 1 := by
    rw [ht, card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega : 1 ≤ K)]; simp
  set w : ℝ := 1 / ((K : ℝ) - 1) with hw
  set T : ℝ := ((∑ i, z i) - K * z k) / ((K : ℝ) - 1) with hT
  set d : Fin K → ℝ := fun i => z i - z k with hd
  have hw1 : ∑ i ∈ t, w = 1 := by
    rw [sum_const, nsmul_eq_mul, hct, hw]; field_simp
  have hwd : ∑ i ∈ t, w • d i = T := by
    simp only [smul_eq_mul, ← mul_sum, hd, sum_sub_distrib, sum_const, nsmul_eq_mul, hct]
    rw [ht, sum_erase_eq_sub (mem_univ k), hw, hT]
    field_simp; ring
  set A : ℝ := ∑ i ∈ t, w • Real.exp (d i) with hAdef
  have hjen := strictConvexOn_exp.convexOn.map_sum_le (t := t) (w := fun _ => w) (p := d)
    (fun _ _ => by rw [hw]; positivity) hw1 (fun _ _ => Set.mem_univ _)
  rw [hwd] at hjen
  have hjeq := strictConvexOn_exp.map_sum_eq_iff_of_pos (t := t) (w := fun _ => w) (p := d)
    (fun _ _ => by rw [hw]; positivity) hw1 (fun _ _ => Set.mem_univ _)
  rw [hwd] at hjeq
  -- A ≥ exp T ; loss = log (1 + (K-1) A)
  have hA : 1 + ((K : ℝ) - 1) * A = (∑ i, Real.exp (z i)) / Real.exp (z k) := by
    have : ((K : ℝ) - 1) * A = ∑ i ∈ t, Real.exp (z i) / Real.exp (z k) := by
      rw [hAdef, mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, hd, Real.exp_sub, hw]; field_simp
    rw [this, ← sum_div, ht, sum_erase_eq_sub (mem_univ k)]
    field_simp; ring
  have hL : ceLoss z k = Real.log (1 + ((K : ℝ) - 1) * A) := by
    rw [hA, ceLoss, ← Real.log_inv, inv_div]
  have hET : 0 < Real.exp T := Real.exp_pos T
  -- concavity step
  set p : ℝ := 1 / (1 + c1) with hp
  set q : ℝ := c1 / (1 + c1) with hq
  have hp0 : 0 < p := by rw [hp]; positivity
  have hq0 : 0 < q := by rw [hq]; positivity
  have hpq : q + p = 1 := by rw [hp, hq]; field_simp; ring
  set a : ℝ := (1 + c1) / c1 with ha
  set b : ℝ := (1 + c1) * ((K : ℝ) - 1) * Real.exp T with hb
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  have hab : q • a + p • b = 1 + ((K : ℝ) - 1) * Real.exp T := by
    rw [smul_eq_mul, smul_eq_mul, hq, ha, hp, hb]; field_simp
  have hlogs : q • Real.log a + p • Real.log b = p * T + cTwo K c1 := by
    rw [smul_eq_mul, smul_eq_mul, hb, Real.log_mul (by positivity) hET.ne', Real.log_exp, cTwo,
      hp, hq, ha]
    ring
  have hconc : q • Real.log a + p • Real.log b ≤ Real.log (q • a + p • b) :=
    strictConcaveOn_log_Ioi.concaveOn.2 ha0 hb0 hq0.le hp0.le hpq
  have hstrict : a ≠ b → q • Real.log a + p • Real.log b < Real.log (q • a + p • b) :=
    fun hne => strictConcaveOn_log_Ioi.2 ha0 hb0 hne hq0 hp0 hpq
  rw [hab, hlogs] at hconc
  have hgoal : 1 / (1 + c1) * ((∑ i, z i) - K * z k) / ((K : ℝ) - 1) = p * T := by
    rw [hp, hT]; ring
  rw [hgoal, hL]
  have hmono : Real.log (1 + ((K : ℝ) - 1) * Real.exp T) ≤ Real.log (1 + ((K : ℝ) - 1) * A) :=
    Real.log_le_log (by positivity) (by nlinarith)
  refine ⟨hconc.trans hmono, ⟨fun heq => ?_, fun ⟨hz, hc⟩ => ?_⟩⟩
  · have e1 : Real.log (1 + ((K : ℝ) - 1) * Real.exp T) = p * T + cTwo K c1 := by linarith
    have e2 : Real.log (1 + ((K : ℝ) - 1) * Real.exp T) = Real.log (1 + ((K : ℝ) - 1) * A) := by
      linarith
    have hApos : 0 < 1 + ((K : ℝ) - 1) * Real.exp T := by positivity
    have e3 : 1 + ((K : ℝ) - 1) * Real.exp T = 1 + ((K : ℝ) - 1) * A :=
      Real.log_injOn_pos hApos (by
        show 0 < 1 + ((K : ℝ) - 1) * A
        nlinarith) e2
    have e4 : Real.exp T = A := by
      have := mul_left_cancel₀ hK1.ne' (by linarith : ((K : ℝ) - 1) * Real.exp T = ((K : ℝ) - 1) * A)
      exact this
    have hjall := hjeq.1 (by simpa [hAdef] using e4)
    have hab' : a = b := by
      by_contra hne
      have := hstrict hne
      rw [hab, hlogs] at this
      linarith
    refine ⟨fun i j hi hj => ?_, ?_⟩
    · have := hjall (mem_erase.2 ⟨hi, mem_univ i⟩) (mem_erase.2 ⟨hj, mem_univ j⟩)
      simpa [hd] using this
    · rw [ha, hb] at hab'
      field_simp at hab' ⊢
      nlinarith [hab']
  · have hall : ∀ i ∈ t, ∀ j ∈ t, d i = d j := by
      intro i hi j hj
      simp only [hd]
      rw [hz i j (ne_of_mem_erase hi) (ne_of_mem_erase hj)]
    have e4 : Real.exp T = A := by simpa [hAdef] using hjeq.2 (fun i hi j hj => hall i hi j hj)
    have hab' : a = b := by
      rw [ha, hb, hc]
      have : ((K : ℝ) - 1) * Real.exp T ≠ 0 := by positivity
      field_simp
    rw [← e4, ← hab, ← hlogs, hab', ← add_smul, ← add_smul, hpq, one_smul, one_smul]

end A

lemma cp_ce_diff {K n : ℕ} (hK : 2 ≤ K) (Z C : Matrix (Fin K) (Fin K × Fin n) ℝ) :
    DifferentiableAt ℝ (fun s : ℝ => ceRisk (Z - s • C)) 0 := by
  have hne : ∀ (s : ℝ) (c : Fin K × Fin n), 0 < ∑ l, Real.exp ((Z - s • C) l c) := by
    intro s c
    have : (Finset.univ : Finset (Fin K)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    exact Finset.sum_pos (fun _ _ => Real.exp_pos _) this
  unfold ceRisk ceLoss
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  refine DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun k _ => DifferentiableAt.fun_sum fun i _ => ?_) _
  refine DifferentiableAt.neg (DifferentiableAt.log ?_ ?_)
  · refine DifferentiableAt.div (by fun_prop) (by fun_prop) ?_
    have := hne 0 (k, i); simpa using this.ne'
  · have := hne 0 (k, i)
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
    exact (div_pos (Real.exp_pos _) this).ne'

lemma cp_frob {m p : Type*} [Fintype m] [Fintype p] (A B : Matrix m p ℝ) :
    HasDerivAt (fun t : ℝ => frobSq (A + t • B)) (∑ i, ∑ j, 2 * A i j * B i j) 0 := by
  unfold frobSq
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  have h : HasDerivAt (fun t : ℝ => A i j + t * B i j) (B i j) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (B i j)).const_add (A i j)
  have e : (fun t : ℝ => (A i j + t * B i j) ^ 2) = fun t => (A i j + t * B i j) * (A i j + t * B i j) := by
    funext t; ring
  rw [e]
  exact (h.mul h).congr_deriv (by ring)


lemma cp_key {K d n : ℕ} (hK : 2 ≤ K) (lamW lamH lamb : ℝ)
    (x : Params K d n) (hx : IsCriticalPoint (objective lamW lamH lamb) x)
    (S : Matrix (Fin d) (Fin d) ℝ) :
    lamW / 2 * (∑ i, ∑ j, 2 * x.1 i j * (x.1 * S) i j) +
      lamH / 2 * (∑ i, ∑ j, 2 * x.2.1 i j * (-(S * x.2.1)) i j) = 0 := by
  obtain ⟨W, H, b⟩ := x
  set φ : ℝ → ℝ := fun s => ceRisk (logits W H b - s • (W * S * (S * H))) with hφ
  have hfun : (fun t : ℝ => objective lamW lamH lamb ((W, H, b) + t • ((W * S, -(S * H), 0) : Params K d n))) =
      fun t => φ (t ^ 2) + lamW / 2 * frobSq (W + t • (W * S)) +
        lamH / 2 * frobSq (H + t • (-(S * H))) + lamb / 2 * sqNorm b := by
    funext t
    have hL : logits (W + t • (W * S)) (H + t • -(S * H)) b = logits W H b - t ^ 2 • (W * S * (S * H)) := by
      unfold logits
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg,
        Matrix.neg_mul, Matrix.mul_assoc]
      module
    simp only [objective, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_zero,
      add_zero, hφ]
    rw [hL]
  have h1 := hx ((W * S, -(S * H), 0) : Params K d n)
  rw [hfun] at h1
  have hd : DifferentiableAt ℝ φ 0 := cp_ce_diff hK _ _
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
    simpa using hasDerivAt_pow 2 (0:ℝ)
  have hcomp : HasDerivAt (fun t : ℝ => φ (t ^ 2)) (deriv φ 0 * 0) 0 := by
    have : HasDerivAt φ (deriv φ 0) ((0:ℝ) ^ 2) := by
      rw [show (0:ℝ) ^ 2 = 0 by norm_num]; exact hd.hasDerivAt
    exact HasDerivAt.comp (h₂ := φ) (h := fun t : ℝ => t ^ 2) (0:ℝ) this hsq
  have h2 := ((hcomp.add ((cp_frob W (W * S)).const_mul (lamW / 2))).add
    ((cp_frob H (-(S * H))).const_mul (lamH / 2))).add_const (lamb / 2 * sqNorm b)
  have := h1.unique h2
  simp only [mul_zero, zero_add] at this
  simpa using this.symm

theorem critical_point_balance {K d n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    (lamW lamH lamb : ℝ) (hW : 0 < lamW) (hH : 0 < lamH) (hb : 0 < lamb)
    (x : Params K d n) (hx : IsCriticalPoint (objective lamW lamH lamb) x) :
    x.1ᵀ * x.1 = (lamH / lamW) • (x.2.1 * x.2.1ᵀ) ∧
      frobSq x.1 = lamH / lamW * frobSq x.2.1 := by
  have entry : ∀ i j, (x.1ᵀ * x.1) i j = ((lamH / lamW) • (x.2.1 * x.2.1ᵀ)) i j := by
    intro i j
    have := cp_key hK lamW lamH lamb x hx (Matrix.single j i 1)
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    have e1 : ∑ a, 2 * x.1 a i * x.1 a j = 2 * ∑ a, x.1 a i * x.1 a j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    have e2 : ∑ c, 2 * x.2.1 j c * x.2.1 i c = 2 * ∑ c, x.2.1 i c * x.2.1 j c := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, e2] at this
    field_simp
    linarith
  refine ⟨Matrix.ext entry, ?_⟩
  have diag : ∀ j, ∑ a, x.1 a j ^ 2 = lamH / lamW * ∑ c, x.2.1 j c ^ 2 := by
    intro j
    have := entry j j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at this
    simpa [sq] using this
  unfold frobSq
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => diag j


lemma rl_col {K d : ℕ} (W : Matrix (Fin K) (Fin d) ℝ) (Hc : Fin d → ℝ) (b : Fin K → ℝ) (k : Fin K) :
    (∑ j, ((∑ a, W j a * Hc a) + b j)) - (K : ℝ) * ((∑ a, W k a * Hc a) + b k) =
      (∑ a, ((∑ j, W j a) - (K : ℝ) * W k a) * Hc a) + ((∑ j, b j) - (K : ℝ) * b k) := by
  simp only [Finset.sum_add_distrib, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hm : (K : ℝ) * ∑ a, W k a * Hc a = ∑ a, (K : ℝ) * W k a * Hc a := by
    rw [Finset.mul_sum]; simp only [mul_assoc]
  rw [mul_add, hm]
  ring

lemma rl_b {K n : ℕ} (b : Fin K → ℝ) :
    ∑ k : Fin K, ∑ i : Fin n, ((∑ j, b j) - (K : ℝ) * b k) = 0 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

lemma rl_u {K d : ℕ} (W : Matrix (Fin K) (Fin d) ℝ) :
    ∑ k, ∑ a, ((∑ j, W j a) - (K : ℝ) * W k a) ^ 2 ≤ (K : ℝ) ^ 2 * frobSq W := by
  unfold frobSq
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => W i j ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have e : ∑ k : Fin K, ((∑ j, W j a) - (K : ℝ) * W k a) ^ 2 =
      (K : ℝ) ^ 2 * ∑ k, W k a ^ 2 - K * (∑ j, W j a) ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [e]
  have : 0 ≤ (K : ℝ) * (∑ j, W j a) ^ 2 := by positivity
  linarith

end NeuralCollapseUFM

open NeuralCollapseUFM in
theorem solution {K d n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    (lamW lamH lamb : ℝ) (hW : 0 < lamW) (hH : 0 < lamH) (hb : 0 < lamb)
    (x : Params K d n) (hx : IsCriticalPoint (objective lamW lamH lamb) x) (c1 : ℝ)
    (hc1 : 0 < c1) :
    -(frobSq x.1) / ((1 + c1) * ((K : ℝ) - 1)) * Real.sqrt (lamW / (lamH * n)) + cTwo K c1 ≤
      ceRisk (logits x.1 x.2.1 x.2.2) := by
  have hbal := (critical_point_balance hK hn lamW lamH lamb hW hH hb x hx).2
  obtain ⟨W, H, b⟩ := x
  simp only at hbal ⊢
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK1 : (0 : ℝ) < (K : ℝ) - 1 := by linarith
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set A : ℝ := 1 / (1 + c1) with hA
  have hA0 : 0 < A := by positivity
  set u : Fin K → Fin d → ℝ := fun k a => (∑ j, W j a) - (K : ℝ) * W k a with hu
  set X : ℝ := ∑ k : Fin K, ∑ i : Fin n, ∑ a, u k a * H a (k, i) with hX
  -- step 1
  have hcol : ∀ k i, (∑ j, logits W H b j (k, i)) - (K : ℝ) * logits W H b k (k, i) =
      (∑ a, u k a * H a (k, i)) + ((∑ j, b j) - (K : ℝ) * b k) := by
    intro k i
    simp only [logits, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, hu]
    exact rl_col W (fun a => H a (k, i)) b k
  have hsumD : ∑ k : Fin K, ∑ i : Fin n,
      ((∑ j, logits W H b j (k, i)) - (K : ℝ) * logits W H b k (k, i)) = X := by
    simp only [hcol, Finset.sum_add_distrib, rl_b, add_zero, hX]
  have h1 : cTwo K c1 + A / (((K : ℝ) - 1) * (K * n)) * X ≤ ceRisk (logits W H b) := by
    unfold ceRisk
    have hle : ∑ k : Fin K, ∑ i : Fin n, (A * ((∑ j, logits W H b j (k, i)) - (K : ℝ) * logits W H b k (k, i)) / ((K : ℝ) - 1) + cTwo K c1)
        ≤ ∑ k, ∑ i, ceLoss (fun j => logits W H b j (k, i)) k :=
      Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i _ =>
        (cl_main hK (fun j => logits W H b j (k, i)) k c1 hc1).1
    have hev : ∑ k : Fin K, ∑ i : Fin n, (A * ((∑ j, logits W H b j (k, i)) - (K : ℝ) * logits W H b k (k, i)) / ((K : ℝ) - 1) + cTwo K c1)
        = A / ((K : ℝ) - 1) * X + (K * n) * cTwo K c1 := by
      rw [← hsumD]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
      · ring
    rw [hev] at hle
    have hKn : (0 : ℝ) < K * n := by positivity
    rw [show cTwo K c1 + A / (((K : ℝ) - 1) * (K * n)) * X = 1 / ((K : ℝ) * n) * (A / ((K : ℝ) - 1) * X + (K * n) * cTwo K c1) by
      field_simp; ring]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin K × Fin n × Fin d))
    (fun p => u p.1 p.2.2) (fun p => H p.2.2 (p.1, p.2.1))
  simp only [Fintype.sum_prod_type] at hCS
  have hU : ∑ k : Fin K, ∑ i : Fin n, ∑ a, u k a ^ 2 ≤ n * ((K : ℝ) ^ 2 * frobSq W) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (rl_u W) (by positivity)
  have hHf : ∑ k : Fin K, ∑ i : Fin n, ∑ a, H a (k, i) ^ 2 = frobSq H := by
    unfold frobSq
    conv_rhs => rw [Finset.sum_comm]
    simp only [Fintype.sum_prod_type]
  have hfW : 0 ≤ frobSq W := by unfold frobSq; positivity
  have hfH : 0 ≤ frobSq H := by unfold frobSq; positivity
  rw [hHf] at hCS
  have hX2 : X ^ 2 ≤ (K : ℝ) ^ 2 * n * frobSq W * frobSq H := by
    calc X ^ 2 ≤ _ := hCS
      _ ≤ n * ((K : ℝ) ^ 2 * frobSq W) * frobSq H := mul_le_mul_of_nonneg_right hU hfH
      _ = _ := by ring
  set sq := Real.sqrt (lamW / (lamH * n)) with hsqd
  have hsq : sq ^ 2 = lamW / (lamH * n) := Real.sq_sqrt (by positivity)
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  have hR : ((K : ℝ) * n * frobSq W * sq) ^ 2 = (K : ℝ) ^ 2 * n * frobSq W * frobSq H := by
    rw [mul_pow, hsq]
    conv_lhs => rw [show ((K : ℝ) * n * frobSq W) ^ 2 = (K : ℝ) ^ 2 * n ^ 2 * frobSq W * frobSq W by ring]
    rw [hbal]; field_simp
  have hR0 : 0 ≤ (K : ℝ) * n * frobSq W * sq := by positivity
  have hlow := (abs_le_of_sq_le_sq' (hR ▸ hX2) hR0).1
  have hKn : (0 : ℝ) < K * n := by positivity
  have he : -(frobSq W) / ((1 + c1) * ((K : ℝ) - 1)) * sq =
      A / (((K : ℝ) - 1) * (K * n)) * (-((K : ℝ) * n * frobSq W * sq)) := by
    rw [hA]; field_simp
  rw [he]
  have := mul_le_mul_of_nonneg_left hlow (le_of_lt (show 0 < A / (((K : ℝ) - 1) * (K * n)) by positivity))
  linarith
