-- Prove2me | solution 1 for GraphAlignment.Possible.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:09:13.692984+00:00
-- url     : https://prove2.me/submissions/3bdd25ed-503f-4986-9093-ac1123832a3e

import Mathlib
import Definitions.Def_GraphAlignment_Possible_PoissonTail

set_option autoImplicit false

open GraphAlignment.Possible

/-- Poisson point mass. -/
noncomputable def pm (μ : ℝ) (i : ℕ) : ℝ := μ ^ i * Real.exp (-μ) / (i.factorial : ℝ)

lemma pm_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (i : ℕ) : 0 ≤ pm μ i := by
  unfold pm; positivity

lemma pm_succ (μ : ℝ) (b : ℕ) : pm μ (b + 1) = pm μ b * μ / ((b : ℝ) + 1) := by
  unfold pm
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  have : (b.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma pm_reflect {μ : ℝ} (hμ : 0 < μ) (a : ℕ) :
    ∀ i : ℕ, i ≤ a → pm μ (a - i) ≤ pm μ a * ((a : ℝ) / μ) ^ i := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h := ih (by omega)
    obtain ⟨b, hb⟩ : ∃ b, a - i = b + 1 := ⟨a - (i + 1), by omega⟩
    have hb' : a - (i + 1) = b := by omega
    rw [hb] at h
    rw [hb']
    have e : pm μ b = pm μ (b + 1) * (((b : ℝ) + 1) / μ) := by
      rw [pm_succ]; field_simp
    have hb1 : ((b : ℝ) + 1) ≤ a := by
      have : b + 1 ≤ a := by omega
      exact_mod_cast this
    have hpm : 0 ≤ pm μ (b + 1) := pm_nonneg hμ.le _
    have hr : 0 ≤ (a : ℝ) / μ := by positivity
    rw [e, pow_succ]
    calc pm μ (b + 1) * (((b : ℝ) + 1) / μ) ≤ pm μ (b + 1) * ((a : ℝ) / μ) := by
          apply mul_le_mul_of_nonneg_left _ hpm
          exact div_le_div_of_nonneg_right hb1 hμ.le
      _ ≤ (pm μ a * ((a : ℝ) / μ) ^ i) * ((a : ℝ) / μ) := by
          apply mul_le_mul_of_nonneg_right h hr
      _ = pm μ a * (((a : ℝ) / μ) ^ i * ((a : ℝ) / μ)) := by ring

lemma pm_head {μ : ℝ} (hμ : 0 < μ) (a : ℕ) (hr : (a : ℝ) < μ) :
    ∑ i ∈ Finset.range (a + 1), pm μ i ≤ pm μ a / (1 - (a : ℝ) / μ) := by
  set r : ℝ := (a : ℝ) / μ with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hrdef, div_lt_one hμ]; exact hr
  have h1 : ∑ i ∈ Finset.range (a + 1), pm μ i = ∑ i ∈ Finset.range (a + 1), pm μ (a + 1 - 1 - i) := by
    rw [Finset.sum_range_reflect (fun i => pm μ i) (a + 1)]
  have h2 : ∑ i ∈ Finset.range (a + 1), pm μ (a + 1 - 1 - i) ≤
      ∑ i ∈ Finset.range (a + 1), pm μ a * r ^ i := by
    apply Finset.sum_le_sum
    intro i hi
    have : i ≤ a := by simpa [Nat.lt_succ_iff] using hi
    have := pm_reflect hμ a i this
    simpa using this
  rw [h1]
  refine h2.trans ?_
  rw [← Finset.mul_sum]
  have hg : (∑ i ∈ Finset.range (a + 1), r ^ i) * (1 - r) = 1 - r ^ (a + 1) := geom_sum_mul_neg r (a + 1)
  have hpos : 0 < 1 - r := by linarith
  have hle : ∑ i ∈ Finset.range (a + 1), r ^ i ≤ 1 / (1 - r) := by
    rw [le_div_iff₀ hpos, hg]
    have : 0 ≤ r ^ (a + 1) := by positivity
    linarith
  calc pm μ a * ∑ i ∈ Finset.range (a + 1), r ^ i ≤ pm μ a * (1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left hle (pm_nonneg hμ.le _)
    _ = pm μ a / (1 - r) := by ring

lemma pm_anti (a : ℕ) {μ₀ μ : ℝ} (h0 : 0 < μ₀) (ha : (a : ℝ) ≤ μ₀) (hμ : μ₀ ≤ μ) :
    pm μ a ≤ pm μ₀ a := by
  unfold pm
  obtain ⟨d, hd, rfl⟩ : ∃ d, 0 ≤ d ∧ μ = μ₀ + d := ⟨μ - μ₀, by linarith, by ring⟩
  have hf : (0 : ℝ) < (a.factorial : ℝ) := by positivity
  apply div_le_div_of_nonneg_right _ hf.le
  have h1 : (μ₀ + d) ^ a ≤ μ₀ ^ a * Real.exp d := by
    have h2 : (μ₀ + d) = μ₀ * (1 + d / μ₀) := by field_simp
    have h3 : 1 + d / μ₀ ≤ Real.exp (d / μ₀) := by linarith [Real.add_one_le_exp (d / μ₀)]
    have h4 : (1 + d / μ₀) ^ a ≤ Real.exp (d / μ₀) ^ a :=
      pow_le_pow_left₀ (by positivity) h3 a
    have h5 : Real.exp (d / μ₀) ^ a = Real.exp (a * (d / μ₀)) := by
      rw [← Real.exp_nat_mul]
    have h6 : (a : ℝ) * (d / μ₀) ≤ d := by
      rw [← mul_div_assoc, div_le_iff₀ h0]; nlinarith
    calc (μ₀ + d) ^ a = μ₀ ^ a * (1 + d / μ₀) ^ a := by rw [← mul_pow, ← h2]
      _ ≤ μ₀ ^ a * Real.exp d := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [h5] at h4
          exact h4.trans (Real.exp_le_exp.mpr h6)
  calc (μ₀ + d) ^ a * Real.exp (-(μ₀ + d)) ≤ μ₀ ^ a * Real.exp d * Real.exp (-(μ₀ + d)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = μ₀ ^ a * Real.exp (-μ₀) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma pm_stirling (a : ℕ) (ha : 8 ≤ a) : pm (4 * ((a : ℝ) + 1) / 3) a ≤ 0.072 := by
  have haR : (8 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by linarith
  set μ₀ : ℝ := 4 * ((a : ℝ) + 1) / 3 with hμ₀
  have hS := Stirling.le_factorial_stirling a
  have hsq : 0 < Real.sqrt (2 * Real.pi * a) := Real.sqrt_pos.mpr (by positivity)
  have hst : 0 < Real.sqrt (2 * Real.pi * a) * ((a : ℝ) / Real.exp 1) ^ a := by positivity
  have hfac : (0 : ℝ) < a.factorial := by positivity
  -- (μ₀)^a ≤ a^a (4/3)^a e
  have e1 : (1 + 1 / (a : ℝ)) ^ a ≤ Real.exp 1 := by
    have h3 : 1 + 1 / (a : ℝ) ≤ Real.exp (1 / a) := by linarith [Real.add_one_le_exp (1 / (a : ℝ))]
    calc (1 + 1 / (a : ℝ)) ^ a ≤ Real.exp (1 / a) ^ a := pow_le_pow_left₀ (by positivity) h3 a
      _ = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp
  have e2 : (4 / 3 : ℝ) ≤ Real.exp 0.29 := by
    have := Real.sum_le_exp_of_nonneg (x := 0.29) (by norm_num) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have e3 : (4 / 3 : ℝ) ^ a ≤ Real.exp (0.29 * a) := by
    calc (4 / 3 : ℝ) ^ a ≤ Real.exp 0.29 ^ a := pow_le_pow_left₀ (by norm_num) e2 a
      _ = Real.exp (0.29 * a) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have e4 : μ₀ ^ a ≤ (a : ℝ) ^ a * (Real.exp (0.29 * a) * Real.exp 1) := by
    have : μ₀ = (a : ℝ) * ((4 / 3) * (1 + 1 / (a : ℝ))) := by
      rw [hμ₀]; field_simp
    rw [this, mul_pow, mul_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul e3 e1 (by positivity) (by positivity)
  have e5 : pm μ₀ a ≤ Real.exp (0.29 * a + 1 + a - μ₀) / Real.sqrt (2 * Real.pi * a) := by
    unfold pm
    rw [div_le_div_iff₀ hfac hsq]
    have hexp : Real.exp (0.29 * a + 1 + a - μ₀) = Real.exp (0.29 * a) * Real.exp 1 * Real.exp a * Real.exp (-μ₀) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; try ring
    rw [hexp]
    have hapow : ((a : ℝ) / Real.exp 1) ^ a = (a : ℝ) ^ a / Real.exp a := by
      rw [div_pow, ← Real.exp_nat_mul]; congr 2; ring
    rw [hapow] at hS
    have h7 : μ₀ ^ a * Real.exp (-μ₀) ≤ (a : ℝ) ^ a * (Real.exp (0.29 * a) * Real.exp 1) * Real.exp (-μ₀) :=
      mul_le_mul_of_nonneg_right e4 (Real.exp_pos _).le
    have h8 : Real.sqrt (2 * Real.pi * a) * ((a : ℝ) ^ a / Real.exp a) ≤ a.factorial := hS
    have hea : 0 < Real.exp a := Real.exp_pos _
    have h9 : Real.sqrt (2 * Real.pi * a) * (a : ℝ) ^ a ≤ a.factorial * Real.exp a := by
      have := mul_le_mul_of_nonneg_right h8 hea.le
      calc Real.sqrt (2 * Real.pi * a) * (a : ℝ) ^ a
          = Real.sqrt (2 * Real.pi * a) * ((a : ℝ) ^ a / Real.exp a) * Real.exp a := by field_simp
        _ ≤ _ := this
    calc μ₀ ^ a * Real.exp (-μ₀) * Real.sqrt (2 * Real.pi * a)
        ≤ (a : ℝ) ^ a * (Real.exp (0.29 * a) * Real.exp 1) * Real.exp (-μ₀) * Real.sqrt (2 * Real.pi * a) :=
          mul_le_mul_of_nonneg_right h7 hsq.le
      _ = Real.exp (0.29 * a) * Real.exp 1 * Real.exp (-μ₀) * (Real.sqrt (2 * Real.pi * a) * (a : ℝ) ^ a) := by ring
      _ ≤ Real.exp (0.29 * a) * Real.exp 1 * Real.exp (-μ₀) * (a.factorial * Real.exp a) :=
          mul_le_mul_of_nonneg_left h9 (by positivity)
      _ = _ := by ring
  refine e5.trans ?_
  -- numeric part
  have hE : 0.29 * (a : ℝ) + 1 + a - μ₀ ≤ -0.68 := by
    rw [hμ₀]; linarith
  have hexp : Real.exp (0.29 * a + 1 + a - μ₀) ≤ 0.508 := by
    have h1 : 1.97 ≤ Real.exp 0.68 := by
      have := Real.sum_le_exp_of_nonneg (x := 0.68) (by norm_num) 5
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      linarith
    have h2 : Real.exp (0.29 * a + 1 + a - μ₀) ≤ Real.exp (-0.68) := Real.exp_le_exp.mpr hE
    have h3 : Real.exp (-0.68) = (Real.exp 0.68)⁻¹ := by
      rw [← Real.exp_neg]
    rw [h3] at h2
    have h4 : (Real.exp 0.68)⁻¹ ≤ 1 / 1.97 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) h1
    linarith [show (1 / 1.97 : ℝ) ≤ 0.508 by norm_num]
  have hsq8 : 7.08 ≤ Real.sqrt (2 * Real.pi * a) := by
    apply Real.le_sqrt_of_sq_le
    have := Real.pi_gt_d2
    nlinarith
  rw [div_le_iff₀ hsq]
  nlinarith [Real.exp_pos (0.29 * a + 1 + a - μ₀)]

lemma head_small (a : ℕ) (ha : 8 ≤ a) (μ : ℝ) (hμ : 4 * ((a : ℝ) + 1) / 3 ≤ μ) :
    ∑ i ∈ Finset.range (a + 1), pm μ i ≤ 0.3 := by
  have haR : (8 : ℝ) ≤ a := by exact_mod_cast ha
  have hμ0 : (a : ℝ) < 4 * ((a : ℝ) + 1) / 3 := by linarith
  have hμpos : 0 < μ := by linarith
  have hr : (a : ℝ) < μ := by linarith
  refine (pm_head hμpos a hr).trans ?_
  have h1 : pm μ a ≤ pm (4 * ((a : ℝ) + 1) / 3) a :=
    pm_anti a (by linarith) hμ0.le hμ
  have h2 : pm (4 * ((a : ℝ) + 1) / 3) a ≤ 0.072 := pm_stirling a ha
  have h3 : (1 : ℝ) / 4 ≤ 1 - (a : ℝ) / μ := by
    have : (a : ℝ) / μ ≤ 3 / 4 := by
      rw [div_le_iff₀ hμpos]; linarith
    linarith
  have hpos : 0 < 1 - (a : ℝ) / μ := by linarith
  rw [div_le_iff₀ hpos]
  have := pm_nonneg hμpos.le a
  nlinarith

theorem solution (lam : ℝ) (hlam : 20 ≤ lam) :
    (0.7 : ℝ) ≤ psi (lam / 2 - 1) (2 * lam / 3) := by
  set μ : ℝ := 2 * lam / 3 with hμ
  set j : ℝ := lam / 2 - 1 with hj
  have hj9 : 9 ≤ j := by rw [hj]; linarith
  have hj0 : 0 ≤ j := by linarith
  set k : ℕ := ⌈j⌉₊ with hk
  have hk9 : 9 ≤ k := by
    have : (9 : ℝ) ≤ k := hj9.trans (Nat.le_ceil j)
    exact_mod_cast this
  have hkj : (k : ℝ) < j + 1 := Nat.ceil_lt_add_one hj0
  obtain ⟨a, ha1⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
  have ha8 : 8 ≤ a := by omega
  have hμa : 4 * ((a : ℝ) + 1) / 3 ≤ μ := by
    have : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
    rw [ha1, this] at hkj
    rw [hμ]; rw [hj] at hkj; linarith
  have hsum : HasSum (fun i : ℕ => pm μ i) 1 := by
    have h : HasSum (fun n : ℕ => μ ^ n / (n.factorial : ℝ)) (Real.exp μ) := by
      rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) μ
    have h2 := h.mul_right (Real.exp (-μ))
    have : Real.exp μ * Real.exp (-μ) = 1 := by rw [← Real.exp_add]; simp
    rw [this] at h2
    have e : (fun i : ℕ => pm μ i) = fun i : ℕ => μ ^ i / (i.factorial : ℝ) * Real.exp (-μ) := by
      ext i; unfold pm; ring
    rw [e]; exact h2
  have hfin : HasSum (fun i : ℕ => if i < a + 1 then pm μ i else 0) (∑ i ∈ Finset.range (a + 1), pm μ i) := by
    have hs : ∑ i ∈ Finset.range (a + 1), (if i < a + 1 then pm μ i else 0) =
        ∑ i ∈ Finset.range (a + 1), pm μ i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_range] at hi
      simp [hi]
    rw [← hs]
    exact hasSum_sum_of_ne_finset_zero (f := fun i : ℕ => if i < a + 1 then pm μ i else 0)
      (s := Finset.range (a + 1)) (by
        intro i hi
        simp only [Finset.mem_range] at hi
        simp [hi])
  have hdiff := hsum.sub hfin
  have hpsi : psi j μ = 1 - ∑ i ∈ Finset.range (a + 1), pm μ i := by
    unfold psi
    rw [← hdiff.tsum_eq]
    congr 1
    ext i
    have : (j ≤ (i : ℝ)) ↔ ¬ (i < a + 1) := by
      rw [← Nat.ceil_le, ← hk, ha1]
      omega
    by_cases h : i < a + 1
    · have h' : ¬ j ≤ (i : ℝ) := fun hh => this.mp hh h
      simp [h, h']
    · have h' : j ≤ (i : ℝ) := this.mpr h
      simp [h, h', pm]
  rw [hpsi]
  have := head_small a ha8 μ hμa
  linarith
