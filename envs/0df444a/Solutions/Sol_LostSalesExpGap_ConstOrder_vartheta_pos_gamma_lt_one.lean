-- Prove2me | solution 1 for LostSalesExpGap.ConstOrder.vartheta_pos_gamma_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:11:59.899988+00:00
-- url     : https://prove2.me/submissions/66afe61f-6c31-49e6-8362-e95c8d1b703d

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder
import Theorems.Thm_LostSalesExpGap_ConstOrder_best_constant_exists

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open LostSalesExpGap.ConstOrder Filter Topology in
theorem solution (P : CappedBaseStock.DemandLaw)
    (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    0 ≤ gamma P c ∧ gamma P c < 1 ∧
      ((phiMinimizers P c).Nonempty → BddAbove (phiMinimizers P c) →
        0 < sSup (phiMinimizers P c)) := by
  obtain ⟨hne, -, hrmem, hrlt⟩ := best_constant_exists P c hP
  set r := rInf P c with hr
  set mean := CappedBaseStock.mean P
  have hr0 : 0 ≤ r := hrmem.1.1
  have hphi0 : ∀ θ : ℝ, 0 ≤ phi P c θ := fun θ =>
    mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)
  have hbdd : BddBelow (Set.range fun θ : Set.Ici (0 : ℝ) => phi P c θ) :=
    ⟨0, by rintro _ ⟨θ, rfl⟩; exact hphi0 θ⟩
  have hγ0 : 0 ≤ gamma P c := le_ciInf fun θ => hphi0 θ
  have hphi_zero : phi P c 0 = 1 := by
    simp [phi]
  -- truncated mean exceeds r
  have htrunc : ∃ M : ℝ, 0 < M ∧ r < ∫ d : ℝ≥0, min (d : ℝ) M ∂P.law := by
    have hlim : Tendsto (fun n : ℕ => ∫ d : ℝ≥0, min (d : ℝ) ((n : ℝ) + 1) ∂P.law) atTop
        (𝓝 (∫ d : ℝ≥0, (d : ℝ) ∂P.law)) := by
      refine tendsto_integral_of_dominated_convergence (fun d : ℝ≥0 => (d : ℝ))
        (fun n => (Measurable.aestronglyMeasurable (by fun_prop))) P.finiteMean
        (fun n => ae_of_all _ fun d => ?_) (ae_of_all _ fun d => ?_)
      · rw [Real.norm_eq_abs, abs_of_nonneg (le_min (NNReal.coe_nonneg d) (by positivity))]
        exact min_le_left _ _
      · apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop (⌈(d : ℝ)⌉₊)] with n hn
        have : (d : ℝ) ≤ (n : ℝ) + 1 := by
          have := Nat.le_ceil (d : ℝ)
          have : (⌈(d : ℝ)⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        exact (min_eq_left this).symm
    have hev := hlim.eventually (lt_mem_nhds (show r < ∫ d : ℝ≥0, (d : ℝ) ∂P.law from hrlt))
    obtain ⟨n, hn⟩ := hev.exists
    exact ⟨(n : ℝ) + 1, by positivity, hn⟩
  obtain ⟨M, hM, hb⟩ := htrunc
  set b := ∫ d : ℝ≥0, min (d : ℝ) M ∂P.law with hbdef
  have hbpos : 0 < b := lt_of_le_of_lt hr0 hb
  set θ := (b - r) / (2 * M * b) with hθ
  have hθpos : 0 < θ := by
    apply div_pos (by linarith); positivity
  have hθM : θ * M ≤ 1 := by
    rw [hθ, div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith
  -- pointwise bound
  have hpt : ∀ d : ℝ≥0, Real.exp (-θ * (d : ℝ)) ≤
      1 - θ * min (d : ℝ) M + θ ^ 2 * M * min (d : ℝ) M := by
    intro d
    set y := θ * min (d : ℝ) M
    have hy0 : 0 ≤ y := mul_nonneg hθpos.le (le_min (NNReal.coe_nonneg d) hM.le)
    have hyM : y ≤ θ * M := mul_le_mul_of_nonneg_left (min_le_right _ _) hθpos.le
    have hy1 : y ≤ 1 := hyM.trans hθM
    have h1 : Real.exp (-θ * (d : ℝ)) ≤ Real.exp (-y) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left (min_le_left (d : ℝ) M) hθpos.le
      simp only [y]; linarith
    have h2 := Real.abs_exp_sub_one_sub_id_le (x := -y) (by rw [abs_neg, abs_of_nonneg hy0]; exact hy1)
    have h3 : Real.exp (-y) ≤ 1 - y + y ^ 2 := by
      have := (abs_le.mp h2).2; rw [neg_sq] at this; linarith
    have h4 : y ^ 2 ≤ θ ^ 2 * M * min (d : ℝ) M := by
      have : y ^ 2 = y * y := sq y
      calc y ^ 2 = y * y := sq y
        _ ≤ (θ * M) * y := mul_le_mul_of_nonneg_right hyM hy0
        _ = θ ^ 2 * M * min (d : ℝ) M := by simp only [y]; ring
    linarith
  have hmin_int : Integrable (fun d : ℝ≥0 => min (d : ℝ) M) P.law := by
    refine Integrable.of_bound (C := M) (Measurable.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (NNReal.coe_nonneg d) hM.le)]; exact min_le_right _ _
  have hE : ∫ d : ℝ≥0, Real.exp (-θ * (d : ℝ)) ∂P.law ≤ 1 - θ * b + θ ^ 2 * M * b := by
    have hexp_int : Integrable (fun d : ℝ≥0 => Real.exp (-θ * (d : ℝ))) P.law := by
      refine Integrable.of_bound (C := 1) (Measurable.aestronglyMeasurable (by fun_prop))
        (ae_of_all _ fun d => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      nlinarith [NNReal.coe_nonneg d]
    have hA : Integrable (fun d : ℝ≥0 => 1 - θ * min (d : ℝ) M) P.law :=
      (integrable_const 1).sub (hmin_int.const_mul θ)
    have hB : Integrable (fun d : ℝ≥0 => θ ^ 2 * M * min (d : ℝ) M) P.law :=
      hmin_int.const_mul _
    refine (integral_mono hexp_int (hA.add hB) hpt).trans (le_of_eq ?_)
    simp only [Pi.add_apply]
    rw [integral_add (f := fun d : ℝ≥0 => 1 - θ * min (d : ℝ) M)
      (g := fun d : ℝ≥0 => θ ^ 2 * M * min (d : ℝ) M) hA hB,
      integral_sub (f := fun _ : ℝ≥0 => (1 : ℝ)) (g := fun d : ℝ≥0 => θ * min (d : ℝ) M)
        (integrable_const 1) (hmin_int.const_mul θ), integral_const_mul,
      integral_const_mul]
    simp [hbdef]
  have hEr : ∫ d : ℝ≥0, Real.exp (-θ * (d : ℝ)) ∂P.law < 1 - θ * r := by
    have : θ * M * b < b - r := by
      rw [hθ]; field_simp; nlinarith
    nlinarith
  have hphiθ : phi P c θ < 1 := by
    simp only [phi]
    have hexp : Real.exp (θ * r) * (1 - θ * r) ≤ 1 := by
      have := Real.add_one_le_exp (-(θ * r))
      calc Real.exp (θ * r) * (1 - θ * r) ≤ Real.exp (θ * r) * Real.exp (-(θ * r)) :=
            mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp (θ * r) * ∫ d : ℝ≥0, Real.exp (-θ * (d : ℝ)) ∂P.law
        < Real.exp (θ * r) * (1 - θ * r) := mul_lt_mul_of_pos_left hEr (Real.exp_pos _)
      _ ≤ 1 := hexp
  have hγ1 : gamma P c < 1 :=
    lt_of_le_of_lt (ciInf_le hbdd ⟨θ, hθpos.le⟩) hphiθ
  refine ⟨hγ0, hγ1, fun hne' hbdd' => ?_⟩
  obtain ⟨θ0, hθ0⟩ := hne'
  by_contra hcon
  push_neg at hcon
  have h0 : θ0 = 0 := le_antisymm ((le_csSup hbdd' hθ0).trans hcon) hθ0.1
  have := hθ0.2
  rw [h0, hphi_zero] at this
  linarith
