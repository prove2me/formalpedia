-- Prove2me | solution 1 for LogBarrierIPM.Curvature.lemma_22
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:46:52.492646+00:00
-- url     : https://prove2.me/submissions/1f595293-4cfa-42fa-8e13-d020ed04bd5d

import Mathlib
import Definitions.Def_LogBarrierIPM_Curvature_Puiseux
import Definitions.Def_LogBarrierIPM_Curvature_TropicalAngle

set_option autoImplicit false

open Filter Topology

namespace LogBarrierIPM.Curvature.L22

open LogBarrierIPM.Curvature

/-- leading-term asymptotics: if every exponent is `≤ m`, `f(t)/t^m → a_m`. -/
theorem tendsto_eval_div (f : Puiseux) (m : ℝ) (hm : ∀ α, f.coeff α ≠ 0 → α ≤ m) :
    Tendsto (fun t : ℝ => f.eval t / t ^ m) atTop (𝓝 (f.coeff m)) := by
  obtain ⟨ρ, hρ, hsum⟩ := f.abs_summable
  set t0 : ℝ := max ρ 1 + 1 with ht0
  have ht0ρ : ρ < t0 := by
    have := le_max_left ρ 1; linarith
  have ht0pos : 0 < t0 := by linarith
  have key : Tendsto (fun t : ℝ => ∑' α : ℝ, f.coeff α * t ^ (α - m)) atTop
      (𝓝 (∑' α : ℝ, if α = m then f.coeff m else 0)) := by
    apply tendsto_tsum_of_dominated_convergence (bound := fun α => |f.coeff α| * t0 ^ α * t0 ^ (-m))
    · exact (hsum t0 ht0ρ).mul_right _
    · intro α
      by_cases hα : α = m
      · subst hα
        simp only [sub_self, Real.rpow_zero, mul_one, if_true]
        exact tendsto_const_nhds
      · rw [if_neg hα]
        by_cases hc : f.coeff α = 0
        · simp only [hc, zero_mul]; exact tendsto_const_nhds
        · have hlt : α < m := lt_of_le_of_ne (hm α hc) hα
          have h1 : Tendsto (fun t : ℝ => t ^ (α - m)) atTop (𝓝 0) := by
            have := tendsto_rpow_neg_atTop (y := m - α) (by linarith)
            simpa [neg_sub] using this
          simpa using h1.const_mul (f.coeff α)
    · filter_upwards [eventually_ge_atTop t0] with t ht α
      have htpos : 0 < t := lt_of_lt_of_le ht0pos ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos htpos _)]
      by_cases hc : f.coeff α = 0
      · simp only [hc, abs_zero, zero_mul]; positivity
      · have hle : α - m ≤ 0 := by linarith [hm α hc]
        have : t ^ (α - m) ≤ t0 ^ (α - m) :=
          Real.rpow_le_rpow_of_nonpos ht0pos ht hle
        rw [mul_assoc, ← Real.rpow_add ht0pos, ← sub_eq_add_neg]
        exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  rw [tsum_ite_eq] at key
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  unfold Puiseux.eval
  rw [← tsum_div_const]
  congr 1
  funext α
  rw [Real.rpow_sub ht, mul_div_assoc]

theorem isGreatest_support (f : Puiseux) (h : (Function.support f.coeff).Nonempty) :
    ∃ M, IsGreatest (Function.support f.coeff) M := by
  obtain ⟨α0, hα0⟩ := h
  have hfin := f.support_finite_above α0
  have hne : hfin.toFinset.Nonempty := ⟨α0, (Set.Finite.mem_toFinset _).mpr ⟨le_refl α0, hα0⟩⟩
  refine ⟨hfin.toFinset.max' hne, ?_, ?_⟩
  · have := hfin.toFinset.max'_mem hne
    rw [Set.Finite.mem_toFinset] at this
    exact this.2
  · intro α hα
    by_cases hle : α0 ≤ α
    · exact hfin.toFinset.le_max' α ((Set.Finite.mem_toFinset _).mpr ⟨hle, hα⟩)
    · have := hfin.toFinset.le_max' α0 ((Set.Finite.mem_toFinset _).mpr ⟨le_refl α0, hα0⟩)
      linarith [not_le.mp hle]

theorem le_of_val_le (f : Puiseux) (m : ℝ) (h : f.val ≤ (m : WithBot ℝ)) :
    ∀ α, f.coeff α ≠ 0 → α ≤ m := by
  intro α hα
  have hne : (Function.support f.coeff).Nonempty := ⟨α, hα⟩
  obtain ⟨M, hM⟩ := isGreatest_support f hne
  have hv : f.val = (M : WithBot ℝ) := by
    unfold Puiseux.val
    rw [if_pos hne, hM.csSup_eq]
  rw [hv, WithBot.coe_le_coe] at h
  exact le_trans (hM.2 hα) h

theorem coeff_ne_zero_of_val_eq (f : Puiseux) (m : ℝ) (h : f.val = (m : WithBot ℝ)) :
    f.coeff m ≠ 0 := by
  by_cases hne : (Function.support f.coeff).Nonempty
  · obtain ⟨M, hM⟩ := isGreatest_support f hne
    have hv : f.val = (M : WithBot ℝ) := by
      unfold Puiseux.val
      rw [if_pos hne, hM.csSup_eq]
    rw [hv, WithBot.coe_inj] at h
    subst h
    exact hM.1
  · exfalso
    unfold Puiseux.val at h
    rw [if_neg hne] at h
    exact WithBot.bot_ne_coe h

theorem val_ge_of_coeff_ne_zero (f : Puiseux) (m : ℝ) (h : f.coeff m ≠ 0) :
    (m : WithBot ℝ) ≤ f.val := by
  have hne : (Function.support f.coeff).Nonempty := ⟨m, h⟩
  obtain ⟨M, hM⟩ := isGreatest_support f hne
  have hv : f.val = (M : WithBot ℝ) := by
    unfold Puiseux.val
    rw [if_pos hne, hM.csSup_eq]
  rw [hv, WithBot.coe_le_coe]
  exact hM.2 h

/-- the normalized vector converges to the leading-coefficient vector `X ≠ 0`. -/
theorem lead_vec {d : ℕ} (x : Fin d → Puiseux) (hx : IsNonNull x) :
    ∃ mx : ℝ, tmax (valVec x) = (mx : WithBot ℝ) ∧
      (fun i => (x i).coeff mx) ≠ 0 ∧
      (∀ i, (x i).coeff mx ≠ 0 → i ∈ targmax (valVec x)) ∧
      Tendsto (fun t : ℝ => (t ^ mx)⁻¹ • evalVec x t) atTop
        (𝓝 (WithLp.toLp 2 (fun i => (x i).coeff mx))) := by
  obtain ⟨i0, α0, hα0⟩ := hx
  have hle : ∀ i, valVec x i ≤ tmax (valVec x) := fun i =>
    Finset.le_sup (f := valVec x) (Finset.mem_univ i)
  have hne : tmax (valVec x) ≠ ⊥ := by
    intro hb
    have h1 := hle i0
    rw [hb, le_bot_iff] at h1
    have := val_ge_of_coeff_ne_zero (x i0) α0 hα0
    rw [show valVec x i0 = (x i0).val from rfl] at h1
    rw [h1] at this
    exact absurd this (by simp)
  obtain ⟨mx, hmx⟩ := WithBot.ne_bot_iff_exists.mp hne
  refine ⟨mx, hmx.symm, ?_, ?_, ?_⟩
  · have hu : (Finset.univ : Finset (Fin d)).Nonempty := ⟨i0, Finset.mem_univ _⟩
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup _ hu (valVec x)
    intro h0
    have hc := coeff_ne_zero_of_val_eq (x j) mx (by
      change valVec x j = _
      rw [← hj]; exact hmx.symm)
    exact hc (congrFun h0 j)
  · intro i hi
    show valVec x i = tmax (valVec x)
    apply le_antisymm (hle i)
    rw [← hmx]
    exact val_ge_of_coeff_ne_zero (x i) mx hi
  · have hcomp : ∀ i, Tendsto (fun t : ℝ => (x i).eval t / t ^ mx) atTop (𝓝 ((x i).coeff mx)) :=
      fun i => tendsto_eval_div (x i) mx (le_of_val_le (x i) mx (by rw [hmx]; exact hle i))
    have hT : Tendsto (fun t : ℝ => WithLp.toLp 2 (fun i => (x i).eval t / t ^ mx)) atTop
        (𝓝 (WithLp.toLp 2 (fun i => (x i).coeff mx))) :=
      ((PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).tendsto _).comp (tendsto_pi_nhds.mpr hcomp)
    refine hT.congr' (Eventually.of_forall fun t => ?_)
    ext i
    simp [evalVec, div_eq_inv_mul]

end LogBarrierIPM.Curvature.L22

open LogBarrierIPM.Curvature Filter Topology in
theorem solution {d : ℕ} (x y : Fin d → Puiseux) (hx : IsNonNull x) (hy : IsNonNull y) :
    (∃ L : ℝ, Tendsto (fun t : ℝ => InnerProductGeometry.angle (evalVec x t) (evalVec y t))
        atTop (𝓝 L)) ∧
    (Disjoint (targmax (valVec x)) (targmax (valVec y)) →
      Tendsto (fun t : ℝ => InnerProductGeometry.angle (evalVec x t) (evalVec y t))
        atTop (𝓝 (Real.pi / 2))) := by
  obtain ⟨mx, -, hX0, hXarg, hXt⟩ := LogBarrierIPM.Curvature.L22.lead_vec x hx
  obtain ⟨my, -, hY0, hYarg, hYt⟩ := LogBarrierIPM.Curvature.L22.lead_vec y hy
  set X : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i => (x i).coeff mx) with hXdef
  set Y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i => (y i).coeff my) with hYdef
  have hXne : X ≠ 0 := by
    intro h; apply hX0; funext i
    have := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v i) h
    simpa [hXdef] using this
  have hYne : Y ≠ 0 := by
    intro h; apply hY0; funext i
    have := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v i) h
    simpa [hYdef] using this
  have hlim : Tendsto (fun t : ℝ => InnerProductGeometry.angle (evalVec x t) (evalVec y t))
      atTop (𝓝 (InnerProductGeometry.angle X Y)) := by
    have hc := (InnerProductGeometry.continuousAt_angle (x := (X, Y)) hXne hYne).tendsto.comp
      (hXt.prodMk_nhds hYt)
    refine hc.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Function.comp_apply]
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (inv_pos.mpr (Real.rpow_pos_of_pos ht _)),
      InnerProductGeometry.angle_smul_right_of_pos _ _ (inv_pos.mpr (Real.rpow_pos_of_pos ht _))]
  refine ⟨⟨_, hlim⟩, fun hdisj => ?_⟩
  have hinner : inner ℝ X Y = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hxi : (x i).coeff mx = 0
    · simp [hXdef, hxi]
    · by_cases hyi : (y i).coeff my = 0
      · simp [hYdef, hyi]
      · exact absurd (Set.disjoint_left.mp hdisj (hXarg i hxi)) (not_not.mpr (hYarg i hyi))
  rw [InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two] at hinner
  rw [← hinner]
  exact hlim
