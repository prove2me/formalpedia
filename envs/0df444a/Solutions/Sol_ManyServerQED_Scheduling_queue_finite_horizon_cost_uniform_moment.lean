-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_finite_horizon_cost_uniform_moment
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:47:08.868944+00:00
-- url     : https://prove2.me/submissions/cd2472ee-cf35-486b-9614-1801d7d1bd98

import Theorems.Thm_ManyServerQED_Scheduling_queue_state_sup_polynomial_moment

open MeasureTheory ProbabilityTheory Filter Topology Set
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy
open scoped ENNReal NNReal

set_option maxHeartbeats 1100000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU) (hγ : 0 < γ)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hPol : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
      IsWorkConserving n (X n) (Ψ n)) :
    ∃ p : ℝ, 1 < p ∧ ∀ T : ℝ, 0 ≤ T → ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ᶠ n in atTop,
      (∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) T,
        ENNReal.ofReal (Real.exp (-γ*t) * costOfTilde Lt (M.Xhat n (X n) ω t)
          (uProc n u0 (X n) (Ψ n) ω t)) ∂volume)^p ∂M.P) ≤ K := by
  let : IsProbabilityMeasure M.P := M.isProb
  let p := 1 + (mU-mL)/(mL+1)
  have hl := hA2.cost.mL_nonneg
  have hg : 0 < mU-mL := sub_pos.mpr hA3.2.1
  have hp : 1 < p := by dsimp [p]; linarith [div_pos hg (by linarith : 0 < mL+1)]
  have hpM : mL*p ≤ mU := by
    dsimp [p]
    have he : mL+1 ≠ 0 := by linarith
    have hh : mL * ((mU-mL)/(mL+1)) ≤ mU-mL := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by linarith : 0 < mL+1)).2
      nlinarith
    nlinarith
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨a,ha,hA⟩ := hA2.cost.growth
  obtain ⟨c,m,hMom⟩ := queue_state_sup_polynomial_moment M mL mU hA3
  obtain ⟨N,hN⟩ := hMom x X0 hX0 X Ψ hPol
  refine ⟨p,hp,fun T hT => ?_⟩
  let A : ℝ≥0∞ := ENNReal.ofReal (a*T)^p * (2:ℝ≥0∞)^p
  let B : ℝ≥0∞ := ENNReal.ofReal (c * (1+l1norm x^m) * (1+T^m))
  have ha0 : A ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0 ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg hp0 (by norm_num))
  refine ⟨A*(2+B),ENNReal.mul_lt_top ha0.lt_top
    (ENNReal.add_lt_top.2 ⟨by norm_num,ENNReal.ofReal_lt_top⟩),?_⟩
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hn1 := (le_max_right N 1).trans hn
  have hC := (hPol n hn1).1.controlled
  have hW := (hPol n hn1).2.2
  have hU (ω : Ω) (t : ℝ) (ht : 0 ≤ t) :
      uProc n u0 (X n) (Ψ n) ω t ∈ stdSimplex ℝ (Fin k) := by
    unfold uProc
    split_ifs with hh
    · refine ⟨fun i => div_nonneg (hC.phi_nonneg ω t i ht) hh.le,?_⟩
      rw [← Finset.sum_div, ← hW ω t ht, max_eq_left hh.le, div_self hh.ne']
    · exact hu0
  let S (ω : Ω) := supDist (M.Xhat n (X n) ω) (fun _ => 0) T
  let g (ω : Ω) (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-γ*t) *
    costOfTilde Lt (M.Xhat n (X n) ω t) (uProc n u0 (X n) (Ψ n) ω t))
  have hpoint (ω : Ω) (t : ℝ) (ht : t ∈ Ioc (0:ℝ) T) :
      g ω t ≤ ENNReal.ofReal a * (1 + S ω^mL) := by
    have hl1 : 0 ≤ l1norm (M.Xhat n (X n) ω t) := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hsup : ENNReal.ofReal (l1norm (M.Xhat n (X n) ω t)) ≤ S ω := by
      apply le_iSup₂_of_le t (show t ∈ Icc 0 T from ⟨ht.1.le,ht.2⟩)
      simp only [Pi.zero_apply,sub_zero,l1norm]
      exact le_rfl
    have hcost := hA _ (hU ω t ht.1.le) (M.Xhat n (X n) ω t)
    have hnon := hA2.cost.nonneg (M.Xhat n (X n) ω t) _ (hU ω t ht.1.le)
    have hE : Real.exp (-γ*t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hγ.le ht.1.le])
    have hCst : g ω t ≤ ENNReal.ofReal (a*(1+l1norm (M.Xhat n (X n) ω t)^mL)) :=
      ENNReal.ofReal_le_ofReal ((mul_le_of_le_one_left hnon hE).trans hcost)
    refine hCst.trans ?_
    rw [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_add zero_le_one (Real.rpow_nonneg hl1 _),
      ENNReal.ofReal_one, ← ENNReal.ofReal_rpow_of_nonneg hl1 hl]
    exact mul_le_mul_right (add_le_add_right (ENNReal.rpow_le_rpow hsup hl) _) _
  have hbound (ω : Ω) :
      (∫⁻ t in Ioc (0:ℝ) T, g ω t ∂volume)^p ≤ A*(2+(S ω)^mU) := by
    have ht : (∫⁻ t in Ioc (0:ℝ) T, g ω t ∂volume) ≤ ENNReal.ofReal (a*T) * (1 + S ω^mL) := by
      apply (setLIntegral_mono' measurableSet_Ioc (hpoint ω)).trans_eq
      rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_mul ha.le]
      ac_rfl
    refine (ENNReal.rpow_le_rpow ht hp0).trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0]
    refine (mul_le_mul_right (ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow 1 (S ω^mL) hp0) _).trans ?_
    rw [ENNReal.one_rpow, ← ENNReal.rpow_mul, ← mul_assoc]
    apply mul_le_mul_right
    have hb : S ω ^ (mL*p) ≤ 1 + S ω^mU := by
      rcases le_total (S ω) 1 with h | h
      · exact ((ENNReal.rpow_le_rpow h (mul_nonneg hl hp0)).trans_eq (ENNReal.one_rpow _)).trans le_self_add
      · exact (ENNReal.rpow_le_rpow_of_exponent_le h hpM).trans (le_add_left (le_refl _))
    have he : (2:ℝ≥0∞) = 1+1 := by norm_num
    rw [he,add_assoc]
    exact add_le_add_right hb _
  change (∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) T, g ω t ∂volume)^p ∂M.P) ≤ _
  refine (lintegral_mono hbound).trans ?_
  rw [lintegral_const_mul' _ _ ha0, lintegral_add_left measurable_const, lintegral_const,
    measure_univ, mul_one]
  exact mul_le_mul_right (add_le_add_right (hN n ((le_max_left N 1).trans hn) T hT) _) _
