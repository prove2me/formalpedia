-- Prove2me | solution 1 for MDPFinance.JumpMarkets.proposition_9_3_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T03:20:26.298037+00:00
-- url     : https://prove2.me/submissions/c05294a1-c8ab-43c5-8b54-5e1a08475cb6

import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_JumpMarket

open MeasureTheory
open scoped ENNReal

namespace MDPFinance.JumpMarkets

variable {d : ℕ}

lemma p932_mu_le (M : JumpMarket d) (i : Fin d) : M.mu i ≤ M.mubar :=
  le_max_of_le_right (le_ciSup (Set.finite_range _).bddAbove i)

lemma p932_rho_le (M : JumpMarket d) : M.rho ≤ M.mubar := le_max_left _ _

lemma p932_mubar_nonneg (M : JumpMarket d) : 0 ≤ M.mubar := M.rho_nonneg.trans (p932_rho_le M)

lemma p932_ybar_nonneg (M : JumpMarket d) : 0 ≤ M.ybar := le_max_left _ _

lemma p932_m_le (M : JumpMarket d) (i : Fin d) : ∫ y, y i ∂M.QY ≤ M.ybar :=
  le_max_of_le_right (le_ciSup (f := fun i => ∫ y, y i ∂M.QY) (Set.finite_range _).bddAbove i)

lemma p932_rate_le (M : JumpMarket d) (u : Fin d → ℝ) (hu : u ∈ Ucal d) :
    M.rho + ∑ i, u i * (M.mu i - M.rho) ≤ M.mubar := by
  obtain ⟨h0, h1⟩ := hu
  have : ∑ i, u i * (M.mu i - M.rho) ≤ ∑ i, u i * (M.mubar - M.rho) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by linarith [p932_mu_le M i]) (h0 i)
  rw [← Finset.sum_mul] at this
  have h2 : (∑ i, u i) * (M.mubar - M.rho) ≤ 1 * (M.mubar - M.rho) :=
    mul_le_mul_of_nonneg_right h1 (by linarith [p932_rho_le M])
  linarith

lemma p932_phi_le (M : JumpMarket d) (a : Control d) {s x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) :
    M.phi a s x ≤ x * Real.exp (M.mubar * s) := by
  unfold JumpMarket.phi
  apply mul_le_mul_of_nonneg_left _ hx
  apply Real.exp_le_exp.mpr
  by_cases hi : IntegrableOn (fun s => M.rho + ∑ i, a.val s i * (M.mu i - M.rho)) (Set.Ioc 0 s)
  · calc ∫ s in Set.Ioc (0 : ℝ) s, (M.rho + ∑ i, a.val s i * (M.mu i - M.rho))
          ≤ ∫ s in Set.Ioc (0 : ℝ) s, M.mubar :=
            setIntegral_mono_on hi (integrableOn_const (by simp)) measurableSet_Ioc
              (fun r _ => p932_rate_le M _ (a.mem r))
      _ = M.mubar * s := by
            rw [setIntegral_const]; simp [hs, smul_eq_mul]; ring
  · rw [integral_undef hi]; exact mul_nonneg (p932_mubar_nonneg M) hs

lemma p932_phi_nonneg (M : JumpMarket d) (a : Control d) (s : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ M.phi a s x := mul_nonneg hx (Real.exp_pos _).le

lemma p932_U_le (M : JumpMarket d) {z : ℝ} (hz : 0 ≤ z) : M.U z ≤ M.U 1 * (1 + z) := by
  have hU0 := M.U_nonneg 0 le_rfl
  have hU1 := M.U_nonneg 1 zero_le_one
  rcases le_or_gt z 1 with h | h
  · have := M.U_mono.monotoneOn (Set.mem_Ici.mpr hz) (Set.mem_Ici.mpr zero_le_one) h
    nlinarith
  · have hz0' : (0:ℝ) < z := by linarith
    have hc := (M.U_concave.concaveOn).2 (Set.mem_Ici.mpr (le_refl (0:ℝ))) (Set.mem_Ici.mpr hz)
      (show (0:ℝ) ≤ 1 - 1/z by rw [sub_nonneg, div_le_one hz0']; linarith)
      (show (0:ℝ) ≤ 1/z by positivity) (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add] at hc
    rw [one_div_mul_cancel (by linarith)] at hc
    have hz0 : 0 < z := by linarith
    have : M.U z ≤ z * M.U 1 := by
      have h2 : 1 / z * M.U z ≤ M.U 1 := by nlinarith [hc, mul_nonneg (sub_nonneg.mpr (show 1/z ≤ 1 by rw [div_le_one hz0]; linarith)) hU0]
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hz0] at h2; linarith
    nlinarith


lemma p932_r_bound (M : JumpMarket d) {gamma : ℝ} (hg : 0 ≤ gamma) :
    ∃ cr : ℝ, ∀ p ∈ M.E, ∀ a : Control d, |M.r a p| ≤ cr * M.bfun gamma p := by
  refine ⟨M.U 1 * Real.exp (M.mubar * M.T), fun p hp a => ?_⟩
  obtain ⟨⟨ht0, htT⟩, hx⟩ := hp
  have hx : 0 ≤ p.2 := hx
  set τ := M.T - p.1 with hτ
  have hτ0 : 0 ≤ τ := by linarith
  have hφ0 := p932_phi_nonneg M a τ hx
  have hφ := p932_phi_le M a hτ0 hx
  have hU0 := M.U_nonneg _ hφ0
  have hUle := p932_U_le M hφ0
  have hU1 := M.U_nonneg 1 zero_le_one
  have e1 : Real.exp (-M.lam * τ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [M.lam_pos])
  have e2 : Real.exp (M.mubar * τ) ≤ Real.exp (M.mubar * M.T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) (p932_mubar_nonneg M))
  have e3 : 1 ≤ Real.exp (M.mubar * M.T) :=
    Real.one_le_exp (mul_nonneg (p932_mubar_nonneg M) M.T_pos.le)
  have e4 : 1 ≤ Real.exp (gamma * τ) := Real.one_le_exp (mul_nonneg hg hτ0)
  unfold JumpMarket.r JumpMarket.bfun
  rw [← hτ, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hU0)]
  have h1 : M.U (M.phi a τ p.2) ≤ M.U 1 * Real.exp (M.mubar * M.T) * (1 + p.2) := by
    calc M.U (M.phi a τ p.2) ≤ M.U 1 * (1 + p.2 * Real.exp (M.mubar * τ)) :=
          hUle.trans (mul_le_mul_of_nonneg_left (by linarith) hU1)
      _ ≤ M.U 1 * (Real.exp (M.mubar * M.T) * (1 + p.2)) := by
          apply mul_le_mul_of_nonneg_left _ hU1
          nlinarith [mul_le_mul_of_nonneg_left e2 hx]
      _ = _ := by ring
  have hK : 0 ≤ M.U 1 * Real.exp (M.mubar * M.T) * (1 + p.2) := by positivity
  calc Real.exp (-M.lam * τ) * M.U (M.phi a τ p.2) ≤ 1 * (M.U 1 * Real.exp (M.mubar * M.T) * (1 + p.2)) :=
        mul_le_mul e1 h1 hU0 zero_le_one
    _ ≤ Real.exp (gamma * τ) * (M.U 1 * Real.exp (M.mubar * M.T) * (1 + p.2)) :=
        mul_le_mul_of_nonneg_right e4 hK
    _ = _ := by ring

lemma p932_Y_int (M : JumpMarket d) (i : Fin d) : Integrable (fun y : Fin d → ℝ => y i) M.QY := by
  have hY : Integrable (fun y : Fin d → ℝ => y) M.QY := ⟨aestronglyMeasurable_id, M.QY_integrable⟩
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).integrable_comp hY

lemma p932_Y_ae (M : JumpMarket d) : ∀ᵐ y ∂M.QY, ∀ i, -1 < y i := by
  have := measure_eq_zero_iff_ae_notMem.mp M.QY_supp
  filter_upwards [this] with y hy
  intro i
  by_contra h
  exact hy ⟨i, not_lt.mp h⟩


lemma p932_inner (M : JumpMarket d) (gamma : ℝ) (a : Control d) (p : ℝ × ℝ) (hx : 0 ≤ p.2)
    (s : ℝ) (hs : 0 < s) :
    ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) *
      ∫⁻ y, ENNReal.ofReal (M.bfun gamma (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i))) ∂M.QY
      ≤ ENNReal.ofReal (M.lam * (1 + M.ybar) * (Real.exp (gamma * (M.T - p.1)) * (1 + p.2)) *
          Real.exp (-(gamma + M.lam - M.mubar) * s)) := by
  have := M.QY_prob
  set φ := M.phi a s p.2 with hφdef
  set e := Real.exp (gamma * (M.T - (p.1 + s))) with he
  have hφ0 : 0 ≤ φ := p932_phi_nonneg M a s hx
  have hφ : φ ≤ p.2 * Real.exp (M.mubar * s) := p932_phi_le M a hs.le hx
  have he0 : 0 < e := Real.exp_pos _
  have hsum : ∀ y : Fin d → ℝ, ∑ i, (e * φ * a.val s i) * y i = e * φ * ∑ i, a.val s i * y i := by
    intro y; rw [Finset.mul_sum]; congr 1; funext i; ring
  have hfun : (fun y : Fin d → ℝ =>
      ENNReal.ofReal (M.bfun gamma (p.1 + s, φ * (1 + ∑ i, a.val s i * y i)))) =
      fun y => ENNReal.ofReal (e * (1 + φ) + ∑ i, (e * φ * a.val s i) * y i) := by
    funext y; congr 1
    show e * (1 + φ * (1 + ∑ i, a.val s i * y i)) = _
    rw [hsum]; ring
  rw [hfun]
  have hint : Integrable (fun y : Fin d → ℝ => e * (1 + φ) + ∑ i, (e * φ * a.val s i) * y i) M.QY :=
    (integrable_const _).add (integrable_finsetSum _ fun i _ => (p932_Y_int M i).const_mul _)
  have hnn : 0 ≤ᵐ[M.QY] fun y : Fin d → ℝ => e * (1 + φ) + ∑ i, (e * φ * a.val s i) * y i := by
    filter_upwards [p932_Y_ae M] with y hy
    have h1 : ∀ i, -(a.val s i) ≤ a.val s i * y i := fun i => by
      nlinarith [(a.mem s).1 i, hy i]
    have h2 : -(∑ i, a.val s i) ≤ ∑ i, a.val s i * y i := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_le_sum fun i _ => h1 i
    have h3 := (a.mem s).2
    show 0 ≤ e * (1 + φ) + ∑ i, (e * φ * a.val s i) * y i
    rw [hsum]
    have hep : 0 ≤ e * φ := mul_nonneg he0.le hφ0
    nlinarith [mul_le_mul_of_nonneg_left h2 hep]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  have hI : ∫ y, (e * (1 + φ) + ∑ i, (e * φ * a.val s i) * y i) ∂M.QY =
      e * (1 + φ) + e * φ * ∑ i, a.val s i * ∫ y, y i ∂M.QY := by
    rw [integral_add (integrable_const _) (integrable_finsetSum _ fun i _ => (p932_Y_int M i).const_mul _),
      integral_const, integral_finsetSum _ fun i _ => (p932_Y_int M i).const_mul _]
    simp only [integral_const_mul, probReal_univ, smul_eq_mul, one_mul, Finset.mul_sum]
    congr 1; refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [hI]
  have hm : ∑ i, a.val s i * ∫ y, y i ∂M.QY ≤ M.ybar := by
    calc ∑ i, a.val s i * ∫ y, y i ∂M.QY ≤ ∑ i, a.val s i * M.ybar :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (p932_m_le M i) ((a.mem s).1 i)
      _ = (∑ i, a.val s i) * M.ybar := by rw [Finset.sum_mul]
      _ ≤ 1 * M.ybar := mul_le_mul_of_nonneg_right (a.mem s).2 (p932_ybar_nonneg M)
      _ = M.ybar := one_mul _
  have hl : 0 ≤ M.lam * Real.exp (-M.lam * s) := mul_nonneg M.lam_pos.le (Real.exp_pos _).le
  rw [← ENNReal.ofReal_mul hl]
  apply ENNReal.ofReal_le_ofReal
  have hy0 := p932_ybar_nonneg M
  have hmu : 1 ≤ Real.exp (M.mubar * s) := Real.one_le_exp (mul_nonneg (p932_mubar_nonneg M) hs.le)
  have key : e * (1 + φ) + e * φ * ∑ i, a.val s i * ∫ y, y i ∂M.QY ≤
      e * ((1 + M.ybar) * (1 + p.2) * Real.exp (M.mubar * s)) := by
    have : φ * (1 + ∑ i, a.val s i * ∫ y, y i ∂M.QY) ≤ p.2 * Real.exp (M.mubar * s) * (1 + M.ybar) :=
      calc _ ≤ φ * (1 + M.ybar) := mul_le_mul_of_nonneg_left (by linarith) hφ0
        _ ≤ _ := mul_le_mul_of_nonneg_right hφ (by linarith)
    have h2 : 1 + p.2 * Real.exp (M.mubar * s) * (1 + M.ybar) ≤
        (1 + M.ybar) * (1 + p.2) * Real.exp (M.mubar * s) := by
      nlinarith [mul_nonneg hx hy0, mul_nonneg (mul_nonneg hx hy0) (sub_nonneg.mpr hmu)]
    have : e * (1 + φ) + e * φ * ∑ i, a.val s i * ∫ y, y i ∂M.QY =
        e * (1 + φ * (1 + ∑ i, a.val s i * ∫ y, y i ∂M.QY)) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ he0.le
    linarith
  have hexp : Real.exp (-M.lam * s) * e * Real.exp (M.mubar * s) =
      Real.exp (gamma * (M.T - p.1)) * Real.exp (-(gamma + M.lam - M.mubar) * s) := by
    rw [he, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc M.lam * Real.exp (-M.lam * s) * (e * (1 + φ) + e * φ * ∑ i, a.val s i * ∫ y, y i ∂M.QY)
      ≤ M.lam * Real.exp (-M.lam * s) * (e * ((1 + M.ybar) * (1 + p.2) * Real.exp (M.mubar * s))) :=
        mul_le_mul_of_nonneg_left key hl
    _ = M.lam * (1 + M.ybar) * (1 + p.2) * (Real.exp (-M.lam * s) * e * Real.exp (M.mubar * s)) := by ring
    _ = _ := by rw [hexp]; ring


lemma p932_Q_bound (M : JumpMarket d) (gamma : ℝ) (p : ℝ × ℝ) (hp : p ∈ M.E) (a : Control d) :
    ∫⁻ q, ENNReal.ofReal (M.bfun gamma q) ∂(M.Q a p) ≤
      ENNReal.ofReal (M.lam * (1 + M.ybar) *
        (∫ s in Set.Ioo (0 : ℝ) M.T, Real.exp (-(gamma + M.lam - M.mubar) * s)) * M.bfun gamma p) := by
  obtain ⟨⟨ht0, htT⟩, hx⟩ := hp
  have hx : 0 ≤ p.2 := hx
  set K := M.lam * (1 + M.ybar) * (Real.exp (gamma * (M.T - p.1)) * (1 + p.2)) with hK
  have hK0 : 0 ≤ K := by
    have := p932_ybar_nonneg M
    have := M.lam_pos
    positivity
  set c := gamma + M.lam - M.mubar
  have hdens : Measurable fun s : ℝ => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) := by
    fun_prop
  unfold JumpMarket.Q
  refine (Measure.lintegral_bind_le _ _ _).trans ?_
  refine (lintegral_withDensity_le_lintegral_mul _ hdens _).trans ?_
  have hcont : Continuous fun s : ℝ => K * Real.exp (-c * s) := by fun_prop
  calc _ ≤ ∫⁻ s in Set.Ioo (0 : ℝ) (M.T - p.1), ENNReal.ofReal (K * Real.exp (-c * s)) := by
        apply setLIntegral_mono (by fun_prop)
        intro s hs
        simp only [Pi.mul_apply]
        refine (mul_le_mul_right (lintegral_map_le _ _) _).trans ?_
        exact p932_inner M gamma a p hx s hs.1
    _ ≤ ∫⁻ s in Set.Ioo (0 : ℝ) M.T, ENNReal.ofReal (K * Real.exp (-c * s)) :=
        lintegral_mono_set (Set.Ioo_subset_Ioo_right (by linarith))
    _ = ENNReal.ofReal (∫ s in Set.Ioo (0 : ℝ) M.T, K * Real.exp (-c * s)) := by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · exact (hcont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
        · exact ae_of_all _ fun s => mul_nonneg hK0 (Real.exp_pos _).le
    _ = _ := by
        rw [integral_const_mul]; congr 1; unfold JumpMarket.bfun; rw [hK]; ring


lemma p932_bf (M : JumpMarket d) {gamma : ℝ} (hg : 0 ≤ gamma) :
    M.IsBoundingFunction (M.bfun gamma) (M.lam * (1 + M.ybar) *
        (∫ s in Set.Ioo (0 : ℝ) M.T, Real.exp (-(gamma + M.lam - M.mubar) * s))) := by
  refine ⟨fun p hp => ?_, p932_r_bound M hg, fun p hp a => p932_Q_bound M gamma p hp a⟩
  have hx : 0 ≤ p.2 := hp.2
  unfold JumpMarket.bfun; positivity

lemma p932_I (T c : ℝ) (hT : 0 ≤ T) (hc : c ≠ 0) :
    ∫ s in Set.Ioo (0 : ℝ) T, Real.exp (-c * s) = (1 - Real.exp (-T * c)) / c := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hT]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => -Real.exp (-c * s) / c)]
  · simp only [mul_zero, Real.exp_zero]; field_simp; ring_nf
  · intro x _
    have := (((hasDerivAt_id x).const_mul (-c)).exp.neg).div_const c
    refine this.congr_deriv ?_
    simp only [id]; field_simp
  · exact (by fun_prop : Continuous fun s : ℝ => Real.exp (-c * s)).intervalIntegrable _ _

theorem p932_core (M : JumpMarket d) :
    (∀ gamma : ℝ, 0 ≤ gamma → ∃ alpha : ℝ, M.IsBoundingFunction (M.bfun gamma) alpha) ∧
    (∀ gamma : ℝ, 0 ≤ gamma → gamma + M.lam ≠ M.mubar →
      M.IsBoundingFunction (M.bfun gamma) (M.alphaGamma gamma)) ∧
    (∃ gamma0 : ℝ, 0 ≤ gamma0 ∧ ∀ gamma : ℝ, gamma0 ≤ gamma →
      M.alphaGamma gamma < 1 ∧ M.IsBoundingFunction (M.bfun gamma) (M.alphaGamma gamma)) := by
  have hB : ∀ gamma : ℝ, 0 ≤ gamma → gamma + M.lam ≠ M.mubar →
      M.IsBoundingFunction (M.bfun gamma) (M.alphaGamma gamma) := by
    intro gamma hg hne
    have h := p932_bf M hg
    have hc : gamma + M.lam - M.mubar ≠ 0 := sub_ne_zero.mpr hne
    rw [p932_I M.T _ M.T_pos.le hc] at h
    convert h using 1
    unfold JumpMarket.alphaGamma; ring
  refine ⟨fun gamma hg => ⟨_, p932_bf M hg⟩, hB, ?_⟩
  have hy := p932_ybar_nonneg M
  have hm := p932_mubar_nonneg M
  have hl := M.lam_pos
  refine ⟨M.mubar + M.lam * (1 + M.ybar) + 1, by positivity, fun gamma hg => ?_⟩
  have hg0 : 0 ≤ gamma := by nlinarith
  have hcpos : M.lam * (1 + M.ybar) < gamma + M.lam - M.mubar := by linarith
  have hc0 : 0 < gamma + M.lam - M.mubar := by nlinarith
  refine ⟨?_, hB gamma hg0 (by linarith)⟩
  unfold JumpMarket.alphaGamma
  have he : 0 < Real.exp (-M.T * (gamma + M.lam - M.mubar)) := Real.exp_pos _
  have h1 : M.lam * (1 + M.ybar) / (gamma + M.lam - M.mubar) < 1 := by
    rw [div_lt_one hc0]; exact hcpos
  have h2 : 0 ≤ M.lam * (1 + M.ybar) / (gamma + M.lam - M.mubar) := by positivity
  nlinarith

end MDPFinance.JumpMarkets

open MDPFinance.JumpMarkets


theorem solution {d : ℕ} (M : JumpMarket d) :
    (∀ gamma : ℝ, 0 ≤ gamma → ∃ alpha : ℝ, M.IsBoundingFunction (M.bfun gamma) alpha) ∧
    (∀ gamma : ℝ, 0 ≤ gamma → gamma + M.lam ≠ M.mubar →
      M.IsBoundingFunction (M.bfun gamma) (M.alphaGamma gamma)) ∧
    (∃ gamma0 : ℝ, 0 ≤ gamma0 ∧ ∀ gamma : ℝ, gamma0 ≤ gamma →
      M.alphaGamma gamma < 1 ∧ M.IsBoundingFunction (M.bfun gamma) (M.alphaGamma gamma)) := by
  exact p932_core M
