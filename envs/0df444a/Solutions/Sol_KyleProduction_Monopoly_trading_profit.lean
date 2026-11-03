-- Prove2me | solution 1 for KyleProduction.Monopoly.trading_profit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:50:43.819937+00:00
-- url     : https://prove2.me/submissions/5f234b19-c925-47c6-bd2d-3889e198a105

import Mathlib
import Definitions.Def_KyleProduction_Monopoly_Model
import Theorems.Thm_KyleProduction_Monopoly_market_maker_update
import Theorems.Thm_KyleProduction_Monopoly_insider_best_response

open MeasureTheory ProbabilityTheory

namespace Aux_tp
open KyleProduction.Monopoly

theorem prob (P : Params) : IsProbabilityMeasure (law P) := by
  unfold law lawA lawU; infer_instance

theorem postVar_pos (P : Params) (hS : P.Standing) : 0 < postVar P := by
  obtain ⟨h1, h2, _⟩ := hS
  unfold postVar; positivity

theorem map_fst (P : Params) : (law P).map (fun x : ℝ × ℝ => x.1) = lawA P := by
  unfold law lawA lawU
  have := Measure.map_fst_prod (μ := gaussianReal (postMean P) (postVar P).toNNReal)
    (ν := gaussianReal 0 P.Su.toNNReal)
  simpa using this

theorem map_snd (P : Params) : (law P).map (fun x : ℝ × ℝ => x.2) = lawU P := by
  unfold law lawA lawU
  have := Measure.map_snd_prod (μ := gaussianReal (postMean P) (postVar P).toNNReal)
    (ν := gaussianReal 0 P.Su.toNNReal)
  simpa using this

theorem gfst (P : Params) : HasGaussianLaw (fun x : ℝ × ℝ => x.1) (law P) :=
  ⟨by rw [map_fst]; unfold lawA; infer_instance⟩

theorem gsnd (P : Params) : HasGaussianLaw (fun x : ℝ × ℝ => x.2) (law P) :=
  ⟨by rw [map_snd]; unfold lawU; infer_instance⟩

theorem indep12 (P : Params) :
    IndepFun (fun x : ℝ × ℝ => x.1) (fun x : ℝ × ℝ => x.2) (law P) := by
  unfold law lawA lawU
  exact indepFun_prod₀ (X := id) (Y := id) aemeasurable_id aemeasurable_id

theorem gpair (P : Params) : HasGaussianLaw (fun x : ℝ × ℝ => (x.1, x.2)) (law P) :=
  IndepFun.hasGaussianLaw (gfst P) (gsnd P) (indep12 P)

theorem memLp1 (P : Params) : MemLp (fun x : ℝ × ℝ => x.1) 2 (law P) := by
  unfold law lawU
  exact (memLp_id_gaussianReal' 2 (by simp)).comp_fst _

theorem memLp2 (P : Params) : MemLp (fun x : ℝ × ℝ => x.2) 2 (law P) := by
  unfold law lawA
  exact (memLp_id_gaussianReal' 2 (by simp)).comp_snd _

theorem var1 (P : Params) (hS : P.Standing) :
    cov[fun x : ℝ × ℝ => x.1, fun x : ℝ × ℝ => x.1; law P] = postVar P := by
  rw [covariance_self (by fun_prop)]
  have : Var[fun x : ℝ × ℝ => x.1; law P] = Var[id; (law P).map (fun x : ℝ × ℝ => x.1)] := by
    rw [variance_map (by fun_prop) (by fun_prop)]; rfl
  rw [this, map_fst]
  unfold lawA
  rw [variance_id_gaussianReal, Real.coe_toNNReal _ (postVar_pos P hS).le]

theorem var2 (P : Params) (hS : P.Standing) :
    cov[fun x : ℝ × ℝ => x.2, fun x : ℝ × ℝ => x.2; law P] = P.Su := by
  rw [covariance_self (by fun_prop)]
  have : Var[fun x : ℝ × ℝ => x.2; law P] = Var[id; (law P).map (fun x : ℝ × ℝ => x.2)] := by
    rw [variance_map (by fun_prop) (by fun_prop)]; rfl
  rw [this, map_snd]
  unfold lawU
  rw [variance_id_gaussianReal, Real.coe_toNNReal _ hS.2.2.1.le]

theorem cov12 (P : Params) :
    cov[fun x : ℝ × ℝ => x.1, fun x : ℝ × ℝ => x.2; law P] = 0 := by
  have := prob P
  exact (indep12 P).covariance_eq_zero (memLp1 P) (memLp2 P)

theorem lin_cov (P : Params) (hS : P.Standing) (c1 c2 d1 d2 : ℝ) :
    cov[fun x : ℝ × ℝ => c1 * x.1 + c2 * x.2, fun x : ℝ × ℝ => d1 * x.1 + d2 * x.2; law P]
      = c1 * d1 * postVar P + c2 * d2 * P.Su := by
  have := prob P
  have m1 := memLp1 P
  have m2 := memLp2 P
  have e1 : (fun x : ℝ × ℝ => c1 * x.1 + c2 * x.2) =
      (fun x : ℝ × ℝ => c1 * x.1) + (fun x : ℝ × ℝ => c2 * x.2) := rfl
  have e2 : (fun x : ℝ × ℝ => d1 * x.1 + d2 * x.2) =
      (fun x : ℝ × ℝ => d1 * x.1) + (fun x : ℝ × ℝ => d2 * x.2) := rfl
  rw [e1, e2, covariance_add_left (m1.const_mul c1) (m2.const_mul c2)
      ((m1.const_mul d1).add (m2.const_mul d2)),
    covariance_add_right (m1.const_mul c1) (m1.const_mul d1) (m2.const_mul d2),
    covariance_add_right (m2.const_mul c2) (m1.const_mul d1) (m2.const_mul d2)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  rw [var1 P hS, var2 P hS, cov12 P, covariance_comm, cov12 P]
  ring

theorem lin_indep (P : Params) (hS : P.Standing) (c1 c2 d1 d2 : ℝ)
    (h : c1 * d1 * postVar P + c2 * d2 * P.Su = 0) :
    IndepFun (fun x : ℝ × ℝ => c1 * x.1 + c2 * x.2) (fun x : ℝ × ℝ => d1 * x.1 + d2 * x.2)
      (law P) := by
  apply HasGaussianLaw.indepFun_of_covariance_eq_zero
  · let L : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
      (c1 • ContinuousLinearMap.fst ℝ ℝ ℝ + c2 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (d1 • ContinuousLinearMap.fst ℝ ℝ ℝ + d2 • ContinuousLinearMap.snd ℝ ℝ ℝ)
    have := (gpair P).map_fun L
    have e : (fun x : ℝ × ℝ => (c1 * x.1 + c2 * x.2, d1 * x.1 + d2 * x.2)) =
        fun ω : ℝ × ℝ => L (ω.1, ω.2) := by
      funext x; simp [L]
    rw [e]; exact this
  · rw [lin_cov P hS, h]


theorem int1 (P : Params) : Integrable (fun x : ℝ × ℝ => x.1) (law P) := by
  have := prob P; exact (memLp1 P).integrable one_le_two

theorem int2 (P : Params) : Integrable (fun x : ℝ × ℝ => x.2) (law P) := by
  have := prob P; exact (memLp2 P).integrable one_le_two

theorem integral1 (P : Params) : ∫ x, x.1 ∂(law P) = postMean P := by
  have : ∫ x, x.1 ∂(law P) = ∫ y, y ∂((law P).map (fun x : ℝ × ℝ => x.1)) :=
    (integral_map (by fun_prop) aestronglyMeasurable_id).symm
  rw [this, map_fst]; unfold lawA; rw [integral_id_gaussianReal]

theorem integral2 (P : Params) : ∫ x, x.2 ∂(law P) = 0 := by
  have : ∫ x, x.2 ∂(law P) = ∫ y, y ∂((law P).map (fun x : ℝ × ℝ => x.2)) :=
    (integral_map (by fun_prop) aestronglyMeasurable_id).symm
  rw [this, map_snd]; unfold lawU; rw [integral_id_gaussianReal]

theorem integral_lin (P : Params) (c1 c2 c0 : ℝ) :
    ∫ x, (c1 * x.1 + c2 * x.2 + c0) ∂(law P) = c1 * postMean P + c0 := by
  have := prob P
  have i1 : Integrable (fun x : ℝ × ℝ => c1 * x.1) (law P) := (int1 P).const_mul c1
  have i2 : Integrable (fun x : ℝ × ℝ => c2 * x.2) (law P) := (int2 P).const_mul c2
  have i12 : Integrable (fun x : ℝ × ℝ => c1 * x.1 + c2 * x.2) (law P) := i1.add i2
  rw [integral_add i12 (integrable_const c0), integral_add i1 i2, integral_const_mul,
    integral_const_mul, integral1, integral2]
  simp

/-- Insider optimality at `q ≠ 0` forces `λ > 0` and the best-response coefficients. -/
theorem insider_coeffs (P : Params) (hS : P.Standing) (q : ℝ) (hq : q ≠ 0) (e : LinStrat)
    (h : InsiderOptimal P q e) :
    0 < e.lam ∧ e.α = -e.μ / (2 * e.lam) ∧ e.β = 1 / (2 * e.lam) := by
  have hpay := fun v => (insider_best_response P hS e v).1
  -- every real value is attained by `firmValue q`
  have hsurj : ∀ v : ℝ, firmValue q (v / q + q) = v := by
    intro v; unfold firmValue; field_simp; ring
  have hopt : ∀ v d : ℝ, insiderPayoff P e v d ≤ insiderPayoff P e v (demand e v) := by
    intro v d
    have := h (v / q + q) d
    rwa [hsurj] at this
  have hlam : 0 < e.lam := by
    by_contra hneg
    push_neg at hneg
    set v := e.μ + 1
    set d0 := demand e v
    set B := insiderPayoff P e v d0
    have h1 := hopt v (|B| + 1)
    rw [hpay v (|B| + 1)] at h1
    have : (v - e.μ - e.lam * (|B| + 1)) * (|B| + 1) ≥ |B| + 1 := by
      have hv : v - e.μ = 1 := by simp [v]
      have hB : 0 ≤ |B| := abs_nonneg B
      nlinarith [mul_nonneg (neg_nonneg.mpr hneg) (mul_nonneg (by linarith : (0:ℝ) ≤ |B| + 1)
        (by linarith : (0:ℝ) ≤ |B| + 1))]
    have := le_abs_self B
    linarith
  have hbr : ∀ v : ℝ, demand e v = -e.μ / (2 * e.lam) + v / (2 * e.lam) := by
    intro v
    exact ((insider_best_response P hS e v).2 hlam (demand e v)).1 (fun d' => hopt v d')
  have h0 := hbr 0
  have h1 := hbr 1
  simp only [demand] at h0 h1
  refine ⟨hlam, by simpa using h0, ?_⟩
  have : e.β = (e.α + e.β * 1) - e.α := by ring
  rw [this, h1, ← (by simpa using h0 : e.α = -e.μ / (2 * e.lam))]
  ring


theorem moments (P : Params) (hS : P.Standing) :
    ∫ x, (x.1 - postMean P) * (x.1 - postMean P) ∂(law P) = postVar P ∧
    ∫ x, (x.1 - postMean P) * x.2 ∂(law P) = 0 := by
  have h1 := var1 P hS
  have h2 := cov12 P
  unfold covariance at h1 h2
  rw [integral1] at h1 h2
  rw [integral2] at h2
  simp only [sub_zero] at h2
  exact ⟨h1, h2⟩

end Aux_tp

open KyleProduction.Monopoly in
theorem solution (P : Params) (hS : P.Standing) (q : ℝ) (e : LinStrat)
    (he : IsLinEq P q e) :
    tradingProfit P q e = |q| / 2 * kappa P := by
  have hP := Aux_tp.prob P
  obtain ⟨hSa, hSθ, hSu, hω, -⟩ := id hS
  have hv : 0 < postVar P := by unfold postVar; positivity
  set r := Real.sqrt P.Su with hr
  set t := Real.sqrt (postVar P) with ht
  have hr0 : 0 < r := Real.sqrt_pos.mpr hSu
  have ht0 : 0 < t := Real.sqrt_pos.mpr hv
  have hr2 : r ^ 2 = P.Su := Real.sq_sqrt hSu.le
  have ht2 : t ^ 2 = postVar P := Real.sq_sqrt hv.le
  have hkap : kappa P = r * t := by
    unfold kappa
    rw [hr, ht, ← Real.sqrt_mul hSu.le]
    congr 1
    unfold postVar
    ring
  set m := postMean P with hm
  obtain ⟨hI, hM⟩ := he
  obtain ⟨hlam, hμ⟩ := (market_maker_update P hS q e).1 hM
  rcases eq_or_ne q 0 with hq | hq
  · -- `q = 0`: no information, zero prices, zero profit
    subst hq
    have hl0 : e.lam = 0 := by rw [hlam]; simp
    have hμ0 : e.μ = 0 := by rw [hμ, hl0]; simp
    unfold tradingProfit
    simp [firmValue, price, hl0, hμ0]
  · obtain ⟨hlpos, hα, hβ⟩ := Aux_tp.insider_coeffs P hS q hq e hI
    rw [← ht2, ← hr2] at hlam
    have hβl : e.β * (2 * e.lam) = 1 := by rw [hβ]; field_simp
    have hlam' : e.lam * (e.β ^ 2 * q ^ 2 * t ^ 2 + r ^ 2) = e.β * q ^ 2 * t ^ 2 := by
      have hden : 0 < e.β ^ 2 * q ^ 2 * t ^ 2 + r ^ 2 := by positivity
      rw [hlam]; field_simp
    have hsq : (2 * e.lam * r) ^ 2 = (|q| * t) ^ 2 := by
      have := congrArg (fun z => 4 * e.lam * z) hlam'
      have e1 : 4 * e.lam * (e.lam * (e.β ^ 2 * q ^ 2 * t ^ 2 + r ^ 2)) =
          (e.β * (2 * e.lam)) ^ 2 * q ^ 2 * t ^ 2 + 4 * e.lam ^ 2 * r ^ 2 := by ring
      have e2 : 4 * e.lam * (e.β * q ^ 2 * t ^ 2) = 2 * (e.β * (2 * e.lam)) * q ^ 2 * t ^ 2 := by
        ring
      rw [e1, e2, hβl] at this
      rw [mul_pow (|q|) t, sq_abs]
      nlinarith [this]
    have hlr : 2 * e.lam * r = |q| * t := by
      have h1 : 0 < 2 * e.lam * r := by positivity
      have h2 : 0 < |q| * t := by have := abs_pos.mpr hq; positivity
      nlinarith [sq_nonneg (2 * e.lam * r - |q| * t), sq_nonneg (2 * e.lam * r + |q| * t)]
    have hαl : e.lam * e.α = -e.μ / 2 := by rw [hα]; field_simp
    have h3 : e.lam * e.β = 1 / 2 := by linarith [hβl]
    have hμv : e.μ = q * (m - q) := by
      have : e.μ = q * (m - q) - (e.lam * e.α + e.lam * e.β * (q * (m - q))) := by
        rw [hμ]; ring
      rw [h3, hαl] at this
      linarith
    -- pointwise form of the integrand
    have hpt : ∀ x : ℝ × ℝ,
        (firmValue q x.1 - price e (orderFlow e q x)) * demand e (firmValue q x.1) =
          q ^ 2 / (4 * e.lam) * ((x.1 - m) * (x.1 - m)) + (-(q / 2)) * ((x.1 - m) * x.2) := by
      intro x
      simp only [firmValue, price, orderFlow, demand]
      rw [hα, hβ, hμv]
      field_simp
      ring
    have hm1 := Aux_tp.memLp1 P
    have hm2 := Aux_tp.memLp2 P
    have hc : MemLp (fun x : ℝ × ℝ => x.1 - m) 2 (law P) := hm1.sub (memLp_const _)
    have hi1 : Integrable (fun x : ℝ × ℝ => (x.1 - m) * (x.1 - m)) (law P) :=
      hc.integrable_mul hc
    have hi2 : Integrable (fun x : ℝ × ℝ => (x.1 - m) * x.2) (law P) :=
      hc.integrable_mul hm2
    obtain ⟨hmo1, hmo2⟩ := Aux_tp.moments P hS
    unfold tradingProfit
    simp_rw [hpt]
    rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul,
      hmo1, hmo2, hkap, ← ht2]
    have hl : e.lam = |q| * t / (2 * r) := by field_simp; linarith
    rw [hl, ← sq_abs q]
    field_simp
    ring
