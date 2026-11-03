-- Prove2me | solution 1 for KyleProduction.Monopoly.market_maker_update
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:46:09.974227+00:00
-- url     : https://prove2.me/submissions/5eb8570f-2e29-4298-b12e-d1711a2da2f8

import Mathlib
import Definitions.Def_KyleProduction_Monopoly_Model

open MeasureTheory ProbabilityTheory

namespace Aux_mmu
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

theorem orderFlow_eq (e : LinStrat) (q : ℝ) (x : ℝ × ℝ) :
    orderFlow e q x = e.α + e.β * (q * (x.1 - q)) + x.2 := by
  simp [orderFlow, demand, firmValue]

/-- The market maker's Gaussian update: `E[V | D] = μ* + λ* D`. -/
theorem key (P : Params) (hS : P.Standing) (q : ℝ) (e : LinStrat) :
    (law P)[fun x => firmValue q x.1 | MeasurableSpace.comap (orderFlow e q) inferInstance]
      =ᵐ[law P] fun x =>
        (q * (postMean P - q) - e.β * q ^ 2 * postVar P / (e.β ^ 2 * q ^ 2 * postVar P + P.Su)
            * (e.α + e.β * (q * (postMean P - q))))
        + e.β * q ^ 2 * postVar P / (e.β ^ 2 * q ^ 2 * postVar P + P.Su) * orderFlow e q x := by
  have hP := prob P
  have hv := postVar_pos P hS
  have hu : 0 < P.Su := hS.2.2.1
  set m := postMean P with hm
  set σ2 := postVar P with hσ2
  set Dn := e.β ^ 2 * q ^ 2 * σ2 + P.Su with hDn
  have hDpos : 0 < Dn := by rw [hDn]; positivity
  set lamS := e.β * q ^ 2 * σ2 / Dn with hlamS
  set muS := q * (m - q) - lamS * (e.α + e.β * (q * (m - q))) with hmuS
  set Y := orderFlow e q with hY
  have hYm : Measurable Y := by rw [hY]; unfold orderFlow demand firmValue; fun_prop
  set c1 := q * (1 - lamS * e.β) with hc1
  set c0 := -(c1 * m) with hc0
  set c0' := e.α - e.β * q ^ 2 with hc0'
  have hlD : lamS * Dn = e.β * q ^ 2 * σ2 := by rw [hlamS]; field_simp
  clear_value m σ2 Dn lamS muS Y c1 c0 c0'
  let R : ℝ × ℝ → ℝ := fun x => c1 * x.1 + (-lamS) * x.2 + c0
  have hRm : Measurable R := by fun_prop
  have hYeq : Y = fun x => (e.β * q) * x.1 + 1 * x.2 + c0' := by
    funext x; rw [hY, orderFlow_eq, hc0']; ring
  have hcov : c1 * (e.β * q) * σ2 + (-lamS) * 1 * P.Su = 0 := by
    rw [hc1]
    linear_combination -hlD + lamS * hDn
  have hind0 := lin_indep P hS c1 (-lamS) (e.β * q) 1 (by rw [← hσ2]; exact hcov)
  have hind : IndepFun R Y (law P) := by
    have := hind0.comp (measurable_add_const c0) (measurable_add_const c0')
    rw [hYeq]
    exact this
  have hVeq : (fun x : ℝ × ℝ => firmValue q x.1) =
      (fun x => muS + lamS * Y x) + R := by
    funext x
    simp only [Pi.add_apply, R, hY, orderFlow_eq, firmValue]
    rw [hmuS, hc0, hc1, hm]
    ring
  have hle : MeasurableSpace.comap Y inferInstance ≤ (inferInstance : MeasurableSpace (ℝ × ℝ)) :=
    hYm.comap_le
  have hleR : MeasurableSpace.comap R inferInstance ≤ (inferInstance : MeasurableSpace (ℝ × ℝ)) :=
    hRm.comap_le
  have hintY : Integrable Y (law P) := by
    rw [hYeq]
    exact ((int1 P).const_mul _ |>.add ((int2 P).const_mul _)).add (integrable_const _)
  have hintR : Integrable R (law P) :=
    ((int1 P).const_mul _ |>.add ((int2 P).const_mul _)).add (integrable_const _)
  have hintG : Integrable (fun x => muS + lamS * Y x) (law P) :=
    (integrable_const _).add (hintY.const_mul _)
  rw [hVeq]
  have h1 := condExp_add hintG hintR (MeasurableSpace.comap Y inferInstance)
  have h2 : (law P)[fun x => muS + lamS * Y x | MeasurableSpace.comap Y inferInstance] =
      fun x => muS + lamS * Y x := by
    apply condExp_of_stronglyMeasurable hle
    · have : Measurable[MeasurableSpace.comap Y inferInstance] Y := comap_measurable Y
      exact (Measurable.const_add (this.const_mul lamS) muS).stronglyMeasurable
    · exact hintG
  have h3 := condExp_indep_eq hleR hle (comap_measurable R).stronglyMeasurable
    ((IndepFun_iff_Indep R Y (law P)).1 hind)
  have h4 : ∫ x, R x ∂(law P) = 0 := by
    simp only [R]
    rw [integral_lin, hc0, hm]
    ring
  filter_upwards [h1, h3] with x hx1 hx3
  rw [hx1, Pi.add_apply, h2, hx3, h4]
  simp


theorem graph_null (P : Params) (hS : P.Standing) (F : ℝ → ℝ) (hF : Measurable F) :
    (law P) {x : ℝ × ℝ | x.2 = F x.1} = 0 := by
  have hu : P.Su.toNNReal ≠ 0 := by simp [hS.2.2.1]
  have hmeas : MeasurableSet {x : ℝ × ℝ | x.2 = F x.1} :=
    measurableSet_eq_fun measurable_snd (hF.comp measurable_fst)
  have : IsProbabilityMeasure (lawU P) := by unfold lawU; infer_instance
  unfold law
  rw [Measure.prod_apply hmeas]
  have e1 : ∀ a, Prod.mk a ⁻¹' {x : ℝ × ℝ | x.2 = F x.1} = {F a} := by
    intro a; ext y; simp
  have e2 : ∀ a, lawU P {F a} = 0 := by
    intro a; unfold lawU
    exact gaussianReal_absolutelyContinuous 0 hu (measure_singleton _)
  simp_rw [e1, e2]
  simp

end Aux_mmu

open KyleProduction.Monopoly in
theorem solution (P : Params) (hS : P.Standing) (q : ℝ) (e : LinStrat) :
    MarketEfficient P q e ↔
      (e.lam = e.β * q ^ 2 * postVar P / (e.β ^ 2 * q ^ 2 * postVar P + P.Su) ∧
       e.μ = q * (postMean P - q) - e.lam * (e.α + e.β * (q * (postMean P - q)))) := by
  have hP := Aux_mmu.prob P
  have hk := Aux_mmu.key P hS q e
  unfold MarketEfficient
  set lamS := e.β * q ^ 2 * postVar P / (e.β ^ 2 * q ^ 2 * postVar P + P.Su) with hlamS
  set A := e.α + e.β * (q * (postMean P - q)) with hA
  set muS := q * (postMean P - q) - lamS * A with hmuS
  constructor
  · intro h
    have hae := h.trans hk
    have hlam : e.lam = lamS := by
      by_contra hne
      have hne' : e.lam - lamS ≠ 0 := sub_ne_zero.mpr hne
      have h0 := Aux_mmu.graph_null P hS
        (fun a => (muS - e.μ) / (e.lam - lamS) - (e.α + e.β * (q * (a - q)))) (by fun_prop)
      rw [measure_eq_zero_iff_ae_notMem] at h0
      obtain ⟨x, hx1, hx2⟩ := (hae.and h0).exists
      apply hx2
      show _ = _
      simp only [price, Aux_mmu.orderFlow_eq] at hx1
      field_simp
      linear_combination hx1
    refine ⟨hlam, ?_⟩
    obtain ⟨x, hx⟩ := hae.exists
    simp only [price] at hx
    rw [hlam] at hx ⊢
    linarith
  · rintro ⟨h1, h2⟩
    refine Filter.EventuallyEq.trans ?_ hk.symm
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [price]
    rw [h2, h1]
