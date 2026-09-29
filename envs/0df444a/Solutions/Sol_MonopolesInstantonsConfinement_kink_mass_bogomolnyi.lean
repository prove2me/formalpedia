-- Prove2me | solution 1 for MonopolesInstantonsConfinement.kink_mass_bogomolnyi
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T03:51:18.916156+00:00
-- url     : https://prove2.me/submissions/159c04c2-ac17-4673-8443-43737ce9a2e6

import Mathlib
import Definitions.Def_MIC_kink_solitons_1d

open Filter Topology
open MonopolesInstantonsConfinement

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem W6_MonopolesInstantonsConfinement_hasDeriv (V : ℝ → ℝ) (hV : Differentiable ℝ V)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) (x : ℝ) :
    HasDerivAt (fun y => 1 / 2 * deriv φ y ^ 2 - V (φ y))
      (1 / 2 * ((2 : ℕ) * deriv φ x ^ (2 - 1) * deriv (deriv φ) x) -
        deriv V (φ x) * deriv φ x) x := by
  have hφ1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hφ2 : Differentiable ℝ (deriv φ) := hφ.differentiable_deriv_two
  have h1 : HasDerivAt (deriv φ) (deriv (deriv φ) x) x := (hφ2 x).hasDerivAt
  have h2 : HasDerivAt (fun y => V (φ y)) (deriv V (φ x) * deriv φ x) x :=
    (hV (φ x)).hasDerivAt.comp x (hφ1 x).hasDerivAt
  exact ((h1.pow 2).const_mul (1 / 2)).sub h2

theorem W6_MonopolesInstantonsConfinement_static_first_integral_deriv_zero (V : ℝ → ℝ) (hV : Differentiable ℝ V)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hEL : ∀ x, deriv (deriv φ) x = deriv V (φ x)) (x : ℝ) :
    deriv (fun y => 1 / 2 * deriv φ y ^ 2 - V (φ y)) x = 0 := by
  rw [(W6_MonopolesInstantonsConfinement_hasDeriv V hV φ hφ x).deriv, hEL x]
  push_cast
  ring

theorem W6_MonopolesInstantonsConfinement_exists_const_of_deriv_zero (V : ℝ → ℝ) (hV : Differentiable ℝ V)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hderiv : ∀ x, deriv (fun y => 1 / 2 * deriv φ y ^ 2 - V (φ y)) x = 0) :
    ∃ c : ℝ, ∀ x, 1 / 2 * deriv φ x ^ 2 - V (φ x) = c := by
  refine ⟨1 / 2 * deriv φ 0 ^ 2 - V (φ 0), fun x => ?_⟩
  have hd : Differentiable ℝ (fun y => 1 / 2 * deriv φ y ^ 2 - V (φ y)) := fun y =>
    (W6_MonopolesInstantonsConfinement_hasDeriv V hV φ hφ y).differentiableAt
  exact is_const_of_deriv_eq_zero hd hderiv x 0

theorem W6_MonopolesInstantonsConfinement_tanh_eq (y : ℝ) :
    Real.tanh y = 1 - 2 / (Real.exp (2 * y) + 1) := by
  rw [Real.tanh_eq, Real.exp_neg]
  have h := Real.exp_pos y
  have h2 : Real.exp (2 * y) = Real.exp y * Real.exp y := by rw [← Real.exp_add]; ring_nf
  rw [h2]
  field_simp
  try ring

theorem W6_MonopolesInstantonsConfinement_phi4Kink_eq (lam F x₀ : ℝ) :
    phi4Kink lam F x₀ = fun x => F * (1 - 2 / (Real.exp (phi4Mass lam F * (x - x₀)) + 1)) := by
  funext x
  unfold phi4Kink
  rw [W6_MonopolesInstantonsConfinement_tanh_eq,
    show 2 * (phi4Mass lam F / 2 * (x - x₀)) = phi4Mass lam F * (x - x₀) by ring]

theorem W6_MonopolesInstantonsConfinement_hasDerivAt_g (m x₀ x : ℝ) :
    HasDerivAt (fun x => Real.exp (m * (x - x₀))) (Real.exp (m * (x - x₀)) * m) x := by
  have h := (((hasDerivAt_id' x).sub_const x₀).const_mul m).exp
  exact h.congr_deriv (by ring)

theorem W6_MonopolesInstantonsConfinement_tendsto_g_atBot (m x₀ : ℝ) (hm : 0 < m) :
    Tendsto (fun x => Real.exp (m * (x - x₀))) atBot (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  apply Tendsto.const_mul_atBot hm
  exact tendsto_atBot_add_const_right _ _ tendsto_id

theorem W6_MonopolesInstantonsConfinement_tendsto_g_atTop (m x₀ : ℝ) (hm : 0 < m) :
    Tendsto (fun x => Real.exp (m * (x - x₀))) atTop atTop := by
  apply Real.tendsto_exp_atTop.comp
  apply Tendsto.const_mul_atTop hm
  exact tendsto_atTop_add_const_right _ _ tendsto_id

/-- Shared facts about the φ⁴ kink, written through `g x = exp (m (x - x₀))`. -/
theorem W6_MonopolesInstantonsConfinement_phi4_facts (lam F x₀ : ℝ) (hlam : 0 < lam) (hF : 0 < F) :
    0 < phi4Mass lam F ∧ phi4Mass lam F ^ 2 = lam * F ^ 2 / 3 ∧
    (∀ x, HasDerivAt (phi4Kink lam F x₀)
      (2 * F * phi4Mass lam F * Real.exp (phi4Mass lam F * (x - x₀)) /
        (Real.exp (phi4Mass lam F * (x - x₀)) + 1) ^ 2) x) := by
  have hm : 0 < phi4Mass lam F := by
    unfold phi4Mass; apply Real.sqrt_pos.2; positivity
  have hm2 : phi4Mass lam F ^ 2 = lam * F ^ 2 / 3 := by
    unfold phi4Mass; exact Real.sq_sqrt (by positivity)
  refine ⟨hm, hm2, fun x => ?_⟩
  rw [W6_MonopolesInstantonsConfinement_phi4Kink_eq]
  have hg := W6_MonopolesInstantonsConfinement_hasDerivAt_g (phi4Mass lam F) x₀ x
  have hpos := Real.exp_pos (phi4Mass lam F * (x - x₀))
  have hne : Real.exp (phi4Mass lam F * (x - x₀)) + 1 ≠ 0 := by linarith
  have h := (((hasDerivAt_const x (2 : ℝ)).div (hg.add_const 1) hne).const_sub 1).const_mul F
  exact h.congr_deriv (by field_simp; try ring)

theorem W6_MonopolesInstantonsConfinement_phi4Kink_isSoliton (lam F x₀ : ℝ) (hlam : 0 < lam) (hF : 0 < F) :
    ContDiff ℝ 2 (phi4Kink lam F x₀) ∧
    (∀ x, deriv (deriv (phi4Kink lam F x₀)) x =
      deriv (phi4Potential lam F) (phi4Kink lam F x₀ x)) ∧
    Tendsto (phi4Kink lam F x₀) atBot (𝓝 (-F)) ∧
    Tendsto (phi4Kink lam F x₀) atTop (𝓝 F) := by
  obtain ⟨hm, hm2, hd1⟩ := W6_MonopolesInstantonsConfinement_phi4_facts lam F x₀ hlam hF
  have hkink := W6_MonopolesInstantonsConfinement_phi4Kink_eq lam F x₀
  set m := phi4Mass lam F with hmdef
  have hgd : ∀ x, HasDerivAt (fun x => Real.exp (m * (x - x₀))) (Real.exp (m * (x - x₀)) * m) x :=
    fun x => W6_MonopolesInstantonsConfinement_hasDerivAt_g m x₀ x
  have hD1 : deriv (phi4Kink lam F x₀) = fun x => 2 * F * m * Real.exp (m * (x - x₀)) /
      (Real.exp (m * (x - x₀)) + 1) ^ 2 :=
    funext fun x => (hd1 x).deriv
  have hd2 : ∀ x, HasDerivAt (fun x => 2 * F * m * Real.exp (m * (x - x₀)) /
      (Real.exp (m * (x - x₀)) + 1) ^ 2)
      (2 * F * m ^ 2 * Real.exp (m * (x - x₀)) * (1 - Real.exp (m * (x - x₀))) /
        (Real.exp (m * (x - x₀)) + 1) ^ 3) x := by
    intro x
    have hpos := Real.exp_pos (m * (x - x₀))
    have hne : (Real.exp (m * (x - x₀)) + 1) ^ 2 ≠ 0 := by positivity
    have hne' : Real.exp (m * (x - x₀)) + 1 ≠ 0 := by positivity
    have h := ((hgd x).const_mul (2 * F * m)).div (((hgd x).add_const 1).pow 2) hne
    exact h.congr_deriv (by (try simp only [Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.mul_apply]); (try push_cast); (try field_simp); (try ring))
  have hV : ∀ y, deriv (phi4Potential lam F) y = lam / 24 * (2 * (y ^ 2 - F ^ 2) * (2 * y)) := by
    intro y
    have h := (((hasDerivAt_pow 2 y).sub_const (F ^ 2)).pow 2).const_mul (lam / 24)
    have h' : HasDerivAt (phi4Potential lam F)
        (lam / 24 * (2 * (y ^ 2 - F ^ 2) * (2 * y))) y :=
      h.congr_deriv (by push_cast; ring)
    exact h'.deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hkink]
    have hgc : ContDiff ℝ 2 (fun x => Real.exp (m * (x - x₀))) :=
      Real.contDiff_exp.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
    exact contDiff_const.mul (contDiff_const.sub (contDiff_const.div (hgc.add contDiff_const)
      (fun x => ne_of_gt (by have := Real.exp_pos (m * (x - x₀)); linarith))))
  · intro x
    rw [hD1, (hd2 x).deriv, hV, hkink]
    beta_reduce
    have hpos := Real.exp_pos (m * (x - x₀))
    have hne : Real.exp (m * (x - x₀)) + 1 ≠ 0 := by positivity
    rw [hm2]
    field_simp
    try ring
  · rw [hkink]
    have h0 := W6_MonopolesInstantonsConfinement_tendsto_g_atBot m x₀ hm
    have h : Tendsto (fun x => F * (1 - 2 / (Real.exp (m * (x - x₀)) + 1))) atBot
        (𝓝 (F * (1 - 2 / (0 + 1)))) :=
      (tendsto_const_nhds.sub (tendsto_const_nhds.div (h0.add_const (1 : ℝ))
        (by norm_num : (0 : ℝ) + 1 ≠ 0))).const_mul F
    have e : F * (1 - 2 / (0 + 1)) = -F := by ring
    rw [e] at h
    exact h
  · rw [hkink]
    have h0 := W6_MonopolesInstantonsConfinement_tendsto_g_atTop m x₀ hm
    have h : Tendsto (fun x => F * (1 - 2 / (Real.exp (m * (x - x₀)) + 1))) atTop
        (𝓝 (F * (1 - 0))) :=
      (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ (1 : ℝ) h0))).const_mul F
    have e : F * (1 - 0) = F := by ring
    rw [e] at h
    exact h

theorem W6_MonopolesInstantonsConfinement_sin_four_arctan (t : ℝ) :
    Real.sin (4 * Real.arctan t) = 4 * t * (1 - t ^ 2) / (1 + t ^ 2) ^ 2 := by
  have hc2 : Real.cos (Real.arctan t) ^ 2 = 1 / (1 + t ^ 2) := Real.cos_sq_arctan t
  have hs : Real.sin (Real.arctan t) = t * Real.cos (Real.arctan t) := by
    rw [Real.sin_arctan, Real.cos_arctan]; ring
  have h4 : 4 * Real.arctan t = 2 * (2 * Real.arctan t) := by ring
  rw [h4, Real.sin_two_mul, Real.sin_two_mul, Real.cos_two_mul, hs]
  have e : 2 * (2 * (t * Real.cos (Real.arctan t)) * Real.cos (Real.arctan t)) *
      (2 * Real.cos (Real.arctan t) ^ 2 - 1) =
      4 * t * Real.cos (Real.arctan t) ^ 2 * (2 * Real.cos (Real.arctan t) ^ 2 - 1) := by ring
  rw [e, hc2]
  have : (1 + t ^ 2) ≠ 0 := by positivity
  field_simp
  try ring

theorem W6_MonopolesInstantonsConfinement_sin_two_arctan (t : ℝ) :
    Real.sin (2 * Real.arctan t) = 2 * t / (1 + t ^ 2) := by
  have hc2 : Real.cos (Real.arctan t) ^ 2 = 1 / (1 + t ^ 2) := Real.cos_sq_arctan t
  have hs : Real.sin (Real.arctan t) = t * Real.cos (Real.arctan t) := by
    rw [Real.sin_arctan, Real.cos_arctan]; ring
  rw [Real.sin_two_mul, hs]
  have e : 2 * (t * Real.cos (Real.arctan t)) * Real.cos (Real.arctan t) =
      2 * t * Real.cos (Real.arctan t) ^ 2 := by ring
  rw [e, hc2]
  ring

theorem W6_MonopolesInstantonsConfinement_cos_four_arctan (t : ℝ) :
    Real.cos (4 * Real.arctan t) = 1 - 8 * t ^ 2 / (1 + t ^ 2) ^ 2 := by
  have h4 : 4 * Real.arctan t = 2 * (2 * Real.arctan t) := by ring
  rw [h4, Real.cos_two_mul, Real.cos_sq', W6_MonopolesInstantonsConfinement_sin_two_arctan]
  have : (1 + t ^ 2) ≠ 0 := by positivity
  field_simp
  try ring

/-- Shared facts about the sine-Gordon kink, with `A = s²`. -/
theorem W6_MonopolesInstantonsConfinement_sg_facts (s F x₀ : ℝ) (hs : 0 < s) (hF : 0 < F) :
    sineGordonMass (s ^ 2) F = 2 * Real.pi * s / F ∧
    (∀ x, HasDerivAt (sineGordonKink (s ^ 2) F x₀)
      (4 * s * Real.exp (2 * Real.pi * s / F * (x - x₀)) /
        (1 + Real.exp (2 * Real.pi * s / F * (x - x₀)) ^ 2)) x) := by
  have hpi := Real.pi_pos
  have hmv : sineGordonMass (s ^ 2) F = 2 * Real.pi * s / F := by
    unfold sineGordonMass; rw [Real.sqrt_sq hs.le]
  refine ⟨hmv, fun x => ?_⟩
  have hk : sineGordonKink (s ^ 2) F x₀ =
      fun x => 2 * F / Real.pi * Real.arctan (Real.exp (2 * Real.pi * s / F * (x - x₀))) := by
    funext x; unfold sineGordonKink; rw [hmv]
  rw [hk]
  have hg := W6_MonopolesInstantonsConfinement_hasDerivAt_g (2 * Real.pi * s / F) x₀ x
  have h := (hg.arctan).const_mul (2 * F / Real.pi)
  have : 1 + Real.exp (2 * Real.pi * s / F * (x - x₀)) ^ 2 ≠ 0 := by positivity
  exact h.congr_deriv (by field_simp; try ring)

theorem W6_MonopolesInstantonsConfinement_sineGordonKink_isSoliton (A F x₀ : ℝ) (hA : 0 < A) (hF : 0 < F) :
    ContDiff ℝ 2 (sineGordonKink A F x₀) ∧
    (∀ x, deriv (deriv (sineGordonKink A F x₀)) x =
      deriv (sineGordonPotential A F) (sineGordonKink A F x₀ x)) ∧
    Tendsto (sineGordonKink A F x₀) atBot (𝓝 0) ∧
    Tendsto (sineGordonKink A F x₀) atTop (𝓝 F) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ A = s ^ 2 :=
    ⟨Real.sqrt A, Real.sqrt_pos.2 hA, (Real.sq_sqrt hA.le).symm⟩
  have hpi := Real.pi_pos
  obtain ⟨hmv, hd1⟩ := W6_MonopolesInstantonsConfinement_sg_facts s F x₀ hs hF
  set m := 2 * Real.pi * s / F with hmdef
  have hm : 0 < m := by rw [hmdef]; positivity
  have hkink : sineGordonKink (s ^ 2) F x₀ =
      fun x => 2 * F / Real.pi * Real.arctan (Real.exp (m * (x - x₀))) := by
    funext x; unfold sineGordonKink; rw [hmv]
  have hgd : ∀ x, HasDerivAt (fun x => Real.exp (m * (x - x₀))) (Real.exp (m * (x - x₀)) * m) x :=
    fun x => W6_MonopolesInstantonsConfinement_hasDerivAt_g m x₀ x
  have hD1 : deriv (sineGordonKink (s ^ 2) F x₀) = fun x => 4 * s * Real.exp (m * (x - x₀)) /
      (1 + Real.exp (m * (x - x₀)) ^ 2) :=
    funext fun x => (hd1 x).deriv
  have hd2 : ∀ x, HasDerivAt (fun x => 4 * s * Real.exp (m * (x - x₀)) /
      (1 + Real.exp (m * (x - x₀)) ^ 2))
      (4 * s * m * Real.exp (m * (x - x₀)) * (1 - Real.exp (m * (x - x₀)) ^ 2) /
        (1 + Real.exp (m * (x - x₀)) ^ 2) ^ 2) x := by
    intro x
    have hne : 1 + Real.exp (m * (x - x₀)) ^ 2 ≠ 0 := by positivity
    have h := ((hgd x).const_mul (4 * s)).div (((hgd x).pow 2).const_add 1) hne
    exact h.congr_deriv (by (try simp only [Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.mul_apply]); (try push_cast); (try field_simp); (try ring))
  have hV : ∀ y, deriv (sineGordonPotential (s ^ 2) F) y =
      s ^ 2 * (Real.sin (2 * Real.pi * y / F) * (2 * Real.pi / F)) := by
    intro y
    have h := ((((hasDerivAt_id' y).const_mul (2 * Real.pi)).div_const F).cos.const_sub 1).const_mul (s ^ 2)
    have h' : HasDerivAt (sineGordonPotential (s ^ 2) F)
        (s ^ 2 * (Real.sin (2 * Real.pi * y / F) * (2 * Real.pi / F))) y :=
      h.congr_deriv (by ring)
    exact h'.deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hkink]
    have hgc : ContDiff ℝ 2 (fun x => Real.exp (m * (x - x₀))) :=
      Real.contDiff_exp.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
    exact contDiff_const.mul (Real.contDiff_arctan.comp hgc)
  · intro x
    rw [hD1, (hd2 x).deriv, hV, hkink]
    beta_reduce
    have harg : 2 * Real.pi * (2 * F / Real.pi * Real.arctan (Real.exp (m * (x - x₀)))) / F =
        4 * Real.arctan (Real.exp (m * (x - x₀))) := by
      field_simp; try ring
    rw [harg, W6_MonopolesInstantonsConfinement_sin_four_arctan, hmdef]
    have : 1 + Real.exp (2 * Real.pi * s / F * (x - x₀)) ^ 2 ≠ 0 := by positivity
    field_simp
    try ring
  · rw [hkink]
    have h0 := W6_MonopolesInstantonsConfinement_tendsto_g_atBot m x₀ hm
    have h := ((Real.continuous_arctan.tendsto 0).comp h0).const_mul (2 * F / Real.pi)
    have e : 2 * F / Real.pi * Real.arctan 0 = 0 := by simp
    rw [e] at h
    exact h
  · rw [hkink]
    have h0 := W6_MonopolesInstantonsConfinement_tendsto_g_atTop m x₀ hm
    have h := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h0).const_mul
      (2 * F / Real.pi)
    have e : 2 * F / Real.pi * (Real.pi / 2) = F := by field_simp
    rw [e] at h
    exact h

theorem W6_MonopolesInstantonsConfinement_lintegral_of_deriv (h Φ : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ x, HasDerivAt Φ (h x) x) (hc : Continuous h) (hnn : ∀ x, 0 ≤ h x)
    (hbot : Tendsto Φ atBot (𝓝 a)) (htop : Tendsto Φ atTop (𝓝 b)) :
    ∫⁻ x, ENNReal.ofReal (h x) = ENNReal.ofReal (b - a) := by
  have hcov : MeasureTheory.AECover MeasureTheory.volume atTop (fun t : ℝ => Set.Icc (-t) t) :=
    MeasureTheory.aecover_Icc tendsto_neg_atTop_atBot tendsto_id
  refine hcov.lintegral_eq_of_tendsto _ hc.measurable.ennreal_ofReal.aemeasurable ?_
  have hI : ∀ t : ℝ, 0 ≤ t → ∫⁻ x in Set.Icc (-t) t, ENNReal.ofReal (h x) =
      ENNReal.ofReal (Φ t - Φ (-t)) := by
    intro t ht
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Icc)
      (MeasureTheory.ae_of_all _ hnn)]
    congr 1
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (hc.intervalIntegrable _ _)
  have hlim : Tendsto (fun t => ENNReal.ofReal (Φ t - Φ (-t))) atTop (𝓝 (ENNReal.ofReal (b - a))) :=
    ENNReal.tendsto_ofReal (htop.sub (hbot.comp tendsto_neg_atTop_atBot))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact (hI t ht).symm

theorem W6_MonopolesInstantonsConfinement_phi4Kink_energy (lam F x₀ : ℝ) (hlam : 0 < lam) (hF : 0 < F) :
    staticEnergy (phi4Potential lam F) (phi4Kink lam F x₀) =
      ENNReal.ofReal (2 * phi4Mass lam F ^ 3 / lam) := by
  obtain ⟨hm, hm2, hd1⟩ := W6_MonopolesInstantonsConfinement_phi4_facts lam F x₀ hlam hF
  have hkink := W6_MonopolesInstantonsConfinement_phi4Kink_eq lam F x₀
  have hsol := W6_MonopolesInstantonsConfinement_phi4Kink_isSoliton lam F x₀ hlam hF
  set m := phi4Mass lam F with hmdef
  have hD1 : deriv (phi4Kink lam F x₀) = fun x => 2 * F * m * Real.exp (m * (x - x₀)) /
      (Real.exp (m * (x - x₀)) + 1) ^ 2 :=
    funext fun x => (hd1 x).deriv
  have hgc : Continuous (fun x => Real.exp (m * (x - x₀))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))
  let hfun : ℝ → ℝ := fun x => (2 * F * m * Real.exp (m * (x - x₀)) /
      (Real.exp (m * (x - x₀)) + 1) ^ 2) ^ 2
  have hint : (fun x => ENNReal.ofReal (1 / 2 * deriv (phi4Kink lam F x₀) x ^ 2 +
      phi4Potential lam F (phi4Kink lam F x₀ x))) = fun x => ENNReal.ofReal (hfun x) := by
    funext x
    congr 1
    rw [hD1, hkink]
    simp only [hfun]
    unfold phi4Potential
    have hpos := Real.exp_pos (m * (x - x₀))
    have hne : Real.exp (m * (x - x₀)) + 1 ≠ 0 := by positivity
    field_simp
    rw [hm2]
    ring
  let Φ : ℝ → ℝ := fun x => m / (2 * F) *
    (F ^ 2 * phi4Kink lam F x₀ x - phi4Kink lam F x₀ x ^ 3 / 3)
  have hΦd : ∀ x, HasDerivAt Φ (hfun x) x := by
    intro x
    have h := (((hd1 x).const_mul (F ^ 2)).sub (((hd1 x).pow 3).div_const 3)).const_mul (m / (2 * F))
    refine h.congr_deriv ?_
    simp only [hfun]
    rw [hkink]
    beta_reduce
    have hpos := Real.exp_pos (m * (x - x₀))
    have hne : Real.exp (m * (x - x₀)) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    try ring
  have hWc : Continuous (fun y : ℝ => m / (2 * F) * (F ^ 2 * y - y ^ 3 / 3)) := by fun_prop
  have hbot : Tendsto Φ atBot (𝓝 (m / (2 * F) * (F ^ 2 * (-F) - (-F) ^ 3 / 3))) :=
    (hWc.tendsto _).comp hsol.2.2.1
  have htop : Tendsto Φ atTop (𝓝 (m / (2 * F) * (F ^ 2 * F - F ^ 3 / 3))) :=
    (hWc.tendsto _).comp hsol.2.2.2
  have hcont : Continuous hfun :=
    ((continuous_const.mul hgc).div ((hgc.add continuous_const).pow 2)
      (fun x => by
        simp only [Pi.add_apply, Pi.pow_apply]
        have := Real.exp_pos (m * (x - x₀)); positivity)).pow 2
  unfold staticEnergy
  rw [hint, W6_MonopolesInstantonsConfinement_lintegral_of_deriv hfun Φ _ _ hΦd hcont
    (fun x => sq_nonneg _) hbot htop]
  congr 1
  have e : m ^ 3 = m * m ^ 2 := by ring
  rw [e, hm2]
  field_simp
  try ring

theorem W6_MonopolesInstantonsConfinement_sineGordonKink_energy (A F x₀ : ℝ) (hA : 0 < A) (hF : 0 < F) :
    staticEnergy (sineGordonPotential A F) (sineGordonKink A F x₀) =
      ENNReal.ofReal (8 * sineGordonMass A F ^ 3 / sineGordonCoupling A F) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ A = s ^ 2 :=
    ⟨Real.sqrt A, Real.sqrt_pos.2 hA, (Real.sq_sqrt hA.le).symm⟩
  have hpi := Real.pi_pos
  obtain ⟨hmv, hd1⟩ := W6_MonopolesInstantonsConfinement_sg_facts s F x₀ hs hF
  have hsol := W6_MonopolesInstantonsConfinement_sineGordonKink_isSoliton (s ^ 2) F x₀ (by positivity) hF
  rw [hmv]
  set m := 2 * Real.pi * s / F with hmdef
  have hm : 0 < m := by rw [hmdef]; positivity
  have hkink : sineGordonKink (s ^ 2) F x₀ =
      fun x => 2 * F / Real.pi * Real.arctan (Real.exp (m * (x - x₀))) := by
    funext x; unfold sineGordonKink; rw [hmv]
  have hgd : ∀ x, HasDerivAt (fun x => Real.exp (m * (x - x₀))) (Real.exp (m * (x - x₀)) * m) x :=
    fun x => W6_MonopolesInstantonsConfinement_hasDerivAt_g m x₀ x
  have hD1 : deriv (sineGordonKink (s ^ 2) F x₀) = fun x => 4 * s * Real.exp (m * (x - x₀)) /
      (1 + Real.exp (m * (x - x₀)) ^ 2) :=
    funext fun x => (hd1 x).deriv
  have hgc : Continuous (fun x => Real.exp (m * (x - x₀))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))
  let hfun : ℝ → ℝ := fun x => 16 * s ^ 2 * Real.exp (m * (x - x₀)) ^ 2 /
    (1 + Real.exp (m * (x - x₀)) ^ 2) ^ 2
  have hint : (fun x => ENNReal.ofReal (1 / 2 * deriv (sineGordonKink (s ^ 2) F x₀) x ^ 2 +
      sineGordonPotential (s ^ 2) F (sineGordonKink (s ^ 2) F x₀ x))) =
      fun x => ENNReal.ofReal (hfun x) := by
    funext x
    congr 1
    rw [hD1, hkink]
    simp only [hfun]
    unfold sineGordonPotential
    have harg : 2 * Real.pi * (2 * F / Real.pi * Real.arctan (Real.exp (m * (x - x₀)))) / F =
        4 * Real.arctan (Real.exp (m * (x - x₀))) := by
      field_simp; try ring
    rw [harg, W6_MonopolesInstantonsConfinement_cos_four_arctan]
    have : 1 + Real.exp (m * (x - x₀)) ^ 2 ≠ 0 := by positivity
    field_simp
    try ring
  let Φ : ℝ → ℝ := fun x => -(2 * s * F / Real.pi) * Real.cos (2 * Real.arctan (Real.exp (m * (x - x₀))))
  have hΦd : ∀ x, HasDerivAt Φ (hfun x) x := by
    intro x
    have h := ((((hgd x).arctan).const_mul 2).cos).const_mul (-(2 * s * F / Real.pi))
    refine h.congr_deriv ?_
    simp only [hfun]
    rw [W6_MonopolesInstantonsConfinement_sin_two_arctan, hmdef]
    have : 1 + Real.exp (2 * Real.pi * s / F * (x - x₀)) ^ 2 ≠ 0 := by positivity
    field_simp
    try ring
  have hWc : Continuous (fun t : ℝ => -(2 * s * F / Real.pi) * Real.cos (2 * Real.arctan t)) := by
    fun_prop
  have h0 := W6_MonopolesInstantonsConfinement_tendsto_g_atBot m x₀ hm
  have hinf := W6_MonopolesInstantonsConfinement_tendsto_g_atTop m x₀ hm
  have hbot : Tendsto Φ atBot
      (𝓝 (-(2 * s * F / Real.pi) * Real.cos (2 * Real.arctan 0))) :=
    (hWc.tendsto _).comp h0
  have hWc' : Continuous (fun θ : ℝ => -(2 * s * F / Real.pi) * Real.cos (2 * θ)) := by
    fun_prop
  have htop : Tendsto Φ atTop
      (𝓝 (-(2 * s * F / Real.pi) * Real.cos (2 * (Real.pi / 2)))) :=
    (hWc'.tendsto _).comp ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hinf)
  have hcont : Continuous hfun :=
    (continuous_const.mul (hgc.pow 2)).div ((continuous_const.add (hgc.pow 2)).pow 2)
      (fun x => by
        try simp only [Pi.add_apply, Pi.pow_apply]
        positivity)
  have hnn : ∀ x, 0 ≤ hfun x := fun x => by simp only [hfun]; positivity
  unfold staticEnergy
  rw [hint, W6_MonopolesInstantonsConfinement_lintegral_of_deriv hfun Φ _ _ hΦd hcont hnn hbot htop]
  congr 1
  unfold sineGordonCoupling
  rw [Real.arctan_zero, mul_zero, Real.cos_zero,
    show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi, hmdef]
  field_simp
  try ring

theorem W6_MonopolesInstantonsConfinement_bogo (V w W φ : ℝ → ℝ) (hφ : Differentiable ℝ φ)
    (hV : Continuous V) (hwc : Continuous w) (hw : ∀ y, HasDerivAt W (w y) y)
    (hVw : ∀ y, V y = 1 / 2 * w y ^ 2) (a b : ℝ)
    (hbot : Tendsto (fun x => W (φ x)) atBot (𝓝 a)) (htop : Tendsto (fun x => W (φ x)) atTop (𝓝 b)) :
    ENNReal.ofReal (b - a) ≤ staticEnergy V φ := by
  let I : ℝ → ℝ := fun x => 1 / 2 * deriv φ x ^ 2 + V (φ x)
  have hImeas : Measurable I :=
    ((measurable_deriv φ).pow_const 2 |>.const_mul _).add (hV.measurable.comp hφ.continuous.measurable)
  have hInn : ∀ x, 0 ≤ I x := fun x => by
    simp only [I]; rw [hVw]; positivity
  let k : ℝ → ℝ := fun x => w (φ x) * deriv φ x
  have hk : ∀ x, HasDerivAt (fun x => W (φ x)) (k x) x := fun x =>
    (hw (φ x)).comp x (hφ x).hasDerivAt
  have hkmeas : Measurable k := (hwc.measurable.comp hφ.continuous.measurable).mul (measurable_deriv φ)
  have hkI : ∀ x, |k x| ≤ I x := by
    intro x
    simp only [k, I]
    rw [hVw, abs_mul]
    nlinarith [sq_nonneg (|w (φ x)| - |deriv φ x|), sq_abs (w (φ x)), sq_abs (deriv φ x)]
  have hE : staticEnergy V φ = ∫⁻ x, ENNReal.ofReal (I x) := rfl
  have key : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal (W (φ t) - W (φ (-t))) ≤ staticEnergy V φ := by
    intro t ht
    have hsub : ∫⁻ x in Set.Icc (-t) t, ENNReal.ofReal (I x) ≤ staticEnergy V φ := by
      rw [hE]; exact MeasureTheory.setLIntegral_le_lintegral _ _
    by_cases hfin : ∫⁻ x in Set.Icc (-t) t, ENNReal.ofReal (I x) = ⊤
    · rw [hfin] at hsub
      exact le_top.trans hsub
    · have hIint : MeasureTheory.IntegrableOn I (Set.Icc (-t) t) := by
        refine ⟨hImeas.aestronglyMeasurable, ?_⟩
        exact (MeasureTheory.hasFiniteIntegral_iff_ofReal (MeasureTheory.ae_of_all _ hInn)).2
          (lt_top_iff_ne_top.2 hfin)
      have hkint : MeasureTheory.IntegrableOn k (Set.Icc (-t) t) :=
        hIint.mono' hkmeas.aestronglyMeasurable
          (MeasureTheory.ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hkI x)
      have hFTC : ∫ x in Set.Icc (-t) t, k x = W (φ t) - W (φ (-t)) := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hk x)
          ((intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 hkint)
      calc ENNReal.ofReal (W (φ t) - W (φ (-t))) = ENNReal.ofReal (∫ x in Set.Icc (-t) t, k x) := by
            rw [hFTC]
        _ ≤ ENNReal.ofReal (∫ x in Set.Icc (-t) t, I x) :=
            ENNReal.ofReal_le_ofReal (MeasureTheory.integral_mono hkint hIint
              (fun x => (le_abs_self _).trans (hkI x)))
        _ = ∫⁻ x in Set.Icc (-t) t, ENNReal.ofReal (I x) :=
            MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIint (MeasureTheory.ae_of_all _ hInn)
        _ ≤ staticEnergy V φ := hsub
  have hlim : Tendsto (fun t => ENNReal.ofReal (W (φ t) - W (φ (-t)))) atTop
      (𝓝 (ENNReal.ofReal (b - a))) :=
    ENNReal.tendsto_ofReal (htop.sub (hbot.comp tendsto_neg_atTop_atBot))
  exact le_of_tendsto hlim ((eventually_ge_atTop 0).mono key)

theorem W6_MonopolesInstantonsConfinement_phi4_bogomolnyi_bound (lam F : ℝ) (hlam : 0 < lam) (hF : 0 < F)
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ)
    (hbot : Tendsto φ atBot (𝓝 (-F))) (htop : Tendsto φ atTop (𝓝 F)) :
    ENNReal.ofReal (2 * phi4Mass lam F ^ 3 / lam) ≤ staticEnergy (phi4Potential lam F) φ := by
  have hm2 : phi4Mass lam F ^ 2 = lam * F ^ 2 / 3 := by
    unfold phi4Mass; exact Real.sq_sqrt (by positivity)
  set m := phi4Mass lam F with hmdef
  let W : ℝ → ℝ := fun y => m / (2 * F) * (F ^ 2 * y - y ^ 3 / 3)
  have hWc : Continuous W := by fun_prop
  have hb := (hWc.tendsto _).comp hbot
  have ht := (hWc.tendsto _).comp htop
  have h := W6_MonopolesInstantonsConfinement_bogo (phi4Potential lam F)
    (fun y => m / (2 * F) * (F ^ 2 - y ^ 2)) W φ hφ
    (by unfold phi4Potential; fun_prop) (by fun_prop)
    (fun y => by
      have h1 := (((hasDerivAt_id' y).const_mul (F ^ 2)).sub ((hasDerivAt_pow 3 y).div_const 3)).const_mul
        (m / (2 * F))
      exact h1.congr_deriv (by push_cast; ring))
    (fun y => by
      unfold phi4Potential
      field_simp
      rw [hm2]
      ring)
    _ _ hb ht
  have e : 2 * m ^ 3 / lam = W F - W (-F) := by
    simp only [W]
    have e3 : m ^ 3 = m * m ^ 2 := by ring
    rw [e3, hm2]
    field_simp
    try ring
  rw [e]
  exact h

theorem W6_MonopolesInstantonsConfinement_sineGordon_bogomolnyi_bound (A F : ℝ) (hA : 0 < A) (hF : 0 < F)
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ)
    (hbot : Tendsto φ atBot (𝓝 0)) (htop : Tendsto φ atTop (𝓝 F)) :
    ENNReal.ofReal (8 * sineGordonMass A F ^ 3 / sineGordonCoupling A F) ≤
      staticEnergy (sineGordonPotential A F) φ := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ A = s ^ 2 :=
    ⟨Real.sqrt A, Real.sqrt_pos.2 hA, (Real.sq_sqrt hA.le).symm⟩
  have hpi := Real.pi_pos
  let W : ℝ → ℝ := fun y => -(2 * s * F / Real.pi) * Real.cos (Real.pi * y / F)
  have hWc : Continuous W := by fun_prop
  have hb := (hWc.tendsto _).comp hbot
  have ht := (hWc.tendsto _).comp htop
  have h := W6_MonopolesInstantonsConfinement_bogo (sineGordonPotential (s ^ 2) F)
    (fun y => 2 * s * Real.sin (Real.pi * y / F)) W φ hφ
    (by unfold sineGordonPotential; fun_prop) (by fun_prop)
    (fun y => by
      have h1 := ((((hasDerivAt_id' y).const_mul Real.pi).div_const F).cos).const_mul
        (-(2 * s * F / Real.pi))
      exact h1.congr_deriv (by field_simp; try ring))
    (fun y => by
      unfold sineGordonPotential
      have e : 2 * Real.pi * y / F = 2 * (Real.pi * y / F) := by ring
      rw [e, Real.cos_two_mul, Real.cos_sq']
      ring)
    _ _ hb ht
  have e : 8 * sineGordonMass (s ^ 2) F ^ 3 / sineGordonCoupling (s ^ 2) F = W F - W 0 := by
    simp only [W]
    unfold sineGordonMass sineGordonCoupling
    rw [Real.sqrt_sq hs.le, mul_zero, zero_div, Real.cos_zero,
      show Real.pi * F / F = Real.pi by field_simp, Real.cos_pi]
    field_simp
    try ring
  rw [e]
  exact h

theorem solution (lam A F x₀ : ℝ) (hlam : 0 < lam) (hA : 0 < A) (hF : 0 < F) :
    (staticEnergy (phi4Potential lam F) (phi4Kink lam F x₀) =
        ENNReal.ofReal (2 * phi4Mass lam F ^ 3 / lam) ∧
      ∀ φ : ℝ → ℝ, Differentiable ℝ φ →
        Tendsto φ atBot (𝓝 (-F)) → Tendsto φ atTop (𝓝 F) →
        staticEnergy (phi4Potential lam F) (phi4Kink lam F x₀) ≤
          staticEnergy (phi4Potential lam F) φ) ∧
    (staticEnergy (sineGordonPotential A F) (sineGordonKink A F x₀) =
        ENNReal.ofReal (8 * sineGordonMass A F ^ 3 / sineGordonCoupling A F) ∧
      ∀ φ : ℝ → ℝ, Differentiable ℝ φ →
        Tendsto φ atBot (𝓝 0) → Tendsto φ atTop (𝓝 F) →
        staticEnergy (sineGordonPotential A F) (sineGordonKink A F x₀) ≤
          staticEnergy (sineGordonPotential A F) φ) := by
  have e1 := W6_MonopolesInstantonsConfinement_phi4Kink_energy lam F x₀ hlam hF
  have e2 := W6_MonopolesInstantonsConfinement_sineGordonKink_energy A F x₀ hA hF
  refine ⟨⟨e1, fun φ hφ hb ht => ?_⟩, ⟨e2, fun φ hφ hb ht => ?_⟩⟩
  · rw [e1]; exact W6_MonopolesInstantonsConfinement_phi4_bogomolnyi_bound lam F hlam hF φ hφ hb ht
  · rw [e2]; exact W6_MonopolesInstantonsConfinement_sineGordon_bogomolnyi_bound A F hA hF φ hφ hb ht
