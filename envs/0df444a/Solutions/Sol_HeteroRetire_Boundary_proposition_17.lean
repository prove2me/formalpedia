-- Prove2me | solution 1 for HeteroRetire.Boundary.proposition_17
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T03:57:34.296471+00:00
-- url     : https://prove2.me/submissions/f2e3add9-5a65-46e0-8217-6148635ab863

import Mathlib
import Definitions.Def_HeteroRetire_Boundary_Market
import Definitions.Def_HeteroRetire_Boundary_Model

open MeasureTheory ProbabilityTheory Set Filter Topology
open HeteroRetire.Boundary

set_option linter.unusedSectionVars false

namespace HRAux

variable {n : ℕ}

lemma sigma_det_ne {M : Market n} (hM : M.Standing) {t : ℝ} (ht : t ∈ Icc 0 M.Tbar) :
    (M.sigma t).det ≠ 0 := by
  intro hdet
  obtain ⟨C, hC, hell⟩ := hM.elliptic
  have hdetT : ((M.sigma t).transpose).det = 0 := by rw [Matrix.det_transpose]; exact hdet
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  have h1 := (hell t ht z).1
  have hzero : (M.sigma t * (M.sigma t).transpose).mulVec z = 0 := by
    rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  simp only [hzero, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1
  have hpos : 0 < ∑ i, z i * z i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz0
    calc (0:ℝ) < z i * z i := mul_self_pos.mpr hi
      _ ≤ ∑ j, z j * z j :=
        Finset.single_le_sum (f := fun j => z j * z j) (fun j _ => mul_self_nonneg _)
          (Finset.mem_univ i)
  have : 0 < C⁻¹ * ∑ i, z i * z i := mul_pos (inv_pos.mpr hC) hpos
  linarith

lemma theta_eq_inv {M : Market n} (hM : M.Standing) {t : ℝ} (ht : t ∈ Icc 0 M.Tbar) :
    M.theta t = (M.sigma t)⁻¹.mulVec (M.mu t) := by
  rw [← hM.theta_eq t ht, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (sigma_det_ne hM ht)), Matrix.one_mulVec]

lemma theta_contOn {M : Market n} (hM : M.Standing) (i : Fin n) :
    ContinuousOn (fun t => M.theta t i) (Icc 0 M.Tbar) := by
  have hsig : ContinuousOn M.sigma (Icc 0 M.Tbar) := by
    intro t ht
    apply continuousWithinAt_pi.mpr; intro a
    apply continuousWithinAt_pi.mpr; intro b
    exact hM.sigma_cont a b t ht
  have hmu : ContinuousOn M.mu (Icc 0 M.Tbar) := by
    intro t ht
    apply continuousWithinAt_pi.mpr; intro a
    exact hM.mu_cont a t ht
  have hinv : ContinuousOn (fun t => (M.sigma t)⁻¹) (Icc 0 M.Tbar) := by
    intro t ht
    have hc : ContinuousAt Inv.inv (M.sigma t) := by
      apply continuousAt_matrix_inv
      have : (Ring.inverse : ℝ → ℝ) = Inv.inv := by
        funext x; exact Ring.inverse_eq_inv x
      rw [this]
      exact continuousAt_inv₀ (sigma_det_ne hM ht)
    exact hc.comp_continuousWithinAt (hsig t ht)
  have hv : ContinuousOn (fun t => (M.sigma t)⁻¹.mulVec (M.mu t)) (Icc 0 M.Tbar) := by
    intro t ht
    apply continuousWithinAt_pi.mpr; intro a
    simp only [Matrix.mulVec, dotProduct]
    apply tendsto_finsetSum
    intro b _
    have h1 : ContinuousWithinAt (fun t => (M.sigma t)⁻¹ a b) (Icc 0 M.Tbar) t :=
      (continuousWithinAt_pi.mp (continuousWithinAt_pi.mp (hinv t ht) a)) b
    have h2 : ContinuousWithinAt (fun t => M.mu t b) (Icc 0 M.Tbar) t :=
      continuousWithinAt_pi.mp (hmu t ht) b
    exact h1.mul h2
  refine ContinuousOn.congr (f := fun t => (M.sigma t)⁻¹.mulVec (M.mu t) i) ?_ ?_
  · intro t ht; exact continuousWithinAt_pi.mp (hv t ht) i
  · intro t ht; simp [theta_eq_inv hM ht]

lemma var_contOn {M : Market n} (hM : M.Standing) :
    ContinuousOn (varianceRate M) (Icc 0 M.Tbar) := by
  unfold varianceRate
  exact continuousOn_finsetSum _ fun i _ => (theta_contOn hM i).pow 2


/-- the variance of `Z u - Z t` -/
noncomputable def sig2 (M : Market n) (t u : ℝ) : ℝ :=
  ((∫ v in t..u, varianceRate M v).toNNReal : ℝ)

lemma expZ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝔽 : Filtration ℝ ‹MeasurableSpace Ω›} {M : Market n} {Z : ℝ → Ω → ℝ}
    (hZ : IsDualNoise P 𝔽 M Z) {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) (hu : u ≤ M.Tbar) :
    Integrable (fun ω => Real.exp (-(Z u ω - Z t ω))) P ∧
      ∫ ω, Real.exp (-(Z u ω - Z t ω)) ∂P = Real.exp (sig2 M t u / 2) := by
  have hX := hZ.law t u ht htu hu
  have hm := mgf_gaussianReal hX (-1)
  have hfun : (fun ω => Real.exp (-(Z u ω - Z t ω))) =
      fun ω => Real.exp ((-1) * (Z u ω - Z t ω)) := by
    funext ω; ring_nf
  refine ⟨?_, ?_⟩
  · rw [hfun]
    apply mgf_pos_iff.mp
    rw [hm]; positivity
  · rw [hfun]
    have : mgf (fun ω => Z u ω - Z t ω) P (-1) = ∫ ω, Real.exp ((-1) * (Z u ω - Z t ω)) ∂P := rfl
    rw [← this, hm, sig2]
    congr 1; ring

lemma measurable_Z {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝔽 : Filtration ℝ ‹MeasurableSpace Ω›} {M : Market n} {Z : ℝ → Ω → ℝ}
    (hZ : IsDualNoise P 𝔽 M Z) (u : ℝ) : Measurable (Z u) :=
  hZ.jointly_measurable.comp (measurable_const.prodMk measurable_id)

lemma dualY_eq {Ω : Type*} (M : Market n) (Z : ℝ → Ω → ℝ) (t y u : ℝ) (ω : Ω) :
    dualY M Z t y u ω = y * Real.exp (∫ s in t..u, (M.rho s - M.r s - varianceRate M s / 2)) *
      Real.exp (-(Z u ω - Z t ω)) := by
  rw [dualY, sub_eq_add_neg _ (Z u ω - Z t ω), Real.exp_add]; ring

lemma drift_contOn {M : Market n} (hM : M.Standing) :
    ContinuousOn (fun s => M.rho s - M.r s - varianceRate M s / 2) (Icc 0 M.Tbar) :=
  ((hM.rho_regular.2.1.sub hM.r_regular.2.1).sub ((var_contOn hM).div_const 2))

lemma prim_contOn {f : ℝ → ℝ} {Tb : ℝ} (hf : ContinuousOn f (Icc 0 Tb)) {t : ℝ}
    (ht : t ∈ Icc 0 Tb) : ContinuousOn (fun u => ∫ s in t..u, f s) (Icc 0 Tb) := by
  have h0 : 0 ≤ Tb := ht.1.trans ht.2
  have hI : IntervalIntegrable f volume 0 Tb :=
    (hf.mono (by rw [uIcc_of_le h0])).intervalIntegrable
  have := intervalIntegral.continuousOn_primitive_interval' hI (by rw [uIcc_of_le h0]; exact ht)
  rwa [uIcc_of_le h0] at this

lemma Fint_contOn {M : Market n} (hM : M.Standing) {t : ℝ} (ht : t ∈ Icc 0 M.Tbar) :
    ContinuousOn (fun u => ∫ s in t..u, (M.rho s - M.r s - varianceRate M s / 2))
      (Icc 0 M.Tbar) := prim_contOn (drift_contOn hM) ht

lemma sig2_contOn {M : Market n} (hM : M.Standing) {t : ℝ} (ht : t ∈ Icc 0 M.Tbar) :
    ContinuousOn (sig2 M t) (Icc 0 M.Tbar) := by
  unfold sig2
  exact NNReal.continuous_coe.comp_continuousOn
    (continuous_real_toNNReal.comp_continuousOn (prim_contOn (var_contOn hM) ht))

lemma disc_contOn {M : Market n} (hM : M.Standing) : ContinuousOn (disc M) (Icc 0 M.Tbar) := by
  unfold disc
  have h0 : (0:ℝ) ∈ Icc 0 M.Tbar := ⟨le_rfl, hM.T_pos.le.trans hM.T_lt.le⟩
  exact Real.continuous_exp.comp_continuousOn (prim_contOn hM.rho_regular.2.1 h0).neg

/-- Product integrability of `c(u) * Y_u(ω)` on `[t,s] × Ω`. -/
lemma prodInt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝔽 : Filtration ℝ ‹MeasurableSpace Ω›} {M : Market n} (hM : M.Standing) {Z : ℝ → Ω → ℝ}
    (hZ : IsDualNoise P 𝔽 M Z) {c : ℝ → ℝ} (hc : ContinuousOn c (Icc 0 M.Tbar))
    {t s y : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) (hs : s ≤ M.Tbar) :
    Integrable (Function.uncurry fun u ω => c u * dualY M Z t y u ω)
      ((volume.restrict (Ioc t s)).prod P) := by
  have htm : t ∈ Icc 0 M.Tbar := ⟨ht, hts.trans hs⟩
  have hsub : Icc t s ⊆ Icc 0 M.Tbar := Icc_subset_Icc ht hs
  set a : ℝ → ℝ := fun u => c u * (y * Real.exp
    (∫ s in t..u, (M.rho s - M.r s - varianceRate M s / 2))) with ha_def
  have ha : ContinuousOn a (Icc 0 M.Tbar) :=
    hc.mul (continuousOn_const.mul (Real.continuous_exp.comp_continuousOn (Fint_contOn hM htm)))
  have hfeq : (Function.uncurry fun u ω => c u * dualY M Z t y u ω) =
      fun p : ℝ × Ω => a p.1 * Real.exp (-(Z p.1 p.2 - Z t p.2)) := by
    funext p; simp only [Function.uncurry, dualY_eq, ha_def]; ring
  rw [hfeq]
  have hZm : Measurable fun p : ℝ × Ω => Real.exp (-(Z p.1 p.2 - Z t p.2)) := by
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.sub hZ.jointly_measurable
    exact (measurable_Z hZ t).comp measurable_snd
  have haeas : AEStronglyMeasurable a (volume.restrict (Ioc t s)) :=
    (ha.mono (Ioc_subset_Icc_self.trans hsub)).aestronglyMeasurable measurableSet_Ioc
  have hmeas : AEStronglyMeasurable (fun p : ℝ × Ω => a p.1 * Real.exp (-(Z p.1 p.2 - Z t p.2)))
      ((volume.restrict (Ioc t s)).prod P) :=
    (haeas.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
      hZm.aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  refine ⟨?_, ?_⟩
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with u hu
    exact (expZ hZ ht hu.1.le (hu.2.trans hs)).1.const_mul (a u)
  · have hcont : ContinuousOn (fun u => |a u| * Real.exp (sig2 M t u / 2)) (Icc t s) :=
      ((ha.mono hsub).abs).mul (Real.continuous_exp.comp_continuousOn
        (((sig2_contOn hM htm).mono hsub).div_const 2))
    have hI : IntegrableOn (fun u => |a u| * Real.exp (sig2 M t u / 2)) (Ioc t s) :=
      (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    refine (hI.congr_fun ?_ measurableSet_Ioc)
    intro u hu
    simp only [norm_mul, Real.norm_eq_abs, Real.abs_exp]
    rw [integral_const_mul, (expZ hZ ht hu.1.le (hu.2.trans hs)).2]

/-- Expectation of `c(u) * Y_u`. -/
lemma expect_Y {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝔽 : Filtration ℝ ‹MeasurableSpace Ω›} {M : Market n} {Z : ℝ → Ω → ℝ}
    (hZ : IsDualNoise P 𝔽 M Z) (c : ℝ → ℝ)
    {t u y : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) (hu : u ≤ M.Tbar) :
    ∫ ω, c u * dualY M Z t y u ω ∂P = c u * (y * Real.exp
      (∫ s in t..u, (M.rho s - M.r s - varianceRate M s / 2))) * Real.exp (sig2 M t u / 2) := by
  simp only [dualY_eq]
  rw [← (expZ hZ ht htu hu).2, ← integral_const_mul]
  congr 1; funext ω; ring


section Core

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝔽 : Filtration ℝ ‹MeasurableSpace Ω›} {M : Market n} {Z : ℝ → Ω → ℝ}

lemma dualY_scale (t y u : ℝ) (ω : Ω) : dualY M Z t y u ω = y * dualY M Z t 1 u ω := by
  simp [dualY]

lemma dualY_pos {t y u : ℝ} (hy : 0 < y) (ω : Ω) : 0 < dualY M Z t y u ω := by
  unfold dualY; positivity

lemma Y_contOn (hM : M.Standing) (hZ : IsDualNoise P 𝔽 M Z) {t : ℝ} (ht : t ∈ Icc 0 M.Tbar)
    (y : ℝ) (ω : Ω) : ContinuousOn (fun u => dualY M Z t y u ω) (Icc 0 M.Tbar) := by
  unfold dualY
  apply continuousOn_const.mul
  apply Real.continuous_exp.comp_continuousOn
  apply (Fint_contOn hM ht).sub
  exact ((hZ.continuous ω).sub continuous_const).continuousOn

noncomputable def Aint (M : Market n) (Z : ℝ → Ω → ℝ) (t : ℝ) (τ : Ω → ℝ) (ω : Ω) : ℝ :=
  ∫ u in t..τ ω, disc M u * M.I u * dualY M Z t 1 u ω

noncomputable def Bint (M : Market n) (t s : ℝ) : ℝ :=
  ∫ u in t..s, disc M u * M.L u

lemma dI_contOn (hM : M.Standing) : ContinuousOn (fun u => disc M u * M.I u) (Icc 0 M.Tbar) :=
  (disc_contOn hM).mul hM.I_regular.2.1

lemma dL_contOn (hM : M.Standing) : ContinuousOn (fun u => disc M u * M.L u) (Icc 0 M.Tbar) :=
  (disc_contOn hM).mul hM.L_regular.2.1

lemma payoff_eq (hM : M.Standing) (hZ : IsDualNoise P 𝔽 M Z) {t y : ℝ} {τ : Ω → ℝ} {ω : Ω}
    (ht : 0 ≤ t) (h1 : t ≤ τ ω) (h2 : τ ω ≤ M.Tbar) :
    payoff M Z t y τ ω = y * Aint M Z t τ ω - Bint M t (τ ω) := by
  have htm : t ∈ Icc 0 M.Tbar := ⟨ht, h1.trans h2⟩
  have hsub : uIcc t (τ ω) ⊆ Icc 0 M.Tbar := by
    rw [uIcc_of_le h1]; exact Icc_subset_Icc ht h2
  have hA : IntervalIntegrable (fun u => disc M u * M.I u * dualY M Z t 1 u ω) volume t (τ ω) :=
    (((dI_contOn hM).mul (Y_contOn hM hZ htm 1 ω)).mono hsub).intervalIntegrable
  have hB : IntervalIntegrable (fun u => disc M u * M.L u) volume t (τ ω) :=
    ((dL_contOn hM).mono hsub).intervalIntegrable
  unfold payoff Aint Bint
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (hA.const_mul y) hB]
  congr 1; funext u
  rw [dualY_scale (M := M) (Z := Z) t y u ω]; ring

lemma Aint_nonneg (hM : M.Standing) {t : ℝ} {τ : Ω → ℝ} {ω : Ω}
    (ht : 0 ≤ t) (h1 : t ≤ τ ω) (h2 : τ ω ≤ M.Tbar) : 0 ≤ Aint M Z t τ ω := by
  unfold Aint
  apply intervalIntegral.integral_nonneg h1
  intro u hu
  have hu' : u ∈ Icc 0 M.Tbar := ⟨ht.trans hu.1, hu.2.trans h2⟩
  have := hM.I_regular.1 u hu'
  have : 0 < disc M u := by unfold disc; positivity
  have := dualY_pos (M := M) (Z := Z) (t := t) (u := u) one_pos ω
  positivity

lemma Bint_nonneg (hM : M.Standing) {t s : ℝ} (ht : 0 ≤ t) (h1 : t ≤ s) (h2 : s ≤ M.Tbar) :
    0 ≤ Bint M t s := by
  unfold Bint
  apply intervalIntegral.integral_nonneg h1
  intro u hu
  have hu' : u ∈ Icc 0 M.Tbar := ⟨ht.trans hu.1, hu.2.trans h2⟩
  have := hM.L_regular.1 u hu'
  have : 0 < disc M u := by unfold disc; positivity
  positivity

lemma tau_meas {t : ℝ} {τ : Ω → ℝ} (h : IsAdmissible 𝔽 M t τ) : Measurable τ := by
  apply measurable_of_Iic
  intro s
  have := 𝔽.le s _ (h.1 s)
  convert this using 1
  ext ω; simp

lemma Bint_tau_int (hM : M.Standing) {t : ℝ} (ht : t ∈ Icc 0 M.T) {τ : Ω → ℝ}
    (h : IsAdmissible 𝔽 M t τ) : Integrable (fun ω => Bint M t (τ ω)) P := by
  have hTb : M.T ≤ M.Tbar := hM.T_lt.le
  have htm : t ∈ Icc 0 M.Tbar := ⟨ht.1, ht.2.trans hTb⟩
  have hB : ContinuousOn (fun s => Bint M t s) (Icc 0 M.Tbar) := prim_contOn (dL_contOn hM) htm
  set cl : ℝ → ℝ := fun s => max t (min M.T s) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
  have hclm : ∀ s, cl s ∈ Icc 0 M.Tbar := fun s =>
    ⟨ht.1.trans (le_max_left _ _), max_le (ht.2.trans hTb) ((min_le_left _ _).trans hTb)⟩
  have hg : Continuous fun s => Bint M t (cl s) := hB.comp_continuous hclc hclm
  have heq : (fun ω => Bint M t (τ ω)) = fun ω => Bint M t (cl (τ ω)) := by
    funext ω
    have h1 := (h.2 ω).1; have h2 := (h.2 ω).2
    simp only [hcl, min_eq_right h2, max_eq_right h1]
  rw [heq]
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := M.Tbar)).exists_bound_of_continuousOn hB
  refine Integrable.of_bound (hg.measurable.comp (tau_meas h)).aestronglyMeasurable C ?_
  filter_upwards with ω
  exact hC _ (hclm _)

lemma G_int (hM : M.Standing) (hZ : IsDualNoise P 𝔽 M Z) {t : ℝ} (ht : t ∈ Icc 0 M.T) :
    Integrable (fun ω => ∫ u in t..M.T, disc M u * M.I u * dualY M Z t 1 u ω) P := by
  have h := (prodInt (P := P) hM hZ (dI_contOn hM) (y := 1) ht.1 ht.2 hM.T_lt.le).integral_prod_right
  refine h.congr ?_
  filter_upwards with ω
  simp only [Function.uncurry]
  rw [intervalIntegral.integral_of_le ht.2]

lemma Aint_le_G (hM : M.Standing) {t : ℝ} {τ : Ω → ℝ} {ω : Ω} (hZ : IsDualNoise P 𝔽 M Z)
    (ht : 0 ≤ t) (h1 : t ≤ τ ω) (h2 : τ ω ≤ M.T) :
    Aint M Z t τ ω ≤ ∫ u in t..M.T, disc M u * M.I u * dualY M Z t 1 u ω := by
  have hTb : M.T ≤ M.Tbar := hM.T_lt.le
  have htm : t ∈ Icc 0 M.Tbar := ⟨ht, (h1.trans h2).trans hTb⟩
  unfold Aint
  apply intervalIntegral.integral_mono_interval le_rfl h1 h2
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with u hu
    have hu' : u ∈ Icc 0 M.Tbar := ⟨ht.trans hu.1.le, hu.2.trans hTb⟩
    have := hM.I_regular.1 u hu'
    have : 0 < disc M u := by unfold disc; positivity
    have := dualY_pos (M := M) (Z := Z) (t := t) (u := u) one_pos ω
    simp only [Pi.zero_apply]; positivity
  · have hsub : uIcc t M.T ⊆ Icc 0 M.Tbar := by
      rw [uIcc_of_le (h1.trans h2)]; exact Icc_subset_Icc ht hTb
    exact (((dI_contOn hM).mul (Y_contOn hM hZ htm 1 ω)).mono hsub).intervalIntegrable

lemma Aint_int (hM : M.Standing) (hZ : IsDualNoise P 𝔽 M Z) {t y : ℝ} (ht : t ∈ Icc 0 M.T)
    (hy : 0 < y) {τ : Ω → ℝ} (h : IsAdmissible 𝔽 M t τ) (hi : Integrable (payoff M Z t y τ) P) :
    Integrable (Aint M Z t τ) P := by
  have := (hi.add (Bint_tau_int hM ht h)).div_const y
  refine this.congr ?_
  filter_upwards with ω
  simp only [Pi.add_apply]
  rw [payoff_eq hM hZ ht.1 (h.2 ω).1 ((h.2 ω).2.trans hM.T_lt.le)]
  field_simp; ring

lemma payoff_int (hM : M.Standing) (hZ : IsDualNoise P 𝔽 M Z) {t : ℝ} (ht : t ∈ Icc 0 M.T)
    (y : ℝ) {τ : Ω → ℝ} (h : IsAdmissible 𝔽 M t τ) (hA : Integrable (Aint M Z t τ) P) :
    Integrable (payoff M Z t y τ) P ∧
      ∫ ω, payoff M Z t y τ ω ∂P = y * ∫ ω, Aint M Z t τ ω ∂P - ∫ ω, Bint M t (τ ω) ∂P := by
  have hB := Bint_tau_int (P := P) hM ht h
  have heq : payoff M Z t y τ = fun ω => y * Aint M Z t τ ω - Bint M t (τ ω) := by
    funext ω; exact payoff_eq hM hZ ht.1 (h.2 ω).1 ((h.2 ω).2.trans hM.T_lt.le)
  rw [heq]
  exact ⟨(hA.const_mul y).sub hB, by rw [integral_sub (hA.const_mul y) hB, integral_const_mul]⟩

/-- the set whose supremum is `Wdual` -/
def Sset (P : Measure Ω) (𝔽 : Filtration ℝ ‹MeasurableSpace Ω›) (M : Market n)
    (Z : ℝ → Ω → ℝ) (t y : ℝ) : Set ℝ :=
  {v : ℝ | ∃ τ : Ω → ℝ, IsAdmissible 𝔽 M t τ ∧ Integrable (payoff M Z t y τ) P ∧
    v = ∫ ω, payoff M Z t y τ ω ∂P}

lemma Wdual_eq (t y : ℝ) : Wdual P 𝔽 M Z t y = sSup (Sset P 𝔽 M Z t y) := rfl

lemma zero_mem {t y : ℝ} (ht : t ≤ M.T) : (0:ℝ) ∈ Sset P 𝔽 M Z t y := by
  have h0 : payoff M Z t y (fun _ => t) = fun _ => 0 := by
    funext ω; simp [payoff]
  refine ⟨fun _ => t, ⟨isStoppingTime_const 𝔽 t, fun _ => ⟨le_rfl, ht⟩⟩, ?_, ?_⟩
  · rw [h0]; exact integrable_zero _ _ _
  · rw [h0]; simp

lemma S_bdd (hM : M.Standing) (hZ : IsDualNoise P 𝔽 M Z) {t y : ℝ} (ht : t ∈ Icc 0 M.T)
    (hy : 0 < y) : BddAbove (Sset P 𝔽 M Z t y) := by
  refine ⟨y * ∫ ω, (∫ u in t..M.T, disc M u * M.I u * dualY M Z t 1 u ω) ∂P, ?_⟩
  rintro v ⟨τ, hτ, hi, rfl⟩
  rw [← integral_const_mul]
  apply integral_mono hi ((G_int hM hZ ht).const_mul y)
  intro ω
  have h1 := (hτ.2 ω).1; have h2 := (hτ.2 ω).2
  rw [payoff_eq hM hZ ht.1 h1 (h2.trans hM.T_lt.le)]
  have := Bint_nonneg hM ht.1 h1 (h2.trans hM.T_lt.le)
  have := Aint_le_G hM hZ (ω := ω) ht.1 h1 h2
  have := mul_le_mul_of_nonneg_left this hy.le
  linarith

lemma W_nonneg (hM : M.Standing) (hZ : IsDualNoise P 𝔽 M Z) {t y : ℝ} (ht : t ∈ Icc 0 M.T)
    (hy : 0 < y) : 0 ≤ Wdual P 𝔽 M Z t y :=
  le_csSup (S_bdd hM hZ ht hy) (zero_mem ht.2)

lemma le_W (hM : M.Standing) (hZ : IsDualNoise P 𝔽 M Z) {t y : ℝ} (ht : t ∈ Icc 0 M.T)
    (hy : 0 < y) {τ : Ω → ℝ} (h : IsAdmissible 𝔽 M t τ) (hi : Integrable (payoff M Z t y τ) P) :
    ∫ ω, payoff M Z t y τ ω ∂P ≤ Wdual P 𝔽 M Z t y :=
  le_csSup (S_bdd hM hZ ht hy) ⟨τ, h, hi, rfl⟩

lemma W_mono (hM : M.Standing) (hZ : IsDualNoise P 𝔽 M Z) {t y₁ y₂ : ℝ} (ht : t ∈ Icc 0 M.T)
    (hy : 0 < y₁) (hle : y₁ ≤ y₂) : Wdual P 𝔽 M Z t y₁ ≤ Wdual P 𝔽 M Z t y₂ := by
  rw [Wdual_eq t y₁]
  apply csSup_le ⟨0, zero_mem ht.2⟩
  rintro v ⟨τ, hτ, hi, rfl⟩
  have hA := Aint_int hM hZ ht hy hτ hi
  have e1 := (payoff_int (P := P) hM hZ ht y₁ hτ hA).2
  have h2 := payoff_int (P := P) hM hZ ht y₂ hτ hA
  have hEA : 0 ≤ ∫ ω, Aint M Z t τ ω ∂P := integral_nonneg fun ω =>
    Aint_nonneg hM ht.1 (hτ.2 ω).1 ((hτ.2 ω).2.trans hM.T_lt.le)
  have := le_W hM hZ ht (hy.trans_le hle) hτ h2.1
  rw [h2.2] at this
  rw [e1]
  nlinarith

lemma W_open (hM : M.Standing) (hZ : IsDualNoise P 𝔽 M Z) {t y : ℝ} (ht : t ∈ Icc 0 M.T)
    (hy : 0 < y) (hW : 0 < Wdual P 𝔽 M Z t y) :
    ∃ y', 0 < y' ∧ y' < y ∧ 0 < Wdual P 𝔽 M Z t y' := by
  rw [Wdual_eq] at hW
  obtain ⟨v, ⟨τ, hτ, hi, rfl⟩, hv⟩ := exists_lt_of_lt_csSup ⟨0, zero_mem ht.2⟩ hW
  have hA := Aint_int hM hZ ht hy hτ hi
  have e1 := (payoff_int (P := P) hM hZ ht y hτ hA).2
  have hEA : 0 ≤ ∫ ω, Aint M Z t τ ω ∂P := integral_nonneg fun ω =>
    Aint_nonneg hM ht.1 (hτ.2 ω).1 ((hτ.2 ω).2.trans hM.T_lt.le)
  have hEB : 0 ≤ ∫ ω, Bint M t (τ ω) ∂P := integral_nonneg fun ω =>
    Bint_nonneg hM ht.1 (hτ.2 ω).1 ((hτ.2 ω).2.trans hM.T_lt.le)
  set EA := ∫ ω, Aint M Z t τ ω ∂P
  set EB := ∫ ω, Bint M t (τ ω) ∂P
  set V := ∫ ω, payoff M Z t y τ ω ∂P
  set y' := y - V / (2 * (EA + 1)) with hy'
  have hpos : 0 < 2 * (EA + 1) := by linarith
  have hVle : V ≤ y * EA := by rw [e1]; linarith
  have hfrac : V / (2 * (EA + 1)) < y / 2 := by
    rw [div_lt_iff₀ hpos]; nlinarith
  have hfrac0 : 0 < V / (2 * (EA + 1)) := div_pos hv hpos
  have hy'pos : 0 < y' := by rw [hy']; linarith
  have h2 := payoff_int (P := P) hM hZ ht y' hτ hA
  refine ⟨y', hy'pos, by rw [hy']; linarith, ?_⟩
  have := le_W hM hZ ht hy'pos hτ h2.1
  rw [h2.2] at this
  have key : y' * EA - EB = V - V * EA / (2 * (EA + 1)) := by
    rw [hy', e1]; field_simp; ring
  have hlt : V * EA / (2 * (EA + 1)) < V := by
    rw [div_lt_iff₀ hpos]; nlinarith
  linarith

lemma b_le_of {t y : ℝ} (hy : 0 < y) (hW : 0 < Wdual P 𝔽 M Z t y) :
    bdry P 𝔽 M Z t ≤ (y : EReal) :=
  sInf_le ⟨y, ⟨hy, hW⟩, rfl⟩

lemma le_b_of {t y : ℝ} (h : ∀ y', 0 < y' → 0 < Wdual P 𝔽 M Z t y' → y ≤ y') :
    (y : EReal) ≤ bdry P 𝔽 M Z t := by
  apply le_sInf
  rintro _ ⟨y', ⟨h1, h2⟩, rfl⟩
  exact EReal.coe_le_coe_iff.mpr (h y' h1 h2)

lemma lt_of_b_lt {t y : ℝ} (h : bdry P 𝔽 M Z t < (y : EReal)) :
    ∃ y', 0 < y' ∧ 0 < Wdual P 𝔽 M Z t y' ∧ y' < y := by
  obtain ⟨_, ⟨y', ⟨h1, h2⟩, rfl⟩, h3⟩ := sInf_lt_iff.mp h
  exact ⟨y', h1, h2, EReal.coe_lt_coe_iff.mp h3⟩

lemma W_eq_zero_iff (hM : M.Standing) (hZ : IsDualNoise P 𝔽 M Z) {t y : ℝ}
    (ht : t ∈ Icc 0 M.T) (hy : 0 < y) :
    Wdual P 𝔽 M Z t y = 0 ↔ (y : EReal) ≤ bdry P 𝔽 M Z t := by
  constructor
  · intro h0
    apply le_b_of
    intro y' hy' hW'
    by_contra hlt
    have := W_mono hM hZ ht hy' (not_le.mp hlt).le
    linarith
  · intro hle
    rcases (W_nonneg hM hZ ht hy).lt_or_eq with hlt | heq
    · obtain ⟨y', hy', hy'y, hW'⟩ := W_open hM hZ ht hy hlt
      have := (b_le_of hy' hW').trans_lt (EReal.coe_lt_coe_iff.mpr hy'y)
      exact absurd (hle.trans_lt this) (lt_irrefl _)
    · exact heq.symm

lemma W_pos_iff (hM : M.Standing) (hZ : IsDualNoise P 𝔽 M Z) {t y : ℝ}
    (ht : t ∈ Icc 0 M.T) (hy : 0 < y) :
    0 < Wdual P 𝔽 M Z t y ↔ bdry P 𝔽 M Z t < (y : EReal) := by
  constructor
  · intro hW
    obtain ⟨y', hy', hy'y, hW'⟩ := W_open hM hZ ht hy hW
    exact (b_le_of hy' hW').trans_lt (EReal.coe_lt_coe_iff.mpr hy'y)
  · intro h
    obtain ⟨y', h1, h2, h3⟩ := lt_of_b_lt h
    exact h2.trans_le (W_mono hM hZ ht h1 h3.le)

lemma W_pos_of_gt (hM : M.Standing) (hZ : IsDualNoise P 𝔽 M Z) {t y : ℝ} (ht : t ∈ Ico 0 M.T)
    (hy : M.L t / M.I t < y) : 0 < Wdual P 𝔽 M Z t y := by
  have hTb : M.T ≤ M.Tbar := hM.T_lt.le
  have htm : t ∈ Icc 0 M.Tbar := ⟨ht.1, ht.2.le.trans hTb⟩
  have hIt := hM.I_regular.1 t htm
  have hLt := hM.L_regular.1 t htm
  have hypos : 0 < y := lt_trans (div_pos hLt hIt) hy
  have hyI : M.L t < y * M.I t := by rwa [div_lt_iff₀ hIt] at hy
  set F : ℝ → ℝ := fun u => ∫ s in t..u, (M.rho s - M.r s - varianceRate M s / 2) with hF
  set φ : ℝ → ℝ := fun u => y * (disc M u * M.I u) * Real.exp (F u) - disc M u * M.L u with hφ
  have hφc : ContinuousOn φ (Icc 0 M.Tbar) :=
    ((continuousOn_const.mul (dI_contOn hM)).mul
      (Real.continuous_exp.comp_continuousOn (Fint_contOn hM htm))).sub (dL_contOn hM)
  have hφt : 0 < φ t := by
    have hd : 0 < disc M t := by unfold disc; positivity
    simp only [hφ, hF, intervalIntegral.integral_same, Real.exp_zero, mul_one]
    nlinarith
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp (hφc t htm) (φ t / 2) (by linarith)
  set s := min (t + δ / 2) M.T with hs
  have hts : t < s := lt_min (by linarith) ht.2
  have hsT : s ≤ M.T := min_le_right _ _
  have hsTb : s ≤ M.Tbar := hsT.trans hTb
  have hφpos : ∀ u ∈ Icc t s, 0 < φ u := by
    intro u hu
    have hu' : u ∈ Icc 0 M.Tbar := ⟨ht.1.trans hu.1, hu.2.trans hsTb⟩
    have hdist : dist u t < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
      have := hu.2; have := min_le_left (t + δ / 2) M.T; linarith
    have := hball hu' hdist
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).1
    linarith
  -- the constant stopping time
  set τ : Ω → ℝ := fun _ => s
  have hτ : IsAdmissible 𝔽 M t τ := ⟨isStoppingTime_const 𝔽 s, fun _ => ⟨hts.le, hsT⟩⟩
  have hprod := prodInt (P := P) hM hZ (dI_contOn hM) (y := 1) ht.1 hts.le hsTb
  have hA : Integrable (Aint M Z t τ) P := by
    refine hprod.integral_prod_right.congr ?_
    filter_upwards with ω
    simp only [Function.uncurry, Aint, τ]
    rw [intervalIntegral.integral_of_le hts.le]
  have hEA : ∫ ω, Aint M Z t τ ω ∂P = ∫ u in t..s, disc M u * M.I u * (1 * Real.exp (F u)) *
      Real.exp (sig2 M t u / 2) := by
    simp only [Aint, τ]
    rw [← intervalIntegral_integral_swap (by rw [uIoc_of_le hts.le]; exact hprod)]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hts.le] at hu
    exact expect_Y hZ (fun u => disc M u * M.I u) ht.1 hu.1 (hu.2.trans hsTb)
  have h2 := payoff_int (P := P) hM hZ ⟨ht.1, ht.2.le⟩ y hτ hA
  have hle := le_W hM hZ ⟨ht.1, ht.2.le⟩ hypos hτ h2.1
  rw [h2.2, hEA] at hle
  simp only [τ, integral_const, probReal_univ, one_smul, Bint] at hle
  set ψ : ℝ → ℝ := fun u => y * (disc M u * M.I u * (1 * Real.exp (F u)) *
      Real.exp (sig2 M t u / 2)) - disc M u * M.L u with hψ
  have hsub : uIcc t s ⊆ Icc 0 M.Tbar := by
    rw [uIcc_of_le hts.le]; exact Icc_subset_Icc ht.1 hsTb
  have hψc : ContinuousOn ψ (Icc 0 M.Tbar) :=
    (continuousOn_const.mul (((dI_contOn hM).mul (continuousOn_const.mul
      (Real.continuous_exp.comp_continuousOn (Fint_contOn hM htm)))).mul
      (Real.continuous_exp.comp_continuousOn ((sig2_contOn hM htm).div_const 2)))).sub
      (dL_contOn hM)
  have hψi : IntervalIntegrable ψ volume t s := (hψc.mono hsub).intervalIntegrable
  have hpos : 0 < ∫ u in t..s, ψ u := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hψi _ hts
    intro u hu
    have hφu := hφpos u (Ioo_subset_Icc_self hu)
    have hu' : u ∈ Icc 0 M.Tbar := ⟨ht.1.trans hu.1.le, hu.2.le.trans hsTb⟩
    have hsg : 0 ≤ sig2 M t u := by unfold sig2; exact NNReal.coe_nonneg _
    have he : 1 ≤ Real.exp (sig2 M t u / 2) := Real.one_le_exp (by linarith)
    have hd : 0 < disc M u := by unfold disc; positivity
    have hI := hM.I_regular.1 u hu'
    have hpos2 : 0 < y * (disc M u * M.I u) * Real.exp (F u) := by positivity
    simp only [hψ]; simp only [hφ] at hφu
    nlinarith
  have hsplit : ∫ u in t..s, ψ u = y * (∫ u in t..s, disc M u * M.I u * (1 * Real.exp (F u)) *
      Real.exp (sig2 M t u / 2)) - ∫ u in t..s, disc M u * M.L u := by
    simp only [hψ]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul]
    · exact (hψi.add (((dL_contOn hM).mono hsub).intervalIntegrable)).congr (by
        intro u _; simp [hψ])
    · exact ((dL_contOn hM).mono hsub).intervalIntegrable
  linarith

lemma prop17_aux (hM : M.Standing) (hZ : IsDualNoise P 𝔽 M Z) {t : ℝ} (ht : t ∈ Ico 0 M.T) :
    bdry P 𝔽 M Z t ≤ ((M.L t / M.I t : ℝ) : EReal) := by
  have htm : t ∈ Icc 0 M.Tbar := ⟨ht.1, ht.2.le.trans hM.T_lt.le⟩
  have hpos : 0 < M.L t / M.I t := div_pos (hM.L_regular.1 t htm) (hM.I_regular.1 t htm)
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  induction c using EReal.rec with
  | bot => exact absurd hc (not_lt.mpr bot_le)
  | top => exact le_top
  | coe c =>
    have hc' : M.L t / M.I t < c := EReal.coe_lt_coe_iff.mp hc
    exact b_le_of (hpos.trans hc') (W_pos_of_gt hM hZ ht hc')

lemma Aint_int' (hM : M.Standing) (hZ : IsDualNoise P 𝔽 M Z) {t : ℝ} (ht : t ∈ Icc 0 M.T)
    {τ : Ω → ℝ} (h : IsAdmissible 𝔽 M t τ) : Integrable (Aint M Z t τ) P := by
  have hprod := prodInt (P := P) hM hZ (dI_contOn hM) (y := 1) ht.1 ht.2 hM.T_lt.le
  set f := Function.uncurry fun u ω => disc M u * M.I u * dualY M Z t 1 u ω with hf
  have hmeasS : MeasurableSet {p : ℝ × Ω | p.1 ≤ τ p.2} :=
    measurableSet_le measurable_fst ((tau_meas h).comp measurable_snd)
  have hg : AEStronglyMeasurable ({p : ℝ × Ω | p.1 ≤ τ p.2}.indicator f)
      ((volume.restrict (Ioc t M.T)).prod P) :=
    hprod.aestronglyMeasurable.indicator hmeasS
  have hmeas : AEStronglyMeasurable (Aint M Z t τ) P := by
    refine (hg.prod_swap.integral_prod_right').congr ?_
    filter_upwards with ω
    have h1 := (h.2 ω).1; have h2 := (h.2 ω).2
    have : (fun u => (({p : ℝ × Ω | p.1 ≤ τ p.2}.indicator f) ∘ Prod.swap) (ω, u)) =
        (Iic (τ ω)).indicator (fun u => disc M u * M.I u * dualY M Z t 1 u ω) := by
      funext u
      simp only [Function.comp, Prod.swap, indicator, mem_setOf_eq, mem_Iic, hf, Function.uncurry]
    change ∫ u, (({p : ℝ × Ω | p.1 ≤ τ p.2}.indicator f) ∘ Prod.swap) (ω, u)
      ∂(volume.restrict (Ioc t M.T)) = _
    rw [this]
    have hset : Ioc t M.T ∩ Iic (τ ω) = Ioc t (τ ω) := by
      ext u
      simp only [mem_inter_iff, mem_Ioc, mem_Iic]
      constructor
      · rintro ⟨⟨a, _⟩, c⟩; exact ⟨a, c⟩
      · rintro ⟨a, c⟩; exact ⟨⟨a, c.trans h2⟩, c⟩
    rw [setIntegral_indicator measurableSet_Iic, Aint, intervalIntegral.integral_of_le h1, hset]
  refine (G_int hM hZ ht).mono' hmeas ?_
  filter_upwards with ω
  have h1 := (h.2 ω).1; have h2 := (h.2 ω).2
  rw [Real.norm_eq_abs, abs_of_nonneg (Aint_nonneg hM ht.1 h1 (h2.trans hM.T_lt.le))]
  exact Aint_le_G hM hZ ht.1 h1 h2

end Core

end HRAux

open MeasureTheory ProbabilityTheory Set Filter Topology
open HeteroRetire.Boundary

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝔽 : Filtration ℝ ‹MeasurableSpace Ω›)
    {n : ℕ} (M : Market n) (hM : M.Standing)
    (Z : ℝ → Ω → ℝ) (hZ : IsDualNoise P 𝔽 M Z)
    (t : ℝ) (ht : t ∈ Ico 0 M.T) :
    bdry P 𝔽 M Z t ≤ ((M.L t / M.I t : ℝ) : EReal) :=
  HRAux.prop17_aux hM hZ ht
