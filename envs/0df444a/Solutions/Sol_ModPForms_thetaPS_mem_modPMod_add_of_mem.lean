-- Prove2me | solution 1 for ModPForms.thetaPS_mem_modPMod_add_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/ce5e8b3c-4472-566f-bc68-61b66aafba7a

import Definitions.Def_CuspForm_ModPForms
import Theorems.Thm_ModularForm_exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le
import Theorems.Thm_ModularForm_exists_gamma0_coe_eq_serreDerivative
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Shift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_thetaPS_mem_modPMod_add_of_mem
set_option autoImplicit false

open ModPForms

section Src_ThetaAn

set_option autoImplicit false

p2m_open "UpperHalfPlane~I"
open Complex Real Function
open ModularForm Derivative
open scoped ModularForm Manifold Topology

namespace E34S

section ThetaAn

variable {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
  (hbdd : IsBoundedAtImInfty f)

include hper in

private lemma periodic_D_comp_ofComplex : Periodic ((D f) ∘ ofComplex) 1 := by
  intro z
  rcases le_or_gt z.im 0 with hz | hz
  · have hz1 : (z + 1).im ≤ 0 := by simp [Complex.add_im, hz]
    exact congrArg (D f) (ofComplex_apply_eq_of_im_nonpos hz1 hz)
  · have hz1 : (0 : ℝ) < (z + 1).im := by simp [Complex.add_im, hz]
    show (2 * π * I : ℂ)⁻¹ * deriv (f ∘ ofComplex) ↑(ofComplex (z + 1))
      = (2 * π * I : ℂ)⁻¹ * deriv (f ∘ ofComplex) ↑(ofComplex z)
    rw [ofComplex_apply_of_im_pos hz1, ofComplex_apply_of_im_pos hz,
      UpperHalfPlane.coe_mk, UpperHalfPlane.coe_mk]
    congr 1
    have heq : (fun x ↦ (f ∘ ofComplex) (x + 1)) = (f ∘ ofComplex) := funext hper
    calc deriv (f ∘ ofComplex) (z + 1)
          = deriv (fun x ↦ (f ∘ ofComplex) (x + 1)) z :=
            (deriv_comp_add_const (f ∘ ofComplex) 1 z).symm
      _ = deriv (f ∘ ofComplex) z := by rw [heq]

include hper hhol hbdd in

private lemma Df_eq_qParam_mul_derivCusp (τ : ℍ) :
    D f τ = Periodic.qParam 1 (τ : ℂ) * deriv (cuspFunction 1 f) (Periodic.qParam 1 (τ : ℂ)) := by
  set F := cuspFunction 1 f
  set q := Periodic.qParam 1 (τ : ℂ) with hqdef
  have hFdiff := differentiableOn_cuspFunction_ball one_pos hper hhol hbdd
  have hq1 : q ∈ Metric.ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hqdef, Periodic.norm_qParam]
    have : (0 : ℝ) < 2 * π * τ.im := by positivity
    calc Real.exp (-2 * π * τ.im / 1) = Real.exp (-(2 * π * τ.im)) := by ring_nf
      _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hFd : DifferentiableAt ℂ F q :=
    (hFdiff q hq1).differentiableAt (Metric.isOpen_ball.mem_nhds hq1)
  have hcomp : (f ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)] F ∘ (Periodic.qParam 1) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
    show f (ofComplex z) = F (Periodic.qParam 1 z)
    rw [ofComplex_apply_of_im_pos hz]
    exact (eq_cuspFunction (⟨z, hz⟩ : ℍ) one_ne_zero hper).symm
  have hqd : HasDerivAt (Periodic.qParam 1) ((2 * π * I) * q) (τ : ℂ) := by
    have h1 : HasDerivAt (fun w ↦ (2 * π * I : ℂ) * w) (2 * π * I) (τ : ℂ) := by
      simpa using (hasDerivAt_id (τ : ℂ)).const_mul (2 * π * I : ℂ)
    refine ((h1.cexp).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall fun w ↦ by simp [Periodic.qParam]
    · rw [hqdef]; simp only [Periodic.qParam, Complex.ofReal_one, div_one]; ring
  have hderiv : deriv (f ∘ ofComplex) (τ : ℂ) = deriv F q * ((2 * π * I) * q) := by
    rw [hcomp.deriv_eq, ← hqd.deriv]; exact deriv_comp _ hFd hqd.differentiableAt
  show (2 * π * I : ℂ)⁻¹ * deriv (f ∘ ofComplex) (τ : ℂ) = q * deriv F q
  rw [hderiv]; field_simp [Complex.two_pi_I_ne_zero]

include hper hhol hbdd in

private lemma isBoundedAtImInfty_D_one : IsBoundedAtImInfty (D f) := by
  set F := cuspFunction 1 f
  have hFdiff := differentiableOn_cuspFunction_ball one_pos hper hhol hbdd
  have hF'diff : DifferentiableOn ℂ (deriv F) (Metric.ball 0 1) :=
    (hFdiff.analyticOnNhd Metric.isOpen_ball).deriv.differentiableOn
  obtain ⟨C, hC⟩ : ∃ C, ∀ q ∈ Metric.closedBall (0 : ℂ) 2⁻¹, ‖deriv F q‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 2⁻¹).bddAbove_image
      ((hF'diff.mono (Metric.closedBall_subset_ball
        (show (2⁻¹ : ℝ) < 1 by norm_num))).continuousOn).norm
    exact ⟨C, fun q hq ↦ hC ⟨q, hq, rfl⟩⟩
  rw [isBoundedAtImInfty_iff]
  refine ⟨C, Real.log 2 / (2 * π), fun τ hτ ↦ ?_⟩
  have h2π : (0 : ℝ) < 2 * π := Real.two_pi_pos
  have hqτ : ‖Periodic.qParam 1 (τ : ℂ)‖ ≤ 2⁻¹ := by
    rw [Periodic.norm_qParam]
    have hle : Real.log 2 ≤ 2 * π * τ.im := by have := (div_le_iff₀ h2π).mp hτ; linarith
    calc Real.exp (-2 * π * τ.im / 1) = Real.exp (-(2 * π * τ.im)) := by ring_nf
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (neg_le_neg hle)
      _ = 2⁻¹ := by rw [Real.exp_neg, Real.exp_log two_pos]
  calc ‖D f τ‖ = ‖Periodic.qParam 1 (τ : ℂ)‖ * ‖deriv F (Periodic.qParam 1 (τ : ℂ))‖ := by
        rw [Df_eq_qParam_mul_derivCusp hper hhol hbdd τ, norm_mul]
    _ ≤ 1 * C :=
        mul_le_mul (le_trans hqτ (by norm_num)) (hC _ (by rwa [Metric.mem_closedBall,
          dist_zero_right])) (norm_nonneg _) zero_le_one
    _ = C := one_mul C

include hper hhol hbdd in

private theorem analyticAt_cuspFunction_normalizedDeriv :
    AnalyticAt ℂ (cuspFunction 1 (D f)) 0 :=
  analyticAt_cuspFunction_zero one_pos (periodic_D_comp_ofComplex hper)
    (normalizedDerivOfComplex_mdifferentiable hhol) (isBoundedAtImInfty_D_one hper hhol hbdd)

include hper hhol hbdd in

private lemma hasSum_D_eq_theta_qExpansion (τ : ℍ) :
    HasSum (fun n : ℕ ↦ ((n : ℂ) * (qExpansion 1 f).coeff n) • (Periodic.qParam 1 (τ : ℂ)) ^ n)
      (D f τ) := by
  set F := cuspFunction 1 f
  set q := Periodic.qParam 1 (τ : ℂ) with hqdef
  have hFdiff := differentiableOn_cuspFunction_ball one_pos hper hhol hbdd
  have hF'diff : DifferentiableOn ℂ (deriv F) (Metric.ball 0 1) :=
    (hFdiff.analyticOnNhd Metric.isOpen_ball).deriv.differentiableOn
  have hq1 : q ∈ Metric.ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hqdef, Periodic.norm_qParam]
    have : (0 : ℝ) < 2 * π * τ.im := by positivity
    calc Real.exp (-2 * π * τ.im / 1) = Real.exp (-(2 * π * τ.im)) := by ring_nf
      _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)

  have hF'sum : HasSum
      (fun m : ℕ ↦ (((m + 1 : ℕ) : ℂ) * (qExpansion 1 f).coeff (m + 1)) • q ^ m)
      (deriv F q) := by
    have H := hasSum_taylorSeries_on_ball hF'diff hq1
    convert H using 1 <;> try with_reducible_and_instances rfl
    funext m
    rw [sub_zero, ← iteratedDeriv_succ', qExpansion_coeff]
    push_cast [Nat.factorial_succ]
    field_simp; ring

  have hqF' : HasSum
      (fun m : ℕ ↦ (((m + 1 : ℕ) : ℂ) * (qExpansion 1 f).coeff (m + 1)) • q ^ (m + 1))
      (q * deriv F q) := by
    have H := hF'sum.mul_left q
    convert H using 1 <;> try with_reducible_and_instances rfl
    funext m; rw [smul_eq_mul, smul_eq_mul, pow_succ]; ring
  have hfull : HasSum (fun n : ℕ ↦ ((n : ℂ) * (qExpansion 1 f).coeff n) • q ^ n)
      (q * deriv F q) := by
    have hshift := (hasSum_nat_add_iff
      (f := fun n : ℕ ↦ ((n : ℂ) * (qExpansion 1 f).coeff n) • q ^ n) 1).mp hqF'
    simpa using hshift
  rw [Df_eq_qParam_mul_derivCusp hper hhol hbdd τ]
  exact hfull

include hper hhol hbdd in

private theorem qExpansion_coeff_normalizedDeriv (n : ℕ) :
    (qExpansion 1 (D f)).coeff n = n * (qExpansion 1 f).coeff n := by
  have han := analyticAt_cuspFunction_normalizedDeriv hper hhol hbdd

  have h1 := (UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction (f := D f)
    (c := fun m ↦ (m : ℂ) * (qExpansion 1 f).coeff m) one_pos han
    (fun τ ↦ hasSum_D_eq_theta_qExpansion hper hhol hbdd τ)).hasFPowerSeriesAt

  have h2 : HasFPowerSeriesAt (cuspFunction 1 (D f))
      (FormalMultilinearSeries.ofScalars ℂ fun m ↦ (qExpansion 1 (D f)).coeff m) 0 := by
    simpa [UpperHalfPlane.qExpansion_coeff, div_eq_mul_inv, mul_comm] using han.hasFPowerSeriesAt
  have h3 := congr_arg (FormalMultilinearSeries.coeff · n) (h1.eq_formalMultilinearSeries h2)
  simpa [FormalMultilinearSeries.coeff_ofScalars] using h3.symm

end ThetaAn

end E34S

end Src_ThetaAn

section Src_ThetaAlg

set_option autoImplicit false

p2m_open "UpperHalfPlane~I"
open Complex Function ModularForm CongruenceSubgroup Derivative
open scoped MatrixGroups ModularForm Manifold Topology

namespace E34S

private def DerivRow : Prop :=
  ∀ (f : ℍ → ℂ), Periodic (f ∘ ofComplex) 1 → MDiff f → IsBoundedAtImInfty f →
    (∀ n : ℕ, (qExpansion 1 (D f)).coeff n = n * (qExpansion 1 f).coeff n) ∧
      AnalyticAt ℂ (cuspFunction 1 (D f)) 0

private def SerreRow (N' : ℕ) : Prop :=
  ∀ (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma0 N') k),
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 N') (k + 2), ⇑g = serreDerivative (k : ℂ) ⇑f

private def HasseRow (p N' : ℕ) : Prop :=
  ∃ (A : ModularForm (CongruenceSubgroup.Gamma0 N') ((p : ℤ) - 1)) (b : ℕ → ℤ),
    (∀ n, ModularFormClass.qCoeff A n = (b n : ℂ)) ∧ (p : ℤ) ∣ b 0 - 1 ∧ ∀ n, 0 < n → (p : ℤ) ∣ b n

section Theta

variable {F : Type} [Field F]

private lemma thetaPS_add (φ ψ : PowerSeries F) : thetaPS (φ + ψ) = thetaPS φ + thetaPS ψ := by
  ext n
  simp only [thetaPS, PowerSeries.coeff_mk, map_add, mul_add]

private lemma thetaPS_smul (c : F) (φ : PowerSeries F) : thetaPS (c • φ) = c • thetaPS φ := by
  ext n
  simp only [thetaPS, PowerSeries.coeff_mk, PowerSeries.coeff_smul, smul_eq_mul]
  ring

private lemma thetaPS_zero : thetaPS (0 : PowerSeries F) = 0 := by
  ext n
  simp only [thetaPS, PowerSeries.coeff_mk, map_zero, mul_zero]

private lemma coeff_thetaPS (φ : PowerSeries F) (n : ℕ) : PowerSeries.coeff n (thetaPS φ) = n * PowerSeries.coeff n φ := by
  simp only [thetaPS, PowerSeries.coeff_mk]

end Theta

section Furniture

variable {N' : ℕ} {k : ℤ}

private lemma T_mem_Gamma0 (N : ℕ) : ModularGroup.T ∈ Gamma0 N := by
  simp [Gamma0_mem, ModularGroup.coe_T]

private lemma one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma0 N)]
  exact AddSubgroup.mem_zmultiples 1

private lemma analyticAt_mf (f : ModularForm (Gamma0 N') k) : AnalyticAt ℂ (cuspFunction 1 ⇑f) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods_Gamma0 N')

private lemma periodic_mf (f : ModularForm (Gamma0 N') k) : Periodic (⇑f ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods_Gamma0 N')

private lemma bdd_mf (f : ModularForm (Gamma0 N') k) : IsBoundedAtImInfty ⇑f :=
  haveI : Fact (IsCusp OnePoint.infty ((Gamma0 N' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods_Gamma0 N')⟩
  ModularFormClass.bdd_at_infty f

private lemma qCoeff_eq (f : ℍ → ℂ) (n : ℕ) : ModularFormClass.qCoeff f n = (qExpansion 1 f).coeff n := rfl

end Furniture

section Gen

variable {N' : ℕ} {k : ℤ}

private def thetaCoeff (p : ℕ) (k : ℤ) (a b : ℕ → ℤ) (n : ℕ) : ℤ :=
  12 * ((p : ℤ) - 1) * (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, b x.1 * (x.2 * a x.2)) -
    12 * k * ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, a x.1 * (x.2 * b x.2)

private theorem exists_form_qCoeff_thetaCoeff (hD : DerivRow) (hS : SerreRow N') {p : ℕ}
    (A : ModularForm (Gamma0 N') ((p : ℤ) - 1)) (b : ℕ → ℤ) (hb : ∀ n, ModularFormClass.qCoeff A n = (b n : ℂ))
    (f : ModularForm (Gamma0 N') k) (a : ℕ → ℤ) (ha : ∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    ∃ G : ModularForm (Gamma0 N') (k + ((p : ℤ) + 1)),
      ∀ n, ModularFormClass.qCoeff G n = (thetaCoeff p k a b n : ℂ) := by
  obtain ⟨gf, hgf⟩ := hS k f
  obtain ⟨gA, hgA⟩ := hS ((p : ℤ) - 1) A
  have h1 : ((p : ℤ) - 1) + (k + 2) = k + ((p : ℤ) + 1) := by ring
  have h2 : k + (((p : ℤ) - 1) + 2) = k + ((p : ℤ) + 1) := by ring
  set G : ModularForm (Gamma0 N') (k + ((p : ℤ) + 1)) :=
    ((12 * ((p : ℂ) - 1)) • (A.mul gf)).mcast h1 - ((12 * (k : ℂ)) • (f.mul gA)).mcast h2 with hGdef
  refine ⟨G, fun n => ?_⟩

  have hG : (⇑G : ℍ → ℂ) = (12 * ((p : ℂ) - 1)) • (⇑A * D ⇑f) - (12 * (k : ℂ)) • (⇑f * D ⇑A) := by
    ext z
    rw [hGdef]
    simp only [ModularForm.coe_sub, Pi.sub_apply, ModularForm.coe_mcast, ModularForm.IsGLPos.coe_smul, Pi.smul_apply,
      ModularForm.coe_mul, Pi.mul_apply, hgf, hgA, serreDerivative_apply, smul_eq_mul]
    push_cast
    ring

  obtain ⟨hDf, hDf_an⟩ := hD ⇑f (periodic_mf f) (ModularFormClass.holo f) (bdd_mf f)
  obtain ⟨hDA, hDA_an⟩ := hD ⇑A (periodic_mf A) (ModularFormClass.holo A) (bdd_mf A)
  have hf_an := analyticAt_mf f
  have hA_an := analyticAt_mf A
  have h1_an : AnalyticAt ℂ (cuspFunction 1 (⇑A * D ⇑f)) 0 := by
    rw [cuspFunction_mul hA_an.continuousAt hDf_an.continuousAt]
    exact hA_an.mul hDf_an
  have h2_an : AnalyticAt ℂ (cuspFunction 1 (⇑f * D ⇑A)) 0 := by
    rw [cuspFunction_mul hf_an.continuousAt hDA_an.continuousAt]
    exact hf_an.mul hDA_an
  have h1s_an : AnalyticAt ℂ (cuspFunction 1 ((12 * ((p : ℂ) - 1)) • (⇑A * D ⇑f))) 0 := by
    rw [cuspFunction_smul h1_an.continuousAt]
    exact h1_an.const_smul
  have h2s_an : AnalyticAt ℂ (cuspFunction 1 ((12 * (k : ℂ)) • (⇑f * D ⇑A))) 0 := by
    rw [cuspFunction_smul h2_an.continuousAt]
    exact h2_an.const_smul

  have hq : qExpansion 1 (⇑G : ℍ → ℂ) =
      (12 * ((p : ℂ) - 1)) • (qExpansion 1 ⇑A * qExpansion 1 (D ⇑f)) -
        (12 * (k : ℂ)) • (qExpansion 1 ⇑f * qExpansion 1 (D ⇑A)) := by
    rw [hG, qExpansion_sub h1s_an h2s_an, qExpansion_smul h1_an, qExpansion_smul h2_an, qExpansion_mul hA_an hDf_an,
      qExpansion_mul hf_an hDA_an]
  have ha' : ∀ i, (qExpansion 1 ⇑f).coeff i = (a i : ℂ) := ha
  have hb' : ∀ i, (qExpansion 1 ⇑A).coeff i = (b i : ℂ) := hb
  rw [qCoeff_eq, hq, map_sub, map_smul, map_smul, PowerSeries.coeff_mul, PowerSeries.coeff_mul, smul_eq_mul,
    smul_eq_mul]
  simp only [hDf, hDA, ha', hb', thetaCoeff]
  push_cast
  all_goals ring

end Gen

section Main

variable {F : Type} [Field F]

private lemma twelve_ne_zero {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) [CharP F p] : (12 : F) ≠ 0 := by
  intro h
  have h' : ((12 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h'
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) h'
  interval_cases p <;> first | omega | exact absurd hp (by decide)

private lemma red_thetaCoeff {p : ℕ} [CharP F p] (k : ℤ) (a b : ℕ → ℤ) (hb0 : (p : ℤ) ∣ b 0 - 1)
    (hbn : ∀ n, 0 < n → (p : ℤ) ∣ b n) :
    (PowerSeries.mk fun n => ((thetaCoeff p k a b n : ℤ) : F)) =
      (-12 : F) • thetaPS (PowerSeries.mk fun n => ((a n : ℤ) : F)) := by
  have hb0F : ((b 0 : ℤ) : F) = 1 := by
    have h : (((b 0 - 1 : ℤ)) : F) = 0 := (CharP.intCast_eq_zero_iff F p _).mpr hb0
    rwa [Int.cast_sub, Int.cast_one, sub_eq_zero] at h
  have hbF : ∀ n, 0 < n → ((b n : ℤ) : F) = 0 := fun n hn => (CharP.intCast_eq_zero_iff F p _).mpr (hbn n hn)
  have hpF : (p : F) = 0 := CharP.cast_eq_zero F p
  ext n
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_smul, coeff_thetaPS, smul_eq_mul, thetaCoeff]
  push_cast
  have hS1 : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, ((b x.1 : ℤ) : F) * ((x.2 : F) * ((a x.2 : ℤ) : F))) =
      (n : F) * ((a n : ℤ) : F) := by
    rw [Finset.sum_eq_single_of_mem (0, n) (by simp)]
    · simp only [hb0F, one_mul]
    · intro x hx hne
      have hx1 : 0 < x.1 := by
        rcases Nat.eq_zero_or_pos x.1 with h | h
        · exfalso
          apply hne
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
          ext
          · exact h
          · show x.2 = n
            omega
        · exact h
      rw [hbF x.1 hx1, zero_mul]
  have hS2 : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, ((a x.1 : ℤ) : F) * ((x.2 : F) * ((b x.2 : ℤ) : F))) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    rcases Nat.eq_zero_or_pos x.2 with h | h
    · rw [h, Nat.cast_zero, zero_mul, mul_zero]
    · rw [hbF x.2 h, mul_zero, mul_zero]
  rw [hS1, hS2, hpF]
  ring

private theorem S_M3_theta_of_hasse (hD : DerivRow) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N']
    (hS : SerreRow N') (hA : HasseRow p N')
    (k : ℤ) (F : Type) [Field F] [CharP F p] (φ : PowerSeries F) (hφ : φ ∈ modPMod N' k F) :
    thetaPS φ ∈ modPMod N' (k + ((p : ℤ) + 1)) F := by
  obtain ⟨A, b, hb, hb0, hbn⟩ := hA
  have h12 : (-12 : F) ≠ 0 := neg_ne_zero.mpr (twelve_ne_zero hp hp5)
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨f, a, ha, rfl⟩ := hφ
    obtain ⟨G, hG⟩ := exists_form_qCoeff_thetaCoeff hD hS A b hb f a ha
    have hmem : (PowerSeries.mk fun n => ((thetaCoeff p k a b n : ℤ) : F)) ∈ modPMod N' (k + ((p : ℤ) + 1)) F :=
      Submodule.subset_span ⟨G, thetaCoeff p k a b, hG, rfl⟩
    have hθ : thetaPS (PowerSeries.mk fun n => ((a n : ℤ) : F)) =
        (-12 : F)⁻¹ • PowerSeries.mk fun n => ((thetaCoeff p k a b n : ℤ) : F) := by
      rw [red_thetaCoeff k a b hb0 hbn, smul_smul, inv_mul_cancel₀ h12, one_smul]
    rw [hθ]
    exact Submodule.smul_mem _ _ hmem
  | zero =>
    rw [thetaPS_zero]
    exact Submodule.zero_mem _
  | add φ ψ _ _ hφ hψ =>
    rw [thetaPS_add]
    exact Submodule.add_mem _ hφ hψ
  | smul c φ _ hφ =>
    rw [thetaPS_smul]
    exact Submodule.smul_mem _ _ hφ

end Main

end E34S

end Src_ThetaAlg

namespace E34S

private theorem hasseRow (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] : HasseRow p N' :=
  ModularForm.exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le p hp hp5 N'

private theorem serreRow (N' : ℕ) [NeZero N'] : SerreRow N' := fun k f =>
  ModularForm.exists_gamma0_coe_eq_serreDerivative N' k f

private theorem derivRow : DerivRow := fun _f hper hhol hbdd =>
  ⟨fun n => qExpansion_coeff_normalizedDeriv hper hhol hbdd n, analyticAt_cuspFunction_normalizedDeriv hper hhol hbdd⟩

end E34S

open E34S in
theorem solution (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] (k : ℤ)
    (F : Type) [Field F] [CharP F p] (φ : PowerSeries F) (hφ : φ ∈ modPMod N' k F) :
    thetaPS φ ∈ modPMod N' (k + ((p : ℤ) + 1)) F :=
  S_M3_theta_of_hasse derivRow p hp hp5 N' (serreRow N') (hasseRow p hp hp5 N') k F φ hφ

end S_ModPForms_thetaPS_mem_modPMod_add_of_mem
end P2MW
export P2MW.S_ModPForms_thetaPS_mem_modPMod_add_of_mem (solution)
