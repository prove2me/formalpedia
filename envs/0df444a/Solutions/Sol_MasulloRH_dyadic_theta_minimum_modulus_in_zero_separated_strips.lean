-- Prove2me | solution 1 for MasulloRH.dyadic_theta_minimum_modulus_in_zero_separated_strips
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:53:57.36254+00:00
-- url     : https://prove2.me/submissions/fc7ac15f-dce2-4e5d-8d7f-59dc9f14f431

import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_MasulloRH_WeightedStripJetSpace
import Mathlib
import Theorems.Thm_MasulloRH_dyadic_gaussian_theta_mellin
import Theorems.Thm_Zeta23_RvM_norm_riemannZeta_sub_one_le

-- Local source: SynthMinimumDiskBase
section StandaloneSynthMinimumDiskBase
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/StrongPNT.lean (fully proved prefix, truncated before JBlaschke/ZeroInequality).
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: kept only a prefix of the file (through `ZerosBound`: the Blaschke-factor /
Borel–Carathéodory bound on zeros in a disk; the remainder of StrongPNT.lean is not ported),
removed the Architect blueprint tooling (import Architect, blueprint_comment blocks,
@[blueprint ...] attributes), dropped the intra-project import of MediumPNT together with the
local notations and the `open ArithmeticFunction` that only the unported remainder used (the two Mathlib
imports previously reached through MediumPNT are imported directly), and added
`import Zeta23.Prelude.InstancePriorities` (this project's instance-priority settings).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

namespace MasulloRH.SynthMinimum.Disc

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory

lemma AnalyticOn.norm_le_of_norm_le_on_sphere {C r R : ℝ} {f : ℂ → ℂ} {w : ℂ}
    (hyp_r : r ≤ R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (cond : ∀ z ∈ Metric.sphere 0 r, ‖f z‖ ≤ C)
    (wInS : w ∈ Metric.closedBall 0 r) :
    ‖f w‖ ≤ C := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := Metric.closedBall 0 r) Metric.isBounded_closedBall
  · apply DifferentiableOn.diffContOnCl
    rw [Metric.closure_closedBall]
    exact AnalyticOn.differentiableOn
      (AnalyticOn.mono analytic
        (Metric.closedBall_subset_closedBall hyp_r))
  · rw [frontier_closedBall']
    exact cond
  · rw [Metric.closure_closedBall]
    exact wInS

theorem borelCaratheodory' {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (Rpos : 0 < R) (hyp_r : r < R)
    (analytic : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖f z‖ ≤ (2 * M * r) / (R - r) := by
  have h_borelCaratheodory : ∀ ε > 0, ‖f z‖ ≤ (2 * (M + ε) * ‖z‖) / (R - ‖z‖) := by
    intro ε εpos;
    apply Complex.borelCaratheodory_zero;
    exacts [by linarith, analytic.differentiableOn, fun z hz => by rw [Set.mem_ofPred_eq]; linarith [realPartBounded z hz], Rpos, by exact Metric.mem_ball.mpr ( lt_of_le_of_lt ( Metric.mem_closedBall.mp hyp_z ) hyp_r ), zeroAtZero]
  have h_limit : ‖f z‖ ≤ (2 * M * ‖z‖) / (R - ‖z‖) := by
    have h_limit : Filter.Tendsto (fun ε => (2 * (M + ε) * ‖z‖) / (R - ‖z‖)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * M * ‖z‖) / (R - ‖z‖))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' ?_ _ _ (by ring_nf))
      exact ((continuous_const.mul (continuous_const.add continuous_id)).mul continuous_const).div_const _
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_limit ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_borelCaratheodory ε hε );
  rw [mem_closedBall_iff_norm, sub_zero] at hyp_z
  refine le_trans h_limit ?_;
  gcongr
  · exact mul_nonneg (mul_nonneg (zero_le_two) (le_of_lt Mpos)) (le_trans (norm_nonneg z) hyp_z)

theorem LogOfAnalyticFunction {r R : ℝ} {B : ℂ → ℂ}
    (zero_lt_r : 0 < r) (r_lt_R : r < R)
    (BanalyticOnNhdOfDR : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (Bnonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) R, B z ≠ 0) :
    ∃ (J_B : ℂ → ℂ), (AnalyticOnNhd ℂ J_B (Metric.ball 0 R)) ∧
      (J_B 0 = 0) ∧
      (∀ z ∈ Metric.closedBall 0 r, (deriv J_B) z = (deriv B) z / (B z)) ∧
      (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
  obtain ⟨J_B, hJB⟩ : ∃ J_B : ℂ → ℂ, (∀ z ∈ Metric.ball 0 R, (HasDerivAt J_B (deriv B z / B z) z)) ∧ J_B 0 = 0 ∧ (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
    set f : ℂ → ℂ := fun z => deriv B z / B z;
    have hf : AnalyticOnNhd ℂ f (Metric.ball 0 R) :=
      (BanalyticOnNhdOfDR.deriv.mono Metric.ball_subset_closedBall).div
        (BanalyticOnNhdOfDR.mono Metric.ball_subset_closedBall)
        (fun z hz => Bnonzero z <| Metric.ball_subset_closedBall hz)
    obtain ⟨J, hJ⟩ := DifferentiableOn.isExactOn_ball hf.differentiableOn
    refine ⟨fun z ↦ J z - J 0, fun z hz ↦ (hJ z hz).sub_const _, by simp, ?_⟩
    set H : ℂ → ℂ := fun z => Complex.exp (J z - J 0) / B z
    have hJB_deriv : ∀ z ∈ Metric.ball 0 R, HasDerivAt (fun z ↦ J z - J 0) (f z) z :=
      fun z hz ↦ (hJ z hz).sub_const _
    have hH_deriv : ∀ z ∈ Metric.ball 0 R, HasDerivAt H 0 z := by
      intro z hz
      have := (Complex.hasDerivAt_exp _).comp z (hJB_deriv z hz)
      convert! this.div (BanalyticOnNhdOfDR.differentiableOn.differentiableAt
        (Metric.closedBall_mem_nhds_of_mem hz) |>.hasDerivAt)
        (Bnonzero z <| Metric.ball_subset_closedBall hz) using 1
      ring_nf!; grind
    have hH_const : ∀ z ∈ Metric.ball 0 R, H z = H 0 := by
      intro z hz
      have h_diffOn : DifferentiableOn ℂ H (Metric.ball 0 R) :=
        fun z hz ↦ (hH_deriv z hz).differentiableAt.differentiableWithinAt
      refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball 0 R) h_diffOn ?_ hz
        (Metric.mem_ball_self (Metric.pos_of_mem_ball hz))
      intro x hx
      rw [fderivWithin_of_isOpen Metric.isOpen_ball hx,
        ← ContinuousLinearMap.toSpanSingleton_zero]
      exact (hH_deriv x hx).hasFDerivAt.fderiv
    have h_exp_re : ∀ z ∈ Metric.ball 0 R, Real.exp (J z - J 0).re = ‖B z‖ / ‖B 0‖ := by
      intro z hz
      have hc := hH_const z hz
      simp only [H, sub_self, Complex.exp_zero, one_div] at hc
      rw [div_eq_iff (Bnonzero z (Metric.ball_subset_closedBall hz)), mul_comm] at hc
      rw [← Complex.norm_exp, ← norm_div, div_eq_mul_inv]
      exact enorm_eq_iff_norm_eq.mp (congrArg enorm hc)
    intro z hz
    have hBz := Bnonzero z (Metric.ball_subset_closedBall hz)
    have hB0 := Bnonzero 0 (by norm_num; linarith)
    rw [← Real.log_div (norm_ne_zero_iff.mpr hBz) (norm_ne_zero_iff.mpr hB0),
      ← h_exp_re z hz, Real.log_exp]
  have hmem : ∀ z, z ∈ Metric.ball (0 : ℂ) r → z ∈ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    apply Metric.mem_closedBall.mpr
    rw [Metric.mem_ball] at hz
    linarith
  refine ⟨J_B, ?_, hJB.2.1, ?_, hJB.2.2⟩
  · intro z hz
    exact DifferentiableOn.analyticAt (fun w hw ↦ (hJB.1 w hw).differentiableAt.differentiableWithinAt) (IsOpen.mem_nhds Metric.isOpen_ball hz)
  · intro z hz
    exact (hJB.1 z (Metric.closedBall_subset_ball r_lt_R hz)).deriv

def SetOfZeros (R : ℝ) (f : ℂ → ℂ) : Set ℂ := {ρ : ℂ | ‖ρ‖ ≤ R ∧ f ρ = 0}

lemma finiteSetOfZeros_mono {r : ℝ} {f : ℂ → ℂ}
    (r_lt_one : r < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) :
    (SetOfZeros r f).Finite := by
  apply Set.Finite.subset finiteZeros
  unfold SetOfZeros
  refine ofPred_subset_ofPred.mpr ?_
  intro z hz
  exact ⟨by linarith, hz.2⟩

open Classical
noncomputable def ZeroFactor (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if h1 : AnalyticAt ℂ f z then
    if h2 : analyticOrderAt f z ≠ ⊤ then
      (h1.analyticOrderAt_ne_top.mp h2).choose z
    else 0
  else 0

lemma ZeroFactorization {R : ℝ} {f : ℂ → ℂ} {ρ : ℂ}
    (RleOne : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0)
    (hρ : ρ ∈ SetOfZeros R f) :
    ∃ h_ρ : ℂ → ℂ, AnalyticAt ℂ h_ρ ρ ∧ h_ρ ρ ≠ 0 ∧ ZeroFactor f ρ = h_ρ ρ ∧
      f =ᶠ[nhds ρ] fun z ↦ (z - ρ) ^ analyticOrderNatAt f ρ * h_ρ z := by
  have zero_mem_closedBall : 0 ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw[mem_closedBall_iff_norm, sub_zero, norm_zero]
    exact zero_le_one
  have ρ_mem_closedBall : ρ ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw[mem_closedBall_iff_norm, sub_zero]
    linarith[hρ.1]
  have orderAtZeroIsZero : analyticOrderAt f 0 = 0 := by
    rw[analyticOrderAt_eq_zero]
    exact Or.symm (Decidable.not_or_of_imp fun a a_1 ↦ hf_neq_zero_at_zero a)
  have finiteOrder : analyticOrderAt f ρ ≠ ⊤ := by
    refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hfAnalytic (Metric.isPreconnected_closedBall) zero_mem_closedBall ρ_mem_closedBall (lt_top_iff_ne_top.mp ?_)
    rw[orderAtZeroIsZero]
    exact ENat.top_pos
  have AnalyticAt_ρ : AnalyticAt ℂ f ρ := by exact (hfAnalytic ρ ρ_mem_closedBall)
  obtain ⟨h_ρ, h_ρ_neq_zero_at_zero, f_eq⟩ := (AnalyticAt_ρ.analyticOrderAt_ne_top.mp finiteOrder).choose_spec
  set g := (AnalyticAt_ρ.analyticOrderAt_ne_top.mp finiteOrder).choose
  refine ⟨g, h_ρ, h_ρ_neq_zero_at_zero, ?_, f_eq⟩
  simp only [ZeroFactor, AnalyticAt_ρ, ↓reduceDIte, ne_eq, finiteOrder, not_false_eq_true,
    smul_eq_mul, g]

noncomputable def Cf (r : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if finite_zeros_mono : (SetOfZeros r f).Finite then
    if _ : z ∈ SetOfZeros r f then
      ZeroFactor f z / ∏ ρ ∈ (finite_zeros_mono.toFinset \ {z}), (z - ρ) ^ (analyticOrderNatAt f ρ)
    else
      f z / ∏ ρ ∈ (finite_zeros_mono.toFinset), (z - ρ) ^ (analyticOrderNatAt f ρ)
  else 1

lemma analyticAt_finset_prod_sub_pow (s : Finset ℂ) (g : ℂ → ℕ) (w : ℂ) :
    AnalyticAt ℂ (fun z => ∏ ρ ∈ s, (z - ρ) ^ g ρ) w := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact analyticAt_const
  | @insert a s' hne ih =>
    have : (fun z => ∏ ρ ∈ insert a s', (z - ρ) ^ g ρ) = fun z => (z - a) ^ g a * ∏ ρ ∈ s', (z - ρ) ^ g ρ :=
      funext fun z => Finset.prod_insert hne
    rw [this]
    exact ((analyticAt_id.sub analyticAt_const).pow _).mul ih

lemma CfAnalytic {r R : ℝ} {f : ℂ → ℂ}
    (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (Cf r f) (Metric.closedBall (0 : ℂ) R) := by
  intro w hw
  unfold Cf
  by_cases finite_zeros_mono : (SetOfZeros r f).Finite
  · simp only [finite_zeros_mono, ↓reduceDIte]
    by_cases w_in_zeros : w ∈ SetOfZeros r f
    · obtain ⟨h_w, hh_w_analytic, hh_w_w_ne_zero, hh_w_eq⟩ := ZeroFactorization (by linarith) (hfAnalytic.mono (Metric.closedBall_subset_closedBall (by linarith))) hf_neq_zero_at_zero w_in_zeros;
      have h_eq : ∀ᶠ z in nhds w, (if h : z ∈ SetOfZeros r f then ZeroFactor f z / ∏ ρ ∈ finite_zeros_mono.toFinset \ {z}, (z - ρ) ^ analyticOrderNatAt f ρ else f z / ∏ ρ ∈ finite_zeros_mono.toFinset, (z - ρ) ^ analyticOrderNatAt f ρ) = h_w z / ∏ ρ ∈ finite_zeros_mono.toFinset \ {w}, (z - ρ) ^ analyticOrderNatAt f ρ := by
        filter_upwards [ hh_w_eq.2, hh_w_analytic.continuousAt.eventually_ne hh_w_w_ne_zero ] with z hz hz';
        by_cases h : z = w
        · subst h
          rw [dif_pos w_in_zeros]
          congr 1
          exact hh_w_eq.1
        · have z_not_in : z ∉ SetOfZeros r f := by
            intro hmem
            have hfz : f z = 0 := hmem.2
            rw [hz] at hfz
            exact absurd hfz (mul_ne_zero (pow_ne_zero _ (sub_ne_zero_of_ne h)) hz')
          rw [dif_neg z_not_in, hz]
          have hw_mem : w ∈ finite_zeros_mono.toFinset := finite_zeros_mono.mem_toFinset.mpr w_in_zeros
          rw [Finset.prod_eq_prod_sdiff_singleton_mul hw_mem (fun ρ => (z - ρ) ^ analyticOrderNatAt f ρ)]
          rw [mul_comm ((z - w) ^ analyticOrderNatAt f w) (h_w z)]
          rw [mul_div_mul_right _ _ (pow_ne_zero _ (sub_ne_zero_of_ne h))]
      apply hh_w_analytic.div _ _ |> fun h => h.congr _;
      · use fun z => ∏ ρ ∈ finite_zeros_mono.toFinset \ { w }, ( z - ρ ) ^ analyticOrderNatAt f ρ;
      · exact analyticAt_finset_prod_sub_pow _ _ _
      · simp only [Finset.prod_eq_zero_iff, ne_eq, pow_eq_zero_iff', Finset.mem_sdiff, Finite.mem_toFinset, Finset.mem_singleton, not_exists, not_and,
          Decidable.not_not, and_imp]
        intro x _ h_ne_w
        exact fun h_eq_w => absurd (sub_eq_zero.mp h_eq_w).symm h_ne_w
      · filter_upwards [ h_eq ] with z hz using hz.symm
    · apply AnalyticAt.congr _ _
      · exact fun z => f z / ∏ ρ ∈ finite_zeros_mono.toFinset, ( z - ρ ) ^ analyticOrderNatAt f ρ
      · refine AnalyticAt.div ?_ ?_ ?_
        · exact hfAnalytic w ( Metric.mem_closedBall.mpr <| le_trans hw.out <| by linarith )
        · exact analyticAt_finset_prod_sub_pow _ _ _
        · simp only [ ne_eq, Finset.prod_eq_zero_iff, Finite.mem_toFinset, pow_eq_zero_iff',
          sub_eq_zero, ↓existsAndEq, true_and, not_and, Decidable.not_not]
          exact fun h => absurd h w_in_zeros
      · filter_upwards [ IsOpen.mem_nhds ( isOpen_compl_iff.mpr finite_zeros_mono.isClosed ) w_in_zeros ] with z hz
        split_ifs with h
        · exact absurd h hz
        · rfl
  · simp only [finite_zeros_mono, ↓reduceDIte]
    exact analyticAt_const

noncomputable def BlaschkeB (r R : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if finite_zeros_mono : (SetOfZeros r f).Finite then
    (Cf r f) z * (∏ ρ ∈ finite_zeros_mono.toFinset, (R - z * (conj ρ) / R) ^ (analyticOrderNatAt f ρ))
  else 1

lemma BlaschkeAnalytic {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (BlaschkeB r R f) (Metric.closedBall (0 : ℂ) R) := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  unfold BlaschkeB
  by_cases finite_zeros_mono : (SetOfZeros r f).Finite
  · simp only [finite_zeros_mono, ↓reduceDIte]
    refine AnalyticOnNhd.mul (CfAnalytic r_lt_R R_lt_one hfAnalytic hf_neq_zero_at_zero) (Finset.analyticOnNhd_fun_prod (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset ?_)
    intro w hw
    refine AnalyticOnNhd.fun_pow (AnalyticOnNhd.sub (analyticOnNhd_const) (AnalyticOnNhd.div (AnalyticOnNhd.mul (analyticOnNhd_id) (analyticOnNhd_const)) (analyticOnNhd_const) ?_)) (analyticOrderAt f w).toNat
    intro w' hw'
    exact_mod_cast ne_of_gt R_pos
  · simp only [finite_zeros_mono, ↓reduceDIte]
    exact analyticOnNhd_const

lemma BlaschkeOfZero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ‖BlaschkeB r R f 0‖ =
      ‖f 0‖ * (∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / ‖ρ‖) ^ (analyticOrderNatAt f ρ)) := by
  have zero_not_zero : ¬(0 ∈ SetOfZeros r f) := by
    apply notMem_ofPred_iff.mpr
    simp only [norm_zero, not_and]
    intro r
    exact mem_support.mp hf_neq_zero_at_zero
  unfold BlaschkeB Cf
  simp only [finiteSetOfZeros_mono r_lt_one finiteZeros, zero_not_zero, ↓reduceDIte, zero_sub, zero_mul, zero_div, sub_zero,
    Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow, norm_neg, norm_real, norm_eq_abs]
  rw[div_eq_mul_inv, mul_assoc, abs_of_pos (by linarith)]
  refine (mul_right_inj' (norm_ne_zero_iff.mpr hf_neq_zero_at_zero)).mpr ?_
  rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  simp only [div_eq_inv_mul, mul_pow, inv_pow]

lemma norm_fOfZero_le_norm_BlaschkeOfZero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ‖f 0‖ ≤ ‖BlaschkeB r R f 0‖ := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  rw [BlaschkeOfZero r_pos r_lt_one r_lt_R finiteZeros hf_neq_zero_at_zero, ← mul_one ‖f 0‖]
  refine mul_le_mul (by rw[mul_one]) ?_ (zero_le_one) (mul_nonneg (norm_nonneg (f 0)) zero_le_one)
  rw [← Finset.prod_const_one (s := (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset)]
  apply Finset.prod_le_prod
  · intro ρ hρ
    exact zero_le_one
  · intro ρ hρ
    simp only [SetOfZeros, Finite.mem_toFinset, mem_ofPred_eq] at hρ
    apply one_le_pow₀
    rw[one_le_div]
    · linarith
    · rw [norm_pos_iff]
      by_contra h
      rw [h] at hρ
      exact hf_neq_zero_at_zero hρ.2

lemma DiskBound {B r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) (fz_bound : ∀ (z : ℂ), ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ‖BlaschkeB r R f z‖ ≤ B := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  refine AnalyticOn.norm_le_of_norm_le_on_sphere (Std.IsPreorder.le_refl R) (AnalyticOnNhd.analyticOn (BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic hf_neq_zero_at_zero)) ?_ hz
  intro w hw
  rw[mem_sphere_iff_norm, sub_zero] at hw
  have hw_not_in : ¬(w ∈ SetOfZeros r f) := by
    apply notMem_ofPred_iff.mpr
    intro le_r
    linarith
  have Bf_eq_f_at_w : ‖BlaschkeB r R f w‖ = ‖f w‖ := by
    unfold BlaschkeB Cf
    simp only [finiteSetOfZeros_mono r_lt_one finiteZeros, hw_not_in, ↓reduceDIte, Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow]
    rw[div_eq_mul_inv, mul_assoc, mul_right_eq_self₀]
    by_cases fw_normZero : ‖f w‖ = 0
    · exact Or.inr fw_normZero
    · apply Or.inl
      rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro w' hw'_in
      have hfact : (R : ℂ) - w * starRingEnd ℂ w' / R = (conj w - conj w') * w / R := by
        rw[sub_mul, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hw, ofReal_pow]
        field_simp
      rw [hfact, norm_div, norm_mul, ← map_sub, norm_conj, Complex.norm_real, hw, Real.norm_of_nonneg (le_of_lt R_pos)]
      field_simp
      rw[← div_pow, div_self, one_pow]
      rw[Set.Finite.mem_toFinset] at hw'_in
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun h => hw_not_in (h ▸ hw'_in)))
  rw[Bf_eq_f_at_w]
  exact fz_bound w (le_of_eq hw)

lemma BlaschkeNonzero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r, BlaschkeB r R f z ≠ 0 := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  intro z hz
  have hz_norm_le_r : ‖z‖ ≤ r := by rwa [mem_closedBall_iff_norm, sub_zero] at hz
  have hz_norm_lt_R : ‖z‖ < R := by linarith
  let hFin := finiteSetOfZeros_mono r_lt_one finiteZeros
  have hBProd : ∏ ρ ∈ hFin.toFinset,
      (↑R - z * (starRingEnd ℂ) ρ / ↑R) ^ analyticOrderNatAt f ρ ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ρ hρ
    apply pow_ne_zero
    norm_num [ sub_eq_zero, Complex.ext_iff ];
    simp only [SetOfZeros, Finite.mem_toFinset, mem_ofPred_eq] at hρ
    rw [ eq_div_iff ] <;> norm_num [ Complex.normSq, Complex.norm_def ] at *;
    · rw [Real.sqrt_lt' (by linarith)] at hz_norm_lt_R
      rw [ Real.sqrt_le_iff ] at hρ
      exact fun h => absurd h ( by nlinarith [ sq_nonneg ( z.re - ρ.re ), sq_nonneg ( z.im - ρ.im ), mul_lt_mul_of_pos_left r_lt_R R_pos ] )
    · linarith
  unfold BlaschkeB Cf
  by_cases z_in_zeros : z ∈ SetOfZeros r f
  · simp only [hFin, z_in_zeros, ↓reduceDIte]
    obtain ⟨_, _, hne, heq⟩ :=
      ZeroFactorization (by linarith) (hfAnalytic.mono (Metric.closedBall_subset_closedBall (by linarith)))
        hf_neq_zero_at_zero z_in_zeros
    rw [heq.1]
    refine mul_ne_zero (div_ne_zero hne (Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
      pow_ne_zero _ (sub_ne_zero.mpr fun h =>
        (Finset.mem_sdiff.mp hρ).2 (Finset.mem_singleton.mpr h.symm)))) hBProd
  · simp only [hFin, z_in_zeros, ↓reduceDIte]
    refine mul_ne_zero (div_ne_zero (fun hfz => z_in_zeros ⟨hz_norm_le_r, hfz⟩)
      (Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
        pow_ne_zero _ (sub_ne_zero.mpr fun h => z_in_zeros (h ▸ hFin.mem_toFinset.mp hρ)))) hBProd

theorem ZerosBound {B r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ ≤
      1 / Real.log (R / r) * Real.log B := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have hf0_ne_zero : f 0 ≠ 0 := by rw [hf0_eq_one]; exact one_ne_zero
  have blaschke_eq := BlaschkeOfZero r_pos r_lt_one r_lt_R finiteZeros hf0_ne_zero
  rw[hf0_eq_one, norm_one, one_mul] at blaschke_eq
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (Real.log_pos (by simp only [lt_div_iff₀ r_pos, one_mul, r_lt_R])), ← Real.log_pow]
  refine Real.log_le_log (pow_pos (div_pos R_pos r_pos) _) ?_
  calc (R / r) ^ ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ
      = ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / r) ^ analyticOrderNatAt f ρ := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / ‖ρ‖) ^ analyticOrderNatAt f ρ := by
      apply Finset.prod_le_prod
      · intro ρ _
        exact pow_nonneg (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) _
      · intro ρ hρ
        have hρ_mem := (finiteSetOfZeros_mono r_lt_one finiteZeros).mem_toFinset.mp hρ
        refine pow_le_pow_left₀ (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) ?_ _
        refine div_le_div_of_nonneg_left (le_of_lt R_pos) (norm_pos_iff.mpr ?_) (hρ_mem.1)
        rintro rfl
        exact hf0_ne_zero hρ_mem.2
    _ ≤ B := by
      rw[← blaschke_eq]
      exact DiskBound r_pos r_lt_R R_lt_one finiteZeros hfAnalytic
        hf0_ne_zero fz_bound (Metric.mem_closedBall_self (le_of_lt R_pos))

end MasulloRH.SynthMinimum.Disc
end StandaloneSynthMinimumDiskBase


-- Local source: SynthMinimumDisk
section StandaloneSynthMinimumDisk
open Complex Metric Set
open scoped ComplexConjugate
namespace MasulloRH.SynthMinimum
noncomputable section
open Disc

private theorem denominator_factor_le {w ρ : ℂ} (hw : ‖w‖≤1/2) (hρ : ‖ρ‖≤3/4) :
    ‖(7/8:ℂ)-w*conj ρ/(7/8:ℂ)‖ ≤ 2 := by
  apply (norm_sub_le _ _).trans
  simp only [norm_div,norm_mul,norm_conj]
  norm_num
  nlinarith [mul_le_mul hw hρ (norm_nonneg _) (by norm_num : 0≤(1/2:ℝ))]

/-- Control of every removed zero factor using its separation from the evaluation point. -/
private theorem blaschke_point_bound {f : ℂ → ℂ} (hf : (SetOfZeros 1 f).Finite)
    {w : ℂ} (hw : ‖w‖≤1/2) (δ : ℝ) (hδ : 0<δ)
    (hsep : ∀ z ∈ SetOfZeros (3/4) f, δ≤‖w-z‖) :
    let S := (finiteSetOfZeros_mono (by norm_num : (3/4:ℝ)<1) hf).toFinset
    ‖BlaschkeB (3/4) (7/8) f w‖ ≤ ‖f w‖*(2/δ)^(∑ z ∈ S, analyticOrderNatAt f z) := by
  classical
  let hS := finiteSetOfZeros_mono (by norm_num : (3/4:ℝ)<1) hf
  have hwz : w ∉ SetOfZeros (3/4) f := by
    intro h
    simpa using (hδ.trans_le (hsep w h))
  dsimp only
  rw [BlaschkeB,dif_pos hS,Cf,dif_pos hS,dif_neg hwz,norm_mul,norm_div,norm_prod,norm_prod,
    div_eq_mul_inv,mul_assoc,←Finset.prod_inv_distrib,←Finset.prod_mul_distrib]
  simp only [norm_pow]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro i hi
    positivity
  · intro i hi
    have hih := hS.mem_toFinset.mp hi
    have hiδ := hsep i hih
    rw [←inv_pow,←mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    rw [←div_eq_inv_mul]
    apply div_le_div₀ (by norm_num) _ hδ hiδ
    push_cast
    exact denominator_factor_le hw hih.1

/-- A pointwise minimum-modulus bound on the inner half-disk using only the outer supremum
and separation from the zero divisor in the three-quarter disk. -/
theorem normalized_disk_log_bound {f : ℂ→ℂ}
    (ha : AnalyticOnNhd ℂ f (closedBall 0 1)) (h0 : f 0=1)
    (hf : (SetOfZeros 1 f).Finite)
    (B : ℝ) (hB : 1≤B) (hupper : ∀ v : ℂ, ‖v‖≤7/8 → ‖f v‖≤B)
    (w : ℂ) (hw : ‖w‖≤1/2) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1)
    (hsep : ∀ u ∈ SetOfZeros (3/4) f, δ≤‖w-u‖) :
    f w ≠ 0 ∧ -Real.log ‖f w‖ ≤
      4*(1+Real.log B) + (1/Real.log ((7/8)/(3/4)))*Real.log B * Real.log (2/δ) := by
  classical
  let G := BlaschkeB (3/4) (7/8) f
  have hf0 : f 0 ≠ 0 := by simp [h0]
  have h₁ := BlaschkeAnalytic (by norm_num : (0:ℝ)<3/4) (by norm_num : (3/4:ℝ)<7/8)
      (by norm_num) hf ha hf0
  have h₂ := BlaschkeNonzero (by norm_num : (0:ℝ)<3/4) (by norm_num : (3/4:ℝ)<7/8)
      (by norm_num) hf ha hf0
  have h₃ := norm_fOfZero_le_norm_BlaschkeOfZero (by norm_num : (0:ℝ)<3/4)
      (by norm_num : (3/4:ℝ)<7/8) (by norm_num) hf hf0
  have hG0 : 1 ≤ ‖G 0‖ := by simpa [G,h0] using h₃
  have hG₀ : 0 < ‖G 0‖ := zero_lt_one.trans_le hG0
  have h₄ (v : ℂ) (hv : ‖v‖≤7/8) : ‖G v‖≤B :=
    DiskBound (by norm_num) (by norm_num) (by norm_num) hf ha hf0 hupper
      (mem_closedBall_zero_iff.mpr hv)
  obtain ⟨J,hJ,hJ0,_,hlog⟩ := LogOfAnalyticFunction (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (1/2:ℝ)<3/4)
    (h₁.mono (closedBall_subset_closedBall (by norm_num))) h₂
  have hjre (v : ℂ) (hv : v ∈ ball 0 (3/4)) : (J v).re ≤ 1+Real.log B := by
    rw [←hlog v hv]
    have hm := Real.log_le_log (norm_pos_iff.mpr (h₂ v (ball_subset_closedBall hv)))
      (h₄ v ((mem_ball_zero_iff.mp hv).le.trans (by norm_num)))
    linarith [Real.log_nonneg hG0]
  have hbound := borelCaratheodory' (by linarith [Real.log_nonneg hB] : 0<1+Real.log B)
    (by norm_num : (0:ℝ)<3/4) (by norm_num : (1/2:ℝ)<3/4) hJ.analyticOn hJ0 hjre
    (mem_closedBall_zero_iff.mpr hw)
  have hw' : w ∈ ball 0 (3/4) := mem_ball_zero_iff.mpr (hw.trans_lt (by norm_num))
  have hgw := hlog w hw'
  have hlow : -Real.log ‖G w‖ ≤ 4*(1+Real.log B) := by
    change Real.log ‖G w‖ - Real.log ‖G 0‖ = (J w).re at hgw
    norm_num at hbound
    linarith [Complex.abs_re_le_norm (J w),neg_le_abs (J w).re,Real.log_nonneg hG0]
  have hw0 : f w ≠ 0 := by
    intro h
    have hm := hsep w ⟨hw.trans (by norm_num),h⟩
    simpa using hδ.trans_le hm
  have n := ZerosBound (by norm_num : (0:ℝ)<3/4) (by norm_num)
    (by norm_num : (3/4:ℝ)<7/8) (by norm_num) ha h0 hf hupper
  have hprod := blaschke_point_bound hf hw δ hδ hsep
  have hlprod := Real.log_le_log (norm_pos_iff.mpr (h₂ w (ball_subset_closedBall hw'))) hprod
  rw [Real.log_mul (norm_pos_iff.mpr hw0).ne' (by positivity),Real.log_pow] at hlprod
  have hdlog : 0 ≤ Real.log (2/δ) := Real.log_nonneg ((one_le_div hδ).mpr (by linarith))
  exact ⟨hw0,by linarith [mul_le_mul_of_nonneg_right n hdlog]⟩

end
end MasulloRH.SynthMinimum
end StandaloneSynthMinimumDisk


-- Local source: SynthMinimumAffine
section StandaloneSynthMinimumAffine
open Complex Metric Set Filter
open scoped Topology
namespace MasulloRH.SynthMinimum
noncomputable section

private theorem finite_normalized_zeros {f : ℂ→ℂ} (hf : Differentiable ℂ f) (hn : f 0≠0) :
    (Disc.SetOfZeros 1 f).Finite := by
  by_contra h
  have hcompact := isCompact_closedBall (0:ℂ) 1
  obtain ⟨x,_,hx⟩ := (Set.not_finite.mp h).exists_accPt_of_subset_isCompact hcompact
    (fun y hy => mem_closedBall_zero_iff.mpr hy.1)
  have hfreq : ∃ᶠ y in 𝓝[≠] x, f y=0 := by
    rw [frequently_nhdsWithin_iff]
    exact (accPt_iff_frequently.mp hx).mono fun y hy => ⟨hy.2.2,hy.1⟩
  have htop := analyticOrderAt_eq_top.mpr ((hf.analyticAt x).frequently_zero_iff_eventually_zero.mp hfreq)
  have heq := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero x hf.analyticAt).mp htop
  exact hn (congrFun heq 0)

/-- Minimum modulus at distance at most two from a nonzero anchor. Only distances to
zeros in the radius-three disk enter, with a radius-four disk for the upper bound. -/
theorem affine_log_bound (F : ℂ→ℂ) (hF : Differentiable ℂ F) (c s : ℂ)
    (hc : F c ≠ 0) (hs : ‖s-c‖≤2) (B : ℝ) (hB : 1≤B)
    (hu : ∀ v : ℂ, ‖v-c‖≤4 → ‖F v‖ ≤ B*‖F c‖)
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) (hsep : ∀ v : ℂ, ‖v-c‖≤3 → F v=0 → 4*δ≤‖s-v‖) :
    F s ≠ 0 ∧ -Real.log ‖F s‖ ≤ -Real.log ‖F c‖ +
      (4*(1+Real.log B) + (1/Real.log ((7/8)/(3/4)))*Real.log B * Real.log (2/δ)) := by
  let f (v : ℂ) := F (c+4*v)/F c
  let w : ℂ := (s-c)/4
  have hf : Differentiable ℂ f := by
    unfold f
    fun_prop
  have h0 : f 0=1 := by simp [f,hc]
  have hw : ‖w‖≤1/2 := by
    dsimp [w]
    rw [norm_div]
    norm_num
    linarith
  have hu' (v : ℂ) (hv : ‖v‖≤7/8) : ‖f v‖≤B := by
    dsimp only [f]
    rw [norm_div,div_le_iff₀ (norm_pos_iff.mpr hc)]
    apply hu
    rw [add_sub_cancel_left,norm_mul]
    norm_num; linarith
  have hsep' (v : ℂ) (hv : v ∈ Disc.SetOfZeros (3/4) f) : δ≤‖w-v‖ := by
    have hv' : F (c+4*v)=0 := by simpa [f,hc] using hv.2
    have hvn : ‖(c+4*v)-c‖≤3 := by
      rw [add_sub_cancel_left,norm_mul]
      norm_num
      linarith [hv.1]
    have ha := hsep (c+4*v) hvn hv'
    rw [show s-(c+4*v) = 4*(w-v) by dsimp [w]; ring,norm_mul] at ha
    norm_num at ha
    linarith
  have ⟨h₁,h₂⟩ := normalized_disk_log_bound (fun x _ => hf.analyticAt x) h0
    (finite_normalized_zeros hf (h0 ▸ one_ne_zero)) B hB hu' w hw δ hδ hδ1 hsep'
  have hsw : c+4*w = s := by dsimp [w]; ring
  dsimp only [f] at h₁ h₂
  rw [hsw] at h₁ h₂
  have hsn : F s≠0 := (div_ne_zero_iff.mp h₁).1
  rw [norm_div,Real.log_div (norm_pos_iff.mpr hsn).ne' (norm_pos_iff.mpr hc).ne'] at h₂
  exact ⟨hsn,by linarith⟩

end
end MasulloRH.SynthMinimum
end StandaloneSynthMinimumAffine


-- Local source: SynthMinimumUniform
section StandaloneSynthMinimumUniform
open Complex Metric Set
namespace MasulloRH.SynthMinimum
noncomputable section

set_option maxHeartbeats 1300000 in
/-- Uniform quadratic control of the positive part of the reciprocal logarithm in a
closed interior strip, outside polynomial neighborhoods of the nontrivial zeros. -/
theorem strip_log_bound (F : ℂ→ℂ) (hF : Differentiable ℂ F)
    (hbnd : ∃ M : ℝ, 0<M ∧ ∀ v : ℂ, |v.re|≤6 → ‖F v‖≤M)
    (hanc : ∃ C : ℝ, 0<C ∧ ∀ v : ℂ, v.re=2 →
      1≤‖F v‖*(C*Real.exp (Real.pi*|v.im|)))
    (hdiv : ∀ v : ℂ, 0<v.re → v.re<1 → F v=0 → riemannZeta v=0)
    (a b : ℝ) (ha : 0<a) (hb : b<1) (d : ℝ) (hd : 0<d) (A : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ s : ℂ, a ≤ s.re → s.re≤b →
      (∀ v : ℂ, riemannZeta v=0 → 0<v.re → v.re<1 → |v.im-s.im|≤3 →
        d/(1+|s.im|)^A ≤ ‖s-v‖) →
      F s≠0 ∧ max 0 (-Real.log ‖F s‖) ≤ D*(1+|s.im|)^2 := by
  obtain ⟨M,hM,hm⟩ := hbnd
  obtain ⟨C,hC,hc⟩ := hanc
  let H := |Real.log M| + |Real.log C| + Real.pi + 1
  let ε := min 1 (min a (min (1-b) d)) / 4
  have hε : 0<ε := by dsimp [ε]; positivity [sub_pos.mpr hb]
  have hε1 : ε≤1 := by dsimp [ε]; linarith [min_le_left (1:ℝ) (min a (min (1-b) d))]
  have hεa : 4*ε≤a := by
    have h := (min_le_right 1 (min a (min (1-b) d))).trans (min_le_left _ _)
    dsimp [ε]; linarith
  have hεb : 4*ε≤1-b := by
    have h := (min_le_right 1 (min a (min (1-b) d))).trans ((min_le_right _ _).trans (min_le_left _ _))
    dsimp [ε]; linarith
  have hεd : 4*ε≤d := by
    have h := (min_le_right 1 (min a (min (1-b) d))).trans ((min_le_right _ _).trans (min_le_right _ _))
    dsimp [ε]; linarith
  let L := Real.log (2/ε)+(A:ℝ)
  have hL0 : 0 ≤ Real.log (2/ε) := Real.log_nonneg ((one_le_div hε).mpr (by linarith))
  have hL : 0≤L := add_nonneg hL0 (by positivity)
  have hH : 0<H := by dsimp [H]; positivity [Real.pi_pos]
  let K : ℝ := 1/Real.log ((7/8)/(3/4))
  have hK : 0<K := by dsimp [K]; positivity [Real.log_pos (by norm_num : (1:ℝ)<(7/8)/(3/4))]
  refine ⟨H+4*(1+H)+K*H*L,by positivity,?_⟩
  intro s hs₁ hs₂ hsep
  let X := 1+|s.im|
  have hX : 1≤X := by dsimp [X]; linarith [abs_nonneg s.im]
  have hXp : 0<X := zero_lt_one.trans_le hX
  have hXpA : 1≤X^A := one_le_pow₀ hX
  let q : ℂ := 2+(s.im:ℂ)*I
  have hqr : q.re=2 := by simp [q]
  have hqi : q.im=s.im := by simp [q]
  have hdiff : s-q = ((s.re-2:ℝ):ℂ) := by
    apply Complex.ext <;> simp [q]
  have hs : ‖s-q‖≤2 := by
    rw [hdiff,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
    linarith
  have hcc := hc q hqr
  rw [hqi] at hcc
  have hq : F q≠0 := by
    intro h
    norm_num [h] at hcc
  have hClog : Real.log C + Real.pi*|s.im| ≤ H*X := by
    have hh := mul_le_mul_of_nonneg_left hX (add_nonneg (abs_nonneg (Real.log M)) (abs_nonneg (Real.log C)))
    dsimp [H,X] at *
    nlinarith [le_abs_self (Real.log C),abs_nonneg (Real.log M),abs_nonneg (Real.log C),abs_nonneg s.im,Real.pi_pos]
  have hMlog : Real.log M + Real.log C + Real.pi*|s.im| ≤ H*X := by
    have hh := mul_le_mul_of_nonneg_left hX (add_nonneg (abs_nonneg (Real.log M)) (abs_nonneg (Real.log C)))
    dsimp [H,X] at hh ⊢
    nlinarith [le_abs_self (Real.log M),le_abs_self (Real.log C),abs_nonneg s.im,Real.pi_pos]
  have hlogq : -Real.log ‖F q‖ ≤ H*X := by
    have hl := Real.log_le_log zero_lt_one hcc
    rw [Real.log_one,Real.log_mul (norm_pos_iff.mpr hq).ne' (by positivity),
      Real.log_mul hC.ne' (Real.exp_pos _).ne',Real.log_exp] at hl
    linarith
  have hu (v : ℂ) (hv : ‖v-q‖≤4) : ‖F v‖ ≤ Real.exp (H*X)*‖F q‖ := by
    have hvb := (Complex.abs_re_le_norm (v-q)).trans hv
    rw [Complex.sub_re,hqr,abs_le] at hvb
    have hM' := hm v (abs_le.mpr ⟨by linarith [hvb.1],by linarith [hvb.2]⟩)
    have hh := Real.exp_le_exp.mpr hMlog
    rw [Real.exp_add,Real.exp_add,Real.exp_log hM,Real.exp_log hC] at hh
    calc
      _ ≤ M := hM'
      _ ≤ M*(‖F q‖*(C*Real.exp (Real.pi*|s.im|))) := by
        simpa using mul_le_mul_of_nonneg_left hcc hM.le
      _ = M*C*Real.exp (Real.pi*|s.im|)*‖F q‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
  let δ := ε/X^A
  have hδ : 0<δ := div_pos hε (pow_pos hXp _)
  have hδε : δ≤ε := div_le_self hε.le hXpA
  have hsep' (v : ℂ) (hv : ‖v-q‖≤3) (hvz : F v=0) : 4*δ≤‖s-v‖ := by
    by_cases h₀ : 0<v.re
    · by_cases h₁ : v.re<1
      · have hi := (Complex.abs_im_le_norm (v-q)).trans hv
        rw [Complex.sub_im,hqi] at hi
        apply le_trans _ (hsep v (hdiv v h₀ h₁ hvz) h₀ h₁ hi)
        rw [show 4*δ=4*ε/X^A by dsimp [δ]; ring]
        exact div_le_div_of_nonneg_right hεd (pow_nonneg hXp.le _)
      · have hre := (neg_le_abs (s-v).re).trans (Complex.abs_re_le_norm (s-v))
        rw [Complex.sub_re] at hre
        linarith
    · have hre := (le_abs_self (s-v).re).trans (Complex.abs_re_le_norm (s-v))
      rw [Complex.sub_re] at hre
      linarith
  have hB : 1≤Real.exp (H*X) := Real.one_le_exp (by positivity)
  obtain ⟨hFs,hl⟩ := affine_log_bound F hF q s hq hs _ hB hu δ hδ (hδε.trans hε1) hsep'
  rw [Real.log_exp] at hl
  have hlogδ : Real.log (2/δ)≤L*X := by
    rw [show 2/δ = (2/ε)*X^A by dsimp [δ]; field_simp,Real.log_mul (by positivity) (pow_pos hXp _).ne',Real.log_pow]
    have hlX := Real.log_le_sub_one_of_pos hXp
    dsimp [L]
    nlinarith [mul_le_mul_of_nonneg_left hX hL0,mul_le_mul_of_nonneg_left hlX (Nat.cast_nonneg (α:=ℝ) A)]
  have hfinal : -Real.log ‖F s‖ ≤ (H+4*(1+H)+K*H*L)*X^2 := by
    change -Real.log ‖F s‖ ≤ -Real.log ‖F q‖ + (4*(1+H*X)+K*(H*X)*Real.log (2/δ)) at hl
    have hX2 : X≤X^2 := by nlinarith [mul_nonneg hXp.le (sub_nonneg.mpr hX)]
    calc
      _ ≤ H*X + (4*(1+H*X) + K*(H*X)*(L*X)) := by
        linarith [mul_le_mul_of_nonneg_left hlogδ (by positivity : 0≤K*(H*X))]
      _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_left hX2 hH.le,hX.trans hX2]
  exact ⟨hFs,max_le (by positivity) hfinal⟩

end
end MasulloRH.SynthMinimum
end StandaloneSynthMinimumUniform


-- Local source: SynthGeneratorAnchor
section StandaloneSynthGeneratorAnchor
open Set MeasureTheory Filter
open scoped Topology
namespace MasulloRH.SynthesisStrip
noncomputable section

private theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin,norm_div,norm_mul,Complex.norm_I,mul_one,show ‖(2:ℂ)‖=2 by norm_num,div_le_iff₀ (by norm_num)]
  apply (norm_sub_le _ _).trans
  simp only [Complex.norm_exp,Complex.mul_I_re,Complex.neg_im,neg_neg]
  linarith [Real.exp_le_exp.mpr (le_abs_self z.im),Real.exp_le_exp.mpr (neg_le_abs z.im)]

private theorem norm_gamma_one (w : ℂ) (hw : w.re=1) : ‖Complex.Gamma w‖ ≤ 1 := by
  rw [Complex.Gamma_eq_integral (by linarith),Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  rw [←integral_exp_neg_Ioi_zero]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_nonneg _),Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.sub_re,hw,Complex.one_re,sub_self,Real.rpow_zero,mul_one]

private theorem inv_gamma_one_high (w : ℂ) (hw : w.re=1) (hi : 1≤|w.im|) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ Real.exp (Real.pi*|w.im|) := by
  have hw' : 1≤‖1-w‖ := hi.trans (by simpa using Complex.abs_im_le_norm (1-w))
  have hw0 : 1-w≠0 := by intro he; rw [he,norm_zero] at hw'; linarith
  have hgt := norm_gamma_one ((1-w)+1) (by simp [hw])
  rw [Complex.Gamma_add_one _ hw0,norm_mul] at hgt
  have hG : ‖Complex.Gamma (1-w)‖ ≤ 1 :=
    (le_mul_of_one_le_left (norm_nonneg _) hw').trans hgt
  have hg₁ : Complex.Gamma w≠0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hg₂ : Complex.Gamma (1-w)≠0 := by
    intro he
    have hh := Complex.Gamma_add_one (1-w) hw0
    rw [he,mul_zero] at hh
    exact Complex.Gamma_ne_zero_of_re_pos (by simp [hw]) hh
  have hs₀ : Complex.sin (Real.pi*w)≠0 := by
    intro h
    have hh := Complex.Gamma_mul_Gamma_one_sub w
    rw [h,div_zero] at hh
    exact mul_ne_zero hg₁ hg₂ hh
  have hπ : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hEq : (Complex.Gamma w)⁻¹=Complex.Gamma (1-w)*Complex.sin (Real.pi*w)/(Real.pi:ℂ) := by
    have he := (eq_div_iff hs₀).mp (Complex.Gamma_mul_Gamma_one_sub w)
    field_simp [hg₁,hπ]
    rw [mul_comm w (Real.pi:ℂ)]
    linear_combination -he
  rw [hEq,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  apply (div_le_self (by positivity) (by linarith [Real.pi_gt_three] : 1≤Real.pi)).trans
  apply (mul_le_of_le_one_left (norm_nonneg _) hG).trans
  have h := norm_sin_le_exp ((Real.pi:ℂ)*w)
  simpa [Complex.mul_im,abs_mul,abs_of_pos Real.pi_pos] using h

theorem inv_gamma_one_bound :
    ∃ C : ℝ, 0<C ∧ ∀ w : ℂ, w.re=1 → ‖(Complex.Gamma w)⁻¹‖ ≤ C*Real.exp (Real.pi*|w.im|) := by
  let f (t : ℝ) := ‖(Complex.Gamma (1+(t:ℂ)*Complex.I))⁻¹‖
  have hc : Continuous f := Complex.differentiable_one_div_Gamma.continuous.norm.comp (by fun_prop)
  obtain ⟨M,hM⟩ := (isCompact_Icc (α:=ℝ) (a:=-1) (b:=1)).bddAbove_image hc.continuousOn
  refine ⟨max M 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),fun w hw => ?_⟩
  have h1 : 1≤Real.exp (Real.pi*|w.im|) := Real.one_le_exp (mul_nonneg Real.pi_pos.le (abs_nonneg _))
  by_cases hh : 1≤|w.im|
  · exact (inv_gamma_one_high w hw hh).trans (le_mul_of_one_le_left (Real.exp_nonneg _) (le_max_right _ _))
  have hI := abs_lt.mp (lt_of_not_ge hh)
  have hM' := hM (mem_image_of_mem f (show w.im∈Icc (-1:ℝ) 1 from ⟨hI.1.le,hI.2.le⟩))
  have he : (1:ℂ)+(w.im:ℂ)*Complex.I=w := by apply Complex.ext <;> simp [hw]
  dsimp only [f] at hM'
  rw [he] at hM'
  exact hM'.trans ((le_max_left _ _).trans (le_mul_of_one_le_right (le_trans (by norm_num : (0:ℝ)≤1) (le_max_right _ _)) h1))

def explicitGenerator (s : ℂ) : ℂ := (1-(2:ℂ)^(-s))*(1-(2:ℂ)^(1-s))*completedRiemannZeta s

theorem generator_anchor :
    ∃ C : ℝ, 0<C ∧ ∀ s : ℂ, s.re=2 →
      1 ≤ ‖explicitGenerator s‖ * (C*Real.exp (Real.pi*|s.im|)) := by
  obtain ⟨M,hM,hm⟩ := inv_gamma_one_bound
  let a := 2-Real.pi^2/6
  have ha : 0<a := by dsimp [a]; nlinarith [Real.pi_lt_d2,Real.pi_pos]
  refine ⟨8*M*Real.pi/a,by positivity,fun s hs => ?_⟩
  have hζ := Zeta23.RvM.norm_riemannZeta_sub_one_le (s:=s) hs.ge
  have hl : a≤‖riemannZeta s‖ := by
    have h := norm_sub_le (riemannZeta s) (riemannZeta s-1)
    simp at h; dsimp [a]; linarith
  have hf (c : ℂ) (hc : c.re = -2 ∨ c.re = -1) : 1/2 ≤ ‖1-(2:ℂ)^c‖ := by
    have h := norm_sub_norm_le (1:ℂ) ((2:ℂ)^c)
    rw [norm_one,show ‖(2:ℂ)^c‖=(2:ℝ)^c.re from Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<2) c] at h
    rcases hc with hh|hh <;> rw [hh] at h <;> norm_num at h <;> linarith
  have ha₁ := hf (-s) (Or.inl (by simp [hs]))
  have ha₂ := hf (1-s) (Or.inr (by simp [hs]; norm_num))
  have hs2 : (s/2).re=1 := by simp [Complex.div_ofNat_re,hs]
  have hn := hm (s/2) hs2
  have hge := Complex.Gamma_ne_zero_of_re_pos (s:=s/2) (by rw [hs2]; norm_num)
  rw [norm_inv,inv_le_iff_one_le_mul₀ (norm_pos_iff.mpr hge)] at hn
  have hh : 1 ≤ ‖Complex.Gamma (s/2)‖*(M*Real.exp (Real.pi*|s.im|)) := by
    apply hn.trans
    rw [mul_comm (M*Real.exp _),Complex.div_ofNat_im,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    gcongr; linarith [abs_nonneg s.im]
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hs0 : s≠0 := by intro he; rw [he,Complex.zero_re] at hs; norm_num at hs
  have hcomp := (eq_div_iff hΓ).mp (riemannZeta_def_of_ne_zero hs0)
  have hpow : ‖(Real.pi:ℂ)^(-s/2)‖=Real.pi⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,Complex.div_ofNat_re,Complex.neg_re,hs]
    norm_num [Real.rpow_neg_one]
  rw [explicitGenerator,← hcomp,Complex.Gammaℝ_def]
  simp only [norm_mul,hpow]
  have hmain := mul_le_mul (mul_le_mul ha₁ ha₂ (by norm_num) (norm_nonneg _)) hl ha.le
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    1 ≤ ‖Complex.Gamma (s/2)‖*(M*Real.exp (Real.pi*|s.im|)) := hh
    _ ≤ _ := by
      have hpi := Real.pi_pos
      field_simp
      nlinarith only [hmain,ha]

end
end MasulloRH.SynthesisStrip
end StandaloneSynthGeneratorAnchor


-- Local source: ThetaGeneralBounds
section StandaloneThetaGeneralBounds
open Set Filter MeasureTheory Asymptotics
open scoped Topology SchwartzMap FourierTransform
namespace MasulloRH
noncomputable section

private def latticeWeight (k : ℕ) (n : ℕ) : ℝ := (((n:ℝ)+1)^k)⁻¹

private lemma summable_latticeWeight (k : ℕ) (hk : 1 < k) : Summable (latticeWeight k) := by
  have h : -((k:ℕ):ℝ) < -1 := by exact_mod_cast (show -((k:ℕ):ℤ) < -1 by omega)
  have hz := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr h)
  apply hz.congr
  intro n
  dsimp [latticeWeight]
  rw [Nat.cast_add, Nat.cast_one, Real.rpow_neg (by positivity), Real.rpow_natCast]

def thetaNat (f : 𝓢(ℝ,ℂ)) (x : ℝ) := ∑' n : ℕ, f (((n:ℝ)+1)*x)

private lemma thetaTerm_bound (f : 𝓢(ℝ,ℂ)) (k n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖f (((n:ℝ)+1)*x)‖ ≤ ((SchwartzMap.seminorm ℝ k 0) f) * (x^k)⁻¹ * latticeWeight k n := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have h := SchwartzMap.norm_pow_mul_le_seminorm ℝ f k (((n:ℝ)+1)*x)
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hn hx), mul_pow] at h
  rw [latticeWeight, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hn _), ← div_eq_mul_inv, le_div_iff₀ (pow_pos hx _)]
  nlinarith only [h]

private lemma thetaNat_summable (f : 𝓢(ℝ,ℂ)) (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => f (((n:ℝ)+1)*x)) :=
  ((summable_latticeWeight 2 (by norm_num)).mul_left _).of_norm_bounded (fun n => thetaTerm_bound f 2 n hx)

private lemma thetaNat_bound (f : 𝓢(ℝ,ℂ)) (k : ℕ) (hk : 1 < k) {x : ℝ} (hx : 0 < x) :
    ‖thetaNat f x‖ ≤ (((SchwartzMap.seminorm ℝ k 0) f) * ∑' n, latticeWeight k n) * (x^k)⁻¹ := by
  apply (norm_tsum_le_tsum_norm ((thetaNat_summable f x hx).norm)).trans
  apply (Summable.tsum_le_tsum (fun n => thetaTerm_bound f k n hx) (thetaNat_summable f x hx).norm
    ((summable_latticeWeight k hk).mul_left _)).trans_eq
  rw [tsum_mul_left]; ring

lemma thetaNat_continuousOn (f : 𝓢(ℝ,ℂ)) : ContinuousOn (thetaNat f) (Ioi 0) := by
  intro x hx
  change 0 < x at hx
  have hu : Summable (fun n : ℕ => (SchwartzMap.seminorm ℝ 2 0 f) * ((x/2)^2)⁻¹ * latticeWeight 2 n) :=
    (summable_latticeWeight 2 (by norm_num)).mul_left _
  have hc : ContinuousOn (thetaNat f) (Ioi (x/2)) := by
    apply continuousOn_tsum (fun n => (f.continuous.comp (continuous_const.mul continuous_id)).continuousOn) hu
    intro n y hy
    have hx' : 0 < x/2 := by positivity
    have hy' : x/2 < y := hy
    apply (thetaTerm_bound f 2 n (lt_trans hx' hy')).trans
    gcongr
    dsimp [latticeWeight]; positivity
  exact ((hc.continuousAt (isOpen_Ioi.mem_nhds (show x/2 < x by linarith)))).continuousWithinAt

def reflectS (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ)) f

def theta (f : 𝓢(ℝ,ℂ)) (x : ℝ) := ∑' n : ℤ, f ((n:ℝ)*x)

lemma theta_split (f : 𝓢(ℝ,ℂ)) (hf : f 0 = 0) {x : ℝ} (hx : 0 < x) :
    theta f x = thetaNat (f + reflectS f) x := by
  have h₁ := thetaNat_summable f x hx
  have h₂ := thetaNat_summable (reflectS f) x hx
  have hpos : Summable (fun n : ℕ => f ((((n:ℤ)+1 : ℤ) : ℝ)*x)) := by simpa using h₁
  have hneg : Summable (fun n : ℕ => f (((-((n:ℤ)+1) : ℤ) : ℝ)*x)) := by
    apply h₂.congr
    intro n
    change f (-(((n:ℝ)+1)*x)) = _
    push_cast; congr 1; ring
  have hsum := tsum_of_add_one_of_neg_add_one (f:=fun n : ℤ => f ((n:ℝ)*x)) hpos hneg
  change (∑' n : ℤ, f ((n:ℝ)*x)) = _
  rw [hsum]
  simp only [Int.cast_add, Int.cast_one, Int.cast_natCast, Int.cast_neg, Int.cast_zero, zero_mul, hf, add_zero]
  change _ = ∑' n : ℕ, (f (((n:ℝ)+1)*x) + f (-(((n:ℝ)+1)*x)))
  rw [h₁.tsum_add (g:=fun n : ℕ => f (-(((n:ℝ)+1)*x))) h₂]
  simp only [neg_mul]

/-- Uniform positive-scale decay of the Schwartz lattice sum in every integral order above one. -/
theorem thetaSchwartz_bound (f : 𝓢(ℝ,ℂ)) (hf : f 0 = 0) (k : ℕ) (hk : 1 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ‖∑' n : ℤ, f ((n:ℝ)*x)‖ ≤ C * (x^k)⁻¹ := by
  refine ⟨(SchwartzMap.seminorm ℝ k 0) (f+reflectS f) * ∑' n, latticeWeight k n, ?_, ?_⟩
  · apply mul_nonneg (by positivity)
    apply tsum_nonneg
    intro n; dsimp [latticeWeight]; positivity
  · intro x hx
    change ‖theta f x‖ ≤ _
    rw [theta_split f hf hx]
    exact thetaNat_bound _ k hk hx

end
end MasulloRH
end StandaloneThetaGeneralBounds


-- Local source: ThetaPoisson
section StandaloneThetaPoisson
open MeasureTheory Filter Set FourierTransform
open scoped SchwartzMap FourierTransform Topology
set_option autoImplicit false
namespace MasulloSynthesis
noncomputable section

theorem theta_poisson_scaled (f : 𝓢(ℝ,ℂ)) {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, f ((n:ℝ)*a)) =
    (a⁻¹:ℝ) • ∑' n : ℤ, (𝓕 f) ((n:ℝ)*a⁻¹) := by
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 a ha.ne')
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hg (x : ℝ) : g x = f (a*x) := rfl
  have hscale (ξ : ℝ) : (𝓕 g) ξ = (a⁻¹:ℝ) • (𝓕 f) (ξ*a⁻¹) := by
    change 𝓕 (⇑g) ξ = (a⁻¹:ℝ) • 𝓕 (⇑f) (ξ*a⁻¹)
    rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
    let F (x : ℝ) := Complex.exp (↑(-2*Real.pi*x*(ξ*a⁻¹)) * Complex.I) • f x
    calc
      _ = ∫ x : ℝ, F (a*x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only [F]
          rw [hg]
          congr 3
          field_simp
      _ = _ := by
        have h := Measure.integral_comp_mul_left F a
        simpa only [abs_of_pos (inv_pos.mpr ha)] using h
  have h := g.tsum_eq_tsum_fourier 0
  simp only [zero_add, hg, hscale, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at h
  rw [← tsum_const_smul'']
  simpa [mul_comm a] using h
end
end MasulloSynthesis
end StandaloneThetaPoisson


-- Local source: StripThetaRows
section StandaloneStripThetaRows
open MeasureTheory Filter Set FourierTransform
open scoped Topology FourierTransform SchwartzMap
namespace MasulloRH.StripTheta
noncomputable section

def logTheta (g : 𝓢(ℝ,ℂ)) (x : ℝ) : ℂ :=
  (Real.exp (x/2):ℂ)* ∑' n : ℤ,g ((n:ℝ)*Real.exp x)

theorem logTheta_continuous (g : 𝓢(ℝ,ℂ)) (h0 : g 0=0) : Continuous (logTheta g) := by
  apply (show Continuous (fun x : ℝ => (Real.exp (x/2):ℂ)) by fun_prop).mul
  have he : (fun x : ℝ => ∑' n : ℤ,g ((n:ℝ)*Real.exp x)) = thetaNat (g+reflectS g) ∘ Real.exp :=
    funext (fun x => theta_split g h0 (Real.exp_pos x))
  rw [he]
  exact (thetaNat_continuousOn _).comp_continuous Real.continuous_exp Real.exp_pos

theorem logTheta_poisson (g : 𝓢(ℝ,ℂ)) (x : ℝ) : logTheta g x=logTheta (𝓕 g) (-x) := by
  simp only [logTheta,MasulloSynthesis.theta_poisson_scaled g (Real.exp_pos x),Real.exp_neg,
    Complex.real_smul,←mul_assoc,←Complex.ofReal_mul]
  congr 2
  rw [←Real.exp_neg,←Real.exp_add]
  congr 1
  ring

private theorem logTheta_decay_right (g : 𝓢(ℝ,ℂ)) (h0 : g 0=0) (k : ℕ) (hk : 1<k) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, ‖logTheta g x‖≤C*Real.exp ((1/2-(k:ℝ))*x) := by
  obtain ⟨C,hC,h⟩ := thetaSchwartz_bound g h0 k hk
  refine ⟨C,hC,fun x => ?_⟩
  rw [logTheta,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply (mul_le_mul_of_nonneg_left (h _ (Real.exp_pos x)) (Real.exp_nonneg _)).trans_eq
  rw [←Real.exp_nat_mul,←Real.exp_neg,mul_left_comm,←Real.exp_add]
  congr 2
  ring

/-- Theta rows of two-moment tests decay faster than any fixed exponential in both log tails. -/
theorem logTheta_exp_decay (g : 𝓢(ℝ,ℂ)) (h0 : g 0=0) (hI : (∫ t : ℝ,g t)=0) (a : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, ‖logTheta g x‖ ≤ C*Real.exp (-a*|x|) := by
  obtain ⟨j,hj⟩ := exists_nat_ge a
  let k := j+2
  have hk : 1<k := by dsimp [k]; omega
  have hka : 1/2-(k:ℝ) ≤ -a := by dsimp [k]; push_cast; linarith
  have hF : (𝓕 g : 𝓢(ℝ,ℂ)) 0=0 := by
    change 𝓕 (⇑g) 0=0; simpa [Real.fourier_real_eq_integral_exp_smul] using hI
  obtain ⟨A,hA,h₁⟩ := logTheta_decay_right g h0 k hk
  obtain ⟨B,hB,h₂⟩ := logTheta_decay_right (𝓕 g) hF k hk
  refine ⟨max A B,hA.trans (le_max_left _ _),fun x => ?_⟩
  rcases le_total 0 x with hx|hx
  · rw [abs_of_nonneg hx]
    exact (h₁ x).trans (mul_le_mul (le_max_left _ _)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hka hx)) (Real.exp_nonneg _) (hA.trans (le_max_left _ _)))
  · rw [abs_of_nonpos hx,logTheta_poisson g x]
    exact (h₂ (-x)).trans (mul_le_mul (le_max_right _ _)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hka (neg_nonneg.mpr hx))) (Real.exp_nonneg _)
      (hB.trans (le_max_right _ _)))

end
end MasulloRH.StripTheta
end StandaloneStripThetaRows


-- Local source: StripPhysicalJets
section StandaloneStripPhysicalJets
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace MasulloRH.StripPhysical
noncomputable section

/-- A polynomial factor uses only the strict margin between the two exponential rates. -/
theorem polynomial_exp_bound {a b : ℝ} (h : |a|<b) (r : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ x : ℝ, |x|^r*Real.exp (a*x) ≤ C*Real.exp (b*|x|) := by
  let d := b-|a|
  have hd : 0<d := sub_pos.mpr h
  let C : ℝ := (r.factorial:ℝ)/d^r
  refine ⟨C,by dsimp [C]; positivity,fun x => ?_⟩
  have hbd := Real.pow_div_factorial_le_exp _ (mul_nonneg hd.le (abs_nonneg x)) r
  have hp : |x|^r ≤ C * Real.exp (d*|x|) := by
    have hb := (div_le_iff₀ (by positivity : 0<(r.factorial:ℝ))).mp hbd
    rw [mul_pow] at hb
    dsimp [C]
    rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hd _)]
    simpa only [mul_comm] using hb
  have he : a*x ≤ |a| *|x| := by rw [← abs_mul]; exact le_abs_self _
  calc
    _ ≤ (C*Real.exp (d*|x|))*Real.exp (|a| *|x|) :=
      mul_le_mul hp (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) (by dsimp [C]; positivity)
    _ = _ := by rw [mul_assoc,← Real.exp_add]; dsimp [d]; ring_nf

end
end MasulloRH.StripPhysical
end StandaloneStripPhysicalJets


-- Local source: StripPhysicalMoments
section StandaloneStripPhysicalMoments
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace MasulloRH.StripPhysical
noncomputable section

def moment (k : ℝ→ℂ) (z : ℂ) (j : ℕ) : ℂ :=
  ∫ y : ℝ, k y*(y:ℂ)^j*Complex.exp (z*(y:ℂ))

theorem moment_integrable {b : ℝ} {k : ℝ→ℂ} (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (b*|y|))) {z : ℂ} (hz : |z.re|<b) (j : ℕ) :
    Integrable (fun y : ℝ => k y*(y:ℂ)^j*Complex.exp (z*(y:ℂ))) := by
  obtain ⟨C,_,hb⟩ := polynomial_exp_bound hz j
  apply (hW.mul_const C).mono'
  · apply (hk.mul (show Continuous (fun y : ℝ => (y:ℂ)^j) by fun_prop).aestronglyMeasurable).mul
    exact (show Continuous (fun y : ℝ => Complex.exp (z*(y:ℂ))) by fun_prop).aestronglyMeasurable
  · apply Eventually.of_forall
    intro y
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left (hb y) (norm_nonneg (k y))).trans_eq (by ring)

end
end MasulloRH.StripPhysical
end StandaloneStripPhysicalMoments


-- Local source: StripTestAmplitude
section StandaloneStripTestAmplitude
open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff BigOperators
namespace MasulloRH.StripTrace
noncomputable section

def lap (f : ℝ → ℂ) (s : ℂ) := ∫ y : ℝ, Complex.exp (s*y)*f y

theorem mellin_eq_lap (φ : ℝ → ℂ) (w : ℂ) : mellin φ w = lap (fun y => φ (Real.exp y)) w := by
  have hd : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have him : Real.exp '' univ = Ioi 0 := by rw [image_univ,Real.range_exp]
  unfold mellin lap
  rw [← him,integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd Real.exp_injective.injOn,setIntegral_univ]
  apply integral_congr_ae; filter_upwards with x
  rw [abs_of_pos (Real.exp_pos _),Complex.real_smul,smul_eq_mul,Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),← Complex.ofReal_log (Real.exp_nonneg _),Real.log_exp,
    Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
  congr 2; ring

end
end MasulloRH.StripTrace
end StandaloneStripTestAmplitude


-- Local source: StripLaplaceMoments
section StandaloneStripLaplaceMoments
open MeasureTheory Filter Set
open scoped Topology
namespace MasulloRH.StripTrace
noncomputable section
open StripPhysical

private def kernelIntegrand (k : ℝ→ℂ) (j : ℕ) (s : ℂ) (y : ℝ) : ℂ :=
  k y*(y:ℂ)^j*Complex.exp (s*(y:ℂ))

private theorem kernel_meas {k : ℝ→ℂ} (hk : AEStronglyMeasurable k) (j : ℕ) (s : ℂ) :
    AEStronglyMeasurable (kernelIntegrand k j s) := by
  apply (hk.mul (show Continuous (fun y : ℝ => (y:ℂ)^j) by fun_prop).aestronglyMeasurable).mul
  exact (show Continuous (fun y : ℝ => Complex.exp (s*(y:ℂ))) by fun_prop).aestronglyMeasurable

theorem moment_hasDerivAt {a : ℝ} {k : ℝ→ℂ} (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (a*|y|))) (j : ℕ) {s : ℂ} (hs : |s.re|<a) :
    HasDerivAt (fun t : ℂ => moment k t j) (moment k s (j+1)) s := by
  let c := (|s.re|+a)/2
  have hc : 0≤c := by dsimp [c]; linarith [abs_nonneg s.re]
  have hsc : |s.re|<c := by dsimp [c]; linarith
  have hca : c<a := by dsimp [c]; linarith
  let U := {t : ℂ | |t.re|<c}
  have hU : U∈𝓝 s := (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).mem_nhds hsc
  obtain ⟨C,hC,hbd⟩ := polynomial_exp_bound (show |c|<a by simpa [abs_of_nonneg hc] using hca) (j+1)
  have hb (y : ℝ) (t : ℂ) (ht : t∈U) :
      ‖kernelIntegrand k (j+1) t y‖ ≤ (‖k y‖*Real.exp (a*|y|)) * C := by
    have h1 : t.re*y ≤ c*|y| := (le_abs_self _).trans
      ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right (show |t.re|<c from ht).le (abs_nonneg _)))
    have h2 := hbd |y|
    rw [abs_abs] at h2
    dsimp only [kernelIntegrand]
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    rw [mul_assoc]
    refine (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1)
      (pow_nonneg (abs_nonneg _) _)).trans h2) (norm_nonneg _)).trans_eq ?_
    ring
  have hd (y : ℝ) (t : ℂ) : HasDerivAt (fun w : ℂ => kernelIntegrand k j w y)
      (kernelIntegrand k (j+1) t y) t := by
    have hh := (((hasDerivAt_id t).mul_const (y:ℂ)).cexp.const_mul (k y*(y:ℂ)^j))
    dsimp only [id_eq,one_mul] at hh
    unfold kernelIntegrand
    convert! hh using 1 <;> first | rfl | (rw [pow_succ]; ring) | ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=kernelIntegrand k j)
    (F':=kernelIntegrand k (j+1)) hU (.of_forall (kernel_meas hk j))
    (moment_integrable hk hW hs j) (kernel_meas hk _ _)
    (.of_forall hb) (hW.mul_const C) (.of_forall (fun y t _ => hd y t))).2

end
end MasulloRH.StripTrace
end StandaloneStripLaplaceMoments


-- Local source: SynthGenerator
section StandaloneSynthGenerator
open Set MeasureTheory Filter
open scoped Topology SchwartzMap
namespace MasulloRH.SynthesisStrip
noncomputable section
open StripTrace (lap)
open StripTheta (logTheta)

def generatorTest : 𝓢(ℝ,ℂ) := Classical.choose dyadic_gaussian_theta_mellin
theorem generatorTest_zero : generatorTest 0=0 := (Classical.choose_spec dyadic_gaussian_theta_mellin).2.1
theorem generatorTest_int : (∫x : ℝ,generatorTest x)=0 := (Classical.choose_spec dyadic_gaussian_theta_mellin).2.2.1

def seed : ℝ→ℂ := logTheta generatorTest
theorem seed_cont : Continuous seed := StripTheta.logTheta_continuous _ generatorTest_zero
theorem seed_decay (a : ℝ) : ∃ C : ℝ, 0≤C ∧ ∀ x, ‖seed x‖≤C*Real.exp (-a*|x|) :=
  StripTheta.logTheta_exp_decay _ generatorTest_zero generatorTest_int a

theorem int_exp : Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  let f (x : ℝ) := Real.exp (-|x|)
  have hr : IntegrableOn f (Ioi 0) := (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).congr_fun
    (fun x hx => by simp [f,abs_of_pos (show 0<x from hx)]) measurableSet_Ioi
  have hl : IntegrableOn f (Iic 0) := (integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<1) 0).congr_fun
    (fun x hx => by simp [f,abs_of_nonpos (show x≤0 from hx)]) measurableSet_Iic
  change Integrable f
  simpa using hl.union hr

theorem seed_weighted (a : ℝ) : Integrable (fun x => ‖seed x‖*Real.exp (a*|x|)) := by
  obtain ⟨C,hC,h⟩ := seed_decay (a+1)
  apply (int_exp.const_mul C).mono' (seed_cont.norm.mul (by fun_prop)).aestronglyMeasurable
  filter_upwards with x
  change ‖‖seed x‖*Real.exp (a*|x|)‖ ≤ _
  rw [Real.norm_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_right (h x) (Real.exp_nonneg _)).trans_eq (by rw [mul_assoc,←Real.exp_add]; congr 2; ring)

/-- Uncentered Mellin argument, so the disc used for minimum modulus is centered at 2+it. -/
def E (s : ℂ) : ℂ := lap seed (s-1/2)

theorem E_entire : Differentiable ℂ E := by
  have he (s : ℂ) : HasDerivAt (lap seed) (StripPhysical.moment seed s 1) s := by
    have he := StripTrace.moment_hasDerivAt seed_cont.aestronglyMeasurable (seed_weighted (|s.re|+1)) 0
      (s:=s) (by linarith)
    have hm : (fun t : ℂ => StripPhysical.moment seed t 0)=lap seed := by
      funext t; unfold StripPhysical.moment lap; simp only [pow_zero,mul_one]; exact integral_congr_ae (.of_forall (fun x => mul_comm _ _))
    rwa [hm] at he
  exact (show Differentiable ℂ (lap seed) from fun s => (he s).differentiableAt).comp (differentiable_id.sub_const _)

theorem E_band_bound (a : ℝ) : ∃ M : ℝ, 0<M ∧ ∀ s : ℂ, |s.re|≤a → ‖E s‖≤M := by
  let G := fun x : ℝ => ‖seed x‖*Real.exp ((a+1)*|x|)
  have hi : Integrable G := seed_weighted _
  refine ⟨(∫ x,G x)+1,by linarith [integral_nonneg (μ:=volume) (f:=G) (fun x => mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))],fun s hs => ?_⟩
  have h (x : ℝ) : ‖Complex.exp ((s-1/2)*(x:ℂ))*seed x‖ ≤ G x := by
    rw [norm_mul,mul_comm,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    have h₁ : |(s-1/2).re|≤a+1 := by
      simp only [Complex.sub_re,Complex.div_ofNat_re,Complex.one_re]
      exact (abs_sub _ _).trans (by rw [abs_of_pos (by norm_num : (0:ℝ)<1/2)]; linarith)
    exact (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right h₁ (abs_nonneg _)))
  exact (norm_integral_le_of_norm_le hi (.of_forall h)).trans (by linarith)

def orbital (x : ℝ) : ℂ := ∑' n : ℤ, generatorTest ((n:ℝ)*x)

theorem E_eq_mellin (s : ℂ) : E s=mellin orbital s := by
  rw [StripTrace.mellin_eq_lap]
  unfold E lap
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [seed,logTheta,orbital]; rw [Complex.ofReal_exp,←mul_assoc,←Complex.exp_add]
  congr 2; push_cast; ring

theorem E_strip (s : ℂ) (h0 : 0<s.re) (h1 : s.re<1) :
    E s=explicitGenerator s ∧ (E s=0 ↔ riemannZeta s=0) ∧
      analyticOrderAt E s=analyticOrderAt riemannZeta s := by
  have h := (Classical.choose_spec dyadic_gaussian_theta_mellin).2.2.2.1 s h0 h1
  rw [show E=mellin orbital from funext E_eq_mellin]
  exact ⟨h.1.2,h.2⟩

theorem E_eq_explicit {s : ℂ} (h₀ : s≠0) (h₁ : s≠1) : E s=explicitGenerator s := by
  let U : Set ℂ := ({0,1}:Set ℂ)ᶜ
  have ho : IsOpen U := (isClosed_singleton.union isClosed_singleton).isOpen_compl
  have ha : AnalyticOnNhd ℂ explicitGenerator U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    apply DifferentiableOn.mul _ (fun z hz => (differentiableAt_completedZeta (by
      intro h; apply hz; simp [h]) (by intro h; apply hz; simp [h])).differentiableWithinAt)
    exact (show Differentiable ℂ (fun s : ℂ => (1-(2:ℂ)^(-s))*(1-(2:ℂ)^(1-s))) by fun_prop).differentiableOn
  have hu := (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) (show ({0,1}:Set ℂ).Countable by simp)).isPreconnected
  have he : E =ᶠ[𝓝 (1/2:ℂ)] explicitGenerator := by
    have hpos : ∀ᶠ z : ℂ in 𝓝 (1/2:ℂ), 0<z.re := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    have hlt : ∀ᶠ z : ℂ in 𝓝 (1/2:ℂ), z.re<1 := (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by norm_num)
    filter_upwards [hpos,hlt] with z hz hZ
    exact (E_strip z hz hZ).1
  apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (U:=U)
    (fun z _ => E_entire.analyticAt z) ha hu (show (1/2:ℂ)∈U by dsimp [U]; norm_num) he
  simp [U,h₀,h₁]

theorem E_anchor : ∃ C : ℝ, 0<C ∧ ∀ s : ℂ, s.re=2 → 1 ≤ ‖E s‖*(C*Real.exp (Real.pi*|s.im|)) := by
  obtain ⟨C,hC,h⟩ := generator_anchor
  refine ⟨C,hC,fun s hs => ?_⟩
  have hn0 : s≠0 := by intro he; simp [he] at hs
  have hn1 : s≠1 := by intro he; simp [he] at hs
  rw [E_eq_explicit hn0 hn1]
  exact h s hs

end
end MasulloRH.SynthesisStrip
end StandaloneSynthGenerator


-- Local source: SynthMinimumGenerator
section StandaloneSynthMinimumGenerator
open MeasureTheory
namespace MasulloRH.SynthesisStrip

/-- Polynomial avoidance of nearby nontrivial zeta zeros gives a quadratic logarithmic
minimum for the entire theta generator on any closed interior strip. -/
theorem E_minimum (a b : ℝ) (ha : 0<a) (hb : b<1) (d : ℝ) (hd : 0<d) (A : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ s : ℂ, a ≤ s.re → s.re≤b →
      (∀ v : ℂ, riemannZeta v=0 → 0<v.re → v.re<1 → |v.im-s.im|≤3 →
        d/(1+|s.im|)^A ≤ ‖s-v‖) →
      E s≠0 ∧ max 0 (-Real.log ‖E s‖) ≤ D*(1+|s.im|)^2 :=
  SynthMinimum.strip_log_bound E E_entire (E_band_bound 6) E_anchor
    (fun s h0 h1 => (E_strip s h0 h1).2.1.mp) a b ha hb d hd A
end MasulloRH.SynthesisStrip
end StandaloneSynthMinimumGenerator


open MasulloRH.SynthesisStrip
open scoped Topology

theorem solution (a b : ℝ) (ha : 0<a) (hb : b<1) (d : ℝ) (hd : 0<d) (A : ℕ) :
    let G := fun s : ℂ => (1-(2:ℂ)^(-s))*(1-(2:ℂ)^(1-s))*completedRiemannZeta s
    ∃ D : ℝ, 0<D ∧ ∀ s : ℂ, a ≤ s.re → s.re≤b →
      (∀ ρ : ℂ, riemannZeta ρ=0 → 0<ρ.re → ρ.re<1 → |ρ.im-s.im|≤3 →
        d/(1+|s.im|)^A≤‖s-ρ‖) →
      G s≠0 ∧ max 0 (-Real.log ‖G s‖)≤D*(1+|s.im|)^2 := by
  obtain ⟨D,hD,h⟩ := E_minimum a b ha hb d hd A
  refine ⟨D,hD,fun s h₁ h₂ hs => ?_⟩
  have he := (E_strip s (ha.trans_le h₁) (h₂.trans_lt hb)).1
  simpa only [he,explicitGenerator] using h s h₁ h₂ hs
