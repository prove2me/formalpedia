-- Prove2me | solution 1 for OAI.SK.Analytic.stretched_uniform_coverage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:02:27.169887+00:00
-- url     : https://prove2.me/submissions/5c424413-ae9e-4794-967d-e5552f8334a0

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S004
import Theorems.Thm_OAI_SK_Analytic_coverage_energy_tail

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageAngle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem coverageAngle_tendsto (L : ℕ → ℝ) (M : ℝ)
    (hsub : Tendsto (fun n => L n/(n:ℝ)) atTop (𝓝 0)) :
    Tendsto (coverageAngle L M) atTop (𝓝 0) := by
  have H := (hsub.const_mul M).sqrt
  change Tendsto (fun n => Real.sqrt (M*L n/(n:ℝ))) atTop (𝓝 0)
  simpa only [← mul_div_assoc,mul_zero,Real.sqrt_zero] using H

theorem coverageAngle_pos {L : ℕ → ℝ} {M : ℝ} (hM : 0 < M) {n : ℕ}
    (hn : 0 < n) (hL : 0 < L n) : 0 < coverageAngle L M n := by
  unfold coverageAngle
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  positivity

theorem sin_eq_sinc_mul (x : ℝ) : Real.sin x = Real.sinc x*x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx,div_mul_cancel₀ _ hx]

theorem coverageAngle_variance_tendsto (L : ℕ → ℝ) {M β : ℝ} (hM : 0 < M)
    (hL : Tendsto L atTop atTop)
    (hsub : Tendsto (fun n => L n/(n:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (β*Real.sin (coverageAngle L M n))^2*(n:ℝ)/L n)
      atTop (𝓝 (β^2*M)) := by
  have hsinc : Tendsto (fun n => Real.sinc (coverageAngle L M n)) atTop (𝓝 (1:ℝ)) := by
    simpa only [Function.comp_def,Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp (coverageAngle_tendsto L M hsub)
  have H := (hsinc.pow 2).const_mul (β^2*M)
  simp only [one_pow,mul_one] at H
  apply H.congr'
  filter_upwards [hL.eventually (eventually_gt_atTop (0:ℝ)),eventually_gt_atTop (0:ℕ)] with n hLn hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hθ : coverageAngle L M n^2 = M*L n/(n:ℝ) :=
    Real.sq_sqrt (by positivity)
  rw [sin_eq_sinc_mul,mul_pow,mul_pow,hθ]
  field_simp

theorem coverageAngle_loss_tendsto (L : ℕ → ℝ) {M β e : ℝ} (hM : 0 < M)
    (hL : Tendsto L atTop atTop)
    (hsub : Tendsto (fun n => L n/(n:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => β*(Real.cos (coverageAngle L M n)-1)*(n:ℝ)*e/L n)
      atTop (𝓝 (-β*M*e/2)) := by
  have hθ := coverageAngle_tendsto L M hsub
  have hsinc : Tendsto (fun n => Real.sinc (coverageAngle L M n)) atTop (𝓝 (1:ℝ)) := by
    simpa only [Function.comp_def,Real.sinc_zero] using Real.continuous_sinc.continuousAt.tendsto.comp hθ
  have hcos : Tendsto (fun n => Real.cos (coverageAngle L M n)) atTop (𝓝 (1:ℝ)) := by
    simpa only [Function.comp_def,Real.cos_zero] using Real.continuous_cos.continuousAt.tendsto.comp hθ
  have H := ((hsinc.pow 2).const_mul (-β*M*e)).div (tendsto_const_nhds.add hcos)
    (by norm_num : (1:ℝ)+1 ≠ 0)
  norm_num only [one_pow,mul_one,one_add_one_eq_two] at H
  apply H.congr'
  filter_upwards [hL.eventually (eventually_gt_atTop (0:ℝ)),eventually_gt_atTop (0:ℕ),
    hcos.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1))] with n hLn hn hc
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hθsq : coverageAngle L M n^2 = M*L n/(n:ℝ) := Real.sq_sqrt (by positivity)
  have htrig := Real.sin_sq_add_cos_sq (coverageAngle L M n)
  rw [sin_eq_sinc_mul,mul_pow,hθsq] at htrig
  have hden : 1+Real.cos (coverageAngle L M n) ≠ 0 := by positivity
  have hcosEq : Real.cos (coverageAngle L M n)-1 =
      -(Real.sinc (coverageAngle L M n)^2*(M*L n/(n:ℝ)))/(1+Real.cos (coverageAngle L M n)) := by
    apply (eq_div_iff hden).mpr
    nlinarith
  change -β*M*e*Real.sinc (coverageAngle L M n)^2/(1+Real.cos (coverageAngle L M n)) =
    β*(Real.cos (coverageAngle L M n)-1)*(n:ℝ)*e/L n
  rw [hcosEq]
  field_simp

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_Basic
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

theorem disorder_coordinate_law {n : ℕ} (e : Edge n) :
    HasLaw (fun J : Disorder n => J e) (gaussianReal 0 1) (disorderLaw n) := by
  exact (measurePreserving_eval (fun _ : Edge n => gaussianReal 0 1) e).hasLaw

theorem disorder_coordinate_gaussian {n : ℕ} (e : Edge n) :
    HasGaussianLaw (fun J : Disorder n => J e) (disorderLaw n) :=
  (disorder_coordinate_law e).hasGaussianLaw

theorem disorder_independent (n : ℕ) :
    iIndepFun (fun e (J : Disorder n) => J e) (disorderLaw n) := by
  exact iIndepFun_pi (fun _ => aemeasurable_id)

theorem disorder_gaussian (n : ℕ) : HasGaussianLaw (fun J : Disorder n => J) (disorderLaw n) :=
  (disorder_independent n).hasGaussianLaw disorder_coordinate_gaussian

theorem hamiltonian_gaussian {n : ℕ} (x : Config n) :
    HasGaussianLaw (fun J : Disorder n => hamiltonian J x) (disorderLaw n) := by
  have h : HasGaussianLaw
      (fun J : Disorder n => fun e : Edge n =>
        J e * spin (x e.val.1) * spin (x e.val.2)) (disorderLaw n) := by
    have hi : iIndepFun (fun e (J : Disorder n) =>
        J e * spin (x e.val.1) * spin (x e.val.2)) (disorderLaw n) := by
      exact iIndepFun_pi (μ := fun _ : Edge n => gaussianReal 0 1)
        (X := fun e z => z * spin (x e.val.1) * spin (x e.val.2))
        (fun _ => by fun_prop)
    apply hi.hasGaussianLaw
    intro e
    convert (disorder_coordinate_gaussian e).fun_smul
      (spin (x e.val.1) * spin (x e.val.2)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [smul_eq_mul]
    funext J
    ring
  simpa only [hamiltonian, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    h.fun_sum.fun_smul (Real.sqrt n)⁻¹

theorem hamiltonian_integrable {n : ℕ} (x : Config n) :
    Integrable (fun J : Disorder n => hamiltonian J x) (disorderLaw n) :=
  (hamiltonian_gaussian x).integrable

theorem disorder_mean_zero {n : ℕ} (e : Edge n) :
    ∫ J : Disorder n, J e ∂disorderLaw n = 0 := by
  rw [disorderLaw, integral_eval]
  exact integral_id_gaussianReal

theorem hamiltonian_mean_zero {n : ℕ} (x : Config n) :
    ∫ J : Disorder n, hamiltonian J x ∂disorderLaw n = 0 := by
  simp only [hamiltonian, div_eq_mul_inv]
  rw [integral_mul_const, integral_finsetSum]
  · simp only [integral_mul_const, disorder_mean_zero, zero_mul, Finset.sum_const_zero]
  · intro e _
    exact ((disorder_coordinate_gaussian e).integrable.mul_const _).mul_const _

theorem disorder_covariance {n : ℕ} (e f : Edge n) :
    cov[fun J : Disorder n => J e, fun J : Disorder n => J f; disorderLaw n] =
      if e = f then 1 else 0 := by
  classical
  by_cases hef : e = f
  · subst f
    rw [covariance_self (disorder_coordinate_gaussian e).aemeasurable, (disorder_coordinate_law e).variance_eq]
    simp
  · rw [(disorder_independent n).indepFun hef |>.covariance_eq_zero
      (disorder_coordinate_gaussian e).memLp_two
      (disorder_coordinate_gaussian f).memLp_two]
    simp [hef]

theorem hamiltonian_covariance_edges {n : ℕ} (x y : Config n) :
    cov[fun J : Disorder n => hamiltonian J x,
      fun J : Disorder n => hamiltonian J y; disorderLaw n] =
    (∑ e : Edge n, spin (x e.val.1) * spin (x e.val.2) *
      (spin (y e.val.1) * spin (y e.val.2))) / n := by
  classical
  simp only [hamiltonian, div_eq_mul_inv, covariance_mul_const_left,
    covariance_mul_const_right]
  rw [covariance_fun_sum_fun_sum]
  · simp only [covariance_mul_const_left, covariance_mul_const_right, disorder_covariance]
    have hsum : (∑ e : Edge n, ∑ f : Edge n,
        (if e = f then (1 : ℝ) else 0) * spin (x e.val.1) * spin (x e.val.2) *
          spin (y f.val.1) * spin (y f.val.2)) =
        ∑ e : Edge n, spin (x e.val.1) * spin (x e.val.2) *
          (spin (y e.val.1) * spin (y e.val.2)) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_eq_single e]
      · simp [mul_assoc]
      · intro f _ hfe
        simp [Ne.symm hfe]
      · simp
    rw [hsum]
    rw [mul_assoc, ← mul_inv, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg n)]
  · intro e
    exact ((disorder_coordinate_gaussian e).memLp_two.mul_const _).mul_const _
  · intro e
    exact ((disorder_coordinate_gaussian e).memLp_two.mul_const _).mul_const _

theorem sum_edges {n : ℕ} (f : Fin n × Fin n → ℝ) :
    (∑ e : Edge n, f e.val) = ∑ i : Fin n, ∑ j : Fin n,
      if i < j then f (i, j) else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
    (by simp) f]
  rw [Finset.sum_filter, Fintype.sum_prod_type]

theorem sum_sq_eq_edges {n : ℕ} (a : Fin n → ℝ) :
    (∑ i, a i) ^ 2 = (∑ i, (a i) ^ 2) + 2 * ∑ e : Edge n, a e.val.1 * a e.val.2 := by
  classical
  rw [sum_edges (fun p : Fin n × Fin n => a p.1 * a p.2), pow_two, Fintype.sum_mul_sum]
  have hsplit (i j : Fin n) : a i * a j =
      (if i = j then a i ^ 2 else 0) +
      (if i < j then a i * a j else 0) +
      (if j < i then a i * a j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j
      simp [pow_two]
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  have hsum : (∑ i : Fin n, ∑ j : Fin n, a i * a j) =
      ∑ i : Fin n, ∑ j : Fin n,
        ((if i = j then a i ^ 2 else 0) +
        (if i < j then a i * a j else 0) +
        (if j < i then a i * a j else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hsplit i j
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  have hd : (∑ i : Fin n, ∑ j : Fin n, if i = j then a i ^ 2 else 0) =
      ∑ i, a i ^ 2 := by simp
  have hs : (∑ i : Fin n, ∑ j : Fin n, if j < i then a i * a j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then a i * a j else 0 := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [hd, hs]
  ring

theorem overlap_self {n : ℕ} (hn : 0 < n) (x : Config n) : overlap x x = 1 := by
  simp only [overlap, ← pow_two, spin_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (Nat.cast_ne_zero.mpr hn.ne')

theorem hamiltonian_covariance {n : ℕ} (hn : 0 < n) (x y : Config n) :
    cov[fun J : Disorder n => hamiltonian J x,
      fun J : Disorder n => hamiltonian J y; disorderLaw n] =
      ((n : ℝ) * overlap x y ^ 2 - 1) / 2 := by
  rw [hamiltonian_covariance_edges]
  have hs := sum_sq_eq_edges (fun i => spin (x i) * spin (y i))
  have hd : (∑ i : Fin n, (spin (x i) * spin (y i)) ^ 2) = (n : ℝ) := by
    simp [mul_pow]
  rw [hd] at hs
  have he : (∑ e : Edge n, spin (x e.val.1) * spin (x e.val.2) *
      (spin (y e.val.1) * spin (y e.val.2))) =
      ((∑ i : Fin n, spin (x i) * spin (y i)) ^ 2 - n) / 2 := by
    have hr : (∑ e : Edge n, spin (x e.val.1) * spin (x e.val.2) *
        (spin (y e.val.1) * spin (y e.val.2))) =
        ∑ e : Edge n, (spin (x e.val.1) * spin (y e.val.1)) *
          (spin (x e.val.2) * spin (y e.val.2)) := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    rw [hr]
    linarith
  rw [he, overlap]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hn']

theorem disorder_linear_gaussian {n : ℕ} (a : Edge n → ℝ) :
    HasGaussianLaw (fun J : Disorder n => ∑ e, a e * J e) (disorderLaw n) := by
  simpa only [sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul] using
    (disorder_gaussian n).map_fun
      (∑ e : Edge n, a e • (ContinuousLinearMap.proj e : Disorder n →L[ℝ] ℝ))

theorem hamiltonian_add_gaussian {n : ℕ} (x y : Config n) :
    HasGaussianLaw (fun J : Disorder n => hamiltonian J x + hamiltonian J y)
      (disorderLaw n) := by
  convert disorder_linear_gaussian (fun e : Edge n =>
      (spin (x e.val.1) * spin (x e.val.2) +
       spin (y e.val.1) * spin (y e.val.2)) / Real.sqrt n) using 1
  all_goals try with_reducible_and_instances rfl
  funext J
  simp only [hamiltonian, div_eq_mul_inv, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem hamiltonian_variance {n : ℕ} (hn : 0 < n) (x : Config n) :
    Var[fun J : Disorder n => hamiltonian J x; disorderLaw n] = ((n : ℝ) - 1) / 2 := by
  rw [← covariance_self (hamiltonian_gaussian x).aemeasurable,
    hamiltonian_covariance hn, overlap_self hn]
  ring

theorem gaussian_exp_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : HasGaussianLaw X μ) (t : ℝ) :
    (∫ ω, Real.exp (t * X ω) ∂μ) =
      Real.exp ((∫ ω, X ω ∂μ) * t + Var[X; μ] * t ^ 2 / 2) := by
  change mgf X μ t = _
  rw [mgf_gaussianReal hX.map_eq_gaussianReal,
    Real.coe_toNNReal _ (variance_nonneg X μ)]

theorem gaussian_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : HasGaussianLaw X μ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X ω)) μ := by
  have := hX.isProbabilityMeasure
  rw [← mgf_pos_iff, mgf_gaussianReal hX.map_eq_gaussianReal]
  exact Real.exp_pos _

theorem hamiltonian_exp_integral {n : ℕ} (hn : 0 < n) (x : Config n) (t : ℝ) :
    (∫ J : Disorder n, Real.exp (t * hamiltonian J x) ∂disorderLaw n) =
      Real.exp (t ^ 2 * ((n : ℝ) - 1) / 4) := by
  rw [gaussian_exp_integral (hamiltonian_gaussian x),
    hamiltonian_mean_zero, hamiltonian_variance hn]
  congr 1
  ring

theorem hamiltonian_add_exp_integral {n : ℕ} (hn : 0 < n)
    (x y : Config n) (t : ℝ) :
    (∫ J : Disorder n, Real.exp (t * (hamiltonian J x + hamiltonian J y))
      ∂disorderLaw n) =
      Real.exp (t ^ 2 * ((n : ℝ) - 1) / 2 +
        t ^ 2 * ((n : ℝ) * overlap x y ^ 2 - 1) / 2) := by
  rw [gaussian_exp_integral (hamiltonian_add_gaussian x y),
    integral_add (hamiltonian_integrable x) (hamiltonian_integrable y),
    hamiltonian_mean_zero, hamiltonian_mean_zero,
    variance_fun_add (hamiltonian_gaussian x).memLp_two (hamiltonian_gaussian y).memLp_two,
    hamiltonian_variance hn, hamiltonian_variance hn, hamiltonian_covariance hn]
  congr 1
  ring

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_DisorderPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

instance disorderLaw_isGaussian (n : ℕ) : IsGaussian (disorderLaw n) := by
  have h := (disorder_gaussian n).isGaussian_map
  change IsGaussian (Measure.map id (disorderLaw n)) at h
  rwa [Measure.map_id] at h

theorem disorderPair_fst_law (n : ℕ) :
    HasLaw (Prod.fst : Disorder n × Disorder n → Disorder n)
      (disorderLaw n) (disorderPairLaw n) :=
  measurePreserving_fst.hasLaw

theorem disorderPair_snd_law (n : ℕ) :
    HasLaw (Prod.snd : Disorder n × Disorder n → Disorder n)
      (disorderLaw n) (disorderPairLaw n) :=
  measurePreserving_snd.hasLaw

theorem disorderPair_independent (n : ℕ) :
    IndepFun (Prod.fst : Disorder n × Disorder n → Disorder n)
      Prod.snd (disorderPairLaw n) := by
  apply (indepFun_iff_hasLaw_prodMk_prod (disorderPair_fst_law n)
    (disorderPair_snd_law n)).2
  exact HasLaw.id

theorem disorderPair_gaussian (n : ℕ) :
    HasGaussianLaw (fun p : Disorder n × Disorder n => p) (disorderPairLaw n) :=
  (disorderPair_independent n).hasGaussianLaw (disorderPair_fst_law n).hasGaussianLaw
    (disorderPair_snd_law n).hasGaussianLaw

theorem disorderPair_fst_coordinate_law {n : ℕ} (e : Edge n) :
    HasLaw (fun p : Disorder n × Disorder n => p.1 e)
      (gaussianReal 0 1) (disorderPairLaw n) :=
  (disorder_coordinate_law e).fun_comp (disorderPair_fst_law n)

theorem disorderPair_snd_coordinate_law {n : ℕ} (e : Edge n) :
    HasLaw (fun p : Disorder n × Disorder n => p.2 e)
      (gaussianReal 0 1) (disorderPairLaw n) :=
  (disorder_coordinate_law e).fun_comp (disorderPair_snd_law n)

theorem disorderPair_fst_covariance {n : ℕ} (e f : Edge n) :
    cov[fun p : Disorder n × Disorder n => p.1 e,
      fun p : Disorder n × Disorder n => p.1 f; disorderPairLaw n] =
      if e = f then 1 else 0 := by
  rw [(disorderPair_fst_law n).covariance_fun_comp
    (disorder_coordinate_law e).aemeasurable (disorder_coordinate_law f).aemeasurable]
  exact disorder_covariance e f

theorem disorderPair_snd_covariance {n : ℕ} (e f : Edge n) :
    cov[fun p : Disorder n × Disorder n => p.2 e,
      fun p : Disorder n × Disorder n => p.2 f; disorderPairLaw n] =
      if e = f then 1 else 0 := by
  rw [(disorderPair_snd_law n).covariance_fun_comp
    (disorder_coordinate_law e).aemeasurable (disorder_coordinate_law f).aemeasurable]
  exact disorder_covariance e f

theorem disorderPair_cross_covariance {n : ℕ} (e f : Edge n) :
    cov[fun p : Disorder n × Disorder n => p.1 e,
      fun p : Disorder n × Disorder n => p.2 f; disorderPairLaw n] = 0 := by
  exact ((disorderPair_independent n).comp (measurable_pi_apply e)
    (measurable_pi_apply f)).covariance_eq_zero
      (disorderPair_fst_coordinate_law e).hasGaussianLaw.memLp_two
      (disorderPair_snd_coordinate_law f).hasGaussianLaw.memLp_two

theorem covariance_linear_combination {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y Z W : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) (hW : MemLp W 2 μ)
    (a b c d : ℝ) :
    cov[fun ω => a * X ω + b * Y ω, fun ω => c * Z ω + d * W ω; μ] =
      a * c * cov[X, Z; μ] + a * d * cov[X, W; μ] +
      b * c * cov[Y, Z; μ] + b * d * cov[Y, W; μ] := by
  change cov[(fun ω => a * X ω) + (fun ω => b * Y ω),
    (fun ω => c * Z ω) + (fun ω => d * W ω); μ] = _
  rw [covariance_add_left (hX.const_mul a) (hY.const_mul b)
      ((hZ.const_mul c).add (hW.const_mul d)),
    covariance_add_right (hX.const_mul a) (hZ.const_mul c) (hW.const_mul d),
    covariance_add_right (hY.const_mul b) (hZ.const_mul c) (hW.const_mul d)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  ring

theorem mixDisorder_gaussian (n : ℕ) (a b : ℝ) :
    HasGaussianLaw (mixDisorder (n := n) a b) (disorderPairLaw n) :=
  (disorderPair_gaussian n).map_fun (mixDisorderCLM n a b)

theorem mixDisorder_mean {n : ℕ} (a b : ℝ) (e : Edge n) :
    (∫ p, mixDisorder a b p e ∂disorderPairLaw n) = 0 := by
  change (∫ p : Disorder n × Disorder n, a * p.1 e + b * p.2 e ∂disorderPairLaw n) = 0
  rw [integral_add
    ((disorderPair_fst_coordinate_law e).hasGaussianLaw.integrable.const_mul a)
    ((disorderPair_snd_coordinate_law e).hasGaussianLaw.integrable.const_mul b),
    integral_const_mul, integral_const_mul,
    (disorderPair_fst_coordinate_law e).integral_eq,
    (disorderPair_snd_coordinate_law e).integral_eq]
  simp

theorem mixDisorder_covariance {n : ℕ} (a b c d : ℝ) (e f : Edge n) :
    cov[fun p => mixDisorder a b p e, fun p => mixDisorder c d p f; disorderPairLaw n] =
      (a * c + b * d) * (if e = f then 1 else 0) := by
  change cov[fun p : Disorder n × Disorder n => a * p.1 e + b * p.2 e,
    fun p : Disorder n × Disorder n => c * p.1 f + d * p.2 f; disorderPairLaw n] = _
  rw [covariance_linear_combination
    (disorderPair_fst_coordinate_law e).hasGaussianLaw.memLp_two
    (disorderPair_snd_coordinate_law e).hasGaussianLaw.memLp_two
    (disorderPair_fst_coordinate_law f).hasGaussianLaw.memLp_two
    (disorderPair_snd_coordinate_law f).hasGaussianLaw.memLp_two,
    disorderPair_fst_covariance, disorderPair_snd_covariance, disorderPair_cross_covariance]
  rw [covariance_comm (fun p : Disorder n × Disorder n => p.2 e),
    disorderPair_cross_covariance]
  ring

theorem mixDisorder_coordinate_law {n : ℕ} (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (e : Edge n) :
    HasLaw (fun p => mixDisorder a b p e) (gaussianReal 0 1) (disorderPairLaw n) := by
  have hg := (mixDisorder_gaussian n a b).eval e
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal, mixDisorder_mean,
    ← covariance_self hg.aemeasurable, mixDisorder_covariance]
  simp only [ite_true, mul_one]
  have h : a * a + b * b = 1 := by nlinarith [hab]
  rw [h]
  norm_num

theorem mixDisorder_law {n : ℕ} (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    HasLaw (mixDisorder (n := n) a b) (disorderLaw n) (disorderPairLaw n) := by
  apply iIndepFun.hasLaw_pi (fun e => mixDisorder_coordinate_law a b hab e)
  apply (mixDisorder_gaussian n a b).iIndepFun_of_covariance_eq_zero
  intro e f hef
  rw [mixDisorder_covariance, ite_eq_right hef, mul_zero]

theorem rotateDisorder_gaussian (n : ℕ) (θ : ℝ) :
    HasGaussianLaw (rotateDisorder (n := n) θ) (disorderPairLaw n) :=
  (disorderPair_gaussian n).map_fun (rotateDisorderCLM n θ)

theorem rotateDisorder_law (n : ℕ) (θ : ℝ) :
    HasLaw (rotateDisorder (n := n) θ) (disorderPairLaw n) (disorderPairLaw n) := by
  have hind : IndepFun (mixDisorder (n := n) (Real.cos θ) (Real.sin θ))
      (mixDisorder (- Real.sin θ) (Real.cos θ)) (disorderPairLaw n) := by
    apply (rotateDisorder_gaussian n θ).indepFun_of_covariance_eval
    intro e f
    rw [mixDisorder_covariance]
    ring
  exact hind.hasLaw_prod
    (mixDisorder_law _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ]))
    (mixDisorder_law _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ]))

theorem directionalEnergy_exp_le {n : ℕ} (β ℓ : ℝ) (J K : Disorder n) :
    Real.exp (ℓ * directionalEnergy β J K) ≤
      ∑ x : Config n, gibbs β J x * Real.exp (ℓ * β * hamiltonian K x) := by
  have h := convexOn_exp.map_sum_le (t := Finset.univ)
    (w := gibbs β J) (p := fun x => ℓ * β * hamiltonian K x)
    (fun x _ => le_of_lt (gibbs_pos β J x)) (gibbs_sum β J)
    (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul, ← Finset.mul_sum, directionalEnergy, mul_assoc,
    mul_left_comm (gibbs β J _)] using h

theorem continuous_partition {n : ℕ} (β : ℝ) :
    Continuous (partition (n := n) β) := by
  unfold partition
  exact continuous_finsetSum _ (fun x _ =>
    Real.continuous_exp.comp (continuous_const.mul (continuous_hamiltonian x)))

theorem continuous_gibbs {n : ℕ} (β : ℝ) (x : Config n) :
    Continuous (fun J : Disorder n => gibbs β J x) := by
  exact (Real.continuous_exp.comp
    (continuous_const.mul (continuous_hamiltonian x))).div
    (continuous_partition β) (fun J => ne_of_gt (partition_pos β J))

theorem gibbs_le_one {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) :
    gibbs β J x ≤ 1 := by
  rw [← gibbs_sum β J]
  exact Finset.single_le_sum (fun z _ => le_of_lt (gibbs_pos β J z)) (Finset.mem_univ x)

theorem gibbs_integrable {n : ℕ} (β : ℝ) (x : Config n) :
    Integrable (fun J : Disorder n => gibbs β J x) (disorderLaw n) := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_gibbs β x).aestronglyMeasurable
  filter_upwards [] with J
  simpa only [Real.norm_eq_abs, abs_of_pos (gibbs_pos β J x)] using gibbs_le_one β J x

theorem continuous_directionalEnergy {n : ℕ} (β : ℝ) :
    Continuous (fun p : Disorder n × Disorder n => directionalEnergy β p.1 p.2) := by
  apply continuous_const.mul
  exact continuous_finsetSum _ (fun x _ =>
    ((continuous_gibbs β x).comp continuous_fst).mul
      ((continuous_hamiltonian x).comp continuous_snd))

theorem directionalEnergy_exp_integrable {n : ℕ} (β ℓ : ℝ) (J : Disorder n) :
    Integrable (fun K : Disorder n => Real.exp (ℓ * directionalEnergy β J K))
      (disorderLaw n) := by
  have hsum : Integrable (fun K : Disorder n =>
      ∑ x : Config n, gibbs β J x * Real.exp (ℓ * β * hamiltonian K x))
      (disorderLaw n) :=
    integrable_finsetSum _ (fun x _ =>
      (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β)).const_mul _)
  apply hsum.mono'
  · exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_directionalEnergy β).comp (continuous_const.prodMk continuous_id)))).aestronglyMeasurable
  · filter_upwards [] with K
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      directionalEnergy_exp_le β ℓ J K

theorem directionalEnergy_exp_integral_le {n : ℕ} (hn : 0 < n)
    (β ℓ : ℝ) (J : Disorder n) :
    (∫ K : Disorder n, Real.exp (ℓ * directionalEnergy β J K) ∂disorderLaw n) ≤
      Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hsum (x : Config n) : Integrable (fun K : Disorder n =>
      gibbs β J x * Real.exp (ℓ * β * hamiltonian K x)) (disorderLaw n) :=
    (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β)).const_mul _
  calc
    _ ≤ ∫ K : Disorder n, (∑ x : Config n,
        gibbs β J x * Real.exp (ℓ * β * hamiltonian K x)) ∂disorderLaw n :=
      integral_mono (directionalEnergy_exp_integrable β ℓ J)
        (integrable_finsetSum _ (fun x _ => hsum x)) (directionalEnergy_exp_le β ℓ J)
    _ = _ := by
      rw [integral_finsetSum _ (fun x _ => hsum x)]
      simp_rw [integral_const_mul, hamiltonian_exp_integral hn]
      rw [← Finset.sum_mul, gibbs_sum, one_mul]

theorem directionalEnergy_pair_exp_integrable {n : ℕ} (β ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) (disorderPairLaw n) := by
  have hsum : Integrable (fun p : Disorder n × Disorder n =>
      ∑ x : Config n, gibbs β p.1 x * Real.exp (ℓ * β * hamiltonian p.2 x))
      (disorderPairLaw n) := by
    apply integrable_finsetSum
    intro x _
    exact (gibbs_integrable β x).mul_prod
      (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β))
  apply hsum.mono'
  · exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_directionalEnergy β))).aestronglyMeasurable
  · filter_upwards [] with p
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      directionalEnergy_exp_le β ℓ p.1 p.2

theorem directionalEnergy_pair_exp_integral_le {n : ℕ} (hn : 0 < n) (β ℓ : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * directionalEnergy β p.1 p.2) ∂disorderPairLaw n) ≤
      Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  rw [disorderPairLaw, integral_prod _ (directionalEnergy_pair_exp_integrable β ℓ)]
  calc
    _ ≤ ∫ _J : Disorder n,
        Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) ∂disorderLaw n :=
      integral_mono (directionalEnergy_pair_exp_integrable β ℓ).integral_prod_left
        (integrable_const _) (directionalEnergy_exp_integral_le hn β ℓ)
    _ = _ := by simp

theorem hamiltonian_mix {n : ℕ} (a b : ℝ) (p : Disorder n × Disorder n) (x : Config n) :
    hamiltonian (mixDisorder a b p) x =
      a * hamiltonian p.1 x + b * hamiltonian p.2 x := by
  simp only [hamiltonian, mixDisorder, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_LogPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

theorem continuous_logPartition {n : ℕ} (β : ℝ) :
    Continuous (logPartition (n := n) β) :=
  (continuous_partition β).log (fun J => ne_of_gt (partition_pos β J))

theorem logPartition_hasDerivAt {n : ℕ} (β : ℝ) (J : ℝ → Disorder n)
    (K : Disorder n) (s : ℝ)
    (hJ : ∀ x, HasDerivAt (fun t => hamiltonian (J t) x) (hamiltonian K x) s) :
    HasDerivAt (fun t => logPartition β (J t)) (directionalEnergy β (J s) K) s := by
  have hp : HasDerivAt (fun t => partition β (J t))
      (∑ x : Config n, Real.exp (β * hamiltonian (J s) x) * (β * hamiltonian K x)) s := by
    exact HasDerivAt.fun_sum (fun x _ => ((hJ x).const_mul β).exp)
  have hl := hp.log (ne_of_gt (partition_pos β (J s)))
  have heq : (∑ x : Config n, Real.exp (β * hamiltonian (J s) x) *
      (β * hamiltonian K x)) / partition β (J s) =
      directionalEnergy β (J s) K := by
    simp only [directionalEnergy, gibbs, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq] at hl
  exact hl

theorem continuous_rotateDisorder (n : ℕ) :
    Continuous (fun q : ℝ × (Disorder n × Disorder n) => rotateDisorder q.1 q.2) := by
  unfold rotateDisorder mixDisorder
  fun_prop

theorem rotation_logPartition_hasDerivAt {n : ℕ} (β θ : ℝ)
    (p : Disorder n × Disorder n) (s : ℝ) :
    HasDerivAt (fun t => logPartition β (rotateDisorder (θ * t) p).1)
      (θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) s := by
  have hd : HasDerivAt (fun t => logPartition β (rotateDisorder t p).1)
      (directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) (θ * s) := by
    apply logPartition_hasDerivAt
    intro x
    simp only [rotateDisorder, hamiltonian_mix]
    exact ((Real.hasDerivAt_cos _).mul_const _).add
      ((Real.hasDerivAt_sin _).mul_const _)
  simpa only [Function.comp_def, mul_one, mul_comm] using
    hd.comp s ((hasDerivAt_id s).const_mul θ)

theorem continuous_rotation_path {n : ℕ} (θ : ℝ) (p : Disorder n × Disorder n) :
    Continuous (fun s : ℝ => rotateDisorder (θ * s) p) := by
  unfold rotateDisorder mixDisorder
  fun_prop

theorem continuous_rotation_energy {n : ℕ} (β θ : ℝ) (p : Disorder n × Disorder n) :
    Continuous (fun s : ℝ => directionalEnergy β (rotateDisorder (θ * s) p).1
      (rotateDisorder (θ * s) p).2) :=
  (continuous_directionalEnergy β).comp (continuous_rotation_path θ p)

theorem rotation_logPartition_integral {n : ℕ} (β θ : ℝ)
    (p : Disorder n × Disorder n) :
    logPartition β (rotateDisorder θ p).1 - logPartition β p.1 =
      ∫ s : ℝ in 0..1,
        θ * directionalEnergy β (rotateDisorder (θ * s) p).1
          (rotateDisorder (θ * s) p).2 := by
  have hc : Continuous (fun s : ℝ =>
      θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) :=
    continuous_const.mul (continuous_rotation_energy β θ p)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => rotation_logPartition_hasDerivAt β θ p s) (hc.intervalIntegrable 0 1)
  simpa only [mul_one, mul_zero, rotateDisorder, mixDisorder, Real.cos_zero,
    Real.sin_zero, zero_smul, one_smul, add_zero] using h.symm

theorem continuous_unitInterval_integrable {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f unitIntervalLaw :=
  hf.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

theorem unitInterval_integral (f : ℝ → ℝ) :
    (∫ s, f s ∂unitIntervalLaw) = ∫ s : ℝ in 0..1, f s := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rfl

theorem rotation_exp_jensen {n : ℕ} (β θ ℓ : ℝ) (p : Disorder n × Disorder n) :
    Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)) ≤
      ∫ s, Real.exp (ℓ * θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) ∂unitIntervalLaw := by
  have hc : Continuous (fun s : ℝ => ℓ * θ *
      directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) :=
    continuous_const.mul (continuous_rotation_energy β θ p)
  have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => Set.mem_univ _))
    (continuous_unitInterval_integrable hc)
    (continuous_unitInterval_integrable (Real.continuous_exp.comp hc))
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  rw [unitInterval_integral, rotation_logPartition_integral,
    ← intervalIntegral.integral_const_mul]
  congr 1
  funext s
  ring

theorem rotated_directionalEnergy_exp_integrable {n : ℕ} (β ℓ s : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β (rotateDisorder s p).1 (rotateDisorder s p).2))
      (disorderPairLaw n) := by
  have hp := (rotateDisorder_law n s).measurePreserving (rotateDisorderCLM n s).continuous.measurable
  exact hp.integrable_comp_of_integrable (directionalEnergy_pair_exp_integrable β ℓ)

theorem rotated_directionalEnergy_exp_integral_le {n : ℕ} (hn : 0 < n) (β ℓ s : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * directionalEnergy β (rotateDisorder s p).1 (rotateDisorder s p).2)
        ∂disorderPairLaw n) ≤ Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hm : AEStronglyMeasurable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) (disorderPairLaw n) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_directionalEnergy (n := n) β))).aestronglyMeasurable
  have heq := (rotateDisorder_law n s).integral_comp (f := fun p =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) hm
  change (∫ p, ((fun q : Disorder n × Disorder n =>
    Real.exp (ℓ * directionalEnergy β q.1 q.2)) ∘ rotateDisorder s) p
      ∂disorderPairLaw n) ≤ _
  rw [heq]
  exact directionalEnergy_pair_exp_integral_le hn β ℓ

theorem continuous_rotationIntegrand {n : ℕ} (β θ ℓ : ℝ) :
    Continuous (Function.uncurry (rotationIntegrand (n := n) β θ ℓ)) := by
  have hm : Continuous (fun q : ℝ × (Disorder n × Disorder n) => (θ * q.1, q.2)) :=
    (continuous_const.mul continuous_fst).prodMk continuous_snd
  have hr := (continuous_rotateDisorder n).comp hm
  dsimp only [Function.comp_def] at hr
  have hd : Continuous (fun q : ℝ × (Disorder n × Disorder n) =>
      directionalEnergy β (rotateDisorder (θ * q.1) q.2).1
        (rotateDisorder (θ * q.1) q.2).2) :=
    (continuous_directionalEnergy (n := n) β).comp hr
  change Continuous (fun q : ℝ × (Disorder n × Disorder n) =>
    Real.exp (ℓ * θ * directionalEnergy β (rotateDisorder (θ * q.1) q.2).1
      (rotateDisorder (θ * q.1) q.2).2))
  exact Real.continuous_exp.comp (continuous_const.mul hd)

theorem rotationIntegrand_integrable {n : ℕ} (hn : 0 < n) (β θ ℓ : ℝ) :
    Integrable (Function.uncurry (rotationIntegrand (n := n) β θ ℓ))
      (unitIntervalLaw.prod (disorderPairLaw n)) := by
  have hm : AEStronglyMeasurable (Function.uncurry (rotationIntegrand (n := n) β θ ℓ))
      (unitIntervalLaw.prod (disorderPairLaw n)) :=
    (continuous_rotationIntegrand (n := n) β θ ℓ).aestronglyMeasurable
  apply (integrable_prod_iff hm).2
  constructor
  · exact ae_of_all _ (fun s => rotated_directionalEnergy_exp_integrable β (ℓ * θ) (θ * s))
  · have hmeas := hm.norm.integral_prod_right'
    apply (integrable_const (Real.exp ((ℓ * θ * β) ^ 2 * ((n : ℝ) - 1) / 4))).mono' hmeas
    filter_upwards [] with s
    have hn0 : 0 ≤ ∫ p, ‖rotationIntegrand β θ ℓ s p‖ ∂disorderPairLaw n :=
      integral_nonneg (fun _ => norm_nonneg _)
    change |∫ p, ‖rotationIntegrand β θ ℓ s p‖ ∂disorderPairLaw n| ≤ _
    rw [abs_of_nonneg hn0]
    simp only [rotationIntegrand, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact rotated_directionalEnergy_exp_integral_le hn β (ℓ * θ) (θ * s)

theorem rotation_exp_integrable {n : ℕ} (hn : 0 < n) (β θ ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)))
      (disorderPairLaw n) := by
  have hright := (rotationIntegrand_integrable hn β θ ℓ).integral_prod_right
  have hc : Continuous (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))) := by
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    exact ((continuous_logPartition β).comp
      ((rotateDisorderCLM n θ).continuous.fst)).sub
      ((continuous_logPartition β).comp continuous_fst)
  apply hright.mono' hc.aestronglyMeasurable
  filter_upwards [] with p
  simpa only [Function.uncurry_apply_pair, rotationIntegrand, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] using
    rotation_exp_jensen β θ ℓ p

theorem rotation_exp_integral_le {n : ℕ} (hn : 0 < n) (β θ ℓ : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))
        ∂disorderPairLaw n) ≤
      Real.exp (ℓ ^ 2 * θ ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hf := rotationIntegrand_integrable hn β θ ℓ
  have hright : Integrable (fun p : Disorder n × Disorder n =>
      ∫ s, rotationIntegrand β θ ℓ s p ∂unitIntervalLaw) (disorderPairLaw n) :=
    hf.integral_prod_right
  have hc : Continuous (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))) := by
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    exact ((continuous_logPartition β).comp
      ((rotateDisorderCLM n θ).continuous.fst)).sub
      ((continuous_logPartition β).comp continuous_fst)
  have hleft : Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)))
      (disorderPairLaw n) := by
    apply hright.mono' hc.aestronglyMeasurable
    filter_upwards [] with p
    simpa only [rotationIntegrand, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using rotation_exp_jensen β θ ℓ p
  calc
    _ ≤ ∫ p, (∫ s, rotationIntegrand β θ ℓ s p ∂unitIntervalLaw) ∂disorderPairLaw n :=
      integral_mono hleft hright (rotation_exp_jensen β θ ℓ)
    _ = ∫ s, (∫ p, rotationIntegrand β θ ℓ s p ∂disorderPairLaw n) ∂unitIntervalLaw :=
      (integral_integral_swap hf).symm
    _ ≤ ∫ _s, Real.exp ((ℓ * θ * β) ^ 2 * ((n : ℝ) - 1) / 4) ∂unitIntervalLaw :=
      integral_mono hf.integral_prod_left (integrable_const _)
        (fun s => rotated_directionalEnergy_exp_integral_le hn β (ℓ * θ) (θ * s))
    _ = _ := by
      simp only [integral_const, probReal_univ, one_smul]
      congr 1
      ring

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem rotation_logPartition_tail {n : ℕ} (hn : 0 < n) (β θ u : ℝ) (hu : 0 ≤ u) :
    (disorderPairLaw n).real {p | u ≤ logPartition β (rotateDisorder θ p).1-
      logPartition β p.1} ≤ Real.exp (-u^2/(θ^2*β^2*(n:ℝ))) := by
  let v : NNReal := ⟨θ^2*β^2*(n:ℝ)/2,by positivity⟩
  have HS : HasSubgaussianMGF (fun p : Disorder n × Disorder n =>
      logPartition β (rotateDisorder θ p).1-logPartition β p.1) v (disorderPairLaw n) := by
    refine ⟨rotation_exp_integrable hn β θ,fun t => ?_⟩
    apply (rotation_exp_integral_le hn β θ t).trans
    apply Real.exp_le_exp.mpr
    change t^2*θ^2*β^2*((n:ℝ)-1)/4 ≤ (θ^2*β^2*(n:ℝ)/2)*t^2/2
    have H : 0 ≤ t^2*θ^2*β^2 := by positivity
    nlinarith
  convert HS.measure_ge_le hu using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  change θ^2*β^2*(n:ℝ) = 2*(θ^2*β^2*(n:ℝ)/2)
  ring

theorem product_event_lower_of_sections {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A : Set X} {E : Set (X × Y)} (hA : MeasurableSet A) (hE : MeasurableSet E)
    {c : ℝ} (hc : 0 ≤ c) (hsec : ∀ x ∈ A, c ≤ ν.real {y | (x,y) ∈ E}) :
    c*μ.real A ≤ (μ.prod ν).real E := by
  have H : ENNReal.ofReal c*μ A ≤ (μ.prod ν) E := by
    rw [Measure.prod_apply hE,← lintegral_indicator_const hA (ENNReal.ofReal c)]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top ν _)).mpr (hsec x hx)
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  have HT := ENNReal.toReal_mono (measure_ne_top (μ.prod ν) E) H
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc,measureReal_def] using HT

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedMoments
attribute [-instance] _root_.OAI.SK.disorderLaw_isGaussian _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem weightedPartition_integrable {n : ℕ} (ν : Config n → ℝ) (b : ℝ) :
    Integrable (weightedPartition ν b) (disorderLaw n) :=
  integrable_finsetSum _ (fun x _ =>
    (gaussian_exp_integrable (hamiltonian_gaussian x) b).const_mul _)

theorem weightedPartition_mean {n : ℕ} (hn : 0 < n) (ν : Config n → ℝ)
    (hν : ∑ x, ν x = 1) (b : ℝ) :
    (∫ G, weightedPartition ν b G ∂disorderLaw n) =
      Real.exp (b^2*((n:ℝ)-1)/4) := by
  unfold weightedPartition
  rw [integral_finsetSum _ (fun x _ =>
    (gaussian_exp_integrable (hamiltonian_gaussian x) b).const_mul _)]
  simp_rw [integral_const_mul,hamiltonian_exp_integral hn]
  rw [← Finset.sum_mul,hν,one_mul]

theorem weightedPartition_sq {n : ℕ} (ν : Config n → ℝ) (b : ℝ) (G : Disorder n) :
    (weightedPartition ν b G)^2 = ∑ x : Config n, ∑ y : Config n,
      (ν x*ν y)*Real.exp (b*(hamiltonian G x+hamiltonian G y)) := by
  unfold weightedPartition
  rw [pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [mul_add,Real.exp_add]
  ring

theorem weightedPartition_sq_integrable {n : ℕ} (ν : Config n → ℝ) (b : ℝ) :
    Integrable (fun G => (weightedPartition ν b G)^2) (disorderLaw n) := by
  simp_rw [weightedPartition_sq]
  exact integrable_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ =>
    (gaussian_exp_integrable (hamiltonian_add_gaussian x y) b).const_mul _))

theorem weightedPartition_secondMoment {n : ℕ} (hn : 0 < n) (ν : Config n → ℝ)
    (hν : ∑ x, ν x = 1) (b : ℝ) :
    (∫ G, (weightedPartition ν b G)^2 ∂disorderLaw n) /
      (∫ G, weightedPartition ν b G ∂disorderLaw n)^2 =
      ∑ x : Config n, ∑ y : Config n,
        ν x*ν y*Real.exp (b^2*((n:ℝ)*overlap x y^2-1)/2) := by
  rw [weightedPartition_mean hn ν hν]
  simp_rw [weightedPartition_sq]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ =>
    (gaussian_exp_integrable (hamiltonian_add_gaussian x y) b).const_mul _))]
  simp_rw [integral_finsetSum _ (fun y _ =>
    (gaussian_exp_integrable (hamiltonian_add_gaussian _ y) b).const_mul _),
    integral_const_mul,hamiltonian_add_exp_integral hn]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  rw [Real.exp_add]
  have he : Real.exp (b^2*((n:ℝ)-1)/2) =
      (Real.exp (b^2*((n:ℝ)-1)/4))^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [he]
  have hp := (Real.exp_pos (b^2*((n:ℝ)-1)/4)).ne'
  field_simp

theorem abs_overlap_le_one {n : ℕ} (x y : Config n) : |overlap x y| ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [overlap]
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold overlap
  rw [abs_div,abs_of_pos hnpos]
  apply (div_le_one hnpos).mpr
  calc
    _ ≤ ∑ i : Fin n, |spin (x i)*spin (y i)| := Finset.abs_sum_le_sum_abs _ _
    _ = (n:ℝ) := by
      have hs (i : Fin n) : |spin (x i)*spin (y i)| = 1 := by
        cases hx : x i <;> cases hy : y i <;> norm_num [spin]
      simp only [hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

theorem weightedPartition_secondMoment_le {n : ℕ} (hn : 0 < n)
    (ν : Config n → ℝ) (hνpos : ∀ x, 0 ≤ ν x) (hν : ∑ x, ν x = 1)
    (b q : ℝ) (hq : 0 ≤ q) :
    (∫ G, (weightedPartition ν b G)^2 ∂disorderLaw n) /
      (∫ G, weightedPartition ν b G ∂disorderLaw n)^2 ≤
      Real.exp (b^2*(n:ℝ)*q^2/2)+
        weightedOverlapMass ν q*Real.exp (b^2*(n:ℝ)/2) := by
  rw [weightedPartition_secondMoment hn ν hν]
  have H (x y : Config n) : ν x*ν y*Real.exp (b^2*((n:ℝ)*overlap x y^2-1)/2) ≤
      ν x*ν y*Real.exp (b^2*(n:ℝ)*q^2/2)+
      (if q ≤ |overlap x y| then ν x*ν y else 0)*Real.exp (b^2*(n:ℝ)/2) := by
    have hw : 0 ≤ ν x*ν y := mul_nonneg (hνpos x) (hνpos y)
    by_cases h : q ≤ |overlap x y|
    · rw [ite_eq_left h]
      have ho : overlap x y^2 ≤ 1 := by
        have hh := abs_overlap_le_one x y
        nlinarith [sq_abs (overlap x y)]
      have he : Real.exp (b^2*((n:ℝ)*overlap x y^2-1)/2) ≤
          Real.exp (b^2*(n:ℝ)/2) := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left ho (show 0 ≤ b^2*(n:ℝ) by positivity)
        nlinarith [sq_nonneg b]
      exact (mul_le_mul_of_nonneg_left he hw).trans (le_add_of_nonneg_left (by positivity))
    · rw [ite_eq_right h,zero_mul,add_zero]
      apply mul_le_mul_of_nonneg_left _ hw
      apply Real.exp_le_exp.mpr
      have ho : overlap x y^2 ≤ q^2 := by
        have hh := (not_le.mp h).le
        nlinarith [sq_abs (overlap x y),abs_nonneg (overlap x y)]
      have hh := mul_le_mul_of_nonneg_left ho (show 0 ≤ b^2*(n:ℝ) by positivity)
      nlinarith [sq_nonneg b]
  calc
    _ ≤ ∑ x : Config n, ∑ y : Config n,
        (ν x*ν y*Real.exp (b^2*(n:ℝ)*q^2/2)+
        (if q ≤ |overlap x y| then ν x*ν y else 0)*Real.exp (b^2*(n:ℝ)/2)) :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => H x y))
    _ = _ := by
      simp_rw [Finset.sum_add_distrib,← Finset.sum_mul]
      simp only [← Finset.mul_sum,hν,mul_one,one_mul,weightedOverlapMass]
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_FiniteCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem finiteMass_nonneg {α : Type*} (ν : α → ℝ) (hν : ∀ x, 0 ≤ ν x) (S : Finset α) :
    0 ≤ finiteMass ν S := Finset.sum_nonneg (fun x _ => hν x)

theorem finiteMass_mono {α : Type*} (ν : α → ℝ) (hν : ∀ x, 0 ≤ ν x)
    {S T : Finset α} (hST : S ⊆ T) : finiteMass ν S ≤ finiteMass ν T :=
  Finset.sum_le_sum_of_subset_of_nonneg hST (fun x _ _ => hν x)

theorem conditionalWeights_nonneg {α : Type*} [DecidableEq α] (ν : α → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (S : Finset α) (x : α) : 0 ≤ conditionalWeights ν S x := by
  unfold conditionalWeights
  split_ifs
  · exact div_nonneg (hν x) (finiteMass_nonneg ν hν S)
  · rfl

theorem conditionalWeights_sum {α : Type*} [Fintype α] [DecidableEq α]
    (ν : α → ℝ) (S : Finset α) (hS : 0 < finiteMass ν S) :
    ∑ x, conditionalWeights ν S x = 1 := by
  unfold conditionalWeights
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,← Finset.sum_div]
  exact div_self hS.ne'

theorem weightedOverlapMass_conditional {n : ℕ} (ν : Config n → ℝ)
    (S : Finset (Config n)) (q : ℝ) :
    weightedOverlapMass (conditionalWeights ν S) q =
      finiteOverlapMass ν S q/(finiteMass ν S)^2 := by
  unfold weightedOverlapMass conditionalWeights finiteOverlapMass
  rw [Finset.sum_div]
  have H (x : Config n) :
      (∑ y : Config n, if q ≤ |overlap x y| then
        (if x ∈ S then ν x/finiteMass ν S else 0)*
        (if y ∈ S then ν y/finiteMass ν S else 0) else 0) =
      if x ∈ S then (∑ y ∈ S, if q ≤ |overlap x y| then ν x*ν y else 0)/
        (finiteMass ν S)^2 else 0 := by
    by_cases hx : x ∈ S
    · rw [ite_eq_left hx,ite_eq_left hx,Finset.sum_div]
      calc
        _ = ∑ y : Config n, if y ∈ S then
            (if q ≤ |overlap x y| then ν x*ν y else 0)/(finiteMass ν S)^2 else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          split_ifs <;> ring
        _ = _ := by
          rw [← Finset.sum_filter]
          simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
    · simp [hx]
  simp_rw [H]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]

theorem finiteOverlapMass_eq_rows {n : ℕ} (ν : Config n → ℝ)
    (S : Finset (Config n)) (q : ℝ) :
    finiteOverlapMass ν S q =
      ∑ x ∈ S, ν x*finiteMass ν (S.filter (fun y => q ≤ |overlap x y|)) := by
  unfold finiteOverlapMass finiteMass
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum,Finset.sum_filter]

theorem finite_coverage_of_pair_bound {n : ℕ} (ν : Config n → ℝ)
    (hν : ∀ x, 0 ≤ ν x) {a b q : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hpair : ∀ S : Finset (Config n), a ≤ finiteMass ν S →
      b ≤ weightedOverlapMass (conditionalWeights ν S) q) :
    ∀ S : Finset (Config n),
      finiteMass ν (S.filter (fun x =>
        finiteMass ν (S.filter (fun y => q ≤ |overlap x y|)) < a*b)) < a := by
  intro S
  let B := S.filter (fun x => finiteMass ν (S.filter (fun y => q ≤ |overlap x y|)) < a*b)
  change finiteMass ν B < a
  by_contra h
  have hB : a ≤ finiteMass ν B := not_lt.mp h
  have hBpos : 0 < finiteMass ν B := ha.trans_le hB
  have hlow := hpair B hB
  rw [weightedOverlapMass_conditional] at hlow
  have hraw : b*(finiteMass ν B)^2 ≤ finiteOverlapMass ν B q :=
    (le_div_iff₀ (sq_pos_of_pos hBpos)).mp hlow
  have hrow (x : Config n) (hx : x ∈ B) :
      finiteMass ν (B.filter (fun y => q ≤ |overlap x y|)) < a*b := by
    have hSx := (Finset.mem_filter.mp hx).2
    apply lt_of_le_of_lt _ hSx
    exact finiteMass_mono ν hν (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
  have hstrict : finiteOverlapMass ν B q < a*b*finiteMass ν B := by
    rw [finiteOverlapMass_eq_rows]
    unfold finiteMass
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum
    · intro x hx
      simpa only [finiteMass,mul_comm] using mul_le_mul_of_nonneg_left (hrow x hx).le (hν x)
    · obtain ⟨x,hx,hxpos⟩ := (Finset.sum_pos_iff_of_nonneg (fun x _ => hν x)).mp hBpos
      exact ⟨x,hx,by simpa only [finiteMass,mul_comm] using mul_lt_mul_of_pos_left (hrow x hx) hxpos⟩
  have hcompare := mul_le_mul_of_nonneg_left hB
    (mul_nonneg hb hBpos.le)
  nlinarith
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_PaleyZygmund
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem paleyZygmund_half {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hfpos : ∀ x, 0 ≤ f x)
    (hfi : Integrable f μ) (hf2 : Integrable (fun x => f x^2) μ)
    (hm : 0 < ∫ x, f x ∂μ) :
    (∫ x, f x ∂μ)^2/(4*(∫ x, f x^2 ∂μ)) ≤
      μ.real {x | (∫ y, f y ∂μ)/2 ≤ f x} := by
  let A := {x | (∫ y, f y ∂μ)/2 ≤ f x}
  have hA : MeasurableSet A := measurableSet_le measurable_const hf
  have hAlow : (∫ x, f x ∂μ)/2 ≤ ∫ x in A, f x ∂μ := by
    have H : (∫ x in Aᶜ, f x ∂μ) ≤ (∫ x, f x ∂μ)/2 := by
      calc
        _ ≤ ∫ _x in Aᶜ, (∫ y, f y ∂μ)/2 ∂μ :=
          setIntegral_mono_on hfi.integrableOn (integrable_const _) hA.compl
            (fun x hx => (not_le.mp (show ¬ (∫ y, f y ∂μ)/2 ≤ f x from hx)).le)
        _ = μ.real Aᶜ * ((∫ y, f y ∂μ)/2) := by simp [integral_const]
        _ ≤ (∫ y, f y ∂μ)/2 := by
          have hp : μ.real Aᶜ ≤ 1 := measureReal_le_one
          nlinarith [measureReal_nonneg (μ := μ) (s := Aᶜ)]
    have Hadd := integral_add_compl hA hfi
    linarith
  have hLp : MemLp f 2 (μ.restrict A) :=
    (memLp_two_iff_integrable_sq hfi.integrableOn.aestronglyMeasurable).2 hf2.integrableOn
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all (μ.restrict A) hfpos)
    (ae_of_all (μ.restrict A) (fun _ => show (0:ℝ) ≤ 1 by norm_num))
    (by simpa using hLp)
    (by simpa using (memLp_const (1:ℝ) : MemLp (fun _ : Ω => (1:ℝ)) 2 (μ.restrict A)))
  simp only [mul_one,Real.rpow_two,one_pow,integral_const,smul_eq_mul,mul_one,
    measureReal_restrict_apply_univ,
    ← Real.sqrt_eq_rpow] at H
  have hmon : (∫ x in A, f x^2 ∂μ) ≤ ∫ x, f x^2 ∂μ := by
    have Hadd := integral_add_compl hA hf2
    have hc : 0 ≤ ∫ x in Aᶜ, f x^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
    linarith
  have hroot : Real.sqrt (∫ x in A, f x^2 ∂μ) ≤ Real.sqrt (∫ x, f x^2 ∂μ) :=
    Real.sqrt_le_sqrt hmon
  have Hfull := H.trans (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _))
  have hepos : 0 ≤ ∫ x, f x^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hppos : 0 ≤ μ.real A := measureReal_nonneg
  have he := Real.sq_sqrt hepos
  have hp := Real.sq_sqrt hppos
  have hnonneg : 0 ≤ Real.sqrt (∫ x, f x^2 ∂μ)*Real.sqrt (μ.real A) := by positivity
  have hmroot : (∫ x, f x ∂μ)/2 ≤
      Real.sqrt (∫ x, f x^2 ∂μ)*Real.sqrt (μ.real A) := hAlow.trans Hfull
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ (∫ x, f x ∂μ)/2) hmroot
  have hrootsq : (Real.sqrt (∫ x, f x^2 ∂μ)*Real.sqrt (μ.real A))^2 =
      (∫ x, f x^2 ∂μ)*μ.real A := by rw [mul_pow,he,hp]
  have Hsq : (∫ x, f x ∂μ)^2 ≤ 4*(∫ x, f x^2 ∂μ)*μ.real A := by nlinarith
  have hegt : 0 < ∫ x, f x^2 ∂μ := by
    by_contra h
    have hz : (∫ x, f x^2 ∂μ) = 0 := le_antisymm (not_lt.mp h) hepos
    rw [hz] at Hsq
    nlinarith
  exact (div_le_iff₀ (by positivity : 0 < 4*(∫ x, f x^2 ∂μ))).mpr (by simpa only [mul_comm] using Hsq)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_SubGaussianQuantile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem mean_ge_of_subGaussian_upper {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {v : NNReal}
    (hv : 0 < (v:ℝ))
    (hsg : HasSubgaussianMGF (fun x => f x-∫ y, f y ∂μ) v μ)
    {a B : ℝ} (hB : 0 ≤ B)
    (hp : Real.exp (-B) ≤ μ.real {x | a ≤ f x}) :
    a-Real.sqrt (2*(v:ℝ)*B) ≤ ∫ x, f x ∂μ := by
  by_cases h : a ≤ ∫ x, f x ∂μ
  · linarith [Real.sqrt_nonneg (2*(v:ℝ)*B)]
  have hd : 0 < a-∫ x, f x ∂μ := sub_pos.mpr (not_le.mp h)
  have ht := hsg.measure_ge_le hd.le
  have hevent : {x | a ≤ f x} = {x | a-(∫ y, f y ∂μ) ≤ f x-(∫ y, f y ∂μ)} := by
    ext x; simp only [Set.mem_ofPred_eq]; constructor <;> intro hx <;> linarith
  rw [← hevent] at ht
  have he := Real.exp_le_exp.mp (hp.trans ht)
  have hs : (a-(∫ y, f y ∂μ))^2 ≤ 2*(v:ℝ)*B := by
    have HH := (le_div_iff₀ (by positivity : 0 < 2*(v:ℝ))).mp
      (show -B ≤ -(a-(∫ y, f y ∂μ))^2/(2*(v:ℝ)) from he)
    nlinarith
  have hr := Real.sq_sqrt (show 0 ≤ 2*(v:ℝ)*B by positivity)
  have hrpos := Real.sqrt_nonneg (2*(v:ℝ)*B)
  nlinarith

theorem subGaussian_half_lower {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {v : NNReal}
    (hf : Measurable f) (hv : 0 < (v:ℝ))
    (hsg : HasSubgaussianMGF (fun x => f x-∫ y, f y ∂μ) v μ)
    {a B : ℝ} (hB : 0 ≤ B)
    (hp : Real.exp (-B) ≤ μ.real {x | a ≤ f x}) :
    (1/2:ℝ) ≤ μ.real {x | a-Real.sqrt (2*(v:ℝ)*B)-
      Real.sqrt (2*(v:ℝ)*Real.log 2) ≤ f x} := by
  have hm := mean_ge_of_subGaussian_upper hv hsg hB hp
  let u := Real.sqrt (2*(v:ℝ)*Real.log 2)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2 = 2*(v:ℝ)*Real.log 2 :=
    Real.sq_sqrt (by positivity)
  have ht := hsg.neg.measure_ge_le hu
  simp only [Pi.neg_apply,neg_sub] at ht
  have hexp : Real.exp (-u^2/(2*(v:ℝ))) = (1/2:ℝ) := by
    rw [hu2]
    have hvn : (v:ℝ) ≠ 0 := hv.ne'
    have he : -(2*(v:ℝ)*Real.log 2)/(2*(v:ℝ)) = -Real.log 2 := by field_simp
    rw [he,Real.exp_neg,Real.exp_log (by norm_num)]
    norm_num
  rw [hexp] at ht
  let A := {x | a-Real.sqrt (2*(v:ℝ)*B)-u ≤ f x}
  have hA : MeasurableSet A := measurableSet_le measurable_const hf
  have hsub : Aᶜ ⊆ {x | u ≤ (∫ y, f y ∂μ)-f x} := by
    intro x hx
    have hx' : f x < a-Real.sqrt (2*(v:ℝ)*B)-u := not_le.mp hx
    simp only [Set.mem_ofPred_eq]
    linarith
  have hb := (measureReal_mono hsub).trans ht
  rw [measureReal_compl hA] at hb
  simp only [probReal_univ] at hb
  change (1/2:ℝ) ≤ μ.real A
  linarith
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_WeightedConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic.Weighted

theorem partition_pos {n : ℕ} [Weights n] (β : ℝ) (J : Disorder n) : 0 < partition β J := by
  have hsum : 0 < ∑ x : Config n, Weights.weight x := by rw [Weights.sum_one]; norm_num
  obtain ⟨x,hx,hpos⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun x _ => Weights.nonneg x)).mp hsum
  exact Finset.sum_pos' (fun x _ => mul_nonneg (Weights.nonneg x) (Real.exp_nonneg _))
    ⟨x,hx,mul_pos hpos (Real.exp_pos _)⟩

theorem gibbs_nonneg {n : ℕ} [Weights n] (β : ℝ) (J : Disorder n) (x : Config n) :
    0 ≤ gibbs β J x :=
  div_nonneg (mul_nonneg (Weights.nonneg x) (Real.exp_nonneg _)) (partition_pos β J).le

theorem gibbs_sum {n : ℕ} [Weights n] (β : ℝ) (J : Disorder n) :
    ∑ x, gibbs β J x = 1 := by
  simp only [gibbs,← Finset.sum_div]
  exact div_self (partition_pos β J).ne'

theorem directionalEnergy_exp_le {n : ℕ} [Weights n] (β ℓ : ℝ) (J K : Disorder n) :
    Real.exp (ℓ * directionalEnergy β J K) ≤
      ∑ x : Config n, gibbs β J x * Real.exp (ℓ * β * hamiltonian K x) := by
  have h := convexOn_exp.map_sum_le (t := Finset.univ)
    (w := gibbs β J) (p := fun x => ℓ * β * hamiltonian K x)
    (fun x _ => gibbs_nonneg β J x) (gibbs_sum β J)
    (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul, ← Finset.mul_sum, directionalEnergy, mul_assoc,
    mul_left_comm (gibbs β J _)] using h

theorem continuous_partition {n : ℕ} [Weights n] (β : ℝ) :
    Continuous (partition (n := n) β) := by
  unfold partition
  exact continuous_finsetSum _ (fun x _ =>
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (continuous_hamiltonian x))))

theorem continuous_gibbs {n : ℕ} [Weights n] (β : ℝ) (x : Config n) :
    Continuous (fun J : Disorder n => gibbs β J x) := by
  exact (continuous_const.mul (Real.continuous_exp.comp
    (continuous_const.mul (continuous_hamiltonian x)))).div
    (continuous_partition β) (fun J => ne_of_gt (partition_pos β J))

theorem gibbs_le_one {n : ℕ} [Weights n] (β : ℝ) (J : Disorder n) (x : Config n) :
    gibbs β J x ≤ 1 := by
  rw [← gibbs_sum β J]
  exact Finset.single_le_sum (fun z _ => gibbs_nonneg β J z) (Finset.mem_univ x)

theorem gibbs_integrable {n : ℕ} [Weights n] (β : ℝ) (x : Config n) :
    Integrable (fun J : Disorder n => gibbs β J x) (disorderLaw n) := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_gibbs β x).aestronglyMeasurable
  filter_upwards [] with J
  simpa only [Real.norm_eq_abs, abs_of_nonneg (gibbs_nonneg β J x)] using gibbs_le_one β J x

theorem continuous_directionalEnergy {n : ℕ} [Weights n] (β : ℝ) :
    Continuous (fun p : Disorder n × Disorder n => directionalEnergy β p.1 p.2) := by
  apply continuous_const.mul
  exact continuous_finsetSum _ (fun x _ =>
    ((continuous_gibbs β x).comp continuous_fst).mul
      ((continuous_hamiltonian x).comp continuous_snd))

theorem directionalEnergy_exp_integrable {n : ℕ} [Weights n] (β ℓ : ℝ) (J : Disorder n) :
    Integrable (fun K : Disorder n => Real.exp (ℓ * directionalEnergy β J K))
      (disorderLaw n) := by
  have hsum : Integrable (fun K : Disorder n =>
      ∑ x : Config n, gibbs β J x * Real.exp (ℓ * β * hamiltonian K x))
      (disorderLaw n) :=
    integrable_finsetSum _ (fun x _ =>
      (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β)).const_mul _)
  apply hsum.mono'
  · exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_directionalEnergy β).comp (continuous_const.prodMk continuous_id)))).aestronglyMeasurable
  · filter_upwards [] with K
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      directionalEnergy_exp_le β ℓ J K

theorem directionalEnergy_exp_integral_le {n : ℕ} [Weights n] (hn : 0 < n)
    (β ℓ : ℝ) (J : Disorder n) :
    (∫ K : Disorder n, Real.exp (ℓ * directionalEnergy β J K) ∂disorderLaw n) ≤
      Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hsum (x : Config n) : Integrable (fun K : Disorder n =>
      gibbs β J x * Real.exp (ℓ * β * hamiltonian K x)) (disorderLaw n) :=
    (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β)).const_mul _
  calc
    _ ≤ ∫ K : Disorder n, (∑ x : Config n,
        gibbs β J x * Real.exp (ℓ * β * hamiltonian K x)) ∂disorderLaw n :=
      integral_mono (directionalEnergy_exp_integrable β ℓ J)
        (integrable_finsetSum _ (fun x _ => hsum x)) (directionalEnergy_exp_le β ℓ J)
    _ = _ := by
      rw [integral_finsetSum _ (fun x _ => hsum x)]
      simp_rw [integral_const_mul, hamiltonian_exp_integral hn]
      rw [← Finset.sum_mul, gibbs_sum, one_mul]

theorem directionalEnergy_pair_exp_integrable {n : ℕ} [Weights n] (β ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) (disorderPairLaw n) := by
  have hsum : Integrable (fun p : Disorder n × Disorder n =>
      ∑ x : Config n, gibbs β p.1 x * Real.exp (ℓ * β * hamiltonian p.2 x))
      (disorderPairLaw n) := by
    apply integrable_finsetSum
    intro x _
    exact (gibbs_integrable β x).mul_prod
      (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β))
  apply hsum.mono'
  · exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_directionalEnergy β))).aestronglyMeasurable
  · filter_upwards [] with p
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      directionalEnergy_exp_le β ℓ p.1 p.2

theorem directionalEnergy_pair_exp_integral_le {n : ℕ} [Weights n] (hn : 0 < n) (β ℓ : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * directionalEnergy β p.1 p.2) ∂disorderPairLaw n) ≤
      Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  rw [disorderPairLaw, integral_prod _ (directionalEnergy_pair_exp_integrable β ℓ)]
  calc
    _ ≤ ∫ _J : Disorder n,
        Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) ∂disorderLaw n :=
      integral_mono (directionalEnergy_pair_exp_integrable β ℓ).integral_prod_left
        (integrable_const _) (directionalEnergy_exp_integral_le hn β ℓ)
    _ = _ := by simp

theorem continuous_logPartition {n : ℕ} [Weights n] (β : ℝ) :
    Continuous (logPartition (n := n) β) :=
  (continuous_partition β).log (fun J => ne_of_gt (partition_pos β J))

theorem logPartition_hasDerivAt {n : ℕ} [Weights n] (β : ℝ) (J : ℝ → Disorder n)
    (K : Disorder n) (s : ℝ)
    (hJ : ∀ x, HasDerivAt (fun t => hamiltonian (J t) x) (hamiltonian K x) s) :
    HasDerivAt (fun t => logPartition β (J t)) (directionalEnergy β (J s) K) s := by
  have hp : HasDerivAt (fun t => partition β (J t))
      (∑ x : Config n, Weights.weight x * (Real.exp (β * hamiltonian (J s) x) * (β * hamiltonian K x))) s := by
    exact HasDerivAt.fun_sum (fun x _ => (((hJ x).const_mul β).exp.const_mul (Weights.weight x)))
  have hl := hp.log (ne_of_gt (partition_pos β (J s)))
  have heq : (∑ x : Config n, Weights.weight x * (Real.exp (β * hamiltonian (J s) x) *
      (β * hamiltonian K x))) / partition β (J s) =
      directionalEnergy β (J s) K := by
    simp only [directionalEnergy, gibbs, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq] at hl
  exact hl

theorem rotation_logPartition_hasDerivAt {n : ℕ} [Weights n] (β θ : ℝ)
    (p : Disorder n × Disorder n) (s : ℝ) :
    HasDerivAt (fun t => logPartition β (rotateDisorder (θ * t) p).1)
      (θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) s := by
  have hd : HasDerivAt (fun t => logPartition β (rotateDisorder t p).1)
      (directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) (θ * s) := by
    apply logPartition_hasDerivAt
    intro x
    simp only [rotateDisorder, hamiltonian_mix]
    exact ((Real.hasDerivAt_cos _).mul_const _).add
      ((Real.hasDerivAt_sin _).mul_const _)
  simpa only [Function.comp_def, mul_one, mul_comm] using
    hd.comp s ((hasDerivAt_id s).const_mul θ)

theorem continuous_rotation_energy {n : ℕ} [Weights n] (β θ : ℝ) (p : Disorder n × Disorder n) :
    Continuous (fun s : ℝ => directionalEnergy β (rotateDisorder (θ * s) p).1
      (rotateDisorder (θ * s) p).2) :=
  (continuous_directionalEnergy β).comp (continuous_rotation_path θ p)

theorem rotation_logPartition_integral {n : ℕ} [Weights n] (β θ : ℝ)
    (p : Disorder n × Disorder n) :
    logPartition β (rotateDisorder θ p).1 - logPartition β p.1 =
      ∫ s : ℝ in 0..1,
        θ * directionalEnergy β (rotateDisorder (θ * s) p).1
          (rotateDisorder (θ * s) p).2 := by
  have hc : Continuous (fun s : ℝ =>
      θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) :=
    continuous_const.mul (continuous_rotation_energy β θ p)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => rotation_logPartition_hasDerivAt β θ p s) (hc.intervalIntegrable 0 1)
  simpa only [mul_one, mul_zero, rotateDisorder, mixDisorder, Real.cos_zero,
    Real.sin_zero, zero_smul, one_smul, add_zero] using h.symm

theorem rotation_exp_jensen {n : ℕ} [Weights n] (β θ ℓ : ℝ) (p : Disorder n × Disorder n) :
    Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)) ≤
      ∫ s, Real.exp (ℓ * θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) ∂unitIntervalLaw := by
  have hc : Continuous (fun s : ℝ => ℓ * θ *
      directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) :=
    continuous_const.mul (continuous_rotation_energy β θ p)
  have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => Set.mem_univ _))
    (continuous_unitInterval_integrable hc)
    (continuous_unitInterval_integrable (Real.continuous_exp.comp hc))
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  rw [unitInterval_integral, rotation_logPartition_integral,
    ← intervalIntegral.integral_const_mul]
  congr 1
  funext s
  ring

theorem rotated_directionalEnergy_exp_integrable {n : ℕ} [Weights n] (β ℓ s : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β (rotateDisorder s p).1 (rotateDisorder s p).2))
      (disorderPairLaw n) := by
  have hp := (rotateDisorder_law n s).measurePreserving (rotateDisorderCLM n s).continuous.measurable
  exact hp.integrable_comp_of_integrable (directionalEnergy_pair_exp_integrable β ℓ)

theorem rotated_directionalEnergy_exp_integral_le {n : ℕ} [Weights n] (hn : 0 < n) (β ℓ s : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * directionalEnergy β (rotateDisorder s p).1 (rotateDisorder s p).2)
        ∂disorderPairLaw n) ≤ Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hm : AEStronglyMeasurable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) (disorderPairLaw n) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_directionalEnergy (n := n) β))).aestronglyMeasurable
  have heq := (rotateDisorder_law n s).integral_comp (f := fun p =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) hm
  change (∫ p, ((fun q : Disorder n × Disorder n =>
    Real.exp (ℓ * directionalEnergy β q.1 q.2)) ∘ rotateDisorder s) p
      ∂disorderPairLaw n) ≤ _
  rw [heq]
  exact directionalEnergy_pair_exp_integral_le hn β ℓ

theorem continuous_rotationIntegrand {n : ℕ} [Weights n] (β θ ℓ : ℝ) :
    Continuous (Function.uncurry (rotationIntegrand (n := n) β θ ℓ)) := by
  have hm : Continuous (fun q : ℝ × (Disorder n × Disorder n) => (θ * q.1, q.2)) :=
    (continuous_const.mul continuous_fst).prodMk continuous_snd
  have hr := (continuous_rotateDisorder n).comp hm
  dsimp only [Function.comp_def] at hr
  have hd : Continuous (fun q : ℝ × (Disorder n × Disorder n) =>
      directionalEnergy β (rotateDisorder (θ * q.1) q.2).1
        (rotateDisorder (θ * q.1) q.2).2) :=
    (continuous_directionalEnergy (n := n) β).comp hr
  change Continuous (fun q : ℝ × (Disorder n × Disorder n) =>
    Real.exp (ℓ * θ * directionalEnergy β (rotateDisorder (θ * q.1) q.2).1
      (rotateDisorder (θ * q.1) q.2).2))
  exact Real.continuous_exp.comp (continuous_const.mul hd)

theorem rotationIntegrand_integrable {n : ℕ} [Weights n] (hn : 0 < n) (β θ ℓ : ℝ) :
    Integrable (Function.uncurry (rotationIntegrand (n := n) β θ ℓ))
      (unitIntervalLaw.prod (disorderPairLaw n)) := by
  have hm : AEStronglyMeasurable (Function.uncurry (rotationIntegrand (n := n) β θ ℓ))
      (unitIntervalLaw.prod (disorderPairLaw n)) :=
    (continuous_rotationIntegrand (n := n) β θ ℓ).aestronglyMeasurable
  apply (integrable_prod_iff hm).2
  constructor
  · exact ae_of_all _ (fun s => rotated_directionalEnergy_exp_integrable β (ℓ * θ) (θ * s))
  · have hmeas := hm.norm.integral_prod_right'
    apply (integrable_const (Real.exp ((ℓ * θ * β) ^ 2 * ((n : ℝ) - 1) / 4))).mono' hmeas
    filter_upwards [] with s
    have hn0 : 0 ≤ ∫ p, ‖rotationIntegrand β θ ℓ s p‖ ∂disorderPairLaw n :=
      integral_nonneg (fun _ => norm_nonneg _)
    change |∫ p, ‖rotationIntegrand β θ ℓ s p‖ ∂disorderPairLaw n| ≤ _
    rw [abs_of_nonneg hn0]
    simp only [rotationIntegrand, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact rotated_directionalEnergy_exp_integral_le hn β (ℓ * θ) (θ * s)

theorem rotation_exp_integrable {n : ℕ} [Weights n] (hn : 0 < n) (β θ ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)))
      (disorderPairLaw n) := by
  have hright := (rotationIntegrand_integrable hn β θ ℓ).integral_prod_right
  have hc : Continuous (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))) := by
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    exact ((continuous_logPartition β).comp
      ((rotateDisorderCLM n θ).continuous.fst)).sub
      ((continuous_logPartition β).comp continuous_fst)
  apply hright.mono' hc.aestronglyMeasurable
  filter_upwards [] with p
  simpa only [Function.uncurry_apply_pair, rotationIntegrand, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] using
    rotation_exp_jensen β θ ℓ p

theorem rotation_exp_integral_le {n : ℕ} [Weights n] (hn : 0 < n) (β θ ℓ : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))
        ∂disorderPairLaw n) ≤
      Real.exp (ℓ ^ 2 * θ ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hf := rotationIntegrand_integrable hn β θ ℓ
  have hright : Integrable (fun p : Disorder n × Disorder n =>
      ∫ s, rotationIntegrand β θ ℓ s p ∂unitIntervalLaw) (disorderPairLaw n) :=
    hf.integral_prod_right
  have hc : Continuous (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))) := by
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    exact ((continuous_logPartition β).comp
      ((rotateDisorderCLM n θ).continuous.fst)).sub
      ((continuous_logPartition β).comp continuous_fst)
  have hleft : Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)))
      (disorderPairLaw n) := by
    apply hright.mono' hc.aestronglyMeasurable
    filter_upwards [] with p
    simpa only [rotationIntegrand, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using rotation_exp_jensen β θ ℓ p
  calc
    _ ≤ ∫ p, (∫ s, rotationIntegrand β θ ℓ s p ∂unitIntervalLaw) ∂disorderPairLaw n :=
      integral_mono hleft hright (rotation_exp_jensen β θ ℓ)
    _ = ∫ s, (∫ p, rotationIntegrand β θ ℓ s p ∂disorderPairLaw n) ∂unitIntervalLaw :=
      (integral_integral_swap hf).symm
    _ ≤ ∫ _s, Real.exp ((ℓ * θ * β) ^ 2 * ((n : ℝ) - 1) / 4) ∂unitIntervalLaw :=
      integral_mono hf.integral_prod_left (integrable_const _)
        (fun s => rotated_directionalEnergy_exp_integral_le hn β (ℓ * θ) (θ * s))
    _ = _ := by
      simp only [integral_const, probReal_univ, one_smul]
      congr 1
      ring

theorem logPartition_difference_exp_integrable {n : ℕ} [Weights n] (hn : 0 < n) (β ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β p.2 - logPartition β p.1))) (disorderPairLaw n) := by
  simpa only [rotateDisorder_pi_div_two_fst] using
    rotation_exp_integrable hn β (Real.pi / 2) ℓ

theorem logPartition_exp_integrable {n : ℕ} [Weights n] (hn : 0 < n) (β ℓ : ℝ) :
    Integrable (fun J : Disorder n => Real.exp (ℓ * logPartition β J)) (disorderLaw n) := by
  have hp := logPartition_difference_exp_integrable hn β ℓ
  obtain ⟨J, hJ⟩ := hp.prod_right_ae.exists
  have hi := hJ.const_mul (Real.exp (ℓ * logPartition β J))
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext K
  rw [← Real.exp_add]
  congr 1
  ring

theorem logPartition_integrable {n : ℕ} [Weights n] (hn : 0 < n) (β : ℝ) :
    Integrable (logPartition (n := n) β) (disorderLaw n) := by
  have hp := logPartition_exp_integrable hn β 1
  have hm := logPartition_exp_integrable hn β (-1)
  apply (hp.add hm).mono' (continuous_logPartition β).aestronglyMeasurable
  filter_upwards [] with J
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have h := Real.add_one_le_exp (-logPartition β J)
    have he := Real.exp_pos (1 * logPartition β J)
    simp only [Pi.add_apply, one_mul, neg_one_mul] at *
    linarith
  · have h := Real.add_one_le_exp (logPartition β J)
    have he := Real.exp_pos (-1 * logPartition β J)
    simp only [Pi.add_apply, one_mul, neg_one_mul] at *
    linarith

theorem logPartition_centered_exp_jensen {n : ℕ} [Weights n] (hn : 0 < n) (β ℓ : ℝ)
    (J : Disorder n) :
    Real.exp (ℓ * (logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)) ≤
      ∫ K, Real.exp (ℓ * (logPartition β J - logPartition β K)) ∂disorderLaw n := by
  have hl : Integrable (fun K : Disorder n => ℓ * (logPartition β J - logPartition β K))
      (disorderLaw n) := ((integrable_const _).sub (logPartition_integrable hn β)).const_mul ℓ
  have he : Integrable (fun K : Disorder n =>
      Real.exp (ℓ * (logPartition β J - logPartition β K))) (disorderLaw n) := by
    have h := (logPartition_exp_integrable hn β (-ℓ)).const_mul
      (Real.exp (ℓ * logPartition β J))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext K
    rw [← Real.exp_add]
    congr 1
    ring
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => Set.mem_univ _)) hl he
  convert hj using 2
  all_goals try with_reducible_and_instances rfl
  rw [integral_const_mul, integral_sub (integrable_const _) (logPartition_integrable hn β)]
  simp

theorem logPartition_centered_exp_integrable {n : ℕ} [Weights n] (hn : 0 < n) (β ℓ : ℝ) :
    Integrable (fun J : Disorder n =>
      Real.exp (ℓ * (logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)))
      (disorderLaw n) := by
  have h := (logPartition_exp_integrable hn β ℓ).const_mul
    (Real.exp (-ℓ * ∫ K, logPartition β K ∂disorderLaw n))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext J
  rw [← Real.exp_add]
  congr 1
  ring

theorem logPartition_centered_exp_integral_le {n : ℕ} [Weights n] (hn : 0 < n) (β ℓ : ℝ) :
    (∫ J : Disorder n,
      Real.exp (ℓ * (logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)) ∂disorderLaw n) ≤
      Real.exp (ℓ ^ 2 * Real.pi ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 16) := by
  have hf : Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β p.1 - logPartition β p.2))) (disorderPairLaw n) := by
    convert logPartition_difference_exp_integrable hn β (-ℓ) using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    congr 1
    ring
  calc
    _ ≤ ∫ J, (∫ K, Real.exp (ℓ * (logPartition β J - logPartition β K)) ∂disorderLaw n)
        ∂disorderLaw n := integral_mono (logPartition_centered_exp_integrable hn β ℓ)
          hf.integral_prod_left (logPartition_centered_exp_jensen hn β ℓ)
    _ = ∫ p : Disorder n × Disorder n,
        Real.exp ((-ℓ) * (logPartition β (rotateDisorder (Real.pi / 2) p).1 -
          logPartition β p.1)) ∂disorderPairLaw n := by
      rw [← integral_prod _ hf]
      apply integral_congr_ae
      filter_upwards [] with p
      rw [rotateDisorder_pi_div_two_fst]
      congr 1
      ring
    _ ≤ Real.exp ((-ℓ) ^ 2 * (Real.pi / 2) ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 4) :=
      rotation_exp_integral_le hn β (Real.pi / 2) (-ℓ)
    _ = _ := by congr 1; ring

theorem logPartition_subGaussian {n : ℕ} [Weights n] (hn : 0 < n) (β : ℝ) :
    HasSubgaussianMGF
      (fun J : Disorder n => logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)
      (logPartitionProxy β n) (disorderLaw n) := by
  refine ⟨logPartition_centered_exp_integrable hn β, fun ℓ => ?_⟩
  apply (logPartition_centered_exp_integral_le hn β ℓ).trans
  apply Real.exp_le_exp.mpr
  change ℓ ^ 2 * Real.pi ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 16 ≤
    (Real.pi ^ 2 * β ^ 2 * (n : ℝ) / 8) * ℓ ^ 2 / 2
  have h : 0 ≤ ℓ ^ 2 * Real.pi ^ 2 * β ^ 2 := by positivity
  nlinarith

end SK.Analytic.Weighted

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_WeightedCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem weightedPartition_pos {n : ℕ} (ν : Config n → ℝ)
    (hνpos : ∀ x, 0 ≤ ν x) (hν : ∑ x, ν x = 1) (b : ℝ) (G : Disorder n) :
    0 < weightedPartition ν b G := by
  let : Weighted.Weights n := ⟨ν,hνpos,hν⟩
  exact Weighted.partition_pos b G

theorem continuous_weightedPartition {n : ℕ} (ν : Config n → ℝ) (b : ℝ) :
    Continuous (weightedPartition ν b) := by
  unfold weightedPartition
  exact continuous_finsetSum _ (fun x _ => continuous_const.mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_hamiltonian x))))

theorem weightedLogPartition_subGaussian {n : ℕ} (hn : 0 < n)
    (ν : Config n → ℝ) (hνpos : ∀ x, 0 ≤ ν x) (hν : ∑ x, ν x = 1) (b : ℝ) :
    HasSubgaussianMGF (fun G : Disorder n => Real.log (weightedPartition ν b G)-
      ∫ K, Real.log (weightedPartition ν b K) ∂disorderLaw n)
      (logPartitionProxy b n) (disorderLaw n) := by
  let : Weighted.Weights n := ⟨ν,hνpos,hν⟩
  exact Weighted.logPartition_subGaussian hn b

theorem weightedPartition_paleyZygmund {n : ℕ} (hn : 0 < n)
    (ν : Config n → ℝ) (hνpos : ∀ x, 0 ≤ ν x) (hν : ∑ x, ν x = 1)
    (b q : ℝ) (hq : 0 ≤ q)
    (hr : weightedOverlapMass ν q*Real.exp (b^2*(n:ℝ)/2) ≤
      Real.exp (b^2*(n:ℝ)*q^2/2)) :
    Real.exp (-(b^2*(n:ℝ)*q^2/2+Real.log 8)) ≤
      (disorderLaw n).real {G | b^2*((n:ℝ)-1)/4-Real.log 2 ≤
        Real.log (weightedPartition ν b G)} := by
  let M := Real.exp (b^2*((n:ℝ)-1)/4)
  let E := Real.exp (b^2*(n:ℝ)*q^2/2)
  let S := ∫ G, (weightedPartition ν b G)^2 ∂disorderLaw n
  have hM : 0 < M := Real.exp_pos _
  have hE : 0 < E := Real.exp_pos _
  have hS : 0 < S := by
    apply (integral_pos_iff_support_of_nonneg (fun G => sq_nonneg _)
      (weightedPartition_sq_integrable ν b)).mpr
    have hsupp : Function.support (fun G => (weightedPartition ν b G)^2) = Set.univ := by
      ext G
      simp only [Function.mem_support,Set.mem_univ,iff_true]
      exact pow_ne_zero 2 (weightedPartition_pos ν hνpos hν b G).ne'
    rw [hsupp]
    simp
  have hm := weightedPartition_mean hn ν hν b
  have hR := (weightedPartition_secondMoment_le hn ν hνpos hν b q hq).trans
    (add_le_add_right hr _)
  rw [hm] at hR
  have hR' : S ≤ (2*E)*M^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hM)).mp
    change S/M^2 ≤ 2*E
    change S/M^2 ≤ E+E at hR
    linarith
  have hp := paleyZygmund_half (disorderLaw n) (weightedPartition ν b)
    (continuous_weightedPartition ν b).measurable
    (fun G => (weightedPartition_pos ν hνpos hν b G).le)
    (weightedPartition_integrable ν b) (weightedPartition_sq_integrable ν b)
    (by rw [hm]; exact hM)
  rw [hm] at hp
  have he : Real.exp (-(b^2*(n:ℝ)*q^2/2+Real.log 8)) = 1/(8*E) := by
    rw [Real.exp_neg,Real.exp_add,Real.exp_log (by norm_num)]
    dsimp only [E]
    ring
  have hbound : Real.exp (-(b^2*(n:ℝ)*q^2/2+Real.log 8)) ≤ M^2/(4*S) := by
    rw [he]
    apply (div_le_div_iff₀ (by positivity : 0 < 8*E) (by positivity : 0 < 4*S)).mpr
    nlinarith
  have hex : Real.exp (b^2*((n:ℝ)-1)/4-Real.log 2) = M/2 := by
    rw [Real.exp_sub,Real.exp_log (by norm_num)]
  have hevent : {G : Disorder n | M/2 ≤ weightedPartition ν b G} =
      {G | b^2*((n:ℝ)-1)/4-Real.log 2 ≤ Real.log (weightedPartition ν b G)} := by
    ext G
    simp only [Set.mem_ofPred_eq]
    symm
    rw [← Real.exp_le_exp,
      Real.exp_log (weightedPartition_pos ν hνpos hν b G),hex]
  rw [← hevent]
  exact hbound.trans hp

theorem weightedPartition_half_gain {n : ℕ} (hn : 0 < n)
    (ν : Config n → ℝ) (hνpos : ∀ x, 0 ≤ ν x) (hν : ∑ x, ν x = 1)
    (b q : ℝ) (hb : b ≠ 0) (hq : 0 ≤ q)
    (hr : weightedOverlapMass ν q*Real.exp (b^2*(n:ℝ)/2) ≤
      Real.exp (b^2*(n:ℝ)*q^2/2)) :
    (1/2:ℝ) ≤ (disorderLaw n).real {G | b^2*((n:ℝ)-1)/4-Real.log 2-
      Real.sqrt (2*(logPartitionProxy b n:ℝ)*(b^2*(n:ℝ)*q^2/2+Real.log 8))-
      Real.sqrt (2*(logPartitionProxy b n:ℝ)*Real.log 2) ≤
        Real.log (weightedPartition ν b G)} := by
  apply subGaussian_half_lower
    ((continuous_weightedPartition ν b).log
      (fun G => (weightedPartition_pos ν hνpos hν b G).ne')).measurable
    (show 0 < (logPartitionProxy b n:ℝ) from by
      change 0 < Real.pi^2*b^2*(n:ℝ)/8
      have hn' : (0:ℝ) < n := by exact_mod_cast hn
      have hb' := sq_pos_of_ne_zero hb
      positivity)
    (weightedLogPartition_subGaussian hn ν hνpos hν b)
    (by positivity)
    (weightedPartition_paleyZygmund hn ν hνpos hν b q hq hr)
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageTrimming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem finiteOverlapMass_mono {n : ℕ} (ν : Config n → ℝ)
    (hν : ∀ x, 0 ≤ ν x) {T S : Finset (Config n)} (hTS : T ⊆ S) (q : ℝ) :
    finiteOverlapMass ν T q ≤ finiteOverlapMass ν S q := by
  unfold finiteOverlapMass
  apply le_trans (Finset.sum_le_sum (g := fun x => ∑ y ∈ S,
    if q ≤ |overlap x y| then ν x*ν y else 0) (fun x _ => ?_))
  · exact Finset.sum_le_sum_of_subset_of_nonneg hTS (fun x _ _ =>
      Finset.sum_nonneg (fun y _ => by split_ifs; exact mul_nonneg (hν x) (hν y); rfl))
  · exact Finset.sum_le_sum_of_subset_of_nonneg hTS (fun y _ _ => by split_ifs; exact mul_nonneg (hν x) (hν y); rfl)

theorem weightedOverlapMass_conditional_mono {n : ℕ} (ν : Config n → ℝ)
    (hν : ∀ x, 0 ≤ ν x) {T S : Finset (Config n)} (hTS : T ⊆ S)
    (hT : 0 < finiteMass ν T) (q : ℝ) :
    weightedOverlapMass (conditionalWeights ν T) q ≤
      (finiteMass ν S/finiteMass ν T)^2*weightedOverlapMass (conditionalWeights ν S) q := by
  have hS : 0 < finiteMass ν S := hT.trans_le (finiteMass_mono ν hν hTS)
  rw [weightedOverlapMass_conditional,weightedOverlapMass_conditional]
  have HE : (finiteMass ν S/finiteMass ν T)^2*(finiteOverlapMass ν S q/(finiteMass ν S)^2) =
      finiteOverlapMass ν S q/(finiteMass ν T)^2 := by
    field_simp
  rw [HE]
  exact div_le_div_of_nonneg_right (finiteOverlapMass_mono ν hν hTS q) (sq_nonneg _)

theorem gibbsMass_energyTrim {n : ℕ} (β e : ℝ) (J : Disorder n) (S : Finset (Config n)) :
    finiteMass (gibbs β J) S-gibbsEnergyTail β e J ≤
      finiteMass (gibbs β J) (energyTrim J e S) := by
  have Hadd := Finset.sum_filter_add_sum_filter_not S
    (fun x => hamiltonian J x ≤ (n:ℝ)*e) (gibbs β J)
  have Hle : (∑ x ∈ S.filter (fun x => ¬hamiltonian J x ≤ (n:ℝ)*e), gibbs β J x) ≤
      gibbsEnergyTail β e J := by
    unfold gibbsEnergyTail
    simp only [not_le]
    rw [Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun x _ _ => by split_ifs; exact le_of_lt (gibbs_pos β J x); rfl)
  change (∑ x ∈ S, gibbs β J x)-gibbsEnergyTail β e J ≤
    ∑ x ∈ S.filter (fun x => hamiltonian J x ≤ (n:ℝ)*e), gibbs β J x
  linarith

theorem partition_ratio_mix {n : ℕ} (β a b : ℝ) (J G : Disorder n) :
    partition β (mixDisorder a b (J,G))/partition β J =
      ∑ x : Config n, gibbs β J x*
        Real.exp (β*(a-1)*hamiltonian J x+β*b*hamiltonian G x) := by
  unfold partition gibbs
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [hamiltonian_mix]
  rw [div_mul_eq_mul_div,← Real.exp_add]
  congr 2
  ring

theorem conditionalWeightedPartition {n : ℕ} (ν : Config n → ℝ)
    (S : Finset (Config n)) (hS : 0 < finiteMass ν S) (b : ℝ) (G : Disorder n) :
    finiteMass ν S*weightedPartition (conditionalWeights ν S) b G =
      ∑ x ∈ S, ν x*Real.exp (b*hamiltonian G x) := by
  unfold weightedPartition conditionalWeights
  rw [Finset.mul_sum]
  have HE (x : Config n) : finiteMass ν S*((if x ∈ S then ν x/finiteMass ν S else 0)*
      Real.exp (b*hamiltonian G x)) =
      if x ∈ S then ν x*Real.exp (b*hamiltonian G x) else 0 := by
    split_ifs
    · field_simp
    · ring
  simp_rw [HE]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]

theorem partition_ratio_mix_lower {n : ℕ} {β a : ℝ} (hβ : 0 ≤ β) (ha : a ≤ 1)
    (b e : ℝ) (J G : Disorder n) (T : Finset (Config n))
    (hT : 0 < finiteMass (gibbs β J) T)
    (henergy : ∀ x ∈ T, hamiltonian J x ≤ (n:ℝ)*e) :
    finiteMass (gibbs β J) T*Real.exp (β*(a-1)*(n:ℝ)*e)*
      weightedPartition (conditionalWeights (gibbs β J) T) (β*b) G ≤
        partition β (mixDisorder a b (J,G))/partition β J := by
  rw [partition_ratio_mix]
  calc
    _ = Real.exp (β*(a-1)*(n:ℝ)*e)*
        ∑ x ∈ T, gibbs β J x*Real.exp ((β*b)*hamiltonian G x) := by
      rw [← conditionalWeightedPartition (gibbs β J) T hT]
      ring
    _ ≤ ∑ x ∈ T, gibbs β J x*
        Real.exp (β*(a-1)*hamiltonian J x+β*b*hamiltonian G x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x hx
      rw [Real.exp_add]
      have he : β*(a-1)*(n:ℝ)*e ≤ β*(a-1)*hamiltonian J x := by
        have HH := mul_le_mul_of_nonpos_left (henergy x hx)
          (mul_nonpos_of_nonneg_of_nonpos hβ (sub_nonpos.mpr ha))
        nlinarith
      have HH := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
        (mul_nonneg (gibbs_pos β J x).le (Real.exp_nonneg ((β*b)*hamiltonian G x)))
      nlinarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun x _ _ => mul_nonneg (gibbs_pos β J x).le (Real.exp_nonneg _))

theorem logPartition_mix_lower {n : ℕ} {β a : ℝ} (hβ : 0 ≤ β) (ha : a ≤ 1)
    (b e : ℝ) (J G : Disorder n) (T : Finset (Config n))
    (hT : 0 < finiteMass (gibbs β J) T)
    (henergy : ∀ x ∈ T, hamiltonian J x ≤ (n:ℝ)*e) :
    Real.log (finiteMass (gibbs β J) T)+β*(a-1)*(n:ℝ)*e+
      Real.log (weightedPartition (conditionalWeights (gibbs β J) T) (β*b) G) ≤
        logPartition β (mixDisorder a b (J,G))-logPartition β J := by
  have hw := weightedPartition_pos (conditionalWeights (gibbs β J) T)
    (conditionalWeights_nonneg (gibbs β J) (fun x => (gibbs_pos β J x).le) T)
    (conditionalWeights_sum (gibbs β J) T hT) (β*b) G
  have H := Real.log_le_log (mul_pos (mul_pos hT (Real.exp_pos _)) hw)
    (partition_ratio_mix_lower hβ ha b e J G T hT henergy)
  rw [Real.log_mul (mul_ne_zero hT.ne' (Real.exp_ne_zero _)) hw.ne',
    Real.log_mul hT.ne' (Real.exp_ne_zero _),Real.log_exp,
    Real.log_div (partition_pos β (mixDisorder a b (J,G))).ne' (partition_pos β J).ne'] at H
  exact H
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_UniformCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem continuous_gibbsMass {n : ℕ} (β : ℝ) (S : Finset (Config n)) :
    Continuous (fun J : Disorder n => finiteMass (gibbs β J) S) :=
  continuous_finsetSum _ (fun x _ => continuous_gibbs β x)

theorem continuous_gibbsOverlapMass {n : ℕ} (β q : ℝ) (S : Finset (Config n)) :
    Continuous (fun J : Disorder n => finiteOverlapMass (gibbs β J) S q) := by
  apply continuous_finsetSum
  intro x _
  apply continuous_finsetSum
  intro y _
  by_cases h : q ≤ |overlap x y|
  · simp only [ite_eq_left h]
    exact (continuous_gibbs β x).mul (continuous_gibbs β y)
  · simp only [ite_eq_right h]
    exact continuous_const

theorem measurableSet_coveragePairBad (n : ℕ) (β m r q : ℝ) :
    MeasurableSet (coveragePairBad n β m r q) := by
  have heq : coveragePairBad n β m r q = ⋃ S : Finset (Config n),
      {J | m ≤ finiteMass (gibbs β J) S} ∩
      {J | finiteOverlapMass (gibbs β J) S q < r*(finiteMass (gibbs β J) S)^2} := by
    ext J
    simp [coveragePairBad]
  rw [heq]
  apply MeasurableSet.iUnion
  intro S
  exact (measurableSet_le measurable_const (continuous_gibbsMass β S).measurable).inter
    (measurableSet_lt (continuous_gibbsOverlapMass β q S).measurable
      (measurable_const.mul ((continuous_gibbsMass β S).measurable.pow_const 2)))

theorem measurable_gibbsEnergyTail {n : ℕ} (β e : ℝ) :
    Measurable (gibbsEnergyTail (N := n) β e) := by
  apply Finset.measurable_sum
  intro x _
  exact Measurable.ite (measurableSet_lt measurable_const (continuous_hamiltonian x).measurable)
    (continuous_gibbs β x).measurable measurable_const

theorem coveragePairBad_probability_le {n : ℕ} (hn : 0 < n)
    {β θ m r q e ε u : ℝ} (hβ : 0 ≤ β) (hm : 0 < m) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (hb : β*Real.sin θ ≠ 0) (hε : ε ≤ m/2) (hu : 0 ≤ u)
    (hsecond : 4*r*Real.exp ((β*Real.sin θ)^2*(n:ℝ)/2) ≤
      Real.exp ((β*Real.sin θ)^2*(n:ℝ)*q^2/2))
    (hgain : u ≤ Real.log (m/2)+β*(Real.cos θ-1)*(n:ℝ)*e+
      freshCoverageGain n (β*Real.sin θ) q) :
    (disorderLaw n).real (coveragePairBad n β m r q) ≤
      (disorderLaw n).real {J | ε < gibbsEnergyTail β e J}+
      2*Real.exp (-u^2/(θ^2*β^2*(n:ℝ))) := by
  let A := coveragePairBad n β m r q ∩ {J | gibbsEnergyTail β e J ≤ ε}
  let E : Set (Disorder n × Disorder n) :=
    {p | u ≤ logPartition β (rotateDisorder θ p).1-logPartition β p.1}
  have hA : MeasurableSet A := (measurableSet_coveragePairBad n β m r q).inter
    (measurableSet_le (measurable_gibbsEnergyTail β e) measurable_const)
  have hE : MeasurableSet E := measurableSet_le measurable_const
    ((((continuous_logPartition β).comp (rotateDisorderCLM n θ).continuous.fst).sub
      ((continuous_logPartition β).comp continuous_fst)).measurable)
  have hsec (J : Disorder n) (hJ : J ∈ A) :
      (1/2:ℝ) ≤ (disorderLaw n).real {G | (J,G) ∈ E} := by
    obtain ⟨S,hS,hraw⟩ := hJ.1
    have htail : gibbsEnergyTail β e J ≤ ε := hJ.2
    let T := energyTrim J e S
    have hST : T ⊆ S := Finset.filter_subset _ _
    have htrim := gibbsMass_energyTrim β e J S
    have hmS : 0 < finiteMass (gibbs β J) S := hm.trans_le hS
    have hhalf : finiteMass (gibbs β J) S/2 ≤ finiteMass (gibbs β J) T := by
      dsimp only [T]
      linarith
    have hmT : 0 < finiteMass (gibbs β J) T := by linarith
    have hratio : finiteMass (gibbs β J) S/finiteMass (gibbs β J) T ≤ 2 := by
      apply (div_le_iff₀ hmT).mpr
      linarith
    have hratio0 : 0 ≤ finiteMass (gibbs β J) S/finiteMass (gibbs β J) T :=
      div_nonneg hmS.le hmT.le
    have hcondS : weightedOverlapMass (conditionalWeights (gibbs β J) S) q ≤ r := by
      rw [weightedOverlapMass_conditional]
      exact (div_le_iff₀ (sq_pos_of_pos hmS)).mpr hraw.le
    have hcondT : weightedOverlapMass (conditionalWeights (gibbs β J) T) q ≤ 4*r := by
      apply (weightedOverlapMass_conditional_mono (gibbs β J)
        (fun x => (gibbs_pos β J x).le) hST hmT q).trans
      have HH := mul_le_mul_of_nonneg_left hcondS
        (sq_nonneg (finiteMass (gibbs β J) S/finiteMass (gibbs β J) T))
      have Hsq : (finiteMass (gibbs β J) S/finiteMass (gibbs β J) T)^2 ≤ 4 := by
        nlinarith
      exact HH.trans (mul_le_mul_of_nonneg_right Hsq hr)
    have hg := weightedPartition_half_gain hn (conditionalWeights (gibbs β J) T)
      (conditionalWeights_nonneg (gibbs β J) (fun x => (gibbs_pos β J x).le) T)
      (conditionalWeights_sum (gibbs β J) T hmT) (β*Real.sin θ) q hb hq
      ((mul_le_mul_of_nonneg_right hcondT (Real.exp_nonneg _)).trans hsecond)
    apply hg.trans
    apply measureReal_mono (μ := disorderLaw n) _ (measure_ne_top _ _)
    intro G hG
    have hmix := logPartition_mix_lower hβ (Real.cos_le_one θ) (Real.sin θ) e J G T hmT
      (fun x hx => (Finset.mem_filter.mp hx).2)
    have hmass : Real.log (m/2) ≤ Real.log (finiteMass (gibbs β J) T) :=
      Real.log_le_log (by positivity) (by linarith)
    change u ≤ logPartition β (mixDisorder (Real.cos θ) (Real.sin θ) (J,G))-
      logPartition β J
    change freshCoverageGain n (β*Real.sin θ) q ≤ _ at hG
    linarith
  have Hint := product_event_lower_of_sections (disorderLaw n) (disorderLaw n)
    hA hE (by norm_num : (0:ℝ) ≤ 1/2) hsec
  have Htail := rotation_logPartition_tail hn β θ u hu
  have Hbad : coveragePairBad n β m r q ⊆ A ∪ {J | ε < gibbsEnergyTail β e J} := by
    intro J hJ
    by_cases h : gibbsEnergyTail β e J ≤ ε
    · exact Or.inl ⟨hJ,h⟩
    · exact Or.inr (lt_of_not_ge h)
  have HB := (measureReal_mono (μ := disorderLaw n) Hbad (measure_ne_top _ _)).trans (measureReal_union_le A {J | ε < gibbsEnergyTail β e J})
  change (1/2)*(disorderLaw n).real A ≤ (disorderPairLaw n).real E at Hint
  change (disorderPairLaw n).real E ≤ _ at Htail
  linarith
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageAsymptotic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem sqrt_div_positive {a L : ℝ} (hL : 0 < L) :
    Real.sqrt a/L = Real.sqrt (a/L^2) := by
  rw [Real.sqrt_div' a (sq_nonneg L),Real.sqrt_sq_eq_abs,abs_of_pos hL]

theorem freshCoverageGain_div {n : ℕ} (hn : 0 < n) (b q L : ℝ) (hL : 0 < L) :
    freshCoverageGain n b q/L =
      (b^2*(n:ℝ)/L)*(1-1/(n:ℝ))/4-Real.log 2/L-
      Real.sqrt (Real.pi^2*(b^2*(n:ℝ)/L)*((b^2*(n:ℝ)/L)*q^2/2+Real.log 8/L)/4)-
      Real.sqrt (Real.pi^2*(b^2*(n:ℝ)/L)*(Real.log 2/L)/4) := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold freshCoverageGain
  rw [sub_div,sub_div,sub_div,sqrt_div_positive hL,sqrt_div_positive hL]
  have hterm : b^2*((n:ℝ)-1)/4/L = (b^2*(n:ℝ)/L)*(1-1/(n:ℝ))/4 := by
    field_simp
  rw [hterm]
  change _-Real.sqrt ((2*(Real.pi^2*b^2*(n:ℝ)/8)*(b^2*(n:ℝ)*q^2/2+Real.log 8))/L^2)-
    Real.sqrt ((2*(Real.pi^2*b^2*(n:ℝ)/8)*Real.log 2)/L^2) = _
  congr 2 <;> field_simp <;> ring_nf

theorem freshCoverageGain_div_tendsto (L b : ℕ → ℝ) {v q : ℝ}
    (hL : Tendsto L atTop atTop)
    (hV : Tendsto (fun n => (b n)^2*(n:ℝ)/L n) atTop (𝓝 v)) :
    Tendsto (fun n => freshCoverageGain n (b n) q/L n) atTop
      (𝓝 (v/4-Real.sqrt (Real.pi^2*v^2*q^2/8))) := by
  have hLi : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp hL
  have hN : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h2 : Tendsto (fun n => Real.log 2/L n) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero,div_eq_mul_inv] using hLi.const_mul (Real.log 2)
  have h8 : Tendsto (fun n => Real.log 8/L n) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero,div_eq_mul_inv] using hLi.const_mul (Real.log 8)
  have H := (((hV.mul ((tendsto_const_nhds (x := (1:ℝ))).sub hN)).div_const 4).sub h2).sub
    ((hV.const_mul (Real.pi^2) |>.mul ((hV.mul_const (q^2) |>.div_const 2).add h8)).div_const 4).sqrt
  have H' := H.sub ((hV.const_mul (Real.pi^2) |>.mul h2).div_const 4).sqrt
  have HH : Tendsto (fun n =>
      ((b n)^2*(n:ℝ)/L n)*(1-1/(n:ℝ))/4-Real.log 2/L n-
      Real.sqrt (Real.pi^2*((b n)^2*(n:ℝ)/L n)*(((b n)^2*(n:ℝ)/L n)*q^2/2+Real.log 8/L n)/4)-
      Real.sqrt (Real.pi^2*((b n)^2*(n:ℝ)/L n)*(Real.log 2/L n)/4)) atTop
      (𝓝 (v/4-Real.sqrt (Real.pi^2*v^2*q^2/8))) := by
    convert H' using 1 <;> simp only [one_div,sub_zero,mul_one,mul_zero,zero_div,Real.sqrt_zero,add_zero]
    congr 2
    ring_nf
  apply HH.congr'
  filter_upwards [hL.eventually (eventually_gt_atTop (0:ℝ)),eventually_gt_atTop (0:ℕ)] with n hLn hn
  exact (freshCoverageGain_div hn (b n) q (L n) hLn).symm

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageGainRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem exists_positive_coverageGainRate {β e : ℝ} (hβ : 0 < β) (he : e < β/2) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ 0 < coverageGainRate β e q := by
  let g := β^2/4-β*e/2
  have hg : 0 < g := by dsimp only [g]; nlinarith
  let q := min (1/2:ℝ) (g/(4*Real.pi*β^2))
  have hq : 0 < q := lt_min (by norm_num) (by positivity)
  have hq1 : q < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hqbound : Real.pi*β^2*q ≤ g/4 := by
    have H := (le_div_iff₀ (show 0 < 4*Real.pi*β^2 by positivity)).mp (min_le_right (1/2:ℝ) (g/(4*Real.pi*β^2)))
    change q*(4*Real.pi*β^2) ≤ g at H
    nlinarith
  have hroot : Real.sqrt (Real.pi^2*(β^2)^2*q^2/8) ≤ Real.pi*β^2*q := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have H : 0 ≤ (Real.pi*β^2*q)^2 := sq_nonneg _
      nlinarith
  refine ⟨q,hq,hq1,?_⟩
  change 0 < g-Real.sqrt (Real.pi^2*(β^2)^2*q^2/8)
  linarith

theorem coverage_totalGain_div_tendsto (L : ℕ → ℝ) {M β e D q : ℝ} (hM : 0 < M)
    (hL : Tendsto L atTop atTop)
    (hsub : Tendsto (fun n => L n/(n:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (Real.log (Real.exp (-D*L n)/2)+
      β*(Real.cos (coverageAngle L M n)-1)*(n:ℝ)*e+
      freshCoverageGain n (β*Real.sin (coverageAngle L M n)) q)/L n)
      atTop (𝓝 (M*coverageGainRate β e q-D)) := by
  have hlog : Tendsto (fun n => Real.log (Real.exp (-D*L n)/2)/L n) atTop (𝓝 (-D)) := by
    have H := (tendsto_const_nhds (x := -D)).sub (hL.const_div_atTop (Real.log 2))
    simp only [sub_zero] at H
    apply H.congr'
    filter_upwards [hL.eventually (eventually_gt_atTop (0:ℝ))] with n hLn
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num),Real.log_exp]
    field_simp
  have hV := coverageAngle_variance_tendsto (β := β) L hM hL hsub
  have hf := freshCoverageGain_div_tendsto (q := q) L
    (fun n => β*Real.sin (coverageAngle L M n)) hL hV
  have he' := coverageAngle_loss_tendsto (β := β) (e := e) L hM hL hsub
  have H := (hlog.add he').add hf
  have hroot : Real.sqrt (Real.pi^2*(β^2*M)^2*q^2/8) =
      M*Real.sqrt (Real.pi^2*(β^2)^2*q^2/8) := by
    rw [show Real.pi^2*(β^2*M)^2*q^2/8 = M^2*(Real.pi^2*(β^2)^2*q^2/8) by ring,
      Real.sqrt_mul (sq_nonneg M),Real.sqrt_sq_eq_abs,abs_of_pos hM]
  convert H using 1
  · funext n
    rw [add_div,add_div]
  · rw [hroot]
    unfold coverageGainRate
    congr 1
    ring

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem coverage_eventually_parameters (L : ℕ → ℝ) {β e q cE D : ℝ}
    (hβ : 0 < β) (hcE : 0 < cE) (hD : 0 < D)
    (hK : 0 < coverageGainRate β e q)
    (hL : Tendsto L atTop atTop)
    (hsub : Tendsto (fun n => L n/(n:ℝ)) atTop (𝓝 0)) :
    ∃ M D₂ : ℝ, 0 < M ∧ 0 < D₂ ∧ ∀ᶠ n : ℕ in atTop,
      0 < n ∧ 0 < L n ∧ β*Real.sin (coverageAngle L M n) ≠ 0 ∧
      Real.exp (-cE*(n:ℝ)) ≤ Real.exp (-D*L n)/2 ∧
      4*Real.exp (-D₂*L n)*Real.exp ((β*Real.sin (coverageAngle L M n))^2*(n:ℝ)/2) ≤
        Real.exp ((β*Real.sin (coverageAngle L M n))^2*(n:ℝ)*q^2/2) ∧
      L n ≤ Real.log (Real.exp (-D*L n)/2)+
        β*(Real.cos (coverageAngle L M n)-1)*(n:ℝ)*e+
        freshCoverageGain n (β*Real.sin (coverageAngle L M n)) q := by
  let M := (D+2)/coverageGainRate β e q
  have hM : 0 < M := by dsimp only [M]; positivity
  let D₂ := β^2*M+2
  have hD₂ : 0 < D₂ := by dsimp only [D₂]; positivity
  have hMG : M*coverageGainRate β e q-D = 2 := by dsimp only [M]; field_simp; ring
  have hgain := coverage_totalGain_div_tendsto (β := β) (e := e) (D := D) (q := q)
    L hM hL hsub
  rw [hMG] at hgain
  have hsmall : Tendsto (fun n : ℕ => D*(L n/(n:ℝ))+Real.log 2/(n:ℝ))
      atTop (𝓝 0) := by
    have H := (hsub.const_mul D).add
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop (Real.log 2))
    simpa using H
  refine ⟨M,D₂,hM,hD₂,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℕ),hL.eventually (eventually_gt_atTop (0:ℝ)),
    hL.eventually (eventually_ge_atTop (Real.log 4)),
    (coverageAngle_tendsto L M hsub).eventually (eventually_lt_nhds Real.pi_pos),
    hsmall.eventually (eventually_lt_nhds hcE),
    (coverageAngle_variance_tendsto (β := β) L hM hL hsub).eventually
      (eventually_lt_nhds (show β^2*M < β^2*M+1 by linarith)),
    hgain.eventually (eventually_gt_nhds (by norm_num : (1:ℝ) < 2))]
    with n hn hLn hLlog hθ htail hV hG
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hθpos := coverageAngle_pos hM hn hLn
  have hb : β*Real.sin (coverageAngle L M n) ≠ 0 :=
    ne_of_gt (mul_pos hβ (Real.sin_pos_of_pos_of_lt_pi hθpos hθ))
  refine ⟨hn,hLn,hb,?_,?_,?_⟩
  · have H : D*L n+Real.log 2 < cE*(n:ℝ) := by
      have HH := (div_lt_iff₀ hn').mp (show (D*L n+Real.log 2)/(n:ℝ) < cE by
        simpa only [add_div,mul_div_assoc] using htail)
      exact HH
    rw [show Real.exp (-D*L n)/2 = Real.exp (-D*L n-Real.log 2) by
      rw [Real.exp_sub,Real.exp_log (by norm_num)]]
    apply Real.exp_le_exp.mpr
    linarith
  · have HV : (β*Real.sin (coverageAngle L M n))^2*(n:ℝ) < (β^2*M+1)*L n :=
      (div_lt_iff₀ hLn).mp hV
    have hML : 0 ≤ β^2*M*L n := by positivity
    have HE : Real.log 4-D₂*L n+(β*Real.sin (coverageAngle L M n))^2*(n:ℝ)/2 ≤ 0 := by
      dsimp only [D₂]
      nlinarith
    calc
      _ = Real.exp (Real.log 4-D₂*L n+(β*Real.sin (coverageAngle L M n))^2*(n:ℝ)/2) := by
        rw [Real.exp_add,Real.exp_sub,Real.exp_log (by norm_num),neg_mul,Real.exp_neg]
        ring
      _ ≤ 1 := (Real.exp_le_one_iff).mpr HE
      _ ≤ _ := Real.one_le_exp (by positivity)
  · simpa only [one_mul] using ((le_div_iff₀ hLn).mp hG.le)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem uniform_coverage_pair {β : ℝ} (hβ : 1 < β) (L : ℕ → ℝ)
    (hL : Tendsto L atTop atTop)
    (hsub : Tendsto (fun n => L n/(n:ℝ)) atTop (𝓝 0)) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ D : ℝ, 0 < D → ∃ D₂ : ℝ, 0 < D₂ ∧
      Tendsto (fun n => (disorderLaw n).real
        (coveragePairBad n β (Real.exp (-D*L n)) (Real.exp (-D₂*L n)) q))
        atTop (𝓝 0) := by
  obtain ⟨e,he,cE,hcE,N₀,hN₀⟩ := coverage_energy_tail hβ
  have hβpos : 0 < β := lt_trans zero_lt_one hβ
  obtain ⟨q,hq,hq1,hK⟩ := exists_positive_coverageGainRate hβpos he.2
  refine ⟨q,hq,hq1,?_⟩
  intro D hD
  obtain ⟨M,D₂,hM,hD₂,hpars⟩ := coverage_eventually_parameters (e := e) (q := q) L hβpos hcE hD hK hL hsub
  refine ⟨D₂,hD₂,?_⟩
  have hbound : ∀ᶠ n : ℕ in atTop,
      (disorderLaw n).real (coveragePairBad n β (Real.exp (-D*L n)) (Real.exp (-D₂*L n)) q) ≤
        Real.exp (-cE*(n:ℝ))+2*Real.exp (-L n/(β^2*M)) := by
    filter_upwards [hpars,eventually_ge_atTop N₀] with n hn hlarge
    obtain ⟨hnpos,hLn,hb,htrim,hsecond,hgain⟩ := hn
    have HH := coveragePairBad_probability_le hnpos hβpos.le
      (Real.exp_pos (-D*L n)) (Real.exp_nonneg (-D₂*L n)) hq.le hb htrim hLn.le hsecond hgain
    have HE := hN₀ n hlarge
    have hn' : (0:ℝ) < n := by exact_mod_cast hnpos
    have hθ : coverageAngle L M n^2 = M*L n/(n:ℝ) := Real.sq_sqrt (by positivity)
    have hquot : -(L n)^2/((coverageAngle L M n)^2*β^2*(n:ℝ)) = -L n/(β^2*M) := by
      rw [hθ]
      field_simp
    rw [hquot] at HH
    exact HH.trans (add_le_add HE le_rfl)
  have hE : Tendsto (fun n : ℕ => Real.exp (-cE*(n:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg (neg_neg_of_pos hcE))
  have hR : Tendsto (fun n => Real.exp (-L n/(β^2*M))) atTop (𝓝 0) := by
    have H := Real.tendsto_exp_atBot.comp
      (hL.const_mul_atTop_of_neg (neg_lt_zero.mpr (show 0 < 1/(β^2*M) by positivity)))
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    congr 1
    ring
  have H := hE.add (hR.const_mul 2)
  simp only [mul_zero,add_zero] at H
  exact squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg)) hbound H

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageTheorem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem uniform_coverage {β : ℝ} (hβ : 1 < β) (L : ℕ → ℝ)
    (hL : Tendsto L atTop atTop)
    (hsub : Tendsto (fun n => L n/(n:ℝ)) atTop (𝓝 0)) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ D : ℝ, 0 < D → ∃ D₃ : ℝ, 0 < D₃ ∧
      ∃ C : (n : ℕ) → Set (Disorder n), (∀ n, MeasurableSet (C n)) ∧
        Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1) ∧
        ∀ n J, J ∈ C n → ∀ S : Finset (Config n),
          finiteMass (gibbs β J) (S.filter (fun x =>
            finiteMass (gibbs β J) (S.filter (fun y => q ≤ |overlap x y|)) <
              Real.exp (-D₃*L n))) < Real.exp (-D*L n) := by
  obtain ⟨q,hq,hq1,H⟩ := uniform_coverage_pair hβ L hL hsub
  refine ⟨q,hq,hq1,?_⟩
  intro D hD
  obtain ⟨D₂,hD₂,hlim⟩ := H D hD
  let C (n : ℕ) := (coveragePairBad n β (Real.exp (-D*L n)) (Real.exp (-D₂*L n)) q)ᶜ
  have hm (n : ℕ) := measurableSet_coveragePairBad n β (Real.exp (-D*L n)) (Real.exp (-D₂*L n)) q
  refine ⟨D+D₂,add_pos hD hD₂,C,(fun n => (hm n).compl),?_,?_⟩
  · have Hlim := (tendsto_const_nhds (x := (1:ℝ))).sub hlim
    simp only [sub_zero] at Hlim
    convert Hlim using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    dsimp only [C]
    rw [measureReal_compl (hm n),probReal_univ]
  · intro n J hJ S
    have hpair (T : Finset (Config n)) (hT : Real.exp (-D*L n) ≤ finiteMass (gibbs β J) T) :
        Real.exp (-D₂*L n) ≤ weightedOverlapMass (conditionalWeights (gibbs β J) T) q := by
      have hraw : Real.exp (-D₂*L n)*(finiteMass (gibbs β J) T)^2 ≤
          finiteOverlapMass (gibbs β J) T q := by
        apply le_of_not_gt
        intro hbad
        exact hJ ⟨T,hT,hbad⟩
      rw [weightedOverlapMass_conditional]
      exact (le_div_iff₀ (sq_pos_of_pos ((Real.exp_pos _).trans_le hT))).mpr hraw
    have Hcov := finite_coverage_of_pair_bound (gibbs β J) (fun x => (gibbs_pos β J x).le)
      (Real.exp_pos (-D*L n)) (Real.exp_nonneg (-D₂*L n)) hpair S
    have heq : Real.exp (-D*L n)*Real.exp (-D₂*L n) = Real.exp (-(D+D₂)*L n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [heq] at Hcov

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem stretchedLogScale_tendsto :
    Tendsto (fun n : ℕ => (n:ℝ)^kappa) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num [kappa])).comp tendsto_natCast_atTop_atTop

theorem stretchedLogScale_sublinear :
    Tendsto (fun n : ℕ => (n:ℝ)^kappa/(n:ℝ)) atTop (𝓝 0) := by
  have H := (tendsto_rpow_neg_atTop (by norm_num [kappa] : 0 < 1-kappa)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  change (n:ℝ)^(-(1-kappa)) = (n:ℝ)^kappa/(n:ℝ)
  rw [show -(1-kappa) = kappa-1 by ring,Real.rpow_sub hn',Real.rpow_one]

theorem stretched_uniform_coverage_oai {β : ℝ} (hβ : 1 < β) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ D : ℝ, 0 < D → ∃ D₃ : ℝ, 0 < D₃ ∧
      ∃ C : (n : ℕ) → Set (Disorder n), (∀ n, MeasurableSet (C n)) ∧
        Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1) ∧
        ∀ n J, J ∈ C n → ∀ S : Finset (Config n),
          finiteMass (gibbs β J) (S.filter (fun x =>
            finiteMass (gibbs β J) (S.filter (fun y => q ≤ |overlap x y|)) <
              Real.exp (-D₃*((n:ℝ)^kappa)))) < Real.exp (-D*((n:ℝ)^kappa)) :=
  uniform_coverage hβ (fun n => (n:ℝ)^kappa) stretchedLogScale_tendsto stretchedLogScale_sublinear

end SK.Analytic

end
end

end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.stretched_uniform_coverage_oai := @OAI.SK.Analytic.stretched_uniform_coverage_oai
