-- Prove2me | solution 1 for OAI.PlanarFalconer.mainTarget_proved
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:23:37.601193+00:00
-- url     : https://prove2.me/submissions/361cb33a-17d7-43e4-a1f1-43f1e9ec8b74

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_exists_normalized_root_setup
import Theorems.Thm_OAI_PlanarFalconer_two_root_has_shell_approximations

section
-- module Solutions.OAIQ038_FA.Falconer_DistanceSet
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set

theorem distanceSet_eq_image (E : Set Plane) :
    distanceSet E = (fun z : Plane × Plane => dist z.1 z.2) '' (E ×ˢ E) := by
  ext r
  constructor
  · rintro ⟨x,hx,y,hy,hr⟩
    exact ⟨(x,y), ⟨hx,hy⟩, hr⟩
  · rintro ⟨⟨x,y⟩, ⟨hx,hy⟩,hr⟩
    exact ⟨x,hx,y,hy,hr⟩

theorem distanceSet_isCompact {E : Set Plane} (hE : IsCompact E) :
    IsCompact (distanceSet E) := by
  rw [distanceSet_eq_image]
  exact (hE.prod hE).image (continuous_fst.dist continuous_snd)

theorem distanceSet_measurable {E : Set Plane} (hE : IsCompact E) :
    MeasurableSet (distanceSet E) :=
  (distanceSet_isCompact hE).measurableSet

theorem positive_volume_of_carried_absolutelyContinuous
    (D : Set ℝ) (τ : Measure ℝ) (hmass : 0 < τ univ)
    (hcarried : τ Dᶜ = 0) (hac : τ ≪ volume) : 0 < volume D := by
  by_contra h
  have hzero : volume D = 0 := le_antisymm (not_lt.mp h) bot_le
  have hτ : τ D = 0 := hac hzero
  have hz := measure_union_null hτ hcarried
  have : τ univ = 0 := by simpa only [union_compl_self] using hz
  exact (ne_of_gt hmass) this

theorem distanceSet_positive_of_measure (E : Set Plane) (τ : Measure ℝ)
    (hmass : 0 < τ univ) (hcarried : τ (distanceSet E)ᶜ = 0) (hac : τ ≪ volume) :
    0 < volume (distanceSet E) :=
  positive_volume_of_carried_absolutelyContinuous (distanceSet E) τ hmass hcarried hac

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_SmoothShellPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceShellPartition_telescope (n : ℕ) (r : ℝ) :
    sourceShellLowpass 0 r + ∑ k ∈ Finset.range n, sourceShellBand k r = sourceShellLowpass n r := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ← add_assoc, ih, sourceShellBand]; ring

theorem sourceShellLowpass_tendsto (r : ℝ) :
    Tendsto (fun n => sourceShellLowpass n r) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => r/(2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
  have h := sourceShellBump.continuous.continuousAt.tendsto.comp ht
  have hz : sourceShellBump (0:ℝ) = 1 := sourceShellBump.one_of_mem_closedBall (by
    change dist (0:ℝ) 0 ≤ 1
    norm_num)
  simpa only [sourceShellLowpass, hz, Function.comp_def] using h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SourceAssemblyParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff

theorem exists_source_assembly_parameters {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ β lam sig kap : ℝ, β = δ/10 ∧ 0 < lam ∧ lam < δ/1000 ∧ 0 < sig ∧
      0 < kap ∧ 1000000*kap < β ∧ sig < kap/1000 ∧
      10000000*(lam+sig)/kap < β/100 := by
  let kap := δ/1000000000
  let lam := δ^2/1000000000000000000000000
  have hd2 : 0 < δ^2 := sq_pos_of_pos hδ
  have hd2δ : δ^2 < δ := by nlinarith
  have hkap : 0 < kap := by dsimp only [kap]; positivity
  refine ⟨δ/10,lam,lam,kap,rfl,?_,?_,?_,hkap,?_,?_,?_⟩
  · dsimp only [lam]; positivity
  · dsimp only [lam]; nlinarith
  · dsimp only [lam]; positivity
  · dsimp only [kap]; linarith
  · dsimp only [lam,kap]; nlinarith
  · apply (div_lt_iff₀ hkap).mpr
    dsimp only [lam,kap]
    nlinarith

theorem exists_assembly_shell_cutoff :
    ∃ Ψ : ℝ → ℝ, ContDiff ℝ ∞ Ψ ∧ (∀ x, 0 ≤ Ψ x) ∧
      (∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) ∧
      (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) := by
  refine ⟨assemblyShellBump,assemblyShellBump.contDiff,fun _ => assemblyShellBump.nonneg,?_,?_⟩
  · intro x hx
    have hh : dist x (5/4:ℝ) < 1 := by
      by_contra hn
      exact hx (assemblyShellBump.zero_of_le_dist (not_lt.mp hn))
    rw [Real.dist_eq,abs_lt] at hh
    constructor <;> linarith
  · intro x hx
    have hh : x ∈ closedBall (5/4:ℝ) assemblyShellBump.rIn := by
      change dist x (5/4:ℝ) ≤ 3/4
      rw [Real.dist_eq,abs_le]
      constructor <;> linarith [hx.1,hx.2]
    rw [assemblyShellBump.one_of_mem_closedBall hh]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_MeasureKernelConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform

theorem shellKernelMeasureConvolution_L1 (τ : Measure ℝ) [IsFiniteMeasure τ] (n : ℕ) :
    Integrable (kernelMeasureConvolution (sourceShellKernel n) τ) ∧
      (∫ x, ‖kernelMeasureConvolution (sourceShellKernel n) τ x‖) ≤
        τ.real univ * ∫ x, ‖sourceShellKernel 0 x‖ := by
  simpa only [sourceShellKernel_uniform_L1] using kernelMeasureConvolution_L1
    (sourceShellKernel n) (sourceShellKernel_continuous n) (sourceShellKernel_integrable n) τ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ShellFrequencyTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped Topology

theorem sourceShellLowpass_abs_le (n : ℕ) (r : ℝ) : |sourceShellLowpass n r| ≤ 1 := by
  rw [abs_of_nonneg (show 0 ≤ sourceShellLowpass n r from sourceShellBump.nonneg)]
  exact sourceShellBump.le_one

theorem sourceShellLowpass_fourier_test (τ : Measure ℝ) [IsFiniteMeasure τ]
    (f : ℝ → ℂ) (hf : Integrable f) :
    Tendsto (fun n => ∫ r, sourceShellLowpass n r • (charFun τ r * f r)) atTop
      (𝓝 (∫ r, charFun τ r * f r)) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun r => sourceShellLowpass n r • (charFun τ r * f r)) volume :=
    (sourceShellLowpass_smooth n).continuous.aestronglyMeasurable.smul
      (continuous_charFun.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  have hb (n : ℕ) : ∀ᵐ r ∂volume,
      ‖sourceShellLowpass n r • (charFun τ r * f r)‖ ≤ τ.real univ * ‖f r‖ := by
    filter_upwards with r
    rw [norm_smul, Real.norm_eq_abs, norm_mul]
    calc
      |sourceShellLowpass n r| * (‖charFun τ r‖ * ‖f r‖) ≤
          1 * (‖charFun τ r‖ * ‖f r‖) :=
        mul_le_mul_of_nonneg_right (sourceShellLowpass_abs_le n r) (by positivity)
      _ ≤ τ.real univ * ‖f r‖ := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right (norm_charFun_le r) (norm_nonneg _)
  have hp : ∀ᵐ r ∂volume,
      Tendsto (fun n => sourceShellLowpass n r • (charFun τ r * f r)) atTop
        (𝓝 (charFun τ r * f r)) := by
    filter_upwards with r
    simpa using (sourceShellLowpass_tendsto r).smul (tendsto_const_nhds (x := charFun τ r * f r))
  exact tendsto_integral_of_dominated_convergence (fun r => τ.real univ * ‖f r‖)
    hm (hf.norm.const_mul _) hb hp

theorem sourceShellPartition_fourier_test (τ : Measure ℝ) [IsFiniteMeasure τ]
    (f : ℝ → ℂ) (hf : Integrable f) :
    Tendsto (fun n => ∫ r, (sourceShellLowpass 0 r +
      ∑ k ∈ Finset.range n, sourceShellBand k r) • (charFun τ r * f r)) atTop
      (𝓝 (∫ r, charFun τ r * f r)) := by
  simpa only [sourceShellPartition_telescope] using sourceShellLowpass_fourier_test τ f hf

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SpatialFourierTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology

 theorem sourceInverseKernel_pairing (f : ℝ → ℂ) (hf : Integrable f)
    (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, φ x * sourceInverseKernel f x) =
      (2*Real.pi)⁻¹ • ∫ r, f r * 𝓕 φ (r/(2*Real.pi)) := by
  let g : ℝ × ℝ → ℂ := fun z =>
    φ z.1 * (Complex.exp (↑(-z.1*z.2)*Complex.I) * f z.2)
  have hg : AEStronglyMeasurable g (volume.prod volume) :=
    φ.continuous.aestronglyMeasurable.comp_fst.mul
      ((by fun_prop : Continuous (fun z : ℝ × ℝ =>
        Complex.exp (↑(-z.1*z.2)*Complex.I))).aestronglyMeasurable.mul
        hf.aestronglyMeasurable.comp_snd)
  have hi : Integrable g (volume.prod volume) :=
    (φ.integrable.norm.mul_prod hf.norm).mono' hg (by
      filter_upwards with z
      simp [g, Complex.norm_exp, Complex.mul_re])
  simp_rw [sourceInverseKernel_formula, mul_smul_comm, ← integral_const_mul]
  rw [integral_smul, integral_integral_swap hi]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  have he : -2*Real.pi*x*(r/(2*Real.pi)) = -x*r := by field_simp
  rw [he, smul_eq_mul]
  ring

 theorem sourceSchwartz_inversion (φ : 𝓢(ℝ, ℂ)) (y : ℝ) :
    (2*Real.pi)⁻¹ • (∫ r, Complex.exp (↑(r*y)*Complex.I) * 𝓕 φ (r/(2*Real.pi))) = φ y := by
  have hs := Measure.integral_comp_div
    (fun u : ℝ => Complex.exp (↑(2*Real.pi*u*y)*Complex.I) * 𝓕 φ u) (2*Real.pi)
  have he (r : ℝ) : 2*Real.pi*(r/(2*Real.pi))*y = r*y := by field_simp
  simp_rw [he] at hs
  rw [hs, abs_of_pos (by positivity : (0:ℝ)<2*Real.pi), smul_smul,
    inv_mul_cancel₀ (by positivity), one_smul]
  have h := congrArg (fun ψ : 𝓢(ℝ, ℂ) => ψ y)
    (show (𝓕⁻ (𝓕 φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = φ from
      FourierTransform.fourierInv_fourier_eq φ)
  simpa only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq', real_inner_eq_re_inner,
    RCLike.inner_apply, conj_trivial, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using h

 theorem source_characteristic_schwartz_test (τ : Measure ℝ) [IsFiniteMeasure τ]
    (φ : 𝓢(ℝ, ℂ)) :
    (2*Real.pi)⁻¹ • (∫ r, charFun τ r * 𝓕 φ (r/(2*Real.pi))) = ∫ y, φ y ∂τ := by
  let f : ℝ → ℂ := fun r => 𝓕 φ (r/(2*Real.pi))
  have hf : Integrable f := (𝓕 φ).integrable.comp_div (by positivity)
  let g : ℝ × ℝ → ℂ := fun z => Complex.exp (↑(z.1*z.2)*Complex.I)*f z.1
  have hp : Integrable g (volume.prod τ) :=
    (hf.norm.comp_fst τ).mono' (by dsimp [g, f]; fun_prop) (by
      filter_upwards with z
      simp [g, Complex.norm_exp, Complex.mul_re])
  simp_rw [charFun_apply_real, ← integral_mul_const]
  have he (r y : ℝ) : Complex.exp ((r:ℂ)*(y:ℂ)*Complex.I) * f r = g (r,y) := by
    simp [g, Complex.ofReal_mul]
  change (2*Real.pi)⁻¹ • (∫ r : ℝ, ∫ y : ℝ, Complex.exp ((r:ℂ)*(y:ℂ)*Complex.I) * f r ∂τ) = _
  simp_rw [he]
  rw [integral_integral_swap hp, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with y
  exact sourceSchwartz_inversion φ y

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_LowFrequencyKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology

 theorem schwartz_charFun_integrable (f : 𝓢(ℝ, ℂ)) (τ : Measure ℝ) [IsFiniteMeasure τ] :
    Integrable (fun r => f r * charFun τ r) := by
  apply (f.integrable.norm.mul_const (τ.real univ)).mono' (by fun_prop)
  filter_upwards with r
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_charFun_le r) (norm_nonneg _)

 theorem schwartzKernelMeasureConvolution_test (f : 𝓢(ℝ, ℂ))
    (τ : Measure ℝ) [IsFiniteMeasure τ] (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, φ x * kernelMeasureConvolution (sourceInverseKernel f) τ x) =
      (2*Real.pi)⁻¹ • ∫ r, f r * (charFun τ r * 𝓕 φ (r/(2*Real.pi))) := by
  have he : kernelMeasureConvolution (sourceInverseKernel f) τ =
      sourceInverseKernel (fun r => f r * charFun τ r) :=
    funext (sourceInverseKernel_measure f f.continuous f.integrable τ)
  rw [he, sourceInverseKernel_pairing _ (schwartz_charFun_integrable f τ) φ]
  simp only [mul_assoc]

 theorem schwartz_cutoff_test_integrable (f φ : 𝓢(ℝ, ℂ)) (τ : Measure ℝ) [IsFiniteMeasure τ] :
    Integrable (fun r => f r * (charFun τ r * 𝓕 φ (r/(2*Real.pi)))) := by
  have h2 := (schwartz_charFun_integrable f τ)
  have hb : ∃ C : ℝ, ∀ r, ‖𝓕 φ (r/(2*Real.pi))‖ ≤ C := by
    obtain ⟨C,_,hC⟩ := (𝓕 φ).decay 0 0
    exact ⟨C, fun r => by simpa using hC (r/(2*Real.pi))⟩
  obtain ⟨C,hC⟩ := hb
  apply (h2.norm.mul_const C).mono' (by fun_prop)
  filter_upwards with r
  rw [← mul_assoc, norm_mul]
  exact mul_le_mul_of_nonneg_left (hC r) (norm_nonneg _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ShellSummability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped ENNReal Topology

 theorem summable_dyadic_decay {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => (2:ℝ)^(-a*(n:ℝ))) := by
  have hq : (2:ℝ)^(-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  convert summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) (-a)) hq using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

 theorem shellL2Term_norm_sq_le (τN : ℕ → FiniteMeasure ℝ) (n : ℕ) :
    ‖shellL2Term τN n‖^2 ≤ (2*Real.pi)⁻¹ * shellEnergy (τN (n+1)) (n+1) := by
  rw [shellL2Term, ← integral_sq_norm_toLp]
  exact (shellKernelMeasureConvolution_L2 (τN (n+1)) n).2

 theorem shellL2Term_norm_summable (τN : ℕ → FiniteMeasure ℝ)
    {γ C : ℝ} (hγ : 0 < γ) (hC : 0 < C) (N₀ : ℕ)
    (hb : ∀ N ≥ N₀, shellEnergy (τN N) N ≤ C*(2:ℝ)^(-γ*(N:ℝ))) :
    Summable (fun n => ‖shellL2Term τN n‖) := by
  have hs := (summable_dyadic_decay (half_pos hγ)).mul_left (Real.sqrt ((2*Real.pi)⁻¹*C))
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N₀] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ (2*Real.pi)⁻¹ * shellEnergy (τN (n+1)) (n+1) := shellL2Term_norm_sq_le τN n
    _ ≤ (2*Real.pi)⁻¹ * (C*(2:ℝ)^(-γ*((n+1:ℕ):ℝ))) :=
      mul_le_mul_of_nonneg_left (hb _ (by omega)) (by positivity)
    _ ≤ (2*Real.pi)⁻¹ * (C*(2:ℝ)^(-γ*(n:ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      nlinarith
    _ = (Real.sqrt ((2*Real.pi)⁻¹*C) * (2:ℝ)^(-(γ/2)*(n:ℝ)))^2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (by norm_num)]
      rw [← mul_assoc]
      congr 2
      push_cast
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ShellErrorSummability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped ENNReal Topology

 theorem shellL1Error_norm_le (τ : FiniteMeasure ℝ) (τN : ℕ → FiniteMeasure ℝ) (n : ℕ) :
    ‖shellL1Error τ τN n‖ ≤ (variationDistance τ (τN (n+1))).toReal *
      ∫ x, ‖sourceShellKernel 0 x‖ := by
  have hi := (shellKernelMeasureConvolution_sub_L1 τ (τN (n+1)) n).1
  rw [shellL1Error, Lp.norm_toLp, eLpNorm_one_eq_lintegral_enorm,
    ← integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable]
  exact (shellKernelMeasureConvolution_sub_L1 τ (τN (n+1)) n).2

 theorem shellL1Error_norm_summable (τ : FiniteMeasure ℝ) (τN : ℕ → FiniteMeasure ℝ)
    {η C : ℝ} (hη : 0 < η) (hC : 0 < C) (N₀ : ℕ)
    (hb : ∀ N ≥ N₀, variationDistance τ (τN N) ≤ ENNReal.ofReal (C*(2:ℝ)^(-η*(N:ℝ)))) :
    Summable (fun n => ‖shellL1Error τ τN n‖) := by
  let K := ∫ x, ‖sourceShellKernel 0 x‖
  have hK : 0 ≤ K := integral_nonneg (fun x => norm_nonneg _)
  have hs := (summable_dyadic_decay hη).mul_left (C*K)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N₀] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  calc
    _ ≤ (variationDistance τ (τN (n+1))).toReal * K := shellL1Error_norm_le τ τN n
    _ ≤ (C*(2:ℝ)^(-η*((n+1:ℕ):ℝ))) * K := by
      apply mul_le_mul_of_nonneg_right _ hK
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb (n+1) (by omega))
      rw [ENNReal.toReal_ofReal (show 0 ≤ C*(2:ℝ)^(-η*((n+1:ℕ):ℝ)) by positivity)] at h
      exact h
    _ ≤ (C*(2:ℝ)^(-η*(n:ℝ))) * K := by
      apply mul_le_mul_of_nonneg_right _ hK
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      nlinarith
    _ = _ := by ring

 theorem shell_approximations_summable (τ : FiniteMeasure ℝ) (hτ : HasShellApproximations τ) :
    ∃ τN : ℕ → FiniteMeasure ℝ,
      Summable (fun n => ‖shellL2Term τN n‖) ∧
      Summable (fun n => ‖shellL1Error τ τN n‖) ∧
      Summable (shellL2Term τN) ∧ Summable (shellL1Error τ τN) := by
  obtain ⟨τN,η,γ,Ctv,Cshell,hη,hγ,hCtv,hCshell,N₀,hb⟩ := hτ
  have h2 := shellL2Term_norm_summable τN hγ hCshell N₀ (fun N hN => (hb N hN).2)
  have h1 := shellL1Error_norm_summable τ τN hη hCtv N₀ (fun N hN => (hb N hN).1)
  exact ⟨τN,h2,h1,h2.of_norm,h1.of_norm⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SchwartzLpTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology ENNReal

 theorem schwartzLpTest_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : 𝓢(ℝ, ℂ))
    (f : Lp (α := ℝ) ℂ p volume) : schwartzLpTest p φ f = ∫ x, φ x * f x := by
  exact Lp.toTemperedDistribution_apply f φ

 theorem schwartzLpTest_toLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : 𝓢(ℝ, ℂ))
    (f : ℝ → ℂ) (hf : MemLp f p volume) :
    schwartzLpTest p φ (hf.toLp f) = ∫ x, φ x * f x := by
  rw [schwartzLpTest_apply]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

 theorem schwartzLpTest_sum_tendsto (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : 𝓢(ℝ, ℂ))
    (f : ℕ → Lp (α := ℝ) ℂ p volume) (hf : Summable f) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, schwartzLpTest p φ (f n)) atTop
      (𝓝 (schwartzLpTest p φ (∑' n, f n))) := by
  simpa only [Function.comp_def, map_sum] using
    ((schwartzLpTest p φ).continuous.tendsto (∑' n, f n)).comp hf.tendsto_sum_tsum_nat

 theorem schwartzLpTest_shell_recombine (τ : FiniteMeasure ℝ) (τN : ℕ → FiniteMeasure ℝ)
    (φ : 𝓢(ℝ, ℂ)) (n : ℕ) :
    schwartzLpTest 1 φ (shellL1Error τ τN n) + schwartzLpTest 2 φ (shellL2Term τN n) =
      ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel n) τ x := by
  rw [shellL1Error, shellL2Term, schwartzLpTest_toLp, schwartzLpTest_toLp]
  have ht : Integrable (fun x => φ x * kernelMeasureConvolution (sourceShellKernel n) τ x) :=
    (φ.memLp_top volume).integrable_mul
      (memLp_one_iff_integrable.mpr (shellKernelMeasureConvolution_L1 τ n).1)
  have hn : Integrable (fun x => φ x *
      kernelMeasureConvolution (sourceShellKernel n) (τN (n+1)) x) :=
    (φ.memLp_top volume).integrable_mul
      (memLp_one_iff_integrable.mpr (shellKernelMeasureConvolution_L1 (τN (n+1)) n).1)
  simp_rw [mul_sub]
  rw [integral_sub ht hn, sub_add_cancel]

 theorem schwartzLpTest_low (τ : FiniteMeasure ℝ) (φ : 𝓢(ℝ, ℂ)) :
    schwartzLpTest 1 φ (sourceLowTerm τ) =
      (2*Real.pi)⁻¹ • ∫ r, sourceShellLowpass 0 r •
        (charFun (τ : Measure ℝ) r * 𝓕 φ (r/(2*Real.pi))) := by
  rw [sourceLowTerm, schwartzLpTest_toLp]
  simpa only [sourceLowKernel, sourceLowpassSchwartz_apply, Complex.real_smul] using
    schwartzKernelMeasureConvolution_test sourceLowpassSchwartz τ φ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ParentConeGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem DyadicSquare.dist_center_le_three_quarters (Q : DyadicSquare)
    (hQ : 0 ≤ Q.side) {x : Plane} (hx : x ∈ Q.carrier) :
    dist x Q.center ≤ 3/4*Q.side := by
  have h0 : |x 0 - Q.center 0| ≤ Q.side/2 := by
    simp only [DyadicSquare.center, WithLp.ofLp_toLp, Matrix.cons_val_zero]
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2.1]
  have h1 : |x 1 - Q.center 1| ≤ Q.side/2 := by
    simp only [DyadicSquare.center, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]
    apply abs_le.mpr
    constructor <;> linarith [hx.2.2.1, hx.2.2.2]
  have hs := EuclideanSpace.dist_sq_eq x Q.center
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at hs
  have hs0 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Q.side/2)).mpr h0
  have hs1 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Q.side/2)).mpr h1
  rw [sq_abs] at hs0 hs1
  nlinarith [sq_nonneg Q.side, dist_nonneg (x := x) (y := Q.center)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_RootSimilarityMeasures
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem distanceSet_dilate (E : Set Plane) {s : ℝ} (hs : 0 < s) :
    distanceSet ((fun x : Plane => s • x) '' E) = (fun r : ℝ => s*r) '' distanceSet E := by
  ext r
  constructor
  · rintro ⟨x,⟨a,ha,rfl⟩,y,⟨b,hb,rfl⟩,hr⟩
    refine ⟨dist a b,⟨a,ha,b,hb,rfl⟩,?_⟩
    simpa only [dist_smul₀,Real.norm_eq_abs,abs_of_pos hs] using hr
  · rintro ⟨t,⟨x,hx,y,hy,rfl⟩,rfl⟩
    exact ⟨s • x,⟨x,hx,rfl⟩,s • y,⟨y,hy,rfl⟩,by simp [dist_smul₀,abs_of_pos hs]⟩

theorem distanceSet_positive_of_dilate (E : Set Plane) {s : ℝ} (hs : 0 < s)
    (hpos : 0 < volume (distanceSet ((fun x : Plane => s • x) '' E))) :
    0 < volume (distanceSet E) := by
  rw [distanceSet_dilate E hs] at hpos
  have he : (fun r : ℝ => s*r) '' distanceSet E = (fun r : ℝ => s⁻¹*r) ⁻¹' distanceSet E := by
    ext r
    constructor
    · rintro ⟨t,ht,rfl⟩
      simpa only [mem_preimage,inv_mul_cancel_left₀ hs.ne'] using ht
    · intro hr
      exact ⟨s⁻¹*r,hr,mul_inv_cancel_left₀ hs.ne' r⟩
  rw [he,Real.volume_preimage_mul_left (inv_ne_zero hs.ne')] at hpos
  exact (ENNReal.mul_pos_iff.mp hpos).2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_DistanceMeasure
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem weightedDistance_mass (π : Measure (Plane × Plane)) :
    weightedDistance π univ = ∫⁻ z, distanceWeight z ∂π := by
  rw [weightedDistance, Measure.map_apply (continuous_fst.dist continuous_snd).measurable
    MeasurableSet.univ, Set.preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

theorem weightedDistance_mass_bounds (π : Measure (Plane × Plane)) [IsProbabilityMeasure π]
    {dmin dmax : ℝ} (hmin : 0 < dmin)
    (hsep : ∀ᵐ z ∂π, dmin ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ dmax) :
    ENNReal.ofReal (dmax ^ (-1/2 : ℝ)) ≤ weightedDistance π univ ∧
      weightedDistance π univ ≤ ENNReal.ofReal (dmin ^ (-1/2 : ℝ)) := by
  rw [weightedDistance_mass]
  constructor
  · calc
      ENNReal.ofReal (dmax ^ (-1/2 : ℝ)) = ∫⁻ _ : Plane × Plane,
        ENNReal.ofReal (dmax ^ (-1/2 : ℝ)) ∂π := by simp
      _ ≤ ∫⁻ z, distanceWeight z ∂π := by
        apply lintegral_mono_ae
        filter_upwards [hsep] with z hz
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow_of_nonpos (hmin.trans_le hz.1) hz.2 (by norm_num)
  · calc
      (∫⁻ z, distanceWeight z ∂π) ≤ ∫⁻ _ : Plane × Plane,
          ENNReal.ofReal (dmin ^ (-1/2 : ℝ)) ∂π := by
        apply lintegral_mono_ae
        filter_upwards [hsep] with z hz
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow_of_nonpos hmin hz.1 (by norm_num)
      _ = ENNReal.ofReal (dmin ^ (-1/2 : ℝ)) := by simp

theorem weightedDistance_positive_finite (π : Measure (Plane × Plane)) [IsProbabilityMeasure π]
    {dmin dmax : ℝ} (hmin : 0 < dmin) (hmax : 0 < dmax)
    (hsep : ∀ᵐ z ∂π, dmin ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ dmax) :
    0 < weightedDistance π univ ∧ weightedDistance π univ < ∞ := by
  obtain ⟨hl,hu⟩ := weightedDistance_mass_bounds π hmin hsep
  exact ⟨(ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hmax _)).trans_le hl,
    hu.trans_lt ENNReal.ofReal_lt_top⟩

theorem weightedDistance_carried (π : Measure (Plane × Plane))
    {E : Set Plane} (hE : IsCompact E) (hcarrier : π (E ×ˢ E)ᶜ = 0) :
    weightedDistance π (distanceSet E)ᶜ = 0 := by
  rw [weightedDistance, Measure.map_apply (continuous_fst.dist continuous_snd).measurable
    (distanceSet_measurable hE).compl]
  apply withDensity_absolutelyContinuous π distanceWeight
  apply measure_mono_null _ hcarrier
  intro z hz hzin
  exact hz ⟨z.1,hzin.1,z.2,hzin.2,rfl⟩

theorem product_carried (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set Plane) (hμ : μ Eᶜ = 0) (hν : ν Eᶜ = 0) :
    (μ.prod ν) (E ×ˢ E)ᶜ = 0 := by
  have hleft : (μ.prod ν) (Eᶜ ×ˢ (univ : Set Plane)) = 0 := by simp [Measure.prod_prod,hμ]
  have hright : (μ.prod ν) ((univ : Set Plane) ×ˢ Eᶜ) = 0 := by simp [Measure.prod_prod,hν]
  apply measure_mono_null _ (measure_union_null hleft hright)
  intro z hz
  by_cases hx : z.1 ∈ E
  · right
    refine ⟨Set.mem_univ _, ?_⟩
    intro hy
    exact hz ⟨hx,hy⟩
  · left
    exact ⟨hx,Set.mem_univ _⟩

theorem positive_distance_volume_of_weighted_ac (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set Plane} (hE : IsCompact E) (hμ : μ Eᶜ = 0) (hν : ν Eᶜ = 0)
    {dmin dmax : ℝ} (hmin : 0 < dmin) (hmax : 0 < dmax)
    (hsep : ∀ᵐ z ∂(μ.prod ν), dmin ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ dmax)
    (hac : weightedDistance (μ.prod ν) ≪ volume) : 0 < volume (distanceSet E) := by
  exact distanceSet_positive_of_measure E (weightedDistance (μ.prod ν))
    (weightedDistance_positive_finite (μ.prod ν) hmin hmax hsep).1
    (weightedDistance_carried (μ.prod ν) hE (product_carried μ ν E hμ hν)) hac

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_NormalizedOuterShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal

theorem separated_unit_roots_distance (Q : Fin 2 → DyadicSquare)
    (hQ : ∀ l, (Q l).side = 1)
    (hlo : 100 ≤ dist (Q 0).center (Q 1).center)
    (hhi : dist (Q 0).center (Q 1).center ≤ 2000)
    (x y : Plane) (hx : x ∈ (Q 0).carrier) (hy : y ∈ (Q 1).carrier) :
    90 ≤ dist x y ∧ dist x y ≤ 2010 := by
  have hx' := (Q 0).dist_center_le_three_quarters (by rw [hQ 0]; norm_num) hx
  have hy' := (Q 1).dist_center_le_three_quarters (by rw [hQ 1]; norm_num) hy
  rw [hQ 0] at hx'
  rw [hQ 1] at hy'
  have hl := dist_triangle4 (Q 0).center x y (Q 1).center
  have hu := dist_triangle4 x (Q 0).center (Q 1).center y
  rw [dist_comm (Q 0).center x] at hl
  rw [dist_comm (Q 1).center y] at hu
  constructor <;> linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_DistributionAbsoluteContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped ENNReal

 theorem locallyIntegrable_rnDeriv_smul (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    (hac : μ ≪ ν) (f : ℝ → ℂ) (hf : LocallyIntegrable f μ) :
    LocallyIntegrable (fun x => (μ.rnDeriv ν x).toReal • f x) ν := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hi := (integrable_rnDeriv_smul_iff hac).mpr
    ((hf.integrableOn_isCompact hK).integrable_indicator hK.measurableSet)
  apply (integrable_indicator_iff hK.measurableSet).mp
  apply hi.congr
  filter_upwards with x
  by_cases hx : x ∈ K <;> simp [hx]

 theorem absolutelyContinuous_of_smooth_test_density (τ : Measure ℝ) [IsFiniteMeasure τ]
    (f : ℝ → ℂ) (hf : LocallyIntegrable f volume)
    (ht : ∀ (g : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      (∫ x, (g x : ℂ) ∂τ) = ∫ x, g x • f x) : τ ≪ volume := by
  let μ : Measure ℝ := τ+volume
  have hτ : τ ≪ μ := Measure.absolutelyContinuous_of_le (by
    apply Measure.le_iff.mpr
    intro s _
    exact le_add_right le_rfl)
  have hv : volume ≪ μ := Measure.absolutelyContinuous_of_le (by
    apply Measure.le_iff.mpr
    intro s _
    exact le_add_left le_rfl)
  let a : ℝ → ℂ := fun x => ((τ.rnDeriv μ x).toReal : ℂ)
  let b : ℝ → ℂ := fun x => (volume.rnDeriv μ x).toReal • f x
  have ha : LocallyIntegrable a μ := by
    simpa only [smul_eq_mul, Complex.real_smul, mul_one] using
      locallyIntegrable_rnDeriv_smul τ μ hτ (fun _ => (1:ℂ))
        (continuous_const.locallyIntegrable)
  have hb : LocallyIntegrable b μ := locallyIntegrable_rnDeriv_smul volume μ hv f hf
  have hab : a =ᵐ[μ] b := by
    apply ae_eq_of_integral_contDiff_smul_eq ha hb
    intro g hg hc
    calc
      _ = ∫ x, (τ.rnDeriv μ x).toReal • (g x : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp [a, Complex.real_smul, mul_comm]
      _ = ∫ x, (g x : ℂ) ∂τ := integral_rnDeriv_smul hτ
      _ = ∫ x, g x • f x := ht g hg hc
      _ = ∫ x, (volume.rnDeriv μ x).toReal • (g x • f x) ∂μ :=
        (integral_rnDeriv_smul hv).symm
      _ = _ := by simp only [b, smul_comm (g _) ((volume.rnDeriv μ _).toReal)]
  intro S hS
  have hS' : ∀ᵐ x ∂volume, x ∉ S := by simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hS
  rw [← Measure.withDensity_rnDeriv_eq volume μ hv] at hS'
  have hz := (ae_withDensity_iff (Measure.measurable_rnDeriv volume μ)).mp hS'
  have hgoal : ∀ᵐ x ∂τ, x ∉ S := by
    rw [← Measure.withDensity_rnDeriv_eq τ μ hτ]
    apply (ae_withDensity_iff (Measure.measurable_rnDeriv τ μ)).mpr
    filter_upwards [hz,hab,Measure.rnDeriv_lt_top τ μ] with x hx he hfin
    intro hax hxS
    have hzero : volume.rnDeriv μ x = 0 := by
      by_contra hn
      exact hx hn hxS
    have hzreal : (τ.rnDeriv μ x).toReal = 0 := by
      have he' : ((τ.rnDeriv μ x).toReal : ℂ) = 0 := by
        simpa only [a,b,hzero,ENNReal.toReal_zero,zero_smul] using he
      exact Complex.ofReal_eq_zero.mp he'
    have heq := ENNReal.ofReal_toReal hfin.ne
    rw [hzreal, ENNReal.ofReal_zero] at heq
    exact hax heq.symm
  simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hgoal

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ShellTestConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology

 theorem sourceShell_spatial_test_tendsto (τ : FiniteMeasure ℝ) (φ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun N => schwartzLpTest 1 φ (sourceLowTerm τ) +
      ∑ n ∈ Finset.range N, ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel n) τ x)
      atTop (𝓝 (∫ x, φ x ∂(τ : Measure ℝ))) := by
  let t : ℝ → ℂ := fun r => charFun (τ : Measure ℝ) r * 𝓕 φ (r/(2*Real.pi))
  have hi0 : Integrable (fun r => sourceShellLowpass 0 r • t r) := by
    simpa only [sourceLowpassSchwartz_apply,Complex.real_smul] using
      schwartz_cutoff_test_integrable sourceLowpassSchwartz φ τ
  have hin (n : ℕ) : Integrable (fun r => sourceShellBand n r • t r) := by
    simpa only [sourceShellSchwartz_apply,Complex.real_smul] using
      schwartz_cutoff_test_integrable (sourceShellSchwartz n) φ τ
  have he (N : ℕ) : schwartzLpTest 1 φ (sourceLowTerm τ) +
      ∑ n ∈ Finset.range N, ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel n) τ x =
      (2*Real.pi)⁻¹ • ∫ r, (sourceShellLowpass 0 r +
        ∑ n ∈ Finset.range N, sourceShellBand n r) • t r := by
    rw [schwartzLpTest_low]
    simp_rw [sourceShellKernel, schwartzKernelMeasureConvolution_test,
      sourceShellSchwartz_apply, ← Complex.real_smul]
    rw [← Finset.smul_sum, ← smul_add]
    congr 1
    simp_rw [add_smul, Finset.sum_smul]
    rw [integral_add hi0 (integrable_finsetSum _ (fun n _ => hin n)),
      integral_finsetSum _ (fun n _ => hin n)]
  simp_rw [he]
  have h := (sourceShellPartition_fourier_test (τ : Measure ℝ)
    (fun r => 𝓕 φ (r/(2*Real.pi))) ((𝓕 φ).integrable.comp_div (by positivity))).const_smul
    ((2*Real.pi)⁻¹)
  rw [source_characteristic_schwartz_test] at h
  exact h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ShellReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology

 theorem shell_reconstruction_test_density (τ : FiniteMeasure ℝ) (hτ : HasShellApproximations τ) :
    ∃ a : Lp (α := ℝ) ℂ 1 volume, ∃ b : Lp (α := ℝ) ℂ 2 volume,
      ∀ φ : 𝓢(ℝ, ℂ), (∫ x, φ x * (a x+b x)) = ∫ x, φ x ∂(τ : Measure ℝ) := by
  obtain ⟨τN,_,_,h2,h1⟩ := shell_approximations_summable τ hτ
  let a : Lp (α := ℝ) ℂ 1 volume := sourceLowTerm τ + ∑' n, shellL1Error τ τN n
  let b : Lp (α := ℝ) ℂ 2 volume := ∑' n, shellL2Term τN n
  refine ⟨a,b,?_⟩
  intro φ
  have hlim := ((schwartzLpTest_sum_tendsto 1 φ _ h1).const_add
    (schwartzLpTest 1 φ (sourceLowTerm τ))).add (schwartzLpTest_sum_tendsto 2 φ _ h2)
  have he (N : ℕ) : (schwartzLpTest 1 φ (sourceLowTerm τ) +
      ∑ n ∈ Finset.range N, schwartzLpTest 1 φ (shellL1Error τ τN n)) +
      ∑ n ∈ Finset.range N, schwartzLpTest 2 φ (shellL2Term τN n) =
      schwartzLpTest 1 φ (sourceLowTerm τ) +
      ∑ n ∈ Finset.range N, ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel n) τ x := by
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    exact schwartzLpTest_shell_recombine τ τN φ n
  simp_rw [he] at hlim
  have hval : schwartzLpTest 1 φ a + schwartzLpTest 2 φ b =
      ∫ x, φ x ∂(τ : Measure ℝ) := by
    have hu := tendsto_nhds_unique hlim (sourceShell_spatial_test_tendsto τ φ)
    simpa only [a,b,map_add] using hu
  have ha := (φ.memLp_top volume).integrable_mul (Lp.memLp a)
  have hb := (φ.memLp 2 volume).integrable_mul (Lp.memLp b)
  change Integrable (fun x => φ x * a x) at ha
  change Integrable (fun x => φ x * b x) at hb
  rw [← hval, schwartzLpTest_apply, schwartzLpTest_apply]
  simp_rw [mul_add]
  exact integral_add ha hb

 theorem shell_reconstruction_locallyIntegrable (τ : FiniteMeasure ℝ)
    (hτ : HasShellApproximations τ) :
    ∃ f : ℝ → ℂ, LocallyIntegrable f volume ∧
      ∀ (g : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        (∫ x, (g x : ℂ) ∂(τ : Measure ℝ)) = ∫ x, g x • f x := by
  obtain ⟨a,b,ht⟩ := shell_reconstruction_test_density τ hτ
  refine ⟨fun x => a x+b x,
    ((Lp.memLp a).locallyIntegrable (by norm_num)).add
      ((Lp.memLp b).locallyIntegrable (by norm_num)), ?_⟩
  intro g hg hc
  let φ : 𝓢(ℝ, ℂ) := (hc.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hg)
  exact (ht φ).symm

 theorem shell_criterion (τ : FiniteMeasure ℝ) (hτ : HasShellApproximations τ) :
    (τ : Measure ℝ) ≪ volume := by
  obtain ⟨f,hf,ht⟩ := shell_reconstruction_locallyIntegrable τ hτ
  exact absolutelyContinuous_of_smooth_test_density τ f hf ht

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem manuscript_main (E : Set Plane) (hE : IsCompact E) (hd : 1 < dimH E) :
    0 < volume (distanceSet E) := by
  obtain ⟨δ,s,hδ,hδ1,hs,Q,hQ,hcent,μ,ν,_,_,hμE,hνE,_,_,hμQ,hνQ,
    C,hC,hball₀,hball₁,K,hK,hμrad,hνrad⟩ := exists_normalized_root_setup E hE hd
  obtain ⟨β,lam,sig,kap,hβ,hlam,hlamδ,hsig,hkap,hkapβ,hgap,hratio⟩ :=
    exists_source_assembly_parameters hδ hδ1
  obtain ⟨Ψ,hΨ,hpos,hsupp,hone⟩ := exists_assembly_shell_cutoff
  have hp1 : 1 < 1+δ/8 := by linarith
  have hpq : (1+δ/8).HolderConjugate ((1+δ/8)/((1+δ/8)-1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp1).mpr rfl
  have hμrad' : ∀ᵐ x ∂(μ:Measure Plane),
      sourceDensityNorm (1+δ/8) ((ν:Measure Plane).map (sourceRadialUnit x)) ≤ K := by
    filter_upwards [(μ:Measure Plane).support_mem_ae] with x hx
    exact hμrad x hx
  have hνrad' : ∀ᵐ y ∂(ν:Measure Plane),
      sourceDensityNorm (1+δ/8) ((μ:Measure Plane).map (sourceRadialUnit y)) ≤ K := by
    filter_upwards [(ν:Measure Plane).support_mem_ae] with y hy
    exact hνrad y hy
  have hlo : 100 ≤ dist (Q 0).center (Q 1).center := by rw [hcent]; norm_num
  have hhi : dist (Q 0).center (Q 1).center ≤ 2000 := by rw [hcent]; norm_num
  obtain ⟨hτ,happrox⟩ := two_root_has_shell_approximations Q hQ hlo hhi μ ν hμQ hνQ
    hδ hδ1 hβ hlam hlamδ hsig hkap hkapβ hgap hratio hC.le hC.le hball₀ hball₁
    hpq hK hμrad' hνrad' hΨ hpos hsupp hone
  have hac := shell_criterion ⟨weightedDistance ((μ:Measure Plane).prod ν),hτ⟩ happrox
  have hsep : ∀ᵐ z ∂(μ:Measure Plane).prod (ν:Measure Plane),
      90 ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ 2010 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hμQ,
      Measure.quasiMeasurePreserving_snd.ae hνQ] with z hx hy
    exact separated_unit_roots_distance Q hQ hlo hhi z.1 z.2 hx hy
  have hcompact : IsCompact ((fun x : Plane => s • x) '' E) := hE.image (by fun_prop)
  have hcarry₀ : (μ:Measure Plane) ((fun x : Plane => s • x) '' E)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hμE) (μ:Measure Plane).support_mem_ae
  have hcarry₁ : (ν:Measure Plane) ((fun x : Plane => s • x) '' E)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hνE) (ν:Measure Plane).support_mem_ae
  apply distanceSet_positive_of_dilate E hs
  exact positive_distance_volume_of_weighted_ac (μ:Measure Plane) (ν:Measure Plane)
    hcompact hcarry₀ hcarry₁ (by norm_num : (0:ℝ) < 90) (by norm_num : (0:ℝ) < 2010) hsep hac

theorem mainTarget_proved_oai : MainTarget := manuscript_main

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.mainTarget_proved_oai := @OAI.PlanarFalconer.mainTarget_proved_oai
