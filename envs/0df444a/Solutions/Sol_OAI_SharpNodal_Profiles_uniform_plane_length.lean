-- Prove2me | solution 1 for OAI.SharpNodal.Profiles.uniform_plane_length
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:27:05.051956+00:00
-- url     : https://prove2.me/submissions/b7420092-b974-4cd4-9ab1-03d2c4a10e1f

import Mathlib
import Definitions.Def_NodalLength
import Definitions.Def_OAIQ4Nl000
import Theorems.Thm_OAI_SharpNodal_Grid_uniform_terminal_growth
import Theorems.Thm_OAI_SharpNodal_Profiles_normalized_small_potential_length

section
-- module Solutions.OAIQ4_Nl.NodalLength_Integration
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

lemma integrable_mul_compact_right {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport g) : Integrable (fun x => f x * g x) := by
  exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left

lemma integral_mul_partial {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport g) (i : Fin 2) :
    (∫ x, f x * coordPartial g i x) = -(∫ x, coordPartial f i x * g x) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_mul_compact_right (smooth_partial hf i) hg hc
  · exact integrable_mul_compact_right hf (smooth_partial hg i) (compact_partial hc i)
  · exact integrable_mul_compact_right hf hg hc
  · intro x _
    exact (hf.differentiable (by simp)).differentiableAt
  · intro x _
    exact (hg.differentiable (by simp)).differentiableAt


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Carleman
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

lemma partial_neg {f : Plane → ℝ} (hf : Smooth f) (i : Fin 2) (x : Plane) :
    coordPartial (fun y => -f y) i x = -coordPartial f i x := by
  simpa only [neg_one_mul] using partial_const_mul hf (-1) i x


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_ProfileTests
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set

noncomputable section
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set

noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma hessian_on_basis {f : Plane → ℝ} (hf : Smooth f) (x₀ : Plane) (i j : Fin 2) :
    fderiv ℝ (fderiv ℝ f) x₀ (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)=
      coordPartial (coordPartial f i) j x₀ := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by simp : (∞:ℕ∞ω)+1≤(∞:ℕ∞ω))).differentiable (by simp)
  unfold coordPartial
  rw [fderiv_clm_apply hdf.differentiableAt (differentiableAt_const _)]
  simp

end SharpNodal.Profiles
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Subharmonic
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
namespace SharpNodal.Profiles
open Carleman InnerProductSpace

lemma plane_laplacian_eq_mathlib {f : Plane → ℝ} (hf : Smooth f) :
    euclideanLaplacian f = Δ f := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 2) ℝ)]
  ext x
  apply Finset.sum_congr rfl
  intro i _
  simp only [EuclideanSpace.basisFun_apply,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  exact (hessian_on_basis hf x i i).symm

lemma laplacian_comp_isometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {f : F → ℝ} (hf : ContDiff ℝ ∞ f) :
    Δ (f∘e) = (Δ f)∘e := by
  let b := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (f∘e) b,
    laplacian_eq_iteratedFDeriv_orthonormalBasis f (b.map e)]
  ext x
  apply Finset.sum_congr rfl
  intro i _
  have hh := e.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right
    hf x (i:=2) (WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))
  rw [show (f∘e)=(f∘e.toContinuousLinearEquiv.toContinuousLinearMap) from rfl,hh]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    OrthonormalBasis.map_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]
  congr 1
  ext k
  fin_cases k <;> rfl

end SharpNodal.Profiles
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Potential
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory

namespace SharpNodal.Profiles
open Carleman

lemma logDenom_pos {ε : ℝ} (hε : 0<ε) (x : Plane) : 0<logDenom ε x := by
  dsimp [logDenom]
  positivity

lemma smooth_logDenom (ε : ℝ) : Smooth (logDenom ε) := by
  exact (contDiff_id.norm_sq (𝕜:=ℝ)).add contDiff_const

lemma partial_logDenom (ε : ℝ) (i : Fin 2) (x : Plane) :
    coordPartial (logDenom ε) i x=2*x i := by
  have hd := ((hasFDerivAt_id (𝕜:=ℝ) x).norm_sq).add_const (ε^2)
  dsimp only [id_eq] at hd
  change (fderiv ℝ (fun y : Plane => ‖y‖^2+ε^2) x) (EuclideanSpace.single i 1)=_
  rw [hd.fderiv]
  simp [EuclideanSpace.inner_single_right]

lemma smooth_regularizedLog {ε : ℝ} (hε : 0<ε) : Smooth (regularizedLog ε) := by
  exact ((smooth_logDenom ε).log (fun x => (logDenom_pos hε x).ne')).div_const 2

lemma partial_regularizedLog {ε : ℝ} (hε : 0<ε) (i : Fin 2) (x : Plane) :
    coordPartial (regularizedLog ε) i x=x i/(logDenom ε x) := by
  have hd := (((smooth_logDenom ε).differentiable (by simp)).differentiableAt.hasFDerivAt.log
    (logDenom_pos hε x).ne').const_mul (1/2:ℝ)
  have he : regularizedLog ε=(fun y => (1/2:ℝ)*Real.log (logDenom ε y)) := by
    funext y; simp [regularizedLog,logDenom,div_eq_mul_inv,mul_comm]
  rw [he,coordPartial,hd.fderiv]
  simp only [smul_apply,smul_eq_mul]
  change (1/2:ℝ)*((logDenom ε x)⁻¹*coordPartial (logDenom ε) i x)=_
  rw [partial_logDenom]
  ring

lemma partial2_regularizedLog {ε : ℝ} (hε : 0<ε) (i : Fin 2) (x : Plane) :
    coordPartial (coordPartial (regularizedLog ε) i) i x=
      (logDenom ε x)⁻¹-2*(x i)^2/(logDenom ε x)^2 := by
  have hD := ((smooth_logDenom ε).differentiable (by simp)).differentiableAt.hasFDerivAt (x:=x)
  have hinv := (hasDerivAt_inv (logDenom_pos hε x).ne').comp_hasFDerivAt x hD
  have hmul := (EuclideanSpace.proj i).hasFDerivAt.mul hinv
  rw [show coordPartial (regularizedLog ε) i=(fun y => y i*(logDenom ε y)⁻¹) from by
    funext y; rw [partial_regularizedLog hε]; rfl]
  change (fderiv ℝ _ x) (EuclideanSpace.single i 1)=_
  change HasFDerivAt (fun y : Plane => y i*(logDenom ε y)⁻¹) _ x at hmul
  rw [hmul.fderiv]
  change x i*(-((logDenom ε x)^2)⁻¹*coordPartial (logDenom ε) i x)+
    (logDenom ε x)⁻¹*(EuclideanSpace.single i 1) i=_
  rw [show (EuclideanSpace.single i (1:ℝ)) i=1 by simp,mul_one]
  rw [partial_logDenom]
  ring

lemma laplacian_regularizedLog {ε : ℝ} (hε : 0<ε) (x : Plane) :
    euclideanLaplacian (regularizedLog ε) x=2*ε^2/(‖x‖^2+ε^2)^2 := by
  simp only [euclideanLaplacian,partial2_regularizedLog hε,Fin.sum_univ_two]
  have hn : ‖x‖^2=(x 0)^2+(x 1)^2 := by
    simpa only [Fin.sum_univ_two,Real.norm_eq_abs,sq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) x
  dsimp [logDenom]
  have hd : ‖x‖^2+ε^2≠0 := (logDenom_pos hε x).ne'
  field_simp
  nlinarith

lemma integral_mul_laplacian {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport g) :
    (∫x,f x*euclideanLaplacian g x)=(∫x,euclideanLaplacian f x*g x) := by
  simp only [euclideanLaplacian,Finset.mul_sum,Finset.sum_mul]
  rw [integral_finsetSum,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_mul_partial hf (smooth_partial hg i) (compact_partial hc i),
      integral_mul_partial (smooth_partial hf i) hg hc,neg_neg]
  · intro i _
    exact integrable_mul_compact_right (smooth_partial (smooth_partial hf i) i) hg hc
  · intro i _
    exact integrable_mul_compact_right hf (smooth_partial (smooth_partial hg i) i)
      (compact_partial (compact_partial hc i) i)

lemma regularizedLog_distribution {ε : ℝ} (hε : 0<ε) {ψ : Plane → ℝ}
    (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ) :
    (∫x,regularizedLog ε x*euclideanLaplacian ψ x)=
      ∫x,(2*ε^2/(‖x‖^2+ε^2)^2)*ψ x := by
  rw [integral_mul_laplacian (smooth_regularizedLog hε) hψ hcψ]
  simp only [laplacian_regularizedLog hε]

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma plane_radial_ball_integral (f : ℝ → ℝ) (R : ℝ) :
    (∫x in Metric.ball (0:Plane) R,f ‖x‖)=2*Real.pi*∫r in Ioo 0 R,r*f r := by
  have he : (Metric.ball (0:Plane) R).indicator (fun x => f ‖x‖)=
       (fun x => (Iio R).indicator f ‖x‖) := by
    funext x
    simp [indicator,Metric.mem_ball,dist_zero_right]
  rw [← integral_indicator measurableSet_ball,he,integral_fun_norm_addHaar]
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one,smul_eq_mul,
    nsmul_eq_mul]
  have hv : (volume : Measure Plane).real (Metric.ball 0 1)=Real.pi := by
    rw [measureReal_def,EuclideanSpace.volume_ball_fin_two]
    norm_num
    exact Real.pi_pos.le
  rw [hv]
  have he' : (fun r : ℝ => r*(Iio R).indicator f r)=
      (Iio R).indicator (fun r => r*f r) := by
    funext r
    by_cases hr : r<R <;> simp [hr]
  rw [he',integral_indicator measurableSet_Iio]
  have hs : Iio R∩Ioi (0:ℝ)=Ioo 0 R := by ext r; exact and_comm
  rw [Measure.restrict_restrict measurableSet_Iio,hs]
  ring

lemma log_norm_integrableOn_ball (R : ℝ) :
    IntegrableOn (fun x : Plane => Real.log ‖x‖) (Metric.ball 0 R) := by
  rw [integrableOn_fun_norm_addHaar]
  simp only [finrank_euclideanSpace_fin,Nat.reduceSub,pow_one,smul_eq_mul]
  by_cases hR : 0≤R
  · have hi : IntervalIntegrable (fun r : ℝ => r*Real.log r) volume 0 R :=
      intervalIntegral.intervalIntegrable_log'.continuousOn_mul continuous_id.continuousOn
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp hi).mono_set Ioo_subset_Ioc_self
  · have he : Ioo (0:ℝ) R=∅ := Ioo_eq_empty_of_le (le_of_not_ge hR)
    simp [he]

lemma regularizedLog_radial_mass {ε R : ℝ} (hε : 0<ε) (hR : 0≤R) :
    (∫x in Metric.ball (0:Plane) R,2*ε^2/(‖x‖^2+ε^2)^2)=
      2*Real.pi*(R^2/(R^2+ε^2)) := by
  rw [plane_radial_ball_integral (fun r => 2*ε^2/(r^2+ε^2)^2) R]
  congr 1
  have hd : ∀r : ℝ,HasDerivAt (fun r : ℝ => r^2/(r^2+ε^2))
      (r*(2*ε^2/(r^2+ε^2)^2)) r := by
    intro r
    have hden : r^2+ε^2≠0 := ne_of_gt (by positivity)
    convert! ((hasDerivAt_id r).pow 2).div (((hasDerivAt_id r).pow 2).add_const (ε^2)) hden using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,mul_one]
    field_simp
    ring
  have hc : Continuous (fun r : ℝ => r*(2*ε^2/(r^2+ε^2)^2)) := by
    fun_prop (disch := intro r; positivity)
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hR,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) (hc.intervalIntegrable 0 R)]
  simp

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma logKernel_nonneg (ε : ℝ) (x : Plane) : 0≤logKernel ε x := by
  unfold logKernel
  positivity

lemma logKernel_eq (ε : ℝ) (x : Plane) :
    logKernel ε x=(2*Real.pi)⁻¹*(2*ε^2/(‖x‖^2+ε^2)^2) := by
  unfold logKernel
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma continuous_logKernel {ε : ℝ} (hε : 0<ε) : Continuous (logKernel ε) := by
  unfold logKernel
  fun_prop (disch := intro x; positivity)

lemma logKernel_uniform_away (u : Set Plane) (hu : IsOpen u) (h0 : (0:Plane)∈u) :
    TendstoUniformlyOn logKernel 0 (𝓝[>]0) (univ\u) := by
  obtain ⟨δ,hδ,hδu⟩ := Metric.mem_nhds_iff.mp (hu.mem_nhds h0)
  have hb (ε : ℝ) (x : Plane) (hx : x∈univ\u) :
      logKernel ε x≤ε^2/(Real.pi*δ^4) := by
    have hxδ : δ≤‖x‖ := le_of_not_gt (fun hh => hx.2 (hδu (by simpa [Metric.mem_ball,dist_zero_right] using hh)))
    unfold logKernel
    apply div_le_div_of_nonneg_left (sq_nonneg ε) (by positivity)
    have hs : δ^2≤‖x‖^2+ε^2 := by nlinarith [sq_nonneg ε]
    have hs' : δ^4≤(‖x‖^2+ε^2)^2 := by nlinarith [sq_nonneg (‖x‖^2+ε^2-δ^2)]
    exact mul_le_mul_of_nonneg_left hs' Real.pi_pos.le
  have ht : Tendsto (fun ε : ℝ => ε^2/(Real.pi*δ^4)) (𝓝[>]0) (𝓝 0) := by
    have hh : Tendsto (fun ε : ℝ => ε^2/(Real.pi*δ^4)) (𝓝 0) (𝓝 (0^2/(Real.pi*δ^4))) :=
      (tendsto_id.pow 2).div_const _
    simpa using hh.mono_left nhdsWithin_le_nhds
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [(tendsto_order.mp ht).2 η hη] with ε hε
  intro x hx
  simpa only [Pi.zero_apply,dist_zero_left,Real.norm_of_nonneg (logKernel_nonneg ε x)] using (hb ε x hx).trans_lt hε

lemma logKernel_mass_tendsto :
    Tendsto (fun ε : ℝ => ∫x in Metric.ball (0:Plane) 1,logKernel ε x) (𝓝[>]0) (𝓝 1) := by
  have he : (fun ε : ℝ => ∫x in Metric.ball (0:Plane) 1,logKernel ε x)=ᶠ[𝓝[>]0]
      (fun ε => (1+ε^2)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [logKernel_eq,integral_const_mul,regularizedLog_radial_mass hε (by norm_num : (0:ℝ)≤1),one_pow]
    field_simp
  apply Tendsto.congr' he.symm
  have hh : Tendsto (fun ε : ℝ => (1+ε^2)⁻¹) (𝓝 0) (𝓝 ((1+0^2)⁻¹)) := by
    apply Tendsto.inv₀
    · exact tendsto_const_nhds.add (tendsto_id.pow 2)
    · norm_num
  simpa using hh.mono_left nhdsWithin_le_nhds

lemma logKernel_test_tendsto {ψ : Plane → ℝ} (hψ : Continuous ψ) (hiψ : Integrable ψ) :
    Tendsto (fun ε : ℝ => ∫x,logKernel ε x*ψ x) (𝓝[>]0) (𝓝 (ψ 0)) := by
  have ht := tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto (μ:=(volume:Measure Plane)) (g:=ψ) (φ:=logKernel)
    (x₀:=(0:Plane)) (s:=univ) (t:=Metric.ball (0:Plane) 1)
    MeasurableSet.univ measurableSet_ball (subset_univ _) (by simpa using Metric.ball_mem_nhds (0:Plane) (by norm_num : (0:ℝ)<1))
    (measure_ball_lt_top.ne) (Eventually.of_forall (fun _ _ _ => logKernel_nonneg _ _))
    logKernel_uniform_away logKernel_mass_tendsto
    (by filter_upwards [self_mem_nhdsWithin] with ε hε using (continuous_logKernel hε).aestronglyMeasurable)
    (by simpa using hiψ) (by rw [nhdsWithin_univ]; convert! hψ.continuousAt (x:=(0:Plane)))
  simpa only [Measure.restrict_univ,smul_eq_mul] using ht

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma regularizedLog_bound {ε R : ℝ} (hε : 0<ε) (hε1 : ε≤1) (hR : 0<R)
    {x : Plane} (hx : x∈Metric.ball 0 R) (hx0 : x≠0) :
    ‖regularizedLog ε x‖≤‖Real.log ‖x‖‖+‖Real.log (R^2+1)/2‖ := by
  have hxnorm : 0<‖x‖ := norm_pos_iff.mpr hx0
  have hxR : ‖x‖<R := by simpa [Metric.mem_ball,dist_zero_right] using hx
  have hlo : Real.log ‖x‖ ≤ regularizedLog ε x := by
    have hh := Real.log_le_log (sq_pos_of_pos hxnorm) (le_add_of_nonneg_right (sq_nonneg ε))
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    dsimp [regularizedLog]
    linarith
  have hhi : regularizedLog ε x≤Real.log (R^2+1)/2 := by
    have hh : ‖x‖^2+ε^2≤R^2+1 := by nlinarith [norm_nonneg x]
    exact div_le_div_of_nonneg_right (Real.log_le_log (logDenom_pos hε x) hh) (by norm_num)
  simp only [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log ‖x‖),abs_nonneg (Real.log (R^2+1)/2)]
  · linarith [le_abs_self (Real.log (R^2+1)/2),abs_nonneg (Real.log ‖x‖)]

lemma regularizedLog_tendsto {x : Plane} (hx : x≠0) :
    Tendsto (fun ε : ℝ => regularizedLog ε x) (𝓝[>]0) (𝓝 (Real.log ‖x‖)) := by
  have hn : ‖x‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hh : Tendsto (fun ε : ℝ => Real.log (‖x‖^2+ε^2)/2) (𝓝 0)
      (𝓝 (Real.log (‖x‖^2+0^2)/2)) := by
    apply Tendsto.div_const
    apply Real.continuousAt_log (by simpa using hn) |>.tendsto.comp
    exact tendsto_const_nhds.add (tendsto_id.pow 2)
  simpa only [regularizedLog,zero_pow (by decide : (2:ℕ)≠0),add_zero,Real.log_pow,Nat.cast_ofNat,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] using hh.mono_left nhdsWithin_le_nhds

lemma regularizedLog_test_limit {g : Plane → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    Tendsto (fun ε : ℝ => ∫x,regularizedLog ε x*g x) (𝓝[>]0)
      (𝓝 (∫x,Real.log ‖x‖*g x)) := by
  obtain ⟨R,hR,hzero⟩ := hc.exists_pos_le_norm
  obtain ⟨M,hM⟩ := hg.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hgM (x : Plane) : ‖g x‖≤M := hM (mem_range_self x)
  let B := fun x : Plane => (‖Real.log ‖x‖‖+‖Real.log (R^2+1)/2‖)*M
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0:Plane) R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (measure_ball_lt_top (μ:=volume) (x:=(0:Plane)) (r:=R))⟩
  have hiB : IntegrableOn B (Metric.ball 0 R) :=
    ((log_norm_integrableOn_ball R).norm.add (integrable_const _)).mul_const M
  have hne : ∀ᵐx : Plane,x≠0 := by simp [ae_iff]
  have hbound : ∀ᶠε : ℝ in 𝓝[>]0,∀ᵐx ∂volume.restrict (Metric.ball (0:Plane) R),
      ‖regularizedLog ε x*g x‖≤B x := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with ε hε hε1
    filter_upwards [self_mem_ae_restrict measurableSet_ball,ae_restrict_of_ae hne] with x hx hx0
    rw [norm_mul]
    exact mul_le_mul (regularizedLog_bound hε hε1.le hR hx hx0) (hgM x) (norm_nonneg _) (by positivity)
  have ht := tendsto_integral_filter_of_dominated_convergence B
    (F:=fun ε x => regularizedLog ε x*g x) (f:=fun x => Real.log ‖x‖*g x)
    (by filter_upwards [self_mem_nhdsWithin] with ε hε using
      ((smooth_regularizedLog hε).continuous.mul hg).aestronglyMeasurable)
    hbound hiB
    (by filter_upwards [ae_restrict_of_ae hne] with x hx using (regularizedLog_tendsto hx).mul_const (g x))
  have he (f : Plane → ℝ) : (∫x in Metric.ball (0:Plane) R,f x*g x)=(∫x,f x*g x) := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Metric.ball (0:Plane) R
    · simp [hx]
    · have hz : g x=0 := hzero x (by simpa [Metric.mem_ball,dist_zero_right,not_lt] using hx)
      simp [hx,hz]
  simpa only [he] using ht

lemma logarithmic_fundamental_solution {ψ : Plane → ℝ} (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ) :
    (∫x,Real.log ‖x‖*euclideanLaplacian ψ x)=2*Real.pi*ψ 0 := by
  have hl := regularizedLog_test_limit (smooth_laplacian hψ).continuous (compact_laplacian hcψ)
  have hr := (logKernel_test_tendsto hψ.continuous (hψ.continuous.integrable_of_hasCompactSupport hcψ)).const_mul (2*Real.pi)
  have he : (fun ε : ℝ => ∫x,regularizedLog ε x*euclideanLaplacian ψ x)=ᶠ[𝓝[>]0]
      (fun ε => (2*Real.pi)*(∫x,logKernel ε x*ψ x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [regularizedLog_distribution hε hψ hcψ,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [logKernel_eq]
    have hp : 2*Real.pi≠0 := by positivity
    field_simp
  exact tendsto_nhds_unique hl (hr.congr' he.symm)

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma log_translate_local {R S : ℝ} {z : Plane} (hz : ‖z‖<S) :
    IntegrableOn (fun x : Plane => Real.log ‖x-z‖) (Metric.ball 0 R) ∧
    (∫x in Metric.ball (0:Plane) R,‖Real.log ‖x-z‖‖) ≤
      ∫x in Metric.ball (0:Plane) (R+S),‖Real.log ‖x‖‖ := by
  let F := (Metric.ball (0:Plane) (R+S)).indicator (fun x => Real.log ‖x‖)
  have hiF : Integrable F := (log_norm_integrableOn_ball (R+S)).integrable_indicator measurableSet_ball
  have hit : Integrable (fun x : Plane => F (x-z)) :=
    (measurePreserving_sub_right volume z).integrable_comp hiF.aestronglyMeasurable |>.mpr hiF
  have he : ∀x∈Metric.ball (0:Plane) R,Real.log ‖x-z‖=F (x-z) := by
    intro x hx
    have hxR : ‖x‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    have hnorm : ‖x-z‖<R+S := (norm_sub_le x z).trans_lt (add_lt_add hxR hz)
    simp only [F,indicator_of_mem (show x-z∈Metric.ball (0:Plane) (R+S) by simpa only [Metric.mem_ball,dist_zero_right] using hnorm)]
  refine ⟨hit.integrableOn.congr_fun (fun x hx => (he x hx).symm) measurableSet_ball,?_⟩
  calc
    _ = ∫x in Metric.ball (0:Plane) R,‖F (x-z)‖ := setIntegral_congr_fun measurableSet_ball (fun x hx => congrArg norm (he x hx))
    _ ≤ ∫x,‖F (x-z)‖ := integral_mono_measure Measure.restrict_le_self (Eventually.of_forall (fun x => norm_nonneg _)) hit.norm
    _ = ∫x,‖F x‖ := integral_sub_right_eq_self (fun x => ‖F x‖) z
    _ = _ := by
      simp only [F,norm_indicator_eq_indicator_norm,integral_indicator measurableSet_ball]

end SharpNodal.Profiles
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Parametrix
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman

lemma smooth_parametrixSmoothLog : Smooth parametrixSmoothLog := by
  apply ContDiff.div_const
  apply ContDiff.log
  · exact (contDiff_id.norm_sq (𝕜:=ℝ)).add (parametrixInner.contDiff.pow 2)
  · intro x
    by_cases hx : x=0
    · subst x
      have ho : parametrixInner (0:Plane)=1 := parametrixInner.one_of_mem_closedBall (by simp [parametrixInner,Metric.mem_closedBall])
      simp [ho]
    · have hpos : 0<‖x‖^2+(parametrixInner x)^2 :=
        add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hx)) (sq_nonneg _)
      exact hpos.ne'

lemma smooth_parametrixCorrection : Smooth parametrixCorrection :=
  (parametrixCutoff.contDiff.sub contDiff_const).mul smooth_parametrixSmoothLog
lemma smooth_parametrixKernel : Smooth parametrixKernel := smooth_laplacian smooth_parametrixCorrection

lemma parametrixSmoothLog_eq {x : Plane} (hx : (1/8:ℝ)≤‖x‖) :
    parametrixSmoothLog x=Real.log ‖x‖ := by
  have hz : parametrixInner x=0 := parametrixInner.zero_of_le_dist (by simpa [parametrixInner,dist_zero_right] using hx)
  simp only [parametrixSmoothLog,hz,zero_pow (by decide : (2:ℕ)≠0),add_zero,Real.log_pow,Nat.cast_ofNat]
  ring

lemma logParametrix_eq (x : Plane) :
    logParametrix x=Real.log ‖x‖+parametrixCorrection x := by
  by_cases hx : ‖x‖≤(1/8:ℝ)
  · have ho : parametrixCutoff x=1 := parametrixCutoff.one_of_mem_closedBall (by simpa [parametrixCutoff,Metric.mem_closedBall,dist_zero_right] using hx)
    simp [logParametrix,parametrixCorrection,ho]
  · rw [parametrixCorrection,parametrixSmoothLog_eq (le_of_not_ge hx)]
    dsimp [logParametrix]; ring

lemma laplacian_of_log_germ {f : Plane → ℝ} (hf : Smooth f) {x : Plane} (hx : x≠0)
    (he : f=ᶠ[𝓝 x](fun y => Real.log ‖y‖)) : euclideanLaplacian f x=0 := by
  let g : ℂ → ℝ := f∘planeComplex.symm
  have hg : ContDiff ℝ ∞ g := hf.comp planeComplex.symm.toContinuousLinearEquiv.contDiff
  have hh : HarmonicAt (fun z : ℂ => Real.log ‖z‖) (planeComplex x) :=
    analyticAt_id.harmonicAt_log_norm (by simpa using hx)
  have he' : g=ᶠ[𝓝 (planeComplex x)](fun z : ℂ => Real.log ‖z‖) := by
    have htend : Tendsto planeComplex.symm (𝓝 (planeComplex x)) (𝓝 x) := by
      simpa only [planeComplex.symm_apply_apply] using (planeComplex.symm.continuous.continuousAt (x:=planeComplex x)).tendsto
    have ht := he.comp_tendsto htend
    filter_upwards [ht] with z hz
    simpa only [g,Function.comp_apply,LinearIsometryEquiv.norm_map] using hz
  have hhg : HarmonicAt g (planeComplex x) := (harmonicAt_congr_nhds he').mpr hh
  have hzero := hhg.2.self_of_nhds
  have heq := congrFun (laplacian_comp_isometry planeComplex.symm hf) (planeComplex x)
  rw [← plane_laplacian_eq_mathlib hf] at heq
  simpa only [g,Function.comp_apply,planeComplex.symm_apply_apply,Pi.zero_apply] using heq.symm.trans hzero

lemma parametrixKernel_zero {x : Plane} (hx : (1/4:ℝ)<‖x‖) : parametrixKernel x=0 := by
  have he : (fun y => -parametrixCorrection y)=ᶠ[𝓝 x](fun y => Real.log ‖y‖) := by
    filter_upwards [(continuous_norm.continuousAt.eventually (eventually_gt_nhds hx))] with y hy
    have hz : parametrixCutoff y=0 := parametrixCutoff.zero_of_le_dist (by simpa [parametrixCutoff,dist_zero_right] using hy.le)
    rw [parametrixCorrection,hz,parametrixSmoothLog_eq (by linarith)]
    ring
  have hh := laplacian_of_log_germ smooth_parametrixCorrection.neg (by intro h; norm_num [h] at hx) he
  have heq : (fun y => -parametrixCorrection y)=(fun y => (-1:ℝ)*parametrixCorrection y) := by funext y; ring
  rw [heq,laplacian_const_mul smooth_parametrixCorrection] at hh
  simpa only [neg_one_mul,neg_eq_zero,parametrixKernel] using hh

lemma logParametrix_zero {x : Plane} (hx : (1/4:ℝ)≤‖x‖) : logParametrix x=0 := by
  have hz : parametrixCutoff x=0 := parametrixCutoff.zero_of_le_dist (by simpa [parametrixCutoff,dist_zero_right] using hx)
  simp [logParametrix,hz]

lemma integral_parametrix_identity {ψ : Plane → ℝ} (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ) :
    (∫x,logParametrix x*euclideanLaplacian ψ x)=2*Real.pi*ψ 0+(∫x,parametrixKernel x*ψ x) := by
  have hlog : Integrable (fun x : Plane => Real.log ‖x‖*euclideanLaplacian ψ x) := by
    obtain ⟨R,hR,hzero⟩ := (compact_laplacian hcψ).exists_pos_le_norm
    obtain ⟨M,hM⟩ := (smooth_laplacian hψ).continuous.norm.bddAbove_range_of_hasCompactSupport (compact_laplacian hcψ).norm
    have hi := (IntegrableOn.integrable_indicator ((log_norm_integrableOn_ball R).norm) measurableSet_ball).mul_const M
    apply hi.mono' ((Real.measurable_log.comp measurable_norm).mul (smooth_laplacian hψ).continuous.measurable).aestronglyMeasurable
    filter_upwards [] with x
    change ‖Real.log ‖x‖*euclideanLaplacian ψ x‖≤((Metric.ball (0:Plane) R).indicator (fun x => ‖Real.log ‖x‖‖) x)*M
    by_cases hx : x∈Metric.ball (0:Plane) R
    · rw [indicator_of_mem hx,norm_mul]
      exact mul_le_mul_of_nonneg_left (hM (mem_range_self x)) (norm_nonneg _)
    · rw [hzero x (by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx),mul_zero,norm_zero,indicator_of_notMem hx,zero_mul]
  have hc : Integrable (fun x => parametrixCorrection x*euclideanLaplacian ψ x) :=
    integrable_mul_compact_right smooth_parametrixCorrection (smooth_laplacian hψ) (compact_laplacian hcψ)
  simp_rw [logParametrix_eq,add_mul]
  rw [integral_add hlog hc,logarithmic_fundamental_solution hψ hcψ,integral_mul_laplacian smooth_parametrixCorrection hψ hcψ]
  rfl
end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma rconv_eq (f g : Plane → ℝ) (x : Plane) : rconv f g x=∫y,f y*g (x-y) := rfl
lemma rconv_swap (f g : Plane → ℝ) (x : Plane) : rconv f g x=∫y,f (x-y)*g y :=
  convolution_eq_swap (ContinuousLinearMap.mul ℝ ℝ)

lemma partial_rconv {f g : Plane → ℝ} (hf : Integrable f) (hg : Smooth g)
    (hc : HasCompactSupport g) (i : Fin 2) :
    coordPartial (rconv f g) i=rconv f (coordPartial g i) := by
  funext x
  have hh := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hf.locallyIntegrable (hg.of_le (by simp : (1:ℕ∞ω)≤(∞:ℕ∞ω))) x
  have he : fderiv ℝ (rconv f g) x=(f ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR Plane,volume] fderiv ℝ g) x := by
    convert! hh.fderiv using 1
    all_goals try with_reducible_and_instances rfl
  change (fderiv ℝ (rconv f g) x) _=_
  rw [he,convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf.locallyIntegrable
    (hc.fderiv ℝ) ((hg.fderiv_right (by simp : (∞:ℕ∞ω)+1≤(∞:ℕ∞ω))).continuous)]
  rfl

lemma laplacian_rconv {f g : Plane → ℝ} (hf : Integrable f) (hg : Smooth g)
    (hc : HasCompactSupport g) :
    euclideanLaplacian (rconv f g)=rconv f (euclideanLaplacian g) := by
  funext x
  simp only [euclideanLaplacian,partial_rconv hf hg hc,
    partial_rconv hf (smooth_partial hg _) (compact_partial hc _)]
  simp only [rconv_eq,euclideanLaplacian,Finset.mul_sum]
  rw [integral_finsetSum]
  intro i _
  exact (compact_partial (compact_partial hc i) i).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) hf.locallyIntegrable (smooth_partial (smooth_partial hg i) i).continuous x

lemma partial_reflection {f : Plane → ℝ} (hf : Smooth f) (z x : Plane) (i : Fin 2) :
    coordPartial (fun y => f (z-y)) i x= -coordPartial f i (z-x) := by
  have hh := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜:=ℝ) x).const_sub z)
  have he : fderiv ℝ (fun y => f (z-y)) x= -(fderiv ℝ f (z-x)) := by
    convert! hh.fderiv using 1
    all_goals try with_reducible_and_instances rfl
    ext v
    simp
  change (fderiv ℝ (fun y => f (z-y)) x) _=_
  rw [he]
  rfl

lemma laplacian_reflection {f : Plane → ℝ} (hf : Smooth f) (z x : Plane) :
    euclideanLaplacian (fun y => f (z-y)) x=euclideanLaplacian f (z-x) := by
  unfold euclideanLaplacian
  apply Finset.sum_congr rfl
  intro i _
  have hrf : Smooth (fun y => coordPartial f i (z-y)) := (smooth_partial hf i).comp (contDiff_const.sub contDiff_id)
  rw [show coordPartial (fun y => f (z-y)) i=(fun y => -coordPartial f i (z-y)) from funext (fun y => partial_reflection hf z y i),
    partial_neg hrf,
    partial_reflection (smooth_partial hf i),neg_neg]

lemma compact_reflection {f : Plane → ℝ} (hc : HasCompactSupport f) (z : Plane) :
    HasCompactSupport (fun y => f (z-y)) := by
  convert! hc.comp_homeomorph ((Homeomorph.neg Plane).trans (Homeomorph.addRight z)) using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  congr 1
  change z-y= -y+z
  abel

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma integrable_logParametrix : Integrable logParametrix := by
  let F := (Metric.ball (0:Plane) 1).indicator (fun x => Real.log ‖x‖)
  have hi : Integrable F := (log_norm_integrableOn_ball 1).integrable_indicator measurableSet_ball
  have he : logParametrix=(fun x => parametrixCutoff x*F x) := by
    funext x
    by_cases hx : x∈Metric.ball (0:Plane) 1
    · simp [logParametrix,F,hx]
    · have hn : 1≤‖x‖ := by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx
      rw [logParametrix_zero (by linarith)]
      simp [F,hx]
  rw [he]
  exact hi.bdd_mul parametrixCutoff.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (parametrixCutoff.nonneg)] using parametrixCutoff.le_one))

lemma laplacian_parametrix_convolution {ψ : Plane → ℝ} (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ) (x : Plane) :
    euclideanLaplacian (rconv logParametrix ψ) x=2*Real.pi*ψ x+rconv parametrixKernel ψ x := by
  rw [laplacian_rconv integrable_logParametrix hψ hcψ,rconv_eq,rconv_eq]
  have hs : Smooth (fun y => ψ (x-y)) := hψ.comp (contDiff_const.sub contDiff_id)
  have hh := integral_parametrix_identity hs (compact_reflection hcψ x)
  simpa only [laplacian_reflection hψ,sub_zero] using hh

end SharpNodal.Profiles
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Decomposition
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma plane_component_norm_le (v : Plane) (i : Fin 2) : |v i|≤‖v‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i

end SharpNodal.Profiles

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_GridImprovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma massExcess_mul_left (c a b : ℝ≥0∞) (hc0 : c≠0) (hct : c≠⊤) :
    massExcess (c*a) (c*b)=massExcess a b := by
  unfold massExcess
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,mul_div_mul_left]
  exact ENNReal.toReal_ne_zero.mpr ⟨hc0,hct⟩

end SharpNodal.Profiles

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Subdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma centeredMass_mono (T : Plane) (U : Plane → ℝ) (y : Plane) {r R : ℝ}
    (hrR : r≤R) : centeredMass T U y r ≤ centeredMass T U y R :=
  lintegral_mono_set (Metric.ball_subset_ball hrR)

lemma centeredMass_weight_bound (T T' : Plane) (U : Plane → ℝ) (y : Plane) {r : ℝ}
    : centeredMass T U y r≤
      ENNReal.ofReal (Real.exp (2*‖T-T'‖*r))*centeredMass T' U y r := by
  unfold centeredMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_pow,mul_pow,← Real.exp_nat_mul,← Real.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  rw [← mul_assoc,← Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  have hnorm : ‖x-y‖ ≤ r := by simpa [dist_eq_norm] using (Metric.mem_ball.mp hx).le
  have hi : -inner ℝ (T-T') (x-y)≤‖T-T'‖*r :=
    (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)))
  rw [inner_sub_left] at hi
  linarith

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma centeredMass_ne_zero_of {T T' : Plane} {U : Plane → ℝ} {y : Plane} {r : ℝ}
    (h : centeredMass T U y r≠0) : centeredMass T' U y r≠0 := by
  intro hz
  have hh := centeredMass_weight_bound T T' U y (r:=r)
  rw [hz,mul_zero] at hh
  exact h (le_antisymm hh bot_le)

lemma centeredMass_ne_top_of {T T' : Plane} {U : Plane → ℝ} {y : Plane} {r : ℝ}
    (h : centeredMass T U y r≠⊤) : centeredMass T' U y r≠⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h)
    (centeredMass_weight_bound T' T U y)

lemma centered_excess_nonneg {T : Plane} {U : Plane → ℝ} {y : Plane} {r R : ℝ}
    (hrR : r ≤ R) (hm0 : centeredMass T U y r≠0) (hmt : centeredMass T U y R≠⊤) :
    0 ≤ massExcess (centeredMass T U y R) (centeredMass T U y r) := by
  have hmono := centeredMass_mono T U y hrR
  have hrt := ne_top_of_le_ne_top hmt hmono
  have hrpos := ENNReal.toReal_pos hm0 hrt
  have hm := ENNReal.toReal_mono hmt hmono
  unfold massExcess
  apply div_nonneg _ (by norm_num)
  apply Real.log_nonneg
  exact (le_div_iff₀ hrpos).mpr (by simpa using hm)

end SharpNodal.Profiles

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Descent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma UnitWave.excess_nonneg {Cp a₀ : ℝ} (D : UnitWave Cp a₀) (b : Plane) :
    0≤D.excess b :=
  centered_excess_nonneg (by norm_num) (centeredMass_ne_zero_of D.inner_nonzero)
    (centeredMass_ne_top_of D.outer_finite)

end SharpNodal.Profiles
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_LogGradients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman

lemma norm_logGradient (x : Plane) : ‖logGradient x‖=‖x‖⁻¹ := by
  by_cases hx : x=0
  · simp [hx,logGradient]
  · have hn := norm_pos_iff.mpr hx
    rw [logGradient,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(‖x‖^2)⁻¹)]
    field_simp

lemma inv_norm_integrableOn_ball (R : ℝ) :
    IntegrableOn (fun x : Plane => ‖x‖⁻¹) (Metric.ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (α:=1) (C:=1) (by simp [Plane]) (by simp [Plane])
    _ (measurable_id.norm.inv.aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Pi.inv_apply,id_eq,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    Real.rpow_neg_one,one_mul,le_refl]

lemma inverse_translate_local {R S : ℝ} {z : Plane} (hz : ‖z‖<S) :
    IntegrableOn (fun x : Plane => ‖x-z‖⁻¹) (Metric.ball 0 R) ∧
    (∫x in Metric.ball (0:Plane) R,‖x-z‖⁻¹) ≤
      ∫x in Metric.ball (0:Plane) (R+S),‖x‖⁻¹ := by
  let F := (Metric.ball (0:Plane) (R+S)).indicator (fun x => ‖x‖⁻¹)
  have hiF : Integrable F := (inv_norm_integrableOn_ball (R+S)).integrable_indicator measurableSet_ball
  have hit : Integrable (fun x : Plane => F (x-z)) :=
    (measurePreserving_sub_right volume z).integrable_comp hiF.aestronglyMeasurable |>.mpr hiF
  have he : ∀x∈Metric.ball (0:Plane) R,‖x-z‖⁻¹=F (x-z) := by
    intro x hx
    have hxR : ‖x‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    have hnorm : ‖x-z‖<R+S := (norm_sub_le x z).trans_lt (add_lt_add hxR hz)
    simp only [F,indicator_of_mem (show x-z∈Metric.ball (0:Plane) (R+S) by simpa only [Metric.mem_ball,dist_zero_right] using hnorm)]
  refine ⟨hit.integrableOn.congr_fun (fun x hx => (he x hx).symm) measurableSet_ball,?_⟩
  calc
    _ = ∫x in Metric.ball (0:Plane) R,F (x-z) := setIntegral_congr_fun measurableSet_ball (fun x hx => he x hx)
    _ ≤ ∫x,F (x-z) := integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall (fun x => indicator_nonneg (fun x _ => inv_nonneg.mpr (norm_nonneg x)) _)) hit
    _ = ∫x,F x := integral_sub_right_eq_self F z
    _ = _ := by rw [integral_indicator measurableSet_ball]

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma partial_regularizedLog_bound {ε : ℝ} (hε : 0<ε) (i : Fin 2) (x : Plane) :
    ‖coordPartial (regularizedLog ε) i x‖ ≤ ‖x‖⁻¹ := by
  by_cases hx : x=0
  · simp [hx,partial_regularizedLog hε]
  have hn : 0<‖x‖ := norm_pos_iff.mpr hx
  rw [partial_regularizedLog hε,norm_div,Real.norm_of_nonneg (logDenom_pos hε x).le]
  apply (div_le_iff₀ (logDenom_pos hε x)).mpr
  calc
    ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
    _ = ‖x‖⁻¹*‖x‖^2 := by field_simp
    _ ≤ ‖x‖⁻¹*logDenom ε x := mul_le_mul_of_nonneg_left (by dsimp [logDenom]; nlinarith [sq_nonneg ε]) (by positivity)

lemma partial_regularizedLog_tendsto (i : Fin 2) {x : Plane} (hx : x≠0) :
    Tendsto (fun ε : ℝ => coordPartial (regularizedLog ε) i x) (𝓝[>]0)
      (𝓝 (logGradient x i)) := by
  have hn : ‖x‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have ht : Tendsto (fun ε : ℝ => x i/(‖x‖^2+ε^2)) (𝓝[>]0) (𝓝 (x i/‖x‖^2)) := by
    apply Tendsto.div tendsto_const_nhds _ hn
    simpa using ((tendsto_const_nhds (x:=‖x‖^2)).add ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).pow 2)).mono_left nhdsWithin_le_nhds
  have he : x i/‖x‖^2=logGradient x i := by simp [logGradient,div_eq_mul_inv,mul_comm]
  rw [he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (partial_regularizedLog hε i x).symm

lemma partial_regularizedLog_test_limit (i : Fin 2) {g : Plane → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) :
    Tendsto (fun ε : ℝ => ∫x,coordPartial (regularizedLog ε) i x*g x) (𝓝[>]0)
      (𝓝 (∫x,logGradient x i*g x)) := by
  obtain ⟨R,hR,hzero⟩ := hc.exists_pos_le_norm
  obtain ⟨M,hM⟩ := hg.norm.bddAbove_range_of_hasCompactSupport hc.norm
  let B := fun x : Plane => ‖x‖⁻¹*M
  have hiB : IntegrableOn B (Metric.ball 0 R) := (inv_norm_integrableOn_ball R).mul_const M
  have hne : ∀ᵐx : Plane,x≠0 := by simp [ae_iff]
  have ht := tendsto_integral_filter_of_dominated_convergence (l:=𝓝[>] (0:ℝ)) B
    (F:=fun ε x =>coordPartial (regularizedLog ε) i x*g x)
    (f:=fun x =>logGradient x i*g x)
    (by filter_upwards [self_mem_nhdsWithin] with ε hε using
      ((smooth_partial (smooth_regularizedLog hε) i).continuous.mul hg).aestronglyMeasurable)
    (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [] with x
      rw [norm_mul]
      exact mul_le_mul (partial_regularizedLog_bound hε i x) (hM (mem_range_self x))
        (norm_nonneg _) (by positivity)) hiB
    (by filter_upwards [ae_restrict_of_ae hne] with x hx using
      (partial_regularizedLog_tendsto i hx).mul_const (g x))
  have he (f : Plane → ℝ) : (∫x in Metric.ball (0:Plane) R,f x*g x)=(∫x,f x*g x) := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Metric.ball (0:Plane) R
    · simp [hx]
    · have hz : g x=0 := hzero x (by simpa [Metric.mem_ball,dist_zero_right,not_lt] using hx)
      simp [hx,hz]
  simpa only [he] using ht

lemma logarithmic_gradient_distribution {ψ : Plane → ℝ} (hψ : Smooth ψ)
    (hcψ : HasCompactSupport ψ) (i : Fin 2) :
    (∫x,Real.log ‖x‖*coordPartial ψ i x)= -(∫x,logGradient x i*ψ x) := by
  have hl := regularizedLog_test_limit (smooth_partial hψ i).continuous (compact_partial hcψ i)
  have hr := (partial_regularizedLog_test_limit i hψ.continuous hcψ).neg
  have he : (fun ε : ℝ => ∫x,regularizedLog ε x*coordPartial ψ i x)=ᶠ[𝓝[>]0]
      (fun ε => -(∫x,coordPartial (regularizedLog ε) i x*ψ x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact integral_mul_partial (smooth_regularizedLog hε) hψ hcψ i
  exact tendsto_nhds_unique hl (hr.congr' he.symm)

end SharpNodal.Profiles

end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_GridPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory

namespace SharpNodal.Profiles

lemma wordIndex_injective (A n : ℕ) : Function.Injective (wordIndex A n) := by
  induction n with
  | zero => intro p q _; exact Subsingleton.elim _ _
  | succ n ih =>
    intro p q hpq
    have hpairs (j : Fin 2) :
        (p 0 j,wordIndex A n (Fin.tail p) j)=(q 0 j,wordIndex A n (Fin.tail q) j) := by
      apply finProdFinEquiv.injective
      exact Fin.cast_injective (pow_succ' A n).symm (congrFun hpq j)
    have hhead : p 0=q 0 := funext (fun j =>congrArg Prod.fst (hpairs j))
    have htail : Fin.tail p=Fin.tail q := ih (funext (fun j =>congrArg Prod.snd (hpairs j)))
    rw [← Fin.cons_self_tail p,← Fin.cons_self_tail q,hhead,htail]

lemma wordCenter_zero (A : ℕ) (w : GridWord A 0) : wordCenter A 0 w=0 := by
  ext j
  norm_num [wordCenter,wordIndex,gridCenter]

lemma wordCenter_succ {A : ℕ} (hA : 0<A) (n : ℕ) (w : GridWord A (n+1)) :
    wordCenter A (n+1) w=gridCenter A (w 0)+(A:ℝ)⁻¹ • wordCenter A n (Fin.tail w) := by
  have hAr : (A:ℝ)≠0 := by exact_mod_cast hA.ne'
  have hpow : ((A:ℝ)^n)≠0 := pow_ne_zero _ hAr
  ext j
  change (((wordIndex A (n+1) w j:ℕ):ℝ)+1/2)/(A^(n+1):ℕ)-1/2=
    (((w 0 j:ℕ):ℝ)+1/2)/(A:ℝ)-1/2+
      (A:ℝ)⁻¹*((((wordIndex A n (Fin.tail w) j:ℕ):ℝ)+1/2)/(A^n:ℕ)-1/2)
  simp only [wordIndex,Fin.val_cast,finProdFinEquiv,Equiv.coe_fn_mk,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
  rw [pow_succ]
  field_simp
  ring

lemma word_rescale_succ {A : ℕ} (hA : 0<A) (n : ℕ) (w : GridWord A (n+1)) :
    rescaleMap (wordCenter A (n+1) w) ((A:ℝ)⁻¹^(n+1))=
      rescaleMap (gridCenter A (w 0)) (A:ℝ)⁻¹ ∘
        rescaleMap (wordCenter A n (Fin.tail w)) ((A:ℝ)⁻¹^n) := by
  funext x
  rw [wordCenter_succ hA]
  simp only [rescaleMap,Function.comp_apply,smul_add,smul_smul,pow_succ]
  module

lemma gridWord_card (A n : ℕ) : Fintype.card (GridWord A n)=(A^n)^2 := by
  simp only [GridWord,GridIndex,Fintype.card_fun,Fintype.card_fin]
  rw [← pow_mul,← pow_mul,Nat.mul_comm]

end SharpNodal.Profiles

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Excursions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set

namespace SharpNodal.Profiles

lemma UnitWave.growth_zero {Cp a₀ : ℝ} (D : UnitWave Cp a₀) :
    D.growth 0=fieldGrowth D.U D.K := by simp only [UnitWave.growth,UnitWave.excess,smul_zero,fieldGrowth]

end SharpNodal.Profiles

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Multipliers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory

namespace SharpNodal.Profiles
open Carleman

lemma locallyIntegrable_logNorm : LocallyIntegrable (fun x : Plane => Real.log ‖x‖) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R,-,hR⟩:=hK.isBounded.exists_pos_norm_lt
  exact (log_norm_integrableOn_ball R).mono_set (fun x hx =>by simpa [Metric.mem_ball,dist_zero_right] using hR x hx)

lemma smooth_rconv_local {f g : Plane → ℝ} (hf : LocallyIntegrable f) (hg : Smooth g)
    (hc : HasCompactSupport g) : Smooth (rconv f g) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hg

lemma partial_rconv_local {f g : Plane → ℝ} (hf : LocallyIntegrable f) (hg : Smooth g)
    (hc : HasCompactSupport g) (i : Fin 2) :
    coordPartial (rconv f g) i=rconv f (coordPartial g i) := by
  funext x
  have hh := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hf (hg.of_le (by simp : (1:ℕ∞ω)≤(∞:ℕ∞ω))) x
  have he : fderiv ℝ (rconv f g) x=(f ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR Plane,volume] fderiv ℝ g) x := by
    convert! hh.fderiv using 1
    all_goals try with_reducible_and_instances rfl
  change (fderiv ℝ (rconv f g) x) _=_
  rw [he,convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf
    (hc.fderiv ℝ) ((hg.fderiv_right (by simp : (∞:ℕ∞ω)+1≤(∞:ℕ∞ω))).continuous)]
  rfl

lemma partial_newtonPotential {g : Plane → ℝ} (hg : Smooth g)
    (hc : HasCompactSupport g) (i : Fin 2) (x : Plane) :
    coordPartial (newtonPotential g) i x=
      (2*Real.pi)⁻¹*∫y,logGradient y i*g (x-y) := by
  unfold newtonPotential
  rw [partial_const_mul (smooth_rconv_local locallyIntegrable_logNorm hg hc),
    partial_rconv_local locallyIntegrable_logNorm hg hc,rconv_eq]
  congr 1
  have hh := logarithmic_gradient_distribution
    (show Smooth (fun y => g (x-y)) from hg.comp (contDiff_const.sub contDiff_id)) (compact_reflection hc x) i
  simp only [partial_reflection hg,mul_neg,integral_neg] at hh
  linarith

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma integral_supported_ball (f g : Plane → ℝ) {R : ℝ}
    (hs : ∀x, R≤‖x‖ → g x=0) :
    (∫x,f x*g x)=∫x in Metric.ball (0:Plane) R,f x*g x := by
  rw [←integral_indicator measurableSet_ball]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x∈Metric.ball (0:Plane) R
  · simp [hx]
  · have hz:=hs x (by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx)
    simp [hx,hz]

lemma integral_mul_norm_bound {f g : Plane → ℝ} {R B : ℝ}
    (hf : IntegrableOn f (Metric.ball 0 R))
    (hb : ∀x∈Metric.ball (0:Plane) R,|g x|≤B) :
    (∫x in Metric.ball (0:Plane) R,‖f x*g x‖)≤
      (∫x in Metric.ball (0:Plane) R,‖f x‖)*B := by
  rw [←integral_mul_const]
  apply integral_mono_of_nonneg (Eventually.of_forall (fun x =>norm_nonneg _))
    (hf.norm.mul_const B)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  rw [norm_mul,Real.norm_eq_abs (g x)]
  exact mul_le_mul_of_nonneg_left (hb x hx) (norm_nonneg _)

lemma abs_newtonPotential_bound {g : Plane → ℝ} {B : ℝ} (hB : 0≤B)
    (hs : ∀x,3≤‖x‖ → g x=0)
    (hb : ∀x∈Metric.ball (0:Plane) 3,|g x|≤B)
    {x : Plane} (hx : x∈Metric.ball 0 3) :
    |newtonPotential g x|≤
      ((2*Real.pi)⁻¹*(∫y in Metric.ball (0:Plane) 6,‖Real.log ‖y‖‖))*B := by
  have hx' : ‖x‖<3 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  obtain ⟨hi,hle⟩:=log_translate_local (R:=3) hx'
  rw [newtonPotential,abs_mul,abs_of_pos (by positivity : 0<(2*Real.pi)⁻¹),rconv_swap,
    integral_supported_ball _ _ hs]
  simp only [norm_sub_rev x]
  calc
    _ ≤ (2*Real.pi)⁻¹*∫y in Metric.ball (0:Plane) 3,‖Real.log ‖y-x‖*g y‖ :=
      mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f:=fun y : Plane =>Real.log ‖y-x‖*g y) (μ:=volume.restrict (Metric.ball (0:Plane) 3))) (by positivity)
    _ ≤ (2*Real.pi)⁻¹*((∫y in Metric.ball (0:Plane) 3,‖Real.log ‖y-x‖‖)*B) :=
      mul_le_mul_of_nonneg_left (integral_mul_norm_bound hi hb) (by positivity)
    _ ≤ _ := by
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by norm_num at hle ⊢; exact hle) (by positivity)) hB

lemma abs_partial_newtonPotential_bound {g : Plane → ℝ} (hg : Smooth g)
    (hc : HasCompactSupport g) {B : ℝ} (hB : 0≤B)
    (hs : ∀x,3≤‖x‖ → g x=0)
    (hb : ∀x∈Metric.ball (0:Plane) 3,|g x|≤B)
    {x : Plane} (hx : x∈Metric.ball 0 3) (i : Fin 2) :
    |coordPartial (newtonPotential g) i x|≤
      ((2*Real.pi)⁻¹*(∫y in Metric.ball (0:Plane) 6,‖y‖⁻¹))*B := by
  have hx' : ‖x‖<3 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  obtain ⟨hi,hle⟩:=inverse_translate_local (R:=3) hx'
  rw [partial_newtonPotential hg hc,abs_mul,abs_of_pos (by positivity : 0<(2*Real.pi)⁻¹)]
  change (2*Real.pi)⁻¹*|rconv (fun y => logGradient y i) g x|≤_
  rw [rconv_swap,integral_supported_ball _ _ hs]
  calc
    _ ≤ (2*Real.pi)⁻¹*∫y in Metric.ball (0:Plane) 3,‖logGradient (x-y) i*g y‖ :=
      mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f:=fun y : Plane =>logGradient (x-y) i*g y) (μ:=volume.restrict (Metric.ball (0:Plane) 3))) (by positivity)
    _ ≤ (2*Real.pi)⁻¹*((∫y in Metric.ball (0:Plane) 3,‖y-x‖⁻¹)*B) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [←integral_mul_const]
      apply integral_mono_of_nonneg (Eventually.of_forall (fun y =>norm_nonneg _)) (hi.mul_const B)
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      rw [norm_mul,Real.norm_eq_abs (g y)]
      apply mul_le_mul _ (hb y hy) (abs_nonneg _) (by positivity)
      simpa only [Real.norm_eq_abs,norm_logGradient,norm_sub_rev] using plane_component_norm_le (logGradient (x-y)) i
    _ ≤ _ := by
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by norm_num at hle ⊢; exact hle) (by positivity)) hB

theorem newton_operator_bounds : ∃C : ℝ,1≤C ∧ ∀(g : Plane → ℝ),
    Smooth g → HasCompactSupport g → ∀B : ℝ,0≤B →
    (∀x,3≤‖x‖ → g x=0) → (∀x∈Metric.ball (0:Plane) 3,|g x|≤B) →
    ∀x∈Metric.ball (0:Plane) 3,
      |newtonPotential g x|≤C*B ∧ ∀i : Fin 2,|coordPartial (newtonPotential g) i x|≤C*B := by
  let L : ℝ := (2*Real.pi)⁻¹*(∫y in Metric.ball (0:Plane) 6,‖Real.log ‖y‖‖)
  let G : ℝ := (2*Real.pi)⁻¹*(∫y in Metric.ball (0:Plane) 6,‖y‖⁻¹)
  have hL : 0≤L := mul_nonneg (by positivity) (integral_nonneg (fun y =>norm_nonneg _))
  have hG : 0≤G := mul_nonneg (by positivity) (integral_nonneg (fun y =>by positivity))
  refine ⟨1+L+G,by linarith,?_⟩
  intro g hg hc B hB hs hb x hx
  refine ⟨(abs_newtonPotential_bound hB hs hb hx).trans ?_,fun i =>
    (abs_partial_newtonPotential_bound hg hc hB hs hb hx i).trans ?_⟩ <;>
    apply mul_le_mul_of_nonneg_right _ hB <;> change _≤1+L+G <;> linarith

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma exists_newtonControl : ∃C : ℝ,NewtonControl C := newton_operator_bounds

end SharpNodal.Profiles
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_GradientAnchors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric

namespace SharpNodal.Profiles
open Carleman
lemma partial_germ {f g : Plane → ℝ} {x : Plane} (he : f=ᶠ[𝓝 x]g) (i : Fin 2) :
    coordPartial f i x=coordPartial g i x := by
  unfold coordPartial; rw [he.fderiv_eq]
lemma laplacian_germ {f g : Plane → ℝ} {x : Plane} (he : f=ᶠ[𝓝 x]g) :
    euclideanLaplacian f x=euclideanLaplacian g x := by
  apply Finset.sum_congr rfl
  intro i _
  apply partial_germ
  filter_upwards [he.eventuallyEq_nhds] with y hy
  exact partial_germ hy i

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma rescaleMap_lipschitz (p : Plane) {r : ℝ} (hr : 0 ≤ r) :
    LipschitzWith (Real.toNNReal r) (rescaleMap p r) := by
  apply LipschitzWith.of_dist_le'
  intro x y
  simp only [rescaleMap,dist_add_left,dist_smul₀,Real.norm_eq_abs,abs_of_nonneg hr,le_refl]

end SharpNodal.Profiles

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_LocalLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
namespace SharpNodal.Profiles
open Carleman

lemma log_sq_le_inv {r : ℝ} (hr : 0 ≤ r) (hr1 : r≤1) : (Real.log r)^2≤4*r⁻¹ := by
  rcases eq_or_lt_of_le hr with he | hp
  · rw [←he]; simp
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (inv_pos.mpr hp))
  rw [Real.log_sqrt (inv_nonneg.mpr hr),Real.log_inv] at h
  have hl := Real.log_nonpos hr hr1
  have hs := Real.sq_sqrt (inv_nonneg.mpr hr)
  have hb : -Real.log r ≤ 2*Real.sqrt r⁻¹ := by linarith
  have hc := mul_self_le_mul_self (by linarith : 0≤-Real.log r) hb
  nlinarith

lemma integrable_logParametrix_sq : Integrable (fun x=>logParametrix x^2) := by
  have hi : IntegrableOn (fun x : Plane=> (Real.log ‖x‖)^2) (ball 0 (1/4)) := by
    apply ((inv_norm_integrableOn_ball (1/4)).const_mul 4).mono'
      ((measurable_id.norm.log.pow_const 2).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    change |(Real.log ‖x‖)^2|≤_
    rw [abs_of_nonneg (sq_nonneg (Real.log ‖x‖))]
    exact log_sq_le_inv (norm_nonneg _) (by have:=mem_ball_zero_iff.mp hx; linarith)
  have hQ : IntegrableOn (fun x=>logParametrix x^2) (ball 0 (1/4)) := by
    apply hi.mono' ((parametrixCutoff.continuous.measurable.mul measurable_id.norm.log).pow_const 2).aestronglyMeasurable
    filter_upwards [] with x
    change |(parametrixCutoff x*Real.log ‖x‖)^2|≤_
    rw [abs_of_nonneg (sq_nonneg (parametrixCutoff x*Real.log ‖x‖)),mul_pow]
    have hc : parametrixCutoff x^2≤1 := by
      have hl:=parametrixCutoff.nonneg (x:=x)
      have hu:=parametrixCutoff.le_one (x:=x)
      nlinarith
    exact mul_le_of_le_one_left (sq_nonneg _) hc
  have he : (fun x=>logParametrix x^2)=(ball (0:Plane) (1/4)).indicator (fun x=>logParametrix x^2) := by
    funext x
    by_cases hx : x∈ball (0:Plane) (1/4)
    · simp only [indicator_of_mem hx]
    · rw [indicator_of_notMem hx,logParametrix_zero (by simpa only [mem_ball,dist_zero_right,not_lt] using hx)]
      norm_num
  rw [he]
  exact hQ.integrable_indicator measurableSet_ball

lemma integral_abs_mul_le_sqrt {f g : Plane → ℝ}
    (hf : MemLp f 2) (hg : MemLp g 2) :
    |∫x,f x*g x|≤Real.sqrt (∫x,f x^2)*Real.sqrt (∫x,g x^2) := by
  have hh:=integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by norm_num; exact hf) (by norm_num; exact hg)
  simp only [Real.norm_eq_abs,Real.rpow_two, sq_abs,←Real.sqrt_eq_rpow] at hh
  exact (norm_integral_le_integral_norm (fun x=>f x*g x)).trans (by simpa only [Real.norm_eq_abs,abs_mul] using hh)

lemma continuous_sq_integrableOn_ball {U : Plane → ℝ} (hU : Continuous U) (R : ℝ) :
    IntegrableOn (fun x=>U x^2) (ball 0 R) :=
  (hU.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall (0:Plane) R) |>.mono_set ball_subset_closedBall

lemma memLp_indicator_ball {U : Plane → ℝ} (hU : Continuous U) (R : ℝ) :
    MemLp ((ball (0:Plane) R).indicator U) 2 := by
  apply (memLp_two_iff_integrable_sq (hU.measurable.indicator measurableSet_ball |>.aestronglyMeasurable)).mpr
  have he : (fun x=>((ball (0:Plane) R).indicator U x)^2)=(ball (0:Plane) R).indicator (fun x=>U x^2) := by
    funext x; by_cases hx : x∈ball (0:Plane) R <;> simp [hx]
  rw [he]
  exact (continuous_sq_integrableOn_ball hU R).integrable_indicator measurableSet_ball

lemma kernel_L2_bound {f U : Plane → ℝ} (hf : MemLp f 2) (hU : Continuous U)
    {x : Plane} {R r : ℝ} (hx : ‖x‖+r<R) (hs : ∀y,r<‖y‖ → f y=0) :
    |rconv f U x|≤Real.sqrt (∫y,f y^2)*Real.sqrt (∫y in ball (0:Plane) R,U y^2) := by
  let V:=(ball (0:Plane) R).indicator U
  have hV:=memLp_indicator_ball hU R
  have ht : MemLp (fun y=>V (x-y)) 2 := hV.comp_measurePreserving ((volume : Measure Plane).measurePreserving_sub_left x)
  have he : rconv f U x=∫y,f y*V (x-y) := by
    rw [rconv_eq]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : r<‖y‖
    · rw [hs y hy]; simp
    · have hm : x-y∈ball (0:Plane) R:=mem_ball_zero_iff.mpr ((norm_sub_le x y).trans_lt (by linarith only [hx,le_of_not_gt hy]))
      simp only [V,indicator_of_mem hm]
  rw [he]
  have hh:=integral_abs_mul_le_sqrt hf ht
  have heI : (∫y,V (x-y)^2)=∫y in ball (0:Plane) R,U y^2 := by
    rw [integral_sub_left_eq_self (fun y=>V y^2) volume x]
    have heV : (fun y=>V y^2)=(ball (0:Plane) R).indicator (fun y=>U y^2) := by
      funext y; by_cases hy : y∈ball (0:Plane) R <;> simp [V,hy]
    rw [heV,integral_indicator measurableSet_ball]
  rwa [heI] at hh

lemma small_potential_parametrix {U q : Plane → ℝ} (hU : Smooth U) (_hq : Smooth q)
    (he : ∀x∈ball (0:Plane) (11/4),euclideanLaplacian U x+q x*U x=0)
    {x : Plane} (hx : x∈ball (0:Plane) (5/2)) :
    2*Real.pi*U x= -rconv logParametrix (fun y=>q y*U y) x-rconv parametrixKernel U x := by
  let χ : ContDiffBump (0:Plane):=⟨11/4,3,by norm_num,by norm_num⟩
  let V : Plane → ℝ:=fun y=>χ y*U y
  have hV : Smooth V:=χ.contDiff.mul hU
  have hcV : HasCompactSupport V:=χ.hasCompactSupport.mul_right
  have hVe {y : Plane} (hy : y∈ball (0:Plane) (11/4)) : V=ᶠ[𝓝 y]U := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    have hz' : z∈closedBall (0:Plane) χ.rIn:=ball_subset_closedBall hz
    simp only [V,χ.one_of_mem_closedBall hz',one_mul]
  have hi:=laplacian_parametrix_convolution hV hcV x
  rw [laplacian_rconv integrable_logParametrix hV hcV] at hi
  have hx' : ‖x‖<5/2:=mem_ball_zero_iff.mp hx
  have ht {y : Plane} (hy : ‖y‖≤1/4) : x-y∈ball (0:Plane) (11/4) :=
    mem_ball_zero_iff.mpr ((norm_sub_le x y).trans_lt (by linarith only [hx',hy]))
  have hQ : rconv logParametrix (euclideanLaplacian V) x= -rconv logParametrix (fun y=>q y*U y) x := by
    rw [rconv_eq,rconv_eq,←integral_neg]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : (1/4:ℝ)≤‖y‖
    · rw [logParametrix_zero hy]; simp
    · rw [laplacian_germ (hVe (ht (lt_of_not_ge hy).le))]
      have hh:=he (x-y) (ht (lt_of_not_ge hy).le)
      rw [show euclideanLaplacian U (x-y)= -(q (x-y)*U (x-y)) by linarith]
      ring
  have hK : rconv parametrixKernel V x=rconv parametrixKernel U x := by
    rw [rconv_eq,rconv_eq]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : (1/4:ℝ)<‖y‖
    · rw [parametrixKernel_zero hy]; simp
    · rw [(hVe (ht (le_of_not_gt hy))).eq_of_nhds]
  rw [hQ,hK,(hVe (ball_subset_ball (by norm_num) hx)).eq_of_nhds] at hi
  linarith

lemma small_potential_L2_interior : ∃C : ℝ,1≤C ∧ ∀(U q : Plane → ℝ),Smooth U → Smooth q →
    (∀x∈ball (0:Plane) (11/4),euclideanLaplacian U x+q x*U x=0) →
    (∀x∈ball (0:Plane) 3,|q x|≤1) →
    ∀x∈ball (0:Plane) (5/2),|U x|≤C*Real.sqrt (∫y in ball (0:Plane) (11/4),U y^2) := by
  have hQ : MemLp logParametrix 2:=
    (memLp_two_iff_integrable_sq (parametrixCutoff.continuous.measurable.mul measurable_id.norm.log |>.aestronglyMeasurable)).mpr integrable_logParametrix_sq
  have hK : MemLp parametrixKernel 2:=
    (memLp_two_iff_integrable_sq smooth_parametrixKernel.continuous.aestronglyMeasurable).mpr
      ((smooth_parametrixKernel.pow 2).continuous.integrable_of_hasCompactSupport (by
        apply HasCompactSupport.intro (isCompact_closedBall (0:Plane) (1/4))
        intro x hx
        rw [parametrixKernel_zero (by simpa only [mem_closedBall,dist_zero_right,not_le] using hx)]
        norm_num))
  let N:=Real.sqrt (∫y,logParametrix y^2)+Real.sqrt (∫y,parametrixKernel y^2)
  let C:=1+(2*Real.pi)⁻¹*N
  have hN : 0≤N:=add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hC : 1≤C:=by dsimp [C]; have : 0≤(2*Real.pi)⁻¹*N:=mul_nonneg (by positivity) hN; linarith
  refine ⟨C,hC,?_⟩
  intro U q hU hq he hb x hx
  have hx' : ‖x‖+(1/4:ℝ)<11/4:=by have:=mem_ball_zero_iff.mp hx; linarith
  have hqU:=kernel_L2_bound hQ (hq.continuous.mul hU.continuous) hx'
    (fun y hy=>logParametrix_zero hy.le)
  have hKU:=kernel_L2_bound hK hU.continuous hx' (fun y hy=>parametrixKernel_zero hy)
  have hsq : (∫y in ball (0:Plane) (11/4),(q y*U y)^2)≤∫y in ball (0:Plane) (11/4),U y^2 := by
    apply integral_mono_ae (continuous_sq_integrableOn_ball (hq.continuous.mul hU.continuous) _) (continuous_sq_integrableOn_ball hU.continuous _)
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hyb:=hb y (ball_subset_ball (by norm_num) hy)
    have hq2 : q y^2≤1:=by have:=abs_nonneg (q y); nlinarith [sq_abs (q y)]
    change (q y*U y)^2≤_
    rw [mul_pow]; exact mul_le_of_le_one_left (sq_nonneg _) hq2
  have hsqrt:=Real.sqrt_le_sqrt hsq
  have hqU':=hqU.trans (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _))
  change |rconv logParametrix (fun y=>q y*U y) x|≤_ at hqU'
  have hei:=small_potential_parametrix hU hq he hx
  have hn:=abs_add_le (-rconv logParametrix (fun y=>q y*U y) x) (-rconv parametrixKernel U x)
  rw [←sub_eq_add_neg,←hei,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi),abs_neg,abs_neg] at hn
  have hpos : 0<2*Real.pi:=by positivity
  have hh : |U x|≤(2*Real.pi)⁻¹*N*Real.sqrt (∫y in ball (0:Plane) (11/4),U y^2) := by
    calc
      |U x|≤(N*Real.sqrt (∫y in ball (0:Plane) (11/4),U y^2))/(2*Real.pi) := by
        apply (le_div_iff₀ hpos).mpr
        dsimp [N]; nlinarith only [hn,hqU',hKU]
      _ = _ := by ring
  exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.sqrt_nonneg _))
end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma exists_local_smallness : ∃C ε δ : ℝ, NewtonControl C ∧ 0<ε ∧ ε≤1 ∧
    0≤δ ∧ δ≤1/4 ∧ C*ε≤δ ∧ Real.exp (8*C*(4*δ/(1-δ)))-1≤1/2048 := by
  obtain ⟨C,hC⟩:=exists_newtonControl
  have hCp : 0<C:=by linarith [hC.1]
  let δ:=min (1/8:ℝ) (Real.log (2049/2048)/(64*C))
  have hlog : 0<Real.log (2049/2048):=Real.log_pos (by norm_num)
  have hδ : 0<δ:=lt_min (by norm_num) (div_pos hlog (by positivity))
  have hδb : δ≤1/8:=min_le_left _ _
  have hδlog : 64*C*δ≤Real.log (2049/2048):=by
    have hd:=min_le_right (1/8:ℝ) (Real.log (2049/2048)/(64*C))
    exact (by nlinarith only [(le_div_iff₀ (show 0<64*C by positivity)).mp hd])
  have he : 8*C*(4*δ/(1-δ))≤Real.log (2049/2048) := by
    have hh : 4*δ/(1-δ)≤8*δ:=by apply (div_le_iff₀ (by linarith : 0<1-δ)).mpr; nlinarith
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans (by nlinarith only [hδlog])
  refine ⟨C,δ/C,δ,hC,div_pos hδ hCp,(div_le_one hCp).mpr (by linarith [hC.1]),hδ.le,by linarith,by field_simp; rfl,?_⟩
  have hh:=Real.exp_le_exp.mpr he
  rw [Real.exp_log (by norm_num : (0:ℝ)<2049/2048)] at hh
  linarith

lemma bump_smoothOn_extension {U : Plane → ℝ} (hU : ContDiffOn ℝ ∞ U (ball 0 3)) :
    ∃V : Plane → ℝ,Smooth V ∧ HasCompactSupport V ∧
      (∀x∈ball (0:Plane) (11/4),V=ᶠ[𝓝 x]U) ∧
      (∀x,|V x|≤|U x|) ∧ (∀x,3≤‖x‖ → V x=0) := by
  let χ : ContDiffBump (0:Plane):=⟨11/4,23/8,by norm_num,by norm_num⟩
  let V : Plane → ℝ:=fun x=>χ x*U x
  have hc : tsupport χ⊆ball (0:Plane) 3 := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by norm_num)
  refine ⟨V,smooth_cutoff_mul isOpen_ball χ.contDiff hc hU,χ.hasCompactSupport.mul_right,?_,?_,?_⟩
  · intro x hx
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    have hy' : y∈closedBall (0:Plane) χ.rIn:=ball_subset_closedBall hy
    simp only [V,χ.one_of_mem_closedBall hy',one_mul]
  · intro x
    dsimp [V]; rw [abs_mul,abs_of_nonneg (χ.nonneg (x:=x))]
    exact mul_le_of_le_one_left (abs_nonneg _) (χ.le_one (x:=x))
  · intro x hx
    have hz : χ x=0:=χ.zero_of_le_dist (by simpa only [dist_zero_right] using (show χ.rOut≤‖x‖ by dsimp [χ]; linarith))
    simp only [V,hz,zero_mul]
end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma inner_L2_anchor {U : Plane → ℝ} (hU : Continuous U)
    (hI : 0<∫x in ball (0:Plane) (1/4),U x^2) :
    ∃y∈ball (0:Plane) (1/4),Real.sqrt (∫x in ball (0:Plane) (1/4),U x^2)/4≤|U y| := by
  let I:=∫x in ball (0:Plane) (1/4),U x^2
  have hn : 0≤Real.sqrt I/4:=by positivity
  have hv : volume.real (ball (0:Plane) (1/4))≤1 := by
    rw [measureReal_def,EuclideanSpace.volume_ball_fin_two]
    simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤1/4),ENNReal.toReal_ofReal Real.pi_pos.le]
    nlinarith [Real.pi_lt_four]
  by_contra he
  push Not at he
  have hb : ∀x∈ball (0:Plane) (1/4),U x^2≤(Real.sqrt I/4)^2 := by
    intro x hx
    have hh : |U x|≤Real.sqrt I/4:=(he x hx).le
    nlinarith [sq_abs (U x),abs_nonneg (U x)]
  have hi:=integral_mono_ae (continuous_sq_integrableOn_ball hU (1/4))
    (integrableOn_const (C:=((Real.sqrt I/4)^2)) measure_ball_ne_top)
    ((ae_restrict_mem measurableSet_ball).mono (fun x hx=>hb x hx))
  rw [integral_const,measureReal_def,Measure.restrict_apply_univ,←measureReal_def,smul_eq_mul] at hi
  have hh:=mul_le_mul_of_nonneg_right hv (sq_nonneg (Real.sqrt I/4))
  have hs:=Real.sq_sqrt hI.le
  dsimp [I] at hi hh ⊢
  nlinarith

lemma sq_integral_ball_mono {U : Plane → ℝ} (hU : Continuous U) {r R : ℝ} (hrR : r≤R) :
    (∫x in ball (0:Plane) r,U x^2)≤∫x in ball (0:Plane) R,U x^2 :=
  integral_mono_measure (Measure.restrict_mono_set volume (ball_subset_ball hrR))
    (Eventually.of_forall (fun x=>sq_nonneg (U x))) (continuous_sq_integrableOn_ball hU R)

theorem small_potential_L2_length : ∃ε L : ℝ,0<ε ∧ 0<L ∧
    ∀(U q : Plane → ℝ),ContDiffOn ℝ ∞ U (ball 0 3) → ContDiffOn ℝ ∞ q (ball 0 3) →
    (∀x∈ball (0:Plane) 3,euclideanLaplacian U x+q x*U x=0) →
    (∀x∈ball (0:Plane) 3,|q x|≤ε) →
    0<(∫x in ball (0:Plane) (1/4),U x^2) →
    Measure.hausdorffMeasure 1 {x | x∈ball (0:Plane) (1/60) ∧ U x=0}≤
      ENNReal.ofReal (L*(1+(Real.log (∫x in ball (0:Plane) (11/4),U x^2)-
        Real.log (∫x in ball (0:Plane) (1/4),U x^2))/2)) := by
  obtain ⟨C,ε,δ,hC,hε,hε1,hδ,hδ1,hsmall,hη⟩:=exists_local_smallness
  obtain ⟨L₀,hL₀,hL⟩:=normalized_small_potential_length
  obtain ⟨B,hB,hBb⟩:=small_potential_L2_interior
  have hBp : 0<B:=by linarith
  have hlogB : 0≤Real.log (4*B):=Real.log_nonneg (by linarith)
  refine ⟨ε,L₀*(1+Real.log (4*B)),hε,mul_pos hL₀ (by linarith),?_⟩
  intro U q hU hq he hqb hI
  obtain ⟨V,hV,-,hVe,-,-⟩:=bump_smoothOn_extension hU
  obtain ⟨Q,hQ,hcQ,hQe,hQb,hQs⟩:=bump_smoothOn_extension hq
  have hSP : SmallPotential C ε δ Q:=⟨hC,hε.le,hδ,hδ1,hsmall,hQ,hcQ,hQs,
    fun x hx=>(hQb x).trans (hqb x hx)⟩
  have hVE : ∀x∈ball (0:Plane) (11/4),euclideanLaplacian V x+Q x*V x=0 := by
    intro x hx
    rw [laplacian_germ (hVe x hx),(hVe x hx).eq_of_nhds,(hQe x hx).eq_of_nhds]
    exact he x (ball_subset_ball (by norm_num) hx)
  have hmass (r : ℝ) (hr : r≤11/4) :
      (∫x in ball (0:Plane) r,V x^2)=∫x in ball (0:Plane) r,U x^2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [(hVe x (ball_subset_ball hr hx)).eq_of_nhds]
  let I:=∫x in ball (0:Plane) (1/4),V x^2
  let O:=∫x in ball (0:Plane) (11/4),V x^2
  have hIp : 0<I:=by dsimp [I]; rwa [hmass (1/4) (by norm_num)]
  have hIO : I≤O:=sq_integral_ball_mono hV.continuous (by norm_num)
  have hOp : 0<O:=lt_of_lt_of_le hIp hIO
  let a:=Real.sqrt I/4
  have hap : 0<a:=div_pos (Real.sqrt_pos.2 hIp) (by norm_num)
  let S:=4*B*Real.sqrt O/Real.sqrt I
  have hS : 1≤S:=by
    apply (le_div_iff₀ (Real.sqrt_pos.2 hIp)).mpr
    have hroot:=Real.sqrt_le_sqrt hIO
    nlinarith [Real.sqrt_nonneg I,Real.sqrt_nonneg O]
  have hW : Smooth (fun x=>a⁻¹*V x):=contDiff_const.mul hV
  have hWE : ∀x∈ball (0:Plane) (5/2),euclideanLaplacian (fun y=>a⁻¹*V y) x+
      Q x*(a⁻¹*V x)=0 := by
    intro x hx
    rw [laplacian_const_mul hV]
    have hh:=hVE x (ball_subset_ball (by norm_num) hx)
    linear_combination a⁻¹*hh
  have hbV:=hBb V Q hV hQ hVE (fun x hx=>(hSP.bound x hx).trans hε1)
  have hWb : ∀x∈ball (0:Plane) (5/2),|a⁻¹*V x|≤S := by
    intro x hx
    rw [abs_mul,abs_of_pos (inv_pos.mpr hap)]
    have ht:=mul_le_mul_of_nonneg_left (hbV x hx) (inv_nonneg.mpr hap.le)
    exact ht.trans_eq (by dsimp [S,a]; ring)
  obtain ⟨y,hy,hyb⟩:=inner_L2_anchor hV.continuous hIp
  have han : ∃y∈ball (0:Plane) (1/4),1≤|a⁻¹*V y| := by
    refine ⟨y,hy,?_⟩
    rw [abs_mul,abs_of_pos (inv_pos.mpr hap),inv_mul_eq_div]
    exact (le_div_iff₀ hap).mpr (by simpa only [one_mul] using hyb)
  have hh:=hL hSP hη hW hWE S hS hWb han
  have hz : {x | x∈ball (0:Plane) (1/60) ∧ a⁻¹*V x=0}=
      {x | x∈ball (0:Plane) (1/60) ∧ U x=0} := by
    ext x
    by_cases hx : x∈ball (0:Plane) (1/60)
    · simp only [mem_ofPred_eq,hx,true_and,mul_eq_zero,inv_ne_zero hap.ne',false_or,
        (hVe x (ball_subset_ball (by norm_num) hx)).eq_of_nhds]
    · simp only [mem_ofPred_eq,hx,false_and]
  rw [hz] at hh
  have heS : Real.log S=Real.log (4*B)+(Real.log O-Real.log I)/2 := by
    dsimp [S]
    rw [Real.log_div (mul_ne_zero (by positivity) (Real.sqrt_pos.2 hOp).ne')
      (Real.sqrt_pos.2 hIp).ne',Real.log_mul (by positivity : 4*B≠0) (Real.sqrt_pos.2 hOp).ne',
      Real.log_sqrt hOp.le,Real.log_sqrt hIp.le]
    ring
  have hE : 0≤(Real.log O-Real.log I)/2:=by have:=Real.log_le_log hIp hIO; linarith
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  rw [heS]
  rw [←hmass (11/4) le_rfl,←hmass (1/4) (by norm_num)]
  change L₀*(1+(Real.log (4*B)+(Real.log O-Real.log I)/2))≤L₀*(1+Real.log (4*B))*(1+(Real.log O-Real.log I)/2)
  nlinarith [mul_nonneg hL₀.le (mul_nonneg hlogB hE)]
end SharpNodal.Profiles

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_InteriorMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
namespace SharpNodal.Profiles
open Carleman

lemma plainMass_mono (U : Plane → ℝ) {E F : Set Plane} (h : E⊆F) : plainMass U E≤plainMass U F:=lintegral_mono_set h
lemma plainMass_center (U : Plane → ℝ) (y : Plane) (r : ℝ) :
    plainMass U (ball y r)=centeredMass 0 U y r := by simp [plainMass,centeredMass]

end SharpNodal.Profiles

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_ConformalLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric TopologicalSpace
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal Bundle
open Set Filter Metric MeasureTheory Bundle Manifold
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Bundle
open Set Filter Metric Bundle Manifold
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff ENNReal NNReal Bundle Manifold
open Set Filter Metric MeasureTheory Bundle Manifold

noncomputable section
open scoped Topology ContDiff ENNReal NNReal
open Set Filter MeasureTheory Metric
namespace SharpNodal.Profiles
open Carleman
lemma centeredMass_integral {U : Plane → ℝ} {R r : ℝ}
    (hU : ContDiffOn ℝ ∞ U (ball 0 R)) (hr : r<R) :
    centeredMass 0 U 0 r=ENNReal.ofReal (∫x in ball (0:Plane) r,U x^2) := by
  have hi : IntegrableOn (fun x=>U x^2) (ball (0:Plane) r) :=
    ((hU.continuousOn.pow 2).mono (closedBall_subset_ball hr)).integrableOn_compact
      (isCompact_closedBall (0:Plane) r) |>.mono_set ball_subset_closedBall
  simp only [centeredMass,inner_zero_left,neg_zero,Real.exp_zero,one_mul]
  exact (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x=>sq_nonneg _))).symm

lemma massExcess_mono {a b A B : ℝ≥0∞} (hBa : B≤b) (haA : a≤A)
    (hba : b≤a) (hB : B≠0) (hA : A≠⊤) :
    massExcess a b ≤ massExcess A B := by
  have ha : a≠⊤:=ne_top_of_le_ne_top hA haA
  have hb : b≠⊤:=ne_top_of_le_ne_top ha hba
  have hBt : B≠⊤:=ne_top_of_le_ne_top hb hBa
  have hb0 : b≠0:=ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hB) hBa)
  have ha0 : a≠0:=ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hb0) hba)
  have hbr : 0<b.toReal:=ENNReal.toReal_pos hb0 hb
  have har : 0<a.toReal:=ENNReal.toReal_pos ha0 ha
  have hBr : 0<B.toReal:=ENNReal.toReal_pos hB hBt
  unfold massExcess
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Real.log_le_log (div_pos har hbr)
  exact (div_le_div_of_nonneg_right (ENNReal.toReal_mono hA haA) hbr.le).trans
    (div_le_div_of_nonneg_left ENNReal.toReal_nonneg hBr (ENNReal.toReal_mono hb hBa))

lemma unit_wave_length : ∃δ L : ℝ,0<δ ∧ 0<L ∧
    ∀{Cp a₀ : ℝ} (D : UnitWave Cp a₀),D.K^2*Cp≤δ →
      Measure.hausdorffMeasure 1 {x | x∈ball (0:Plane) 1 ∧ D.U x=0}≤
        ENNReal.ofReal (L*(1+D.excess 0)) := by
  obtain ⟨ε,L,hε,hL,hmain⟩:=small_potential_L2_length
  refine ⟨ε/3600,60*L,by positivity,by positivity,?_⟩
  intro Cp a₀ D hsmall
  let F:=rescaleMap (0:Plane) 60
  let V:=D.U∘F
  let q:=fun x=>3600*D.K^2*D.p (F x)
  have hF : MapsTo F (ball 0 3) (ball 0 1000) := by
    intro x hx
    simp only [F,rescaleMap,zero_add,mem_ball_zero_iff,norm_smul,Real.norm_eq_abs] at *
    norm_num at *; linarith
  have hV : ContDiffOn ℝ ∞ V (ball 0 3):=
    D.smooth_U.comp (smooth_rescaleMap 0 60).contDiffOn hF
  have hq : ContDiffOn ℝ ∞ q (ball 0 3):=
    contDiffOn_const.mul (D.smooth_p.comp (smooth_rescaleMap 0 60).contDiffOn hF)
  have he : ∀x∈ball (0:Plane) 3,euclideanLaplacian V x+q x*V x=0 := by
    intro x hx
    rw [laplacian_rescale_local isOpen_ball D.smooth_U 0 60 x (hF hx)]
    have hh:=D.equation _ (hF hx)
    dsimp [V,q] at *
    nlinarith only [hh]
  have hqb : ∀x∈ball (0:Plane) 3,|q x|≤ε := by
    intro x hx
    dsimp [q]
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤3600*D.K^2)]
    have hh:=mul_le_mul_of_nonneg_left (D.coefficient_bound _ (hF hx))
      (by positivity : 0≤3600*D.K^2)
    nlinarith
  have hscale (r : ℝ) : centeredMass 0 V 0 r=
      ENNReal.ofReal (60^2:ℝ)⁻¹*centeredMass 0 D.U 0 (60*r) := by
    simpa only [smul_zero,rescaleMap,zero_add] using
      centeredMass_rescale (0:Plane) D.U 0 0 (by norm_num : (0:ℝ)<60) r
  have h15 : centeredMass 0 D.U 0 15≠0:=ne_of_gt
    (lt_of_lt_of_le (pos_iff_ne_zero.mpr D.inner_nonzero) (centeredMass_mono _ _ _ (by norm_num)))
  have hI : 0<(∫x in ball (0:Plane) (1/4),V x^2) := by
    apply ENNReal.ofReal_pos.mp
    rw [←centeredMass_integral hV (by norm_num),hscale]
    norm_num
    exact pos_iff_ne_zero.mpr h15
  have hlen:=hmain V q hV hq he hqb hI
  have hdiff : (Real.log (∫x in ball (0:Plane) (11/4),V x^2)-
      Real.log (∫x in ball (0:Plane) (1/4),V x^2))/2=
      massExcess (centeredMass 0 V 0 (11/4)) (centeredMass 0 V 0 (1/4)) := by
    rw [centeredMass_integral hV (by norm_num),centeredMass_integral hV (by norm_num)]
    rw [massExcess,ENNReal.toReal_ofReal (integral_nonneg fun x=>sq_nonneg _),
      ENNReal.toReal_ofReal hI.le,Real.log_div]
    · exact ne_of_gt (hI.trans_le (integral_mono_measure
        (Measure.restrict_mono_set volume (ball_subset_ball (by norm_num)))
        (Eventually.of_forall (fun x=>sq_nonneg _))
        (((hV.continuousOn.pow 2).mono (closedBall_subset_ball (by norm_num))).integrableOn_compact
          (isCompact_closedBall (0:Plane) (11/4)) |>.mono_set ball_subset_closedBall)))
    · exact hI.ne'
  rw [hdiff] at hlen
  have hexc : massExcess (centeredMass 0 V 0 (11/4)) (centeredMass 0 V 0 (1/4))≤D.excess 0 := by
    rw [hscale,hscale,massExcess_mul_left _ _ _ (by norm_num) (by norm_num)]
    norm_num only [show (60:ℝ)*(11/4)=165 by norm_num,show (60:ℝ)*(1/4)=15 by norm_num]
    simp only [UnitWave.excess,smul_zero]
    exact massExcess_mono (centeredMass_mono _ _ _ (by norm_num))
      (centeredMass_mono _ _ _ (by norm_num)) (centeredMass_mono _ _ _ (by norm_num))
      D.inner_nonzero D.outer_finite
  let T:={x : Plane | x∈ball (0:Plane) (1/60) ∧ V x=0}
  have hset : {x : Plane | x∈ball (0:Plane) 1 ∧ D.U x=0}⊆F '' T := by
    intro x hx
    refine ⟨(1/60:ℝ) • x,⟨?_,?_⟩,?_⟩
    · apply mem_ball_zero_iff.mpr
      rw [norm_smul,Real.norm_eq_abs]
      norm_num
      have hh:=mem_ball_zero_iff.mp hx.1
      linarith
    · simpa [V,F,rescaleMap,smul_smul] using hx.2
    · simp [F,rescaleMap,smul_smul]
  have hLips:=(rescaleMap_lipschitz (0:Plane) (by norm_num : (0:ℝ)≤60)).hausdorffMeasure_image_le
    (d:=1) (by norm_num) T
  norm_num only [ENNReal.rpow_one,Real.toNNReal_ofNat,ENNReal.coe_ofNat] at hLips
  apply (measure_mono hset).trans (hLips.trans _)
  apply (mul_le_mul' le_rfl hlen).trans
  rw [←ENNReal.ofReal_ofNat (n:=60),←ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith
end SharpNodal.Profiles

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_PlaneLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric TopologicalSpace
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal Bundle
open Set Filter Metric MeasureTheory Bundle Manifold
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Bundle
open Set Filter Metric Bundle Manifold
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff ENNReal NNReal Bundle Manifold
open Set Filter Metric MeasureTheory Bundle Manifold
open scoped Topology ContDiff ENNReal NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators
open Set Filter MeasureTheory Metric

namespace SharpNodal.Profiles
lemma grid_ball_cover {N : ℕ} (hN : 0<N) {x : Plane} (hx : x∈ball (0:Plane) (1/4)) :
    ∃p : GridIndex N,x∈ball (gridCenter N p) (N:ℝ)⁻¹ := by
  have hNr : 0<(N:ℝ):=Nat.cast_pos.mpr hN
  have hxc (j : Fin 2) : |x j|<1/4:= (plane_component_norm_le x j).trans_lt (mem_ball_zero_iff.mp hx)
  have hnonneg (j : Fin 2) : 0≤(N:ℝ)*(x j+1/2) := by
    have hh:=(abs_lt.mp (hxc j)).1
    exact mul_nonneg hNr.le (by linarith)
  have hlt (j : Fin 2) : (N:ℝ)*(x j+1/2)<N := by
    have hh:=(abs_lt.mp (hxc j)).2
    nlinarith
  let p : GridIndex N:=fun j=>⟨⌊(N:ℝ)*(x j+1/2)⌋₊,(Nat.floor_lt (hnonneg j)).mpr (hlt j)⟩
  refine ⟨p,?_⟩
  have hd (j : Fin 2) : |(x-gridCenter N p) j|≤(N:ℝ)⁻¹/2 := by
    have hl:=Nat.floor_le (hnonneg j)
    have hu:=Nat.lt_floor_add_one ((N:ℝ)*(x j+1/2))
    change (p j:ℝ)≤(N:ℝ)*(x j+1/2) at hl
    change (N:ℝ)*(x j+1/2)<(p j:ℝ)+1 at hu
    change |x j-(((p j:ℝ)+1/2)/(N:ℝ)-1/2)|≤(N:ℝ)⁻¹/2
    have he : x j-(((p j:ℝ)+1/2)/(N:ℝ)-1/2)=
        ((N:ℝ)*(x j+1/2)-(p j:ℝ)-1/2)/(N:ℝ) := by field_simp; ring
    rw [he,abs_div,abs_of_pos hNr]
    have hb : |(N:ℝ)*(x j+1/2)-(p j:ℝ)-1/2|≤1/2:=by rw [abs_le]; constructor <;> linarith
    apply (div_le_div_of_nonneg_right hb hNr.le).trans_eq
    ring
  have h0:=pow_le_pow_left₀ (abs_nonneg _) (hd 0) 2
  have h1:=pow_le_pow_left₀ (abs_nonneg _) (hd 1) 2
  rw [sq_abs] at h0 h1
  have hn:=EuclideanSpace.real_norm_sq_eq (x-gridCenter N p)
  rw [Fin.sum_univ_two] at hn
  rw [mem_ball,dist_eq_norm]
  apply (sq_lt_sq₀ (norm_nonneg _) (inv_nonneg.mpr hNr.le)).mp
  have hs : ‖x-gridCenter N p‖^2≤((N:ℝ)⁻¹)^2/2:=by nlinarith only [h0,h1,hn]
  exact hs.trans_lt (by nlinarith only [sq_pos_of_pos (inv_pos.mpr hNr)])

lemma wordIndex_surjective (A n : ℕ) : Function.Surjective (wordIndex A n) := by
  exact ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨wordIndex_injective A n,by simp [GridWord,GridIndex,←pow_mul,Nat.mul_comm]⟩).2

lemma word_ball_cover {A : ℕ} (hA : 0<A) (n : ℕ) {x : Plane} (hx : x∈ball (0:Plane) (1/4)) :
    ∃w : GridWord A n,x∈ball (wordCenter A n w) ((A:ℝ)^n)⁻¹ := by
  obtain ⟨p,hp⟩:=grid_ball_cover (pow_pos hA _) hx
  obtain ⟨w,rfl⟩:=wordIndex_surjective A n p
  exact ⟨w,by simpa only [wordCenter,Nat.cast_pow] using hp⟩

lemma word_margin {A : ℕ} (hA : 10000<A) (n : ℕ) (w : GridWord A n) :
    ‖wordCenter A n w‖+1000*((A:ℝ)^n)⁻¹≤1000 := by
  have hAr : (10000:ℝ)<A:=by exact_mod_cast hA
  cases n with
  | zero => simp [wordCenter_zero]
  | succ n =>
    have hc:=gridCenter_norm (pow_pos (by omega : 0<A) _) (wordIndex A (n+1) w)
    have hp : (A:ℝ)≤(A:ℝ)^(n+1):=le_self_pow₀ (by linarith) (by omega)
    have hi : ((A:ℝ)^(n+1))⁻¹≤(A:ℝ)⁻¹:=inv_anti₀ (by linarith) hp
    have hiA : (A:ℝ)⁻¹≤1/10000:= (inv_le_comm₀ (by linarith) (by norm_num)).mpr (by norm_num; linarith)
    change ‖wordCenter A (n+1) w‖≤1 at hc
    linarith

lemma pathGrowth_rescale {A : ℕ} (hA : 0<A) (n : ℕ) (U : Plane → ℝ) (K : ℝ) (w : GridWord A n) :
    pathGrowth A n U K w=fieldGrowth (U∘rescaleMap (wordCenter A n w) ((A:ℝ)^n)⁻¹) (K/(A:ℝ)^n) := by
  induction n generalizing U K with
  | zero =>
    simp only [pathGrowth,pow_zero,inv_one,div_one,wordCenter_zero]
    congr 1
    funext x
    simp [rescaleMap]
  | succ n ih =>
    rw [pathGrowth,ih]
    have he:=word_rescale_succ hA n w
    simp only [inv_pow] at he
    rw [he,←Function.comp_assoc]
    congr 1
    rw [pow_succ,div_div,mul_comm (A:ℝ) ((A:ℝ)^n)]
end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal NNReal BigOperators
open Set Filter Metric MeasureTheory
namespace SharpNodal.Profiles
lemma localized_zero_image {U : Plane → ℝ} (y : Plane) {r : ℝ} (hr : 0 < r) :
    {x | x∈ball y r ∧ U x=0}⊆rescaleMap y r '' {x | x∈ball (0:Plane) 1 ∧ (U∘rescaleMap y r) x=0} := by
  intro x hx
  refine ⟨r⁻¹ • (x-y),⟨?_,?_⟩,?_⟩
  · rw [mem_ball_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    have hh:=hx.1
    rw [mem_ball,dist_eq_norm] at hh
    exact (inv_mul_lt_iff₀ hr).mpr (by simpa using hh)
  · simpa [Function.comp_apply,rescaleMap,smul_smul,hr.ne'] using hx.2
  · simp [rescaleMap,smul_smul,hr.ne']

lemma terminal_grid_length {A : ℕ} (hA : 10000<A) {Cp a₀ L δ C : ℝ}
    (ha₀ : 0<a₀) (hL : 0≤L) (hC : 0≤C)
    (hlen : ∀{Cp a₀ : ℝ} (D : UnitWave Cp a₀),D.K^2*Cp≤δ →
      Measure.hausdorffMeasure 1 {x | x∈ball (0:Plane) 1 ∧ D.U x=0}≤ENNReal.ofReal (L*(1+D.excess 0)))
    (D : ScaledWave Cp a₀) (n : ℕ)
    (hbottom : a₀≤D.K/(A:ℝ)^n) (hsmall : (D.K/(A:ℝ)^n)^2*Cp≤δ)
    (hmean : (𝔼 w : GridWord A n,pathGrowth A n D.U D.K w)≤C)
    (hmass : ∀y r,0 < r → ball y r⊆ball (0:Plane) 1000 → centeredMass 0 D.U y r≠0) :
    Measure.hausdorffMeasure 1 {x | x∈ball (0:Plane) (1/4) ∧ D.U x=0}≤
      ENNReal.ofReal (L*(a₀⁻¹+C)*D.K) := by
  have hAp : 0<A:=by omega
  have hAr : (1:ℝ)≤A:=by exact_mod_cast (show 1≤A by omega)
  let N : ℝ:=(A:ℝ)^n
  let r : ℝ:=N⁻¹
  have hN : 0<N:=pow_pos (by positivity) _
  have hN1 : 1≤N:=one_le_pow₀ hAr
  have hr : 0 < r:=inv_pos.mpr hN
  have hr1 : r≤1:=inv_le_one_of_one_le₀ hN1
  have hK : 0<D.K:=ha₀.trans_le D.frequency_lower
  have hmargin (w : GridWord A n) : ‖wordCenter A n w‖+1000*r≤1000:=word_margin hA n w
  have hmaps (w : GridWord A n) : ball (wordCenter A n w) (1000*r)⊆ball (0:Plane) 1000 := by
    intro x hx
    have hn : ‖x‖≤‖x-wordCenter A n w‖+‖wordCenter A n w‖:=by simpa using norm_add_le (x-wordCenter A n w) (wordCenter A n w)
    rw [mem_ball,dist_eq_norm] at hx
    rw [mem_ball_zero_iff]
    linarith [hmargin w]
  have hin (w : GridWord A n) : centeredMass 0 D.U (wordCenter A n w) r≠0:=
    hmass _ _ hr ((ball_subset_ball (by linarith)).trans (hmaps w))
  have hout (w : GridWord A n) : centeredMass 0 D.U (wordCenter A n w) (1000*r)≠⊤ := by
    apply ne_top_of_le_ne_top D.outer_finite
    rw [←plainMass_center,←plainMass_center]
    exact plainMass_mono _ (hmaps w)
  have hbot : a₀≤D.K*r:=by simpa only [r,N,div_eq_mul_inv] using hbottom
  let E (w : GridWord A n):=D.rebase (wordCenter A n w) r hr hr1 (hmargin w) hbot (hin w) (hout w)
  have hexc (w : GridWord A n) : (E w).excess 0=(D.K*r)*pathGrowth A n D.U D.K w := by
    have hp : pathGrowth A n D.U D.K w=(E w).growth 0 := by
      rw [pathGrowth_rescale hAp,UnitWave.growth_zero]
      simp only [E,ScaledWave.rebase,r,N,div_eq_mul_inv]
    rw [hp,UnitWave.growth]
    exact (mul_div_cancel₀ _ (mul_ne_zero hK.ne' hr.ne')).symm
  have hg (w : GridWord A n) : 0≤pathGrowth A n D.U D.K w := by
    have hh:=(E w).excess_nonneg 0
    rw [hexc] at hh
    exact nonneg_of_mul_nonneg_right hh (mul_pos hK hr)
  have hpiece (w : GridWord A n) :
      Measure.hausdorffMeasure 1 {x | x∈ball (wordCenter A n w) r ∧ D.U x=0}≤
      ENNReal.ofReal (r*L*(1+D.K*r*pathGrowth A n D.U D.K w)) := by
    have hl:=hlen (E w).toUnitWave (by simpa only [E,ScaledWave.rebase,div_eq_mul_inv,r,N] using hsmall)
    rw [hexc] at hl
    have hLip:=(rescaleMap_lipschitz (wordCenter A n w) hr.le).hausdorffMeasure_image_le
      (d:=1) (by norm_num) {x | x∈ball (0:Plane) 1 ∧ (E w).U x=0}
    rw [ENNReal.rpow_one] at hLip
    change _≤ENNReal.ofReal r*_ at hLip
    apply (measure_mono (localized_zero_image (U:=D.U) (wordCenter A n w) hr)).trans (hLip.trans _)
    apply (mul_le_mul' le_rfl hl).trans
    rw [←ENNReal.ofReal_mul hr.le]
    apply ENNReal.ofReal_le_ofReal
    exact le_of_eq (by ring)
  have hcover : {x | x∈ball (0:Plane) (1/4) ∧ D.U x=0}⊆
      ⋃w : GridWord A n,{x | x∈ball (wordCenter A n w) r ∧ D.U x=0} := by
    intro x hx
    obtain ⟨w,hw⟩:=word_ball_cover hAp n hx.1
    exact mem_iUnion.mpr ⟨w,hw,hx.2⟩
  apply (measure_mono hcover).trans (measure_iUnion_fintype_le _ _ |>.trans ((Finset.sum_le_sum (fun w _=>hpiece w)).trans _))
  rw [←ENNReal.ofReal_sum_of_nonneg (fun w _=>by have := hg w; positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hcard : (Fintype.card (GridWord A n):ℝ)=N^2:=by rw [gridWord_card]; simp [N]
  have hsum : (∑w : GridWord A n,pathGrowth A n D.U D.K w)≤N^2*C := by
    rw [Fintype.expect_eq_sum_div_card,hcard] at hmean
    exact ((div_le_iff₀ (sq_pos_of_pos hN)).mp hmean).trans_eq (mul_comm _ _)
  have hNbound : N≤D.K/a₀ := by
    apply (le_div_iff₀ ha₀).mpr
    exact (mul_comm N a₀).trans_le ((le_div_iff₀ hN).mp hbottom)
  calc
    _ = r*L*(N^2+D.K*r*∑w : GridWord A n,pathGrowth A n D.U D.K w) := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard,←Finset.mul_sum]
      simp only [mul_one]
    _ ≤ r*L*(N^2+D.K*r*(N^2*C)) := by gcongr
    _ = L*(N+D.K*C) := by dsimp [r]; field_simp
    _ ≤ L*(D.K/a₀+D.K*C) := by gcongr
    _ = L*(a₀⁻¹+C)*D.K := by ring
end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal BigOperators
open Set Filter MeasureTheory Metric
namespace SharpNodal.Profiles

lemma uniform_plane_length_oai {Cp T : ℝ} (hCp : 0≤Cp) (hT : 0<T) (Cinit : ℝ) :
    ∃a₀ B : ℝ,0<a₀ ∧ a₀≤T ∧ 0≤B ∧ ∀D : ScaledWave Cp a₀,
      D.growth 0≤Cinit →
      (∀y r,0 < r → ball y r⊆ball (0:Plane) 1000 → centeredMass 0 D.U y r≠0) →
      Measure.hausdorffMeasure 1 {x | x∈ball (0:Plane) (1/4) ∧ D.U x=0}≤ENNReal.ofReal (B*D.K) := by
  obtain ⟨δ,L,hδ,hL,hlen⟩:=unit_wave_length
  obtain ⟨A,hA,hmean⟩:=Grid.uniform_terminal_growth
  have hAr : (1:ℝ)<A:=by exact_mod_cast (show 1<A by omega)
  have hAp : 0<(A:ℝ):=by linarith
  let a₀:=min T (min 1 (δ/((A:ℝ)^2*(Cp+1))))
  have ha₀ : 0<a₀:=lt_min hT (lt_min (by norm_num) (by positivity))
  have haT : a₀≤T:=min_le_left _ _
  have ha1 : a₀≤1:=(min_le_right _ _).trans (min_le_left _ _)
  have had : a₀≤δ/((A:ℝ)^2*(Cp+1)):=(min_le_right _ _).trans (min_le_right _ _)
  have hsmall : ((A:ℝ)*a₀)^2*Cp≤δ := by
    have hd:=(le_div_iff₀ (by positivity : 0<(A:ℝ)^2*(Cp+1))).mp had
    have ha2 : a₀^2≤a₀:=by nlinarith
    calc
      _ = (A:ℝ)^2*a₀^2*Cp := by ring
      _ ≤ (A:ℝ)^2*a₀*(Cp+1) := by gcongr; linarith
      _ ≤ δ := by nlinarith only [hd]
  obtain ⟨C,hC,hCb⟩:=hmean Cp hCp a₀ ha₀ Cinit
  refine ⟨a₀,L*(a₀⁻¹+C),ha₀,haT,by positivity,?_⟩
  intro D hinit hmass
  have hK : 0<D.K:=ha₀.trans_le D.frequency_lower
  obtain ⟨n,hn,hn'⟩:=exists_nat_pow_near ((one_le_div ha₀).mpr D.frequency_lower) hAr
  have hpow : 0<(A:ℝ)^n:=pow_pos hAp _
  have hbottom : a₀≤D.K/(A:ℝ)^n := by
    apply (le_div_iff₀ hpow).mpr
    have hh:=(le_div_iff₀ ha₀).mp hn
    nlinarith only [hh]
  have hupper : D.K/(A:ℝ)^n<(A:ℝ)*a₀ := by
    apply (div_lt_iff₀ hpow).mpr
    have hh:=(div_lt_iff₀ ha₀).mp hn'
    rw [pow_succ] at hh
    nlinarith only [hh]
  have hterminal : (D.K/(A:ℝ)^n)^2*Cp≤δ :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (div_pos hK hpow).le hupper.le 2) hCp).trans hsmall
  exact terminal_grid_length hA ha₀ hL.le hC hlen D n hbottom hterminal (hCb D n hinit hbottom) hmass
end SharpNodal.Profiles

end
end
end

end OAI
end

theorem solution : type_of% @OAI.SharpNodal.Profiles.uniform_plane_length_oai := @OAI.SharpNodal.Profiles.uniform_plane_length_oai
