-- Prove2me | solution 1 for OAI.SharpNodal.Profiles.sup_profile_le_local
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:24:08.730559+00:00
-- url     : https://prove2.me/submissions/dff72974-0234-41da-959d-e51f5e06dad0

import Mathlib
import Definitions.Def_NodalLength
import Definitions.Def_OAIQ4Nl000

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
-- module Solutions.OAIQ4_Nl.NodalLength_MassComparison
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

noncomputable section
open scoped Topology ENNReal
open MeasureTheory Filter Set
namespace SharpNodal.Profiles

lemma ereal_pos_mul_lt_coe_iff {c : ℝ} (hc : 0 < c) (a : EReal) (b : ℝ) :
    (c:EReal)*a < (b:EReal) ↔ a < ((b/c : ℝ):EReal) := by
  cases a using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hc]
  | top => simp [EReal.coe_mul_top_of_pos hc]
  | coe a =>
    rw [← EReal.coe_mul, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    simp only [lt_div_iff₀ hc, mul_comm]

lemma ereal_coe_lt_pos_mul_iff {c : ℝ} (hc : 0 < c) (a : EReal) (b : ℝ) :
    (b:EReal) < (c:EReal)*a ↔ ((b/c : ℝ):EReal) < a := by
  cases a using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hc]
  | top => simp [EReal.coe_mul_top_of_pos hc]
  | coe a =>
    rw [← EReal.coe_mul, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    simp only [div_lt_iff₀ hc, mul_comm]

lemma logRate_lt_iff {S a : ℝ} (hS : 0<S) (m : ℝ≥0∞) :
    logRate S m < (a:EReal) ↔ m < ENNReal.ofReal (Real.exp (2*S*a)) := by
  rw [logRate, ereal_pos_mul_lt_coe_iff (inv_pos.mpr (by positivity : 0<2*S))]
  rw [div_inv_eq_mul, show a*(2*S)=2*S*a by ring]
  rw [show ((2*S*a : ℝ):EReal)=(ENNReal.ofReal (Real.exp (2*S*a))).log by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]]
  exact ENNReal.log_lt_log_iff

lemma lt_logRate_iff {S a : ℝ} (hS : 0<S) (m : ℝ≥0∞) :
    (a:EReal) < logRate S m ↔ ENNReal.ofReal (Real.exp (2*S*a)) < m := by
  rw [logRate, ereal_coe_lt_pos_mul_iff (inv_pos.mpr (by positivity : 0<2*S))]
  rw [div_inv_eq_mul, show a*(2*S)=2*S*a by ring]
  rw [show ((2*S*a : ℝ):EReal)=(ENNReal.ofReal (Real.exp (2*S*a))).log by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]]
  exact ENNReal.log_lt_log_iff

lemma logRate_le_iff {S a : ℝ} (hS : 0<S) (m : ℝ≥0∞) :
    logRate S m ≤ (a:EReal) ↔ m ≤ ENNReal.ofReal (Real.exp (2*S*a)) := by
  simpa only [not_lt] using not_congr (lt_logRate_iff (a:=a) hS m)

end SharpNodal.Profiles

end
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
-- module Solutions.OAIQ4_Nl.NodalLength_ProfileExtraction
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

namespace SharpNodal.Profiles

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]

lemma basisProfile_le (ell : countableBasis X → EReal) (i : countableBasis X)
    {x : X} (hx : x∈i.val) : basisProfile ell x≤ell i :=
  (iInf_le_of_le i (iInf_le_of_le hx le_rfl))

end SharpNodal.Profiles
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

lemma inv_norm_integrableOn_ball (R : ℝ) :
    IntegrableOn (fun x : Plane => ‖x‖⁻¹) (Metric.ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (α:=1) (C:=1) (by simp [Plane]) (by simp [Plane])
    _ (measurable_id.norm.inv.aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Pi.inv_apply,id_eq,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    Real.rpow_neg_one,one_mul,le_refl]

end SharpNodal.Profiles

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

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
namespace SharpNodal.Profiles
open Carleman

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

namespace SharpNodal.Profiles

variable {X : Type*}

lemma supMass_mono (u : X → ℝ) {s t : Set X} (h : s⊆t) : supMass u s≤ supMass u t := by
  exact iSup₂_mono' fun x hx=>⟨x,h hx,le_rfl⟩

lemma supMass_le {u : X → ℝ} {s : Set X} {a : ℝ≥0∞} :
    supMass u s≤a ↔ ∀x∈s,ENNReal.ofReal ((u x)^2)≤a := by
  simp only [supMass,iSup_le_iff]

variable [TopologicalSpace X] [SecondCountableTopology X]

lemma supProfile_le_of_local {u : ℕ → X → ℝ} {S : ℕ → ℝ} {ell : countableBasis X → EReal}
    (hS : ∀j,0<S j)
    (hlim : ∀i : countableBasis X,Tendsto (fun j=>logRate (S j) (supMass (u j) i.val)) atTop (𝓝 (ell i)))
    {x : X} {a : ℝ} (h : SupLocalBound u S x a) : basisProfile ell x≤(a:EReal) := by
  obtain ⟨G,hG,hxG,hb⟩:=h
  obtain ⟨U,hU,hxU,hUG⟩:=(isBasis_countableBasis X).exists_subset_of_mem_open hxG hG
  let i : countableBasis X:=⟨U,hU⟩
  apply (basisProfile_le ell i hxU).trans
  apply le_of_tendsto (hlim i)
  filter_upwards [hb] with j hj
  exact (logRate_le_iff (hS j) _).mpr ((supMass_mono _ hUG).trans hj)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
namespace SharpNodal.Profiles
open Carleman

lemma bounded_potential_L2_interior : ∃C : ℝ,1≤C ∧ ∀(U q : Plane → ℝ),Smooth U → Smooth q →
    ∀Q : ℝ,1≤Q →
    (∀x∈ball (0:Plane) (11/4),euclideanLaplacian U x+q x*U x=0) →
    (∀x∈ball (0:Plane) 3,|q x|≤Q) →
    ∀x∈ball (0:Plane) (5/2),|U x|≤C*Q*Real.sqrt (∫y in ball (0:Plane) (11/4),U y^2) := by
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
  intro U q hU hq Q hQ1 he hb x hx
  have hQ0 : 0≤Q:=by linarith
  have hx' : ‖x‖+(1/4:ℝ)<11/4:=by have:=mem_ball_zero_iff.mp hx; linarith
  have hqU:=kernel_L2_bound hQ (hq.continuous.mul hU.continuous) hx'
    (fun y hy=>logParametrix_zero hy.le)
  have hKU:=kernel_L2_bound hK hU.continuous hx' (fun y hy=>parametrixKernel_zero hy)
  have hsq : (∫y in ball (0:Plane) (11/4),(q y*U y)^2)≤Q^2*(∫y in ball (0:Plane) (11/4),U y^2) := by
    rw [←integral_const_mul]
    apply integral_mono_ae (continuous_sq_integrableOn_ball (hq.continuous.mul hU.continuous) _) ((continuous_sq_integrableOn_ball hU.continuous _).const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hyb:=hb y (ball_subset_ball (by norm_num) hy)
    have hq2 : q y^2≤Q^2:=by have:=abs_nonneg (q y); nlinarith [sq_abs (q y)]
    change (q y*U y)^2≤_
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right hq2 (sq_nonneg _)
  have hsqrt:=Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul (sq_nonneg Q),Real.sqrt_sq hQ0] at hsqrt
  have hqU':=hqU.trans (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _))
  change |rconv logParametrix (fun y=>q y*U y) x|≤_ at hqU'
  have hKU' : |rconv parametrixKernel U x|≤Real.sqrt (∫y,parametrixKernel y^2)*(Q*Real.sqrt (∫y in ball (0:Plane) (11/4),U y^2)) := by
    apply hKU.trans
    gcongr
    exact le_mul_of_one_le_left (Real.sqrt_nonneg _) hQ1
  have hei:=small_potential_parametrix hU hq he hx
  have hn:=abs_add_le (-rconv logParametrix (fun y=>q y*U y) x) (-rconv parametrixKernel U x)
  rw [←sub_eq_add_neg,←hei,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi),abs_neg,abs_neg] at hn
  have hpos : 0<2*Real.pi:=by positivity
  have hh : |U x|≤(2*Real.pi)⁻¹*N*Q*Real.sqrt (∫y in ball (0:Plane) (11/4),U y^2) := by
    calc
      |U x|≤(N*Q*Real.sqrt (∫y in ball (0:Plane) (11/4),U y^2))/(2*Real.pi) := by
        apply (le_div_iff₀ hpos).mpr
        dsimp [N]; nlinarith only [hn,hqU',hKU']
      _ = _ := by ring
  exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hQ0) (Real.sqrt_nonneg _))
end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
namespace SharpNodal.Profiles
open Carleman

lemma bounded_potential_supMass : ∃C : ℝ,0<C ∧ ∀(U q : Plane → ℝ),
    ContDiffOn ℝ ∞ U (ball 0 3) → ContDiffOn ℝ ∞ q (ball 0 3) → ∀Q : ℝ,1≤Q →
    (∀x∈ball (0:Plane) 3,euclideanLaplacian U x+q x*U x=0) →
    (∀x∈ball (0:Plane) 3,|q x|≤Q) →
    supMass U (ball 0 2)≤ENNReal.ofReal (C*Q^2)*centeredMass 0 U 0 (11/4) := by
  obtain ⟨C,hC,hCb⟩:=bounded_potential_L2_interior
  refine ⟨C ^ 2,sq_pos_of_pos (by linarith),?_⟩
  intro U q hU hq Q hQ he hb
  obtain ⟨V,hV,-,hVe,-,-⟩:=bump_smoothOn_extension hU
  obtain ⟨P,hP,-,hPe,hPb,-⟩:=bump_smoothOn_extension hq
  have hVP : ∀x∈ball (0:Plane) (11/4),euclideanLaplacian V x+P x*V x=0 := by
    intro x hx
    rw [laplacian_germ (hVe x hx),(hVe x hx).eq_of_nhds,(hPe x hx).eq_of_nhds]
    exact he x (ball_subset_ball (by norm_num) hx)
  have hI : ENNReal.ofReal (∫x in ball (0:Plane) (11/4),V x^2)=centeredMass 0 U 0 (11/4) := by
    rw [ofReal_integral_eq_lintegral_ofReal (continuous_sq_integrableOn_ball hV.continuous _) (Eventually.of_forall fun x=>sq_nonneg _)]
    apply setLIntegral_congr_fun measurableSet_ball
    intro x hx
    simp only [inner_zero_left,neg_zero,Real.exp_zero,one_mul]
    rw [(hVe x hx).eq_of_nhds]
  apply supMass_le.mpr
  intro x hx
  have hh:=hCb V P hV hP Q hQ hVP (fun y hy=>(hPb y).trans (hb y hy)) x (ball_subset_ball (by norm_num) hx)
  have hs : (U x)^2≤C ^ 2*Q^2*(∫y in ball (0:Plane) (11/4),V y^2) := by
    rw [←(hVe x (ball_subset_ball (by norm_num) hx)).eq_of_nhds]
    have hI0 : 0≤∫y in ball (0:Plane) (11/4),V y^2:=integral_nonneg fun y=>sq_nonneg _
    have hsq:=sq_le_sq₀ (abs_nonneg (V x)) (by positivity) |>.mpr hh
    rw [sq_abs,mul_pow,mul_pow,Real.sq_sqrt hI0] at hsq
    exact hsq
  calc
    _ ≤ ENNReal.ofReal (C ^ 2*Q^2*(∫y in ball (0:Plane) (11/4),V y^2)):=ENNReal.ofReal_le_ofReal hs
    _ = _ := by rw [ENNReal.ofReal_mul (by positivity),hI]

lemma polynomial_exponential_gap {S : ℕ → ℝ} (hS : Tendsto S atTop atTop)
    {a b C : ℝ} (hab : a<b) (hC : 0<C) (m : ℕ) :
    ∀ᶠj in atTop,C*(S j)^m*Real.exp (2*S j*a)≤Real.exp (2*S j*b) := by
  have hδ : 0<2*(b-a):=by linarith
  have hh:=(isLittleO_pow_exp_pos_mul_atTop m hδ).bound (inv_pos.mpr hC)
  have he:=hS.eventually hh
  filter_upwards [he,hS.eventually (eventually_ge_atTop 0)] with j hj hSj
  simp only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hSj m),abs_of_pos (Real.exp_pos _)] at hj
  have hmul : C*(S j)^m≤Real.exp (2*(b-a)*S j) := by
    calc
      _ ≤ C*(C⁻¹*Real.exp (2*(b-a)*S j)):=mul_le_mul_of_nonneg_left hj hC.le
      _ = _ := by rw [←mul_assoc,mul_inv_cancel₀ hC.ne',one_mul]
  calc
    _ ≤ Real.exp (2*(b-a)*S j)*Real.exp (2*S j*a):=mul_le_mul_of_nonneg_right hmul (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
namespace SharpNodal.Profiles
open Carleman

lemma plainMass_mono (U : Plane → ℝ) {E F : Set Plane} (h : E⊆F) : plainMass U E≤plainMass U F:=lintegral_mono_set h
lemma plainMass_center (U : Plane → ℝ) (y : Plane) (r : ℝ) :
    plainMass U (ball y r)=centeredMass 0 U y r := by simp [plainMass,centeredMass]
lemma plainMass_tilted (U : Plane → ℝ) (S : ℝ) (E : Set Plane) :
    plainMass U E=tiltedMass S 0 U 1 0 E := by simp [plainMass,tiltedMass,tiltedWeight]

lemma local_sup_mass {Ω : Set Plane} (hΩ : IsOpen Ω) {y : Plane} {r Cp : ℝ}
    (hr : 0 < r) (hCp : 0≤Cp) (hball : ball y (3*r)⊆Ω) :
    ∃C : ℝ,0<C ∧ ∀(U p : Plane → ℝ) (K : ℝ),
      ContDiffOn ℝ ∞ U Ω → ContDiffOn ℝ ∞ p Ω →
      (∀x∈Ω,euclideanLaplacian U x+K^2*p x*U x=0) →
      (∀x∈Ω,|p x|≤Cp) →
      supMass U (ball y (2*r))≤ENNReal.ofReal (C*(1+r^2*K^2*Cp)^2)*plainMass U (closedBall y (3*r)) := by
  obtain ⟨B,hB,hBb⟩:=bounded_potential_supMass
  refine ⟨B/r^2,div_pos hB (sq_pos_of_pos hr),?_⟩
  intro U p K hU hp he hb
  let f:=rescaleMap y r
  let V:=U ∘ f
  let q:=fun z=>r^2*K^2*p (f z)
  have hf : MapsTo f (ball 0 3) Ω := by
    intro z hz
    apply hball
    change dist (y+r • z) y<3*r
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    have hz':=mem_ball_zero_iff.mp hz
    nlinarith
  have hV : ContDiffOn ℝ ∞ V (ball 0 3):=hU.comp (smooth_rescaleMap y r).contDiffOn hf
  have hq : ContDiffOn ℝ ∞ q (ball 0 3):=contDiffOn_const.mul (hp.comp (smooth_rescaleMap y r).contDiffOn hf)
  have hQ : 1≤1+r^2*K^2*Cp:=by
    have hh : 0 ≤ r^2*K^2*Cp:=by positivity
    linarith
  have he' : ∀z∈ball (0:Plane) 3,euclideanLaplacian V z+q z*V z=0 := by
    intro z hz
    rw [laplacian_rescale_local hΩ hU y r z (hf hz)]
    have hh:=he _ (hf hz)
    dsimp [q,V,f]; nlinarith only [hh]
  have hb' : ∀z∈ball (0:Plane) 3,|q z|≤1+r^2*K^2*Cp := by
    intro z hz
    dsimp [q]
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ r^2*K^2)]
    have hh:=mul_le_mul_of_nonneg_left (hb _ (hf hz)) (by positivity : 0 ≤ r^2*K^2)
    linarith
  have hh:=hBb V q hV hq _ hQ he' hb'
  have hm : centeredMass 0 V 0 (11/4)=ENNReal.ofReal (r^2)⁻¹*plainMass U (ball y (r*(11/4))) := by
    have ht:=centeredMass_rescale (0:Plane) U y 0 hr (11/4)
    simpa only [smul_zero,rescaleMap,smul_zero,add_zero,←plainMass_center,V,f] using ht
  have hmle : plainMass U (ball y (r*(11/4)))≤plainMass U (closedBall y (3*r)) :=
    plainMass_mono U ((ball_subset_ball (by nlinarith)).trans ball_subset_closedBall)
  have hsv : supMass U (ball y (2*r))≤ supMass V (ball 0 2) := by
    apply supMass_le.mpr
    intro x hx
    let z:=r⁻¹ • (x-y)
    have hz : z∈ball (0:Plane) 2 := by
      rw [mem_ball_zero_iff]
      dsimp [z]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
      have hhx:=mem_ball.mp hx
      rw [dist_eq_norm] at hhx
      exact (inv_mul_lt_iff₀ hr).mpr (by nlinarith)
    have hfx : f z=x := by dsimp [f,rescaleMap,z]; rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul,add_sub_cancel]
    have hval : V z=U x:=by change U (f z)=U x; rw [hfx]
    rw [←hval]
    exact le_iSup₂_of_le z hz le_rfl
  apply hsv.trans
  rw [hm] at hh
  calc
    _ ≤ ENNReal.ofReal (B*(1+r^2*K^2*Cp)^2)*(ENNReal.ofReal (r^2)⁻¹*plainMass U (closedBall y (3*r))):=
      hh.trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl hmle))
    _ = _ := by
      rw [←mul_assoc,←ENNReal.ofReal_mul (by positivity)]
      congr 2
      simp only [div_eq_mul_inv]; ring

end SharpNodal.Profiles

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_GlobalProfiles
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

namespace SharpNodal.Profiles
open Carleman

lemma WeightedProfileBounds.plain_upper {Ω : Set Plane} {S : ℕ → ℝ} {U : ℕ → Plane → ℝ} {W : Plane → EReal}
    (h : WeightedProfileBounds Ω S 0 U 1 W) {F : Set Plane} (hF : IsCompact F) (hFΩ : F⊆Ω) :
    limsup (fun j=>logRate (S j) (plainMass (U j) F)) atTop≤⨆x∈F,W x := by
  simpa only [Pi.zero_apply,Pi.one_apply,EReal.coe_zero,add_zero,←plainMass_tilted] using
    h.upper 0 continuousOn_const F hF hFΩ

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]

lemma sup_profile_le_local_oai {Ω : Set Plane} (hΩ : IsOpen Ω)
    {e : OpenPartialHomeomorph X Plane} (hΩe : Ω⊆e.target)
    {u : ℕ → X → ℝ} {p : ℕ → Plane → ℝ} {S K : ℕ → ℝ} {Cp : ℝ}
    {ell : countableBasis X → EReal} {W : Plane → EReal}
    (hSpos : ∀j,0<S j) (hS : Tendsto S atTop atTop) (hK : ∀ᶠj in atTop,|K j|≤S j)
    (hCp : 0≤Cp)
    (hU : ∀j,ContDiffOn ℝ ∞ (u j ∘ e.symm) Ω) (hp : ∀j,ContDiffOn ℝ ∞ (p j) Ω)
    (he : ∀j x,x∈Ω → euclideanLaplacian (u j ∘ e.symm) x+(K j)^2*p j x*u j (e.symm x)=0)
    (hb : ∀j x,x∈Ω → |p j x|≤Cp)
    (hlim : ∀i : countableBasis X,Tendsto (fun j=>logRate (S j) (supMass (u j) i.val)) atTop (𝓝 (ell i)))
    (hW : UpperSemicontinuous W)
    (hprofile : WeightedProfileBounds Ω S 0 (fun j=>u j ∘ e.symm) 1 W)
    {y : Plane} (hy : y∈Ω) : basisProfile ell (e.symm y)≤W y := by
  by_contra hn
  obtain ⟨a,hWa,haV⟩:=EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  obtain ⟨b,hab,hbV⟩:=EReal.lt_iff_exists_real_btwn.mp haV
  have hab' : a<b:=EReal.coe_lt_coe_iff.mp hab
  obtain ⟨t,ht,htH⟩:=Metric.isOpen_iff.mp (hΩ.inter (hW.isOpen_preimage (a:EReal))) y ⟨hy,hWa⟩
  let r:=t/4
  have hr : 0 < r:=by dsimp [r]; positivity
  have hF : closedBall y (3*r)⊆Ω∩W ⁻¹' Iio (a:EReal) :=
    (closedBall_subset_ball (by dsimp [r]; linarith)).trans htH
  obtain ⟨C,hC,hCb⟩:=local_sup_mass hΩ hr hCp (ball_subset_closedBall.trans (fun z hz=>(hF hz).1))
  let a':=(a+b)/2
  have haa' : a<a':=by dsimp [a']; linarith
  have ha'b : a'<b:=by dsimp [a']; linarith
  have hupper:=hprofile.plain_upper (isCompact_closedBall y (3*r)) (fun z hz=>(hF hz).1)
  have hsup : (⨆z∈closedBall y (3*r),W z)≤(a:EReal):=iSup_le fun z=>iSup_le fun hz=>(hF hz).2.le
  have hevmass:=eventually_lt_of_limsup_lt (hupper.trans_lt (hsup.trans_lt (EReal.coe_lt_coe_iff.mpr haa')))
  let D:=C*(1+r^2*Cp)^2
  have hD : 0<D:=by dsimp [D]; positivity
  have hpoly:=polynomial_exponential_gap hS ha'b hD 4
  have hsbound : ∀ᶠj in atTop,supMass (u j ∘ e.symm) (ball y (2*r))≤ENNReal.ofReal (Real.exp (2*S j*b)) := by
    filter_upwards [hevmass,hpoly,hK,hS.eventually (eventually_ge_atTop 1)] with j hj hpj hKj hSj
    have hSj0 : 0≤S j:=by linarith
    have hK2 : (K j)^2≤(S j)^2:=by nlinarith [sq_abs (K j),abs_nonneg (K j)]
    have hcoeff : 1+r^2*(K j)^2*Cp≤(1+r^2*Cp)*(S j)^2 := by
      have hh:=mul_le_mul_of_nonneg_left hK2 (by positivity : 0 ≤ r^2*Cp)
      nlinarith [sq_nonneg (S j-1)]
    have hcoeff0 : 0≤1+r^2*(K j)^2*Cp:=by positivity
    have hc2 : C*(1+r^2*(K j)^2*Cp)^2≤D*(S j)^4 := by
      have hh:=(sq_le_sq₀ hcoeff0 (by positivity)).mpr hcoeff
      have hh':=mul_le_mul_of_nonneg_left hh hC.le
      dsimp [D]; nlinarith only [hh']
    calc
      _ ≤ ENNReal.ofReal (C*(1+r^2*(K j)^2*Cp)^2)*plainMass (u j ∘ e.symm) (closedBall y (3*r)):=hCb _ _ _ (hU j) (hp j) (he j) (hb j)
      _ ≤ ENNReal.ofReal (D*(S j)^4)*ENNReal.ofReal (Real.exp (2*S j*a')):=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hc2) ((logRate_lt_iff (hSpos j) _).mp hj).le
      _ ≤ _ := by rw [←ENNReal.ofReal_mul (by positivity)]; exact ENNReal.ofReal_le_ofReal hpj
  have hlocal : SupLocalBound u S (e.symm y) b := by
    refine ⟨e.source∩e ⁻¹' ball y (2*r),e.isOpen_inter_preimage isOpen_ball,?_,?_⟩
    · exact ⟨e.map_target (hΩe hy),by rw [mem_preimage,e.right_inv (hΩe hy)]; exact mem_ball_self (by positivity)⟩
    · filter_upwards [hsbound] with j hj
      apply (supMass_le.mpr ?_).trans hj
      intro x hx
      have hv : u j x=(u j ∘ e.symm) (e x):=by rw [Function.comp_apply,e.left_inv hx.1]
      rw [hv]
      exact le_iSup₂_of_le (e x) hx.2 le_rfl
  exact (not_le_of_gt hbV) (supProfile_le_of_local hSpos hlim hlocal)

end SharpNodal.Profiles

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpNodal.Profiles.sup_profile_le_local_oai.{u_1} := @OAI.SharpNodal.Profiles.sup_profile_le_local_oai.{u_1}
