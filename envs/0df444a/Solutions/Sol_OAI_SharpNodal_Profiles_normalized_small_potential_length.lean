-- Prove2me | solution 1 for OAI.SharpNodal.Profiles.normalized_small_potential_length
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:21:33.857981+00:00
-- url     : https://prove2.me/submissions/9a707dbf-8ee6-4b32-b6f3-0f755742fa52

import Mathlib
import Definitions.Def_NodalLength
import Definitions.Def_OAIQ4Nl000

section
-- module Solutions.OAIQ4_Nl.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

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

lemma partial_mul {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (i : Fin 2) (x : Plane) :
    coordPartial (fun y => f y * g y) i x =
      coordPartial f i x * g x + f x * coordPartial g i x := by
  unfold coordPartial
  rw [fderiv_fun_mul (hf.differentiable (by simp)).differentiableAt
    (hg.differentiable (by simp)).differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

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

lemma partial_partial {f : Plane → ℝ} (hf : Smooth f) (i j : Fin 2) (x : Plane) :
    coordPartial (coordPartial f i) j x =
      coordPartial (coordPartial f j) i x := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))).differentiable
      (by simp)
  have h (a b : Fin 2) : coordPartial (coordPartial f a) b x =
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single b 1) (EuclideanSpace.single a 1) := by
    unfold coordPartial
    rw [fderiv_clm_apply hdf.differentiableAt (differentiableAt_const _)]
    simp
  rw [h i j, h j i]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).eq _ _


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Commutator
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

lemma partial_finset_sum {ι : Type*} (s : Finset ι) {f : ι → Plane → ℝ}
    (hf : ∀ i ∈ s, Smooth (f i)) (k : Fin 2) (x : Plane) :
    coordPartial (fun y => ∑ i ∈ s, f i y) k x = ∑ i ∈ s, coordPartial (f i) k x := by
  unfold coordPartial
  rw [fderiv_fun_sum (fun i hi => ((hf i hi).differentiable (by simp)).differentiableAt)]
  simp only [sum_apply]


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

lemma partial_const (c : ℝ) (i : Fin 2) (x : Plane) :
    coordPartial (fun _ => c) i x = 0 := by simp [coordPartial]


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Cutoffs
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

lemma partial2_mul {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (i : Fin 2) (x : Plane) :
    coordPartial (coordPartial (fun y => f y*g y) i) i x =
      coordPartial (coordPartial f i) i x*g x+2*coordPartial f i x*coordPartial g i x+
      f x*coordPartial (coordPartial g i) i x := by
  rw [show coordPartial (fun y => f y*g y) i =
      (fun y => coordPartial f i y*g y+f y*coordPartial g i y) from funext (partial_mul hf hg i)]
  rw [partial_add ((smooth_partial hf i).mul hg) (hf.mul (smooth_partial hg i)),
    partial_mul (smooth_partial hf i) hg, partial_mul hf (smooth_partial hg i)]
  ring

lemma laplacian_mul {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g) (x : Plane) :
    euclideanLaplacian (fun y => f y*g y) x =
      euclideanLaplacian f x*g x+2*(∑ i : Fin 2, coordPartial f i x*coordPartial g i x)+
      f x*euclideanLaplacian g x := by
  simp only [euclideanLaplacian, Fin.sum_univ_two, partial2_mul hf hg]
  ring

end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_MassComparison
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

namespace SharpNodal
namespace Profiles
open Carleman

lemma laplacian_const (c : ℝ) (x : Plane) : euclideanLaplacian (fun _ => c) x=0 := by
  unfold euclideanLaplacian
  apply Finset.sum_eq_zero
  intro i _
  have h : coordPartial (fun _ => c) i=(fun _ => 0) := funext (partial_const c i)
  rw [h, partial_const]

end Profiles
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

lemma compact_parametrixKernel : HasCompactSupport parametrixKernel := by
  apply HasCompactSupport.intro (isCompact_closedBall (0:Plane) (1/4:ℝ))
  intro x hx
  exact parametrixKernel_zero (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx)

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

lemma smooth_rconv {f g : Plane → ℝ} (hf : Integrable f) (hg : Smooth g)
    (hc : HasCompactSupport g) : Smooth (rconv f g) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf.locallyIntegrable hg

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
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma norm_rconv_le {w K : Plane → ℝ} (hw : Integrable w)
    (hK : Continuous K) (hcK : HasCompactSupport K) {C : ℝ} (hC : ∀x,‖K x‖≤C) (x : Plane) :
    ‖rconv w K x‖≤C*(∫y,‖w y‖) := by
  have hi := hcK.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hw.locallyIntegrable hK x
  calc
    _ ≤ ∫y,‖w y*K (x-y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫y,‖w y‖*C := by
      apply integral_mono_ae hi.norm (hw.norm.mul_const C)
      filter_upwards [] with y
      change ‖w y*K (x-y)‖≤‖w y‖*C
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC (x-y)) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const,mul_comm]

end SharpNodal.Profiles
end
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

lemma plane_basis_expansion (v : Plane) :
    v=(v 0) • EuclideanSpace.single 0 1+(v 1) • EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp

lemma plane_component_norm_le (v : Plane) (i : Fin 2) : |v i|≤‖v‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i

lemma plane_clm_norm_le_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Plane →L[ℝ] F) {C : ℝ} (hC : 0≤C)
    (hA : ∀i : Fin 2,‖A (EuclideanSpace.single i 1)‖≤C) : ‖A‖≤2*C := by
  apply A.opNorm_le_bound (by positivity)
  intro v
  conv_lhs => rw [plane_basis_expansion v]
  rw [map_add,map_smul,map_smul]
  calc
    _ ≤ ‖(v 0) • A (EuclideanSpace.single 0 1)‖+‖(v 1) • A (EuclideanSpace.single 1 1)‖ := norm_add_le _ _
    _ = |v 0| *‖A (EuclideanSpace.single 0 1)‖+|v 1| *‖A (EuclideanSpace.single 1 1)‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ‖v‖*C+‖v‖*C := add_le_add
      (mul_le_mul (plane_component_norm_le v 0) (hA 0) (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul (plane_component_norm_le v 1) (hA 1) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

lemma fderiv_norm_le_two {f : Plane → ℝ} {C : ℝ} (hC : 0≤C) (x : Plane)
    (h : ∀i : Fin 2,|coordPartial f i x|≤C) : ‖fderiv ℝ f x‖≤2*C :=
  plane_clm_norm_le_two _ hC (fun i => by simpa only [coordPartial,Real.norm_eq_abs] using h i)

end SharpNodal.Profiles

end
end
end
end
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

lemma laplacian_rconv_local {f g : Plane → ℝ} (hf : LocallyIntegrable f) (hg : Smooth g)
    (hc : HasCompactSupport g) :
    euclideanLaplacian (rconv f g)=rconv f (euclideanLaplacian g) := by
  funext x
  simp only [euclideanLaplacian,partial_rconv_local hf hg hc,
    partial_rconv_local hf (smooth_partial hg _) (compact_partial hc _)]
  simp only [rconv_eq,euclideanLaplacian,Finset.mul_sum]
  rw [integral_finsetSum]
  intro i _
  exact (compact_partial (compact_partial hc i) i).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) hf (smooth_partial (smooth_partial hg i) i).continuous x

lemma smooth_newtonPotential {g : Plane → ℝ} (hg : Smooth g)
    (hc : HasCompactSupport g) : Smooth (newtonPotential g) :=
  contDiff_const.mul (smooth_rconv_local locallyIntegrable_logNorm hg hc)

lemma laplacian_newtonPotential {g : Plane → ℝ} (hg : Smooth g)
    (hc : HasCompactSupport g) : euclideanLaplacian (newtonPotential g)=g := by
  funext x
  unfold newtonPotential
  rw [laplacian_const_mul (smooth_rconv_local locallyIntegrable_logNorm hg hc),
    laplacian_rconv_local locallyIntegrable_logNorm hg hc]
  change (2*Real.pi)⁻¹*(∫y,Real.log ‖y‖*euclideanLaplacian g (x-y))=g x
  have hh := logarithmic_fundamental_solution
    (show Smooth (fun y => g (x-y)) from hg.comp (contDiff_const.sub contDiff_id)) (compact_reflection hc x)
  simp only [laplacian_reflection hg,sub_zero] at hh
  rw [hh]
  field_simp

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
noncomputable section
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma smooth_neumannTerm {q : Plane → ℝ} (hq : Smooth q) (hc : HasCompactSupport q) :
    ∀n,Smooth (neumannTerm q n) := by
  intro n
  induction n with
  | zero => exact contDiff_const
  | succ n ih => exact (smooth_newtonPotential (hq.mul ih) hc.mul_right).neg

lemma smooth_multiplierApprox {q : Plane → ℝ} (hq : Smooth q) (hc : HasCompactSupport q)
    (n : ℕ) : Smooth (multiplierApprox q n) :=
  contDiff_const.add (ContDiff.sum (fun j _ =>smooth_neumannTerm hq hc (j+1)))

lemma multiplierApprox_zero (q : Plane → ℝ) : multiplierApprox q 0=(fun _ =>1) := by
  funext x; simp [multiplierApprox]

lemma multiplierApprox_succ (q : Plane → ℝ) (n : ℕ) :
    multiplierApprox q (n+1)=(fun x =>multiplierApprox q n x+neumannTerm q (n+1) x) := by
  funext x; simp [multiplierApprox,Finset.sum_range_succ,add_assoc]

lemma laplacian_neumannTerm_succ {q : Plane → ℝ} (hq : Smooth q)
    (hc : HasCompactSupport q) (n : ℕ) (x : Plane) :
    euclideanLaplacian (neumannTerm q (n+1)) x= -q x*neumannTerm q n x := by
  have hs:=smooth_newtonPotential (hq.mul (smooth_neumannTerm hq hc n)) hc.mul_right
  change euclideanLaplacian (fun y => -newtonPotential (fun z =>q z*neumannTerm q n z) y) x=_
  have he : (fun y => -newtonPotential (fun z =>q z*neumannTerm q n z) y)=
      (fun y =>(-1:ℝ)*newtonPotential (fun z =>q z*neumannTerm q n z) y) := by simp
  rw [he,laplacian_const_mul hs,laplacian_newtonPotential (hq.mul (smooth_neumannTerm hq hc n)) hc.mul_right]
  simp

lemma multiplierApprox_equation {q : Plane → ℝ} (hq : Smooth q)
    (hc : HasCompactSupport q) (n : ℕ) (x : Plane) :
    euclideanLaplacian (multiplierApprox q n) x+q x*multiplierApprox q n x=q x*neumannTerm q n x := by
  induction n with
  | zero => simp [multiplierApprox_zero,laplacian_const,neumannTerm]
  | succ n ih =>
      rw [multiplierApprox_succ,laplacian_add (smooth_multiplierApprox hq hc n)
        (smooth_neumannTerm hq hc (n+1)),laplacian_neumannTerm_succ hq hc]
      dsimp only
      nlinarith only [ih]

lemma neumannTerm_bounds {C ε δ : ℝ} (hC : NewtonControl C) (hε : 0≤ε) (hδ : 0≤δ)
    (hsmall : C*ε≤δ) {q : Plane → ℝ} (hq : Smooth q) (hc : HasCompactSupport q)
    (hs : ∀x,3≤‖x‖ → q x=0) (hb : ∀x∈Metric.ball (0:Plane) 3,|q x|≤ε) :
    ∀n x,x∈Metric.ball (0:Plane) 3 →
      |neumannTerm q n x|≤δ^n ∧ (n≠0 → ∀i : Fin 2,|coordPartial (neumannTerm q n) i x|≤δ^n) := by
  intro n
  induction n with
  | zero => intro x _; simp [neumannTerm]
  | succ n ih =>
      intro x hx
      have hB : 0≤ε*δ^n := by positivity
      have hs' : ∀x,3≤‖x‖ → q x*neumannTerm q n x=0 := by intro y hy; rw [hs y hy,zero_mul]
      have hb' : ∀x∈Metric.ball (0:Plane) 3,|q x*neumannTerm q n x|≤ε*δ^n := by
        intro y hy
        rw [abs_mul]
        exact mul_le_mul (hb y hy) (ih y hy).1 (abs_nonneg _) hε
      obtain ⟨hv,hd⟩:=hC.2 _ (hq.mul (smooth_neumannTerm hq hc n)) hc.mul_right _ hB hs' hb' x hx
      have hnum : C*(ε*δ^n)≤δ^(n+1) := by
        rw [←mul_assoc,pow_succ']
        exact mul_le_mul_of_nonneg_right hsmall (pow_nonneg hδ n)
      refine ⟨?_,fun _ i => ?_⟩
      · simpa only [neumannTerm,abs_neg] using hv.trans hnum
      · simpa only [neumannTerm,partial_neg (smooth_newtonPotential (hq.mul (smooth_neumannTerm hq hc n)) hc.mul_right),abs_neg] using (hd i).trans hnum

lemma geometric_succ_sum_le {δ : ℝ} (hδ : 0≤δ) (hδ' : δ<1) (n : ℕ) :
    (∑j∈Finset.range n,δ^(j+1))≤δ/(1-δ) := by
  have hsum : Summable (fun j : ℕ => δ^(j+1)) := (summable_geometric_of_lt_one hδ hδ').comp_injective Nat.succ_injective
  calc
    _ ≤ ∑'j : ℕ,δ^(j+1) := hsum.sum_le_tsum _ (fun j _ =>pow_nonneg hδ _)
    _ = δ/(1-δ) := by
      simp_rw [pow_succ']
      rw [tsum_mul_left,tsum_geometric_of_lt_one hδ hδ']
      rfl

lemma multiplierApprox_bounds {C ε δ : ℝ} (hC : NewtonControl C) (hε : 0≤ε)
    (hδ : 0≤δ) (hδ' : δ<1) (hsmall : C*ε≤δ)
    {q : Plane → ℝ} (hq : Smooth q) (hc : HasCompactSupport q)
    (hs : ∀x,3≤‖x‖ → q x=0) (hb : ∀x∈Metric.ball (0:Plane) 3,|q x|≤ε)
    (n : ℕ) {x : Plane} (hx : x∈Metric.ball 0 3) :
    |multiplierApprox q n x-1|≤δ/(1-δ) ∧
      ∀i : Fin 2,|coordPartial (multiplierApprox q n) i x|≤δ/(1-δ) := by
  have ht:=neumannTerm_bounds hC hε hδ hsmall hq hc hs hb
  have hbound : ∀j,|neumannTerm q (j+1) x|≤δ^(j+1) := fun j => (ht (j+1) x hx).1
  refine ⟨?_,fun i =>?_⟩
  · change |(1+∑j∈Finset.range n,neumannTerm q (j+1) x)-1|≤_
    rw [add_sub_cancel_left]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun j _ =>hbound j)).trans (geometric_succ_sum_le hδ hδ' n))
  · unfold multiplierApprox
    rw [partial_add contDiff_const (ContDiff.sum (fun j _ =>smooth_neumannTerm hq hc (j+1))),
      partial_const,zero_add,partial_finset_sum _ (fun j _ =>smooth_neumannTerm hq hc (j+1))]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun j _ =>(ht (j+1) x hx).2 (by omega) i)).trans
        (geometric_succ_sum_le hδ hδ' n))

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma multiplierLimit_hasFDerivAt {C ε δ : ℝ} (hC : NewtonControl C) (hε : 0≤ε)
    (hδ : 0≤δ) (hδ' : δ<1) (hsmall : C*ε≤δ)
    {q : Plane → ℝ} (hq : Smooth q) (hc : HasCompactSupport q)
    (hs : ∀x,3≤‖x‖ → q x=0) (hb : ∀x∈Metric.ball (0:Plane) 3,|q x|≤ε)
    {x : Plane} (hx : x∈Metric.ball 0 3) :
    HasFDerivAt (multiplierLimit q) (∑'j : ℕ,fderiv ℝ (neumannTerm q (j+1)) x) x := by
  have ht:=neumannTerm_bounds hC hε hδ hsmall hq hc hs hb
  have hsum : Summable (fun j : ℕ =>δ^(j+1)) :=
    (summable_geometric_of_lt_one hδ hδ').comp_injective Nat.succ_injective
  have hd (j : ℕ) (y : Plane) (hy : y∈Metric.ball (0:Plane) 3) :
      ‖fderiv ℝ (neumannTerm q (j+1)) y‖≤2*δ^(j+1) :=
    fderiv_norm_le_two (by positivity) y ((ht (j+1) y hy).2 (by omega))
  have hi := hasFDerivAt_tsum_of_isPreconnected (hsum.mul_left 2) Metric.isOpen_ball
    (convex_ball (0:Plane) 3).isPreconnected
    (fun j y _ =>(smooth_neumannTerm hq hc (j+1)).differentiable (by simp) |>.differentiableAt.hasFDerivAt)
    hd (show (0:Plane)∈Metric.ball 0 3 by simp)
    (hsum.of_norm_bounded (fun j => by simpa only [Real.norm_eq_abs] using (ht (j+1) 0 (by simp)).1)) hx
  exact hi.const_add 1

lemma multiplierLimit_convergence {C ε δ : ℝ} (hC : NewtonControl C) (hε : 0≤ε)
    (hδ : 0≤δ) (hδ' : δ<1) (hsmall : C*ε≤δ)
    {q : Plane → ℝ} (hq : Smooth q) (hc : HasCompactSupport q)
    (hs : ∀x,3≤‖x‖ → q x=0) (hb : ∀x∈Metric.ball (0:Plane) 3,|q x|≤ε) :
    TendstoUniformlyOn (multiplierApprox q) (multiplierLimit q) atTop (Metric.ball 0 3) ∧
    TendstoUniformlyOn (fun n x =>fderiv ℝ (multiplierApprox q n) x)
      (fun x =>fderiv ℝ (multiplierLimit q) x) atTop (Metric.ball 0 3) := by
  have ht:=neumannTerm_bounds hC hε hδ hsmall hq hc hs hb
  have hsum : Summable (fun j : ℕ =>δ^(j+1)) :=
    (summable_geometric_of_lt_one hδ hδ').comp_injective Nat.succ_injective
  have hval:=tendstoUniformlyOn_tsum_nat (f:=fun j x =>neumannTerm q (j+1) x) hsum
    (fun j x (hx : x∈Metric.ball (0:Plane) 3) =>by simpa only [Real.norm_eq_abs] using (ht (j+1) x hx).1)
  have hder:=tendstoUniformlyOn_tsum_nat (f:=fun j x =>fderiv ℝ (neumannTerm q (j+1)) x) (hsum.mul_left 2)
    (fun j x (hx : x∈Metric.ball (0:Plane) 3) =>
      fderiv_norm_le_two (by positivity) x ((ht (j+1) x hx).2 (by omega)))
  constructor
  · exact (tendsto_const_nhds.tendstoUniformlyOn_const (β:=ℝ) (b:=1) _).add hval
  · have he (n : ℕ) (x : Plane) :
        fderiv ℝ (multiplierApprox q n) x=∑j∈Finset.range n,fderiv ℝ (neumannTerm q (j+1)) x := by
      unfold multiplierApprox
      rw [fderiv_const_add, fderiv_fun_sum (fun j _ =>(smooth_neumannTerm hq hc (j+1)).differentiable (by simp) |>.differentiableAt)]
    simpa only [he] using hder.congr_right (fun x hx =>
      (multiplierLimit_hasFDerivAt hC hε hδ hδ' hsmall hq hc hs hb hx).fderiv.symm)

lemma multiplierLimit_bounds {C ε δ : ℝ} (hC : NewtonControl C) (hε : 0≤ε)
    (hδ : 0≤δ) (hδ' : δ<1) (hsmall : C*ε≤δ)
    {q : Plane → ℝ} (hq : Smooth q) (hc : HasCompactSupport q)
    (hs : ∀x,3≤‖x‖ → q x=0) (hb : ∀x∈Metric.ball (0:Plane) 3,|q x|≤ε)
    {x : Plane} (hx : x∈Metric.ball 0 3) :
    |multiplierLimit q x-1|≤δ/(1-δ) ∧
      ∀i : Fin 2,|coordPartial (multiplierLimit q) i x|≤δ/(1-δ) := by
  obtain ⟨hv,hd⟩:=multiplierLimit_convergence hC hε hδ hδ' hsmall hq hc hs hb
  have hp:=multiplierApprox_bounds hC hε hδ hδ' hsmall hq hc hs hb
  refine ⟨le_of_tendsto (((hv.tendsto_at hx).sub_const 1).abs) (Eventually.of_forall (fun n =>(hp n hx).1)),fun i =>?_⟩
  have ht := ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.tendsto _).comp (hd.tendsto_at hx)
  exact le_of_tendsto ht.abs (Eventually.of_forall (fun n =>(hp n hx).2 i))

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma smooth_positiveApprox {q : Plane → ℝ} (hq : Smooth q) (hc : HasCompactSupport q)
    (n : ℕ) : Smooth (positiveApprox q n) :=
  contDiff_const.add (multiplierCutoff.contDiff.mul ((smooth_multiplierApprox hq hc n).sub contDiff_const))

lemma positiveApprox_eq {q : Plane → ℝ} {n : ℕ} {x : Plane}
    (hx : x∈Metric.ball 0 (5/2)) : positiveApprox q n x=multiplierApprox q n x := by
  have he : multiplierCutoff x=1 := multiplierCutoff.one_of_mem_closedBall (by
    simpa only [multiplierCutoff] using Metric.ball_subset_closedBall hx)
  simp [positiveApprox,he]

lemma positiveApprox_eventuallyEq {q : Plane → ℝ} {n : ℕ} {x : Plane}
    (hx : x∈Metric.ball 0 (5/2)) : positiveApprox q n =ᶠ[𝓝 x] multiplierApprox q n := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
  exact positiveApprox_eq hy

lemma positiveApprox_bound {C ε δ : ℝ} (hC : NewtonControl C) (hε : 0≤ε)
    (hδ : 0≤δ) (hδ' : δ<1) (hsmall : C*ε≤δ)
    {q : Plane → ℝ} (hq : Smooth q) (hc : HasCompactSupport q)
    (hs : ∀x,3≤‖x‖ → q x=0) (hb : ∀x∈Metric.ball (0:Plane) 3,|q x|≤ε)
    (n : ℕ) (x : Plane) : |positiveApprox q n x-1|≤δ/(1-δ) := by
  by_cases hx : x∈Metric.ball (0:Plane) 3
  · have he:= (multiplierApprox_bounds hC hε hδ hδ' hsmall hq hc hs hb n hx).1
    simp only [positiveApprox,add_sub_cancel_left,abs_mul]
    rw [abs_of_nonneg (multiplierCutoff.nonneg (x:=x))]
    exact (mul_le_mul_of_nonneg_right (multiplierCutoff.le_one (x:=x)) (abs_nonneg _)).trans (by simpa using he)
  · have hz : multiplierCutoff x=0 := multiplierCutoff.zero_of_le_dist (by
      simp only [Metric.mem_ball,dist_zero_right,not_lt] at hx
      change 11/4≤dist x 0
      simpa only [dist_zero_right] using (show (11/4:ℝ)≤‖x‖ by linarith))
    simp only [positiveApprox,hz,zero_mul,add_zero,sub_self,abs_zero]
    positivity

lemma positiveApprox_lower {C ε δ : ℝ} (hC : NewtonControl C) (hε : 0≤ε)
    (hδ : 0≤δ) (hδ' : δ≤1/4) (hsmall : C*ε≤δ)
    {q : Plane → ℝ} (hq : Smooth q) (hc : HasCompactSupport q)
    (hs : ∀x,3≤‖x‖ → q x=0) (hb : ∀x∈Metric.ball (0:Plane) 3,|q x|≤ε)
    (n : ℕ) (x : Plane) : 1/2≤positiveApprox q n x := by
  have hd : δ<1 := by linarith
  have he:=positiveApprox_bound hC hε hδ hd hsmall hq hc hs hb n x
  have hb' : δ/(1-δ)≤1/2 := (div_le_iff₀ (by linarith : 0<1-δ)).mpr (by linarith)
  have hh:= (abs_le.mp (he.trans hb')).1
  linarith

lemma positiveApprox_equation {q : Plane → ℝ} (hq : Smooth q) (hc : HasCompactSupport q)
    (n : ℕ) {x : Plane} (hx : x∈Metric.ball 0 (5/2)) :
    euclideanLaplacian (positiveApprox q n) x+q x*positiveApprox q n x=q x*neumannTerm q n x := by
  rw [(laplacian_eventuallyEq (positiveApprox_eventuallyEq hx)).eq_of_nhds,positiveApprox_eq hx]
  exact multiplierApprox_equation hq hc n x

lemma positiveApprox_partial {q : Plane → ℝ} {n : ℕ} {x : Plane}
    (hx : x∈Metric.ball 0 (5/2)) (i : Fin 2) :
    coordPartial (positiveApprox q n) i x=coordPartial (multiplierApprox q n) i x :=
  (partial_eventuallyEq (positiveApprox_eventuallyEq hx) i).eq_of_nhds

lemma quotient_laplacian {U φ : Plane → ℝ} (hU : Smooth U) (hφ : Smooth φ)
    (hne : ∀x,φ x≠0) {q r : Plane → ℝ} {x : Plane}
    (hUE : euclideanLaplacian U x+q x*U x=0)
    (hφE : euclideanLaplacian φ x+q x*φ x=r x) :
    euclideanLaplacian (fun y =>U y/φ y) x/2=
      -(∑i : Fin 2,coordPartial φ i x/φ x*coordPartial (fun y =>U y/φ y) i x)-
      r x*(U x/φ x)/(2*φ x) := by
  have hv : Smooth (fun y =>U y/φ y) := hU.div hφ hne
  have he : U=(fun y =>φ y*(U y/φ y)) := by funext y; field_simp [hne y]
  have hl:=laplacian_mul hφ hv x
  rw [←he] at hl
  have hp:=hne x
  simp only [Fin.sum_univ_two] at hl ⊢
  field_simp [hp] at hl ⊢
  linear_combination (φ x)*hUE-(U x)*hφE-hl

end SharpNodal.Profiles

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_ComplexDerivatives
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

namespace SharpNodal.Profiles
open Carleman

lemma csmooth_partial {f : Plane → ℂ} (hf : CSmooth f) (i : Fin 2) :
    CSmooth (complexPartial f i) :=
  (hf.fderiv_right (by simp : (∞ : ℕ∞ω)+1≤(∞ : ℕ∞ω))).clm_apply contDiff_const

lemma csmooth_ofReal {f : Plane → ℝ} (hf : Smooth f) : CSmooth (fun x =>(f x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

lemma complexPartial_ofReal {f : Plane → ℝ} (hf : Smooth f) (i : Fin 2) (x : Plane) :
    complexPartial (fun y =>(f y : ℂ)) i x=(coordPartial f i x : ℂ) := by
  have he := Complex.ofRealCLM.hasFDerivAt.comp x (hf.differentiable (by simp) |>.differentiableAt.hasFDerivAt)
  exact congrFun (congrArg DFunLike.coe he.fderiv) (EuclideanSpace.single i 1)

lemma complexPartial_add {f g : Plane → ℂ} (hf : CSmooth f) (hg : CSmooth g)
    (i : Fin 2) (x : Plane) :
    complexPartial (fun y =>f y+g y) i x=complexPartial f i x+complexPartial g i x := by
  unfold complexPartial
  rw [fderiv_fun_add (hf.differentiable (by simp) |>.differentiableAt)
    (hg.differentiable (by simp) |>.differentiableAt)]
  rfl

lemma complexPartial_mul {f g : Plane → ℂ} (hf : CSmooth f) (hg : CSmooth g)
    (i : Fin 2) (x : Plane) :
    complexPartial (fun y =>f y*g y) i x=complexPartial f i x*g x+f x*complexPartial g i x := by
  unfold complexPartial
  rw [fderiv_fun_mul (hf.differentiable (by simp) |>.differentiableAt)
    (hg.differentiable (by simp) |>.differentiableAt)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

lemma complexPartial_const_mul {f : Plane → ℂ} (hf : CSmooth f) (c : ℂ)
    (i : Fin 2) (x : Plane) :
    complexPartial (fun y =>c*f y) i x=c*complexPartial f i x := by
  rw [complexPartial_mul contDiff_const hf]
  simp [complexPartial]

lemma complexPartial_sub {f g : Plane → ℂ} (hf : CSmooth f) (hg : CSmooth g)
    (i : Fin 2) (x : Plane) :
    complexPartial (fun y =>f y-g y) i x=complexPartial f i x-complexPartial g i x := by
  unfold complexPartial
  rw [fderiv_fun_sub (hf.differentiable (by simp) |>.differentiableAt)
    (hg.differentiable (by simp) |>.differentiableAt)]
  rfl

lemma barPartial_add {f g : Plane → ℂ} (hf : CSmooth f) (hg : CSmooth g) (x : Plane) :
    barPartial (fun y =>f y+g y) x=barPartial f x+barPartial g x := by
  simp only [barPartial,complexPartial_add hf hg]; ring

lemma barPartial_sub {f g : Plane → ℂ} (hf : CSmooth f) (hg : CSmooth g) (x : Plane) :
    barPartial (fun y =>f y-g y) x=barPartial f x-barPartial g x := by
  simp only [barPartial,complexPartial_sub hf hg]; ring

lemma barPartial_mul {f g : Plane → ℂ} (hf : CSmooth f) (hg : CSmooth g) (x : Plane) :
    barPartial (fun y =>f y*g y) x=barPartial f x*g x+f x*barPartial g x := by
  simp only [barPartial,complexPartial_mul hf hg]; ring

lemma barPartial_const_mul {f : Plane → ℂ} (hf : CSmooth f) (c : ℂ) (x : Plane) :
    barPartial (fun y =>c*f y) x=c*barPartial f x := by
  simp only [barPartial,complexPartial_const_mul hf]; ring

lemma csmooth_gradient {f : Plane → ℝ} (hf : Smooth f) : CSmooth (complexGradient f) :=
  (csmooth_ofReal (smooth_partial hf 0)).sub (contDiff_const.mul (csmooth_ofReal (smooth_partial hf 1)))

lemma barPartial_gradient {f : Plane → ℝ} (hf : Smooth f) (x : Plane) :
    barPartial (complexGradient f) x=(euclideanLaplacian f x : ℂ)/2 := by
  unfold barPartial complexGradient
  simp only [
    complexPartial_sub (csmooth_ofReal (smooth_partial hf 0))
      (contDiff_const.mul (csmooth_ofReal (smooth_partial hf 1))),
    complexPartial_const_mul (csmooth_ofReal (smooth_partial hf 1)),
    complexPartial_ofReal (smooth_partial hf 0),complexPartial_ofReal (smooth_partial hf 1)]
  rw [partial_partial hf 0 1]
  simp only [euclideanLaplacian,Fin.sum_univ_two,Complex.ofReal_add]
  ring_nf
  simp only [Complex.I_sq]
  ring

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma smooth_real_component {g : Plane → ℂ} (hg : CSmooth g) :
    Smooth (fun x =>(g x).re) := Complex.reCLM.contDiff.comp hg

lemma smooth_imag_component {g : Plane → ℂ} (hg : CSmooth g) :
    Smooth (fun x =>(g x).im) := Complex.imCLM.contDiff.comp hg

lemma compact_real_component {g : Plane → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (fun x =>(g x).re) := hg.comp_left Complex.zero_re

lemma compact_imag_component {g : Plane → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (fun x =>(g x).im) := hg.comp_left Complex.zero_im

lemma csmooth_cauchyPotential {g : Plane → ℂ} (hg : CSmooth g)
    (hc : HasCompactSupport g) : CSmooth (cauchyPotential g) :=
  (contDiff_const.mul (csmooth_gradient (smooth_newtonPotential
    (smooth_real_component hg) (compact_real_component hc)))).add
  (contDiff_const.mul (contDiff_const.mul (csmooth_gradient (smooth_newtonPotential
    (smooth_imag_component hg) (compact_imag_component hc)))))

lemma barPartial_cauchyPotential {g : Plane → ℂ} (hg : CSmooth g)
    (hc : HasCompactSupport g) (x : Plane) : barPartial (cauchyPotential g) x=g x := by
  have hr:=smooth_newtonPotential (smooth_real_component hg) (compact_real_component hc)
  have hi:=smooth_newtonPotential (smooth_imag_component hg) (compact_imag_component hc)
  unfold cauchyPotential
  rw [barPartial_add (contDiff_const.mul (csmooth_gradient hr))
    (contDiff_const.mul (contDiff_const.mul (csmooth_gradient hi))),
    barPartial_const_mul (csmooth_gradient hr),
    barPartial_const_mul (contDiff_const.mul (csmooth_gradient hi)),
    barPartial_const_mul (csmooth_gradient hi),barPartial_gradient hr,barPartial_gradient hi,
    laplacian_newtonPotential (smooth_real_component hg) (compact_real_component hc),
    laplacian_newtonPotential (smooth_imag_component hg) (compact_imag_component hc)]
  have he:=Complex.re_add_im (g x)
  linear_combination he

lemma norm_complexGradient_le {f : Plane → ℝ} {B : ℝ} {x : Plane}
    (hb : ∀i : Fin 2,|coordPartial f i x|≤B) : ‖complexGradient f x‖≤2*B := by
  unfold complexGradient
  calc
    _ ≤ ‖(coordPartial f 0 x : ℂ)‖+‖Complex.I*(coordPartial f 1 x : ℂ)‖ := norm_sub_le _ _
    _ ≤ B+B := by simpa only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] using add_le_add (hb 0) (hb 1)
    _ = _ := by ring

lemma norm_cauchyPotential_le {C B : ℝ} (hC : NewtonControl C) (hB : 0≤B)
    {g : Plane → ℂ} (hg : CSmooth g) (hc : HasCompactSupport g)
    (hs : ∀x,3≤‖x‖ → g x=0) (hb : ∀x∈Metric.ball (0:Plane) 3,‖g x‖≤B)
    {x : Plane} (hx : x∈Metric.ball 0 3) : ‖cauchyPotential g x‖≤8*C*B := by
  have hsr : ∀x,3≤‖x‖ → (g x).re=0 := fun x hx =>by simp [hs x hx]
  have hsi : ∀x,3≤‖x‖ → (g x).im=0 := fun x hx =>by simp [hs x hx]
  have hbr : ∀x∈Metric.ball (0:Plane) 3,|(g x).re|≤B := fun x hx =>(Complex.abs_re_le_norm _).trans (hb x hx)
  have hbi : ∀x∈Metric.ball (0:Plane) 3,|(g x).im|≤B := fun x hx =>(Complex.abs_im_le_norm _).trans (hb x hx)
  have hr:=norm_complexGradient_le (hC.2 _ (smooth_real_component hg) (compact_real_component hc) B hB hsr hbr x hx).2
  have hi:=norm_complexGradient_le (hC.2 _ (smooth_imag_component hg) (compact_imag_component hc) B hB hsi hbi x hx).2
  unfold cauchyPotential
  calc
    _ ≤ ‖(2:ℂ)*complexGradient (newtonPotential (fun y =>(g y).re)) x‖+
        ‖Complex.I*(2*complexGradient (newtonPotential (fun y =>(g y).im)) x)‖ := norm_add_le _ _
    _ ≤ 2*(2*(C*B))+2*(2*(C*B)) := by
      norm_num only [norm_mul,Complex.norm_I,one_mul,Complex.norm_ofNat]
      gcongr
    _ = _ := by ring

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma complexPartial_exp {f : Plane → ℂ} (hf : CSmooth f) (i : Fin 2) (x : Plane) :
    complexPartial (fun y =>Complex.exp (f y)) i x=Complex.exp (f x)*complexPartial f i x := by
  have he:=(hf.differentiable (by simp) |>.differentiableAt (x:=x) |>.hasFDerivAt).cexp
  exact congrFun (congrArg DFunLike.coe he.fderiv) (EuclideanSpace.single i 1)

lemma barPartial_exp {f : Plane → ℂ} (hf : CSmooth f) (x : Plane) :
    barPartial (fun y =>Complex.exp (f y)) x=Complex.exp (f x)*barPartial f x := by
  simp only [barPartial,complexPartial_exp hf]; ring

lemma complexPartial_neg {f : Plane → ℂ} (hf : CSmooth f) (i : Fin 2) (x : Plane) :
    complexPartial (fun y => -f y) i x= -complexPartial f i x := by
  have he:=(hf.differentiable (by simp) |>.differentiableAt (x:=x) |>.hasFDerivAt).neg
  exact congrFun (congrArg DFunLike.coe he.fderiv) (EuclideanSpace.single i 1)

lemma barPartial_neg {f : Plane → ℂ} (hf : CSmooth f) (x : Plane) :
    barPartial (fun y => -f y) x= -barPartial f x := by
  simp only [barPartial,complexPartial_neg hf]; ring

lemma barPartial_similarity {w α : Plane → ℂ} (hw : CSmooth w) (ha : CSmooth α)
    (hc : HasCompactSupport α) (x : Plane) :
    barPartial (fun y =>Complex.exp (-cauchyPotential α y)*w y) x=
      Complex.exp (-cauchyPotential α x)*(barPartial w x-α x*w x) := by
  have hs:=csmooth_cauchyPotential ha hc
  rw [barPartial_mul hs.neg.cexp hw,barPartial_exp hs.neg,barPartial_neg hs,
    barPartial_cauchyPotential ha hc]
  ring

lemma complexToPlane_one : complexToPlane (1:ℂ)=EuclideanSpace.single 0 1 := by
  ext i
  fin_cases i <;> simp [complexToPlane,Complex.orthonormalBasisOneI_repr_apply]

lemma complexToPlane_I : complexToPlane Complex.I=EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp [complexToPlane,Complex.orthonormalBasisOneI_repr_apply]

lemma holomorphic_of_barPartial_eq_zero {f : Plane → ℂ} {x : Plane}
    (hf : DifferentiableAt ℝ f x) (hz : barPartial f x=0) :
    DifferentiableAt ℂ (fun z =>f (complexToPlane z)) (planeToComplex x) := by
  have hbase : HasFDerivAt f (fderiv ℝ f x) (complexToPlane (planeToComplex x)) := by
    simpa only [planeToComplex,LinearIsometryEquiv.apply_symm_apply] using hf.hasFDerivAt
  have hcomp:=hbase.comp (planeToComplex x) complexToPlane.toContinuousLinearEquiv.hasFDerivAt
  simp only [Function.comp_def] at hcomp
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨hcomp.differentiableAt,?_⟩
  rw [hcomp.fderiv]
  change (fderiv ℝ f x) (complexToPlane Complex.I)=Complex.I*(fderiv ℝ f x) (complexToPlane 1)
  rw [complexToPlane_I,complexToPlane_one]
  have hzero : complexPartial f 0 x+Complex.I*complexPartial f 1 x=0 :=
    by simpa only [barPartial,div_eq_zero_iff,OfNat.ofNat_ne_zero,or_false] using hz
  have hi:=congrArg (fun z : ℂ => Complex.I*z) hzero
  simp only [mul_add,←mul_assoc,Complex.I_mul_I,neg_one_mul,mul_zero] at hi
  change complexPartial f 1 x=Complex.I*complexPartial f 0 x
  linear_combination -hi

end SharpNodal.Profiles

end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Similarity
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

namespace SharpNodal.Profiles
open Carleman

lemma smooth_normSq {w : Plane → ℂ} (hw : CSmooth w) :
    Smooth (fun x =>Complex.normSq (w x)) :=
  ((smooth_real_component hw).mul (smooth_real_component hw)).add
    ((smooth_imag_component hw).mul (smooth_imag_component hw))

lemma csmooth_regularizedCoefficient {w b : Plane → ℂ} (hw : CSmooth w) (hb : CSmooth b)
    {η : ℝ} (hη : 0<η) : CSmooth (regularizedCoefficient w b η) := by
  have hn : ∀x,Complex.normSq (w x)+η^2≠0 := fun x =>
    ne_of_gt (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (sq_pos_of_pos hη))
  unfold regularizedCoefficient
  simp only [div_eq_mul_inv,←Complex.ofReal_inv]
  exact (hb.mul (Complex.conjCLE.contDiff.comp hw)).mul
    (csmooth_ofReal (((smooth_normSq hw).add contDiff_const).inv hn))

lemma norm_regularizedCoefficient_le {w b : Plane → ℂ} {η B : ℝ} {x : Plane}
    (hη : 0<η) (hB : 0≤B) (hb : ‖b x‖≤B*‖w x‖) :
    ‖regularizedCoefficient w b η x‖≤B := by
  have hd : 0<Complex.normSq (w x)+η^2 := add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (sq_pos_of_pos hη)
  simp only [regularizedCoefficient,norm_div,norm_mul,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  calc
    ‖b x‖*‖w x‖ ≤ B*‖w x‖*‖w x‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ ≤ B*(Complex.normSq (w x)+η^2) := by rw [Complex.normSq_eq_norm_sq]; nlinarith [mul_nonneg hB (sq_nonneg η)]

lemma regularizedCoefficient_residual {w b : Plane → ℂ} {η : ℝ} (hη : 0<η) (x : Plane) :
    b x-regularizedCoefficient w b η x*w x=
      b x*((η^2 : ℝ):ℂ)/((Complex.normSq (w x)+η^2 : ℝ):ℂ) := by
  have hd : ((Complex.normSq (w x)+η^2 : ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (sq_pos_of_pos hη)))
  unfold regularizedCoefficient
  field_simp [hd]
  simp only [Complex.ofReal_add]
  have he:=Complex.mul_conj (w x)
  linear_combination -(b x)*he

lemma norm_regularizedCoefficient_residual_le {w b : Plane → ℂ} {η B : ℝ} {x : Plane}
    (hη : 0<η) (hB : 0≤B) (hb : ‖b x‖≤B*‖w x‖) :
    ‖b x-regularizedCoefficient w b η x*w x‖≤B*η := by
  have hd : 0<Complex.normSq (w x)+η^2 := add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (sq_pos_of_pos hη)
  rw [regularizedCoefficient_residual hη]
  simp only [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd,abs_of_nonneg (sq_nonneg η)]
  apply (div_le_iff₀ hd).mpr
  calc
    ‖b x‖*η^2 ≤ (B*‖w x‖)*η^2 := mul_le_mul_of_nonneg_right hb (sq_nonneg η)
    _ ≤ B*η*(Complex.normSq (w x)+η^2) := by
      rw [Complex.normSq_eq_norm_sq]
      have he : ‖w x‖*η≤‖w x‖^2+η^2 := by nlinarith [sq_nonneg (‖w x‖-η)]
      nlinarith [mul_le_mul_of_nonneg_left he (mul_nonneg hB hη.le)]

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
namespace SharpNodal.Profiles
open Carleman

lemma csmooth_barPartial {w : Plane → ℂ} (hw : CSmooth w) : CSmooth (barPartial w) :=
  ((csmooth_partial hw 0).add (contDiff_const.mul (csmooth_partial hw 1))).div_const 2

lemma norm_cutoff_mul_le (ζ : ContDiffBump (0:Plane)) {g : Plane → ℂ} {B : ℝ}
    (hB : 0≤B) (hb : ∀x∈Metric.ball (0:Plane) ζ.rOut,‖g x‖≤B) (x : Plane) :
    ‖(ζ x : ℂ)*g x‖≤B := by
  by_cases hx : x∈Metric.ball (0:Plane) ζ.rOut
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ζ.nonneg]
    exact (mul_le_mul_of_nonneg_right ζ.le_one (norm_nonneg _)).trans (by simpa using hb x hx)
  · have hz : ζ x=0 := ζ.zero_of_le_dist (by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx)
    simpa only [hz,Complex.ofReal_zero,zero_mul,norm_zero] using hB

lemma norm_exp_neg_le {ψ : Plane → ℂ} {s : ℝ} {x : Plane} (hs : ‖ψ x‖ ≤ s) :
    ‖Complex.exp (-ψ x)‖≤Real.exp s := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans ((Complex.abs_re_le_norm (-ψ x)).trans (by simpa only [norm_neg] using hs))

theorem approximate_similarity {C B E η : ℝ} (hC : NewtonControl C) (hB : 0≤B)
    (hE : 0≤E) (hη : 0<η) {w b : Plane → ℂ} (hw : CSmooth w) (hb : CSmooth b)
    (hbnd : ∀x∈Metric.ball (0:Plane) (9/4),‖b x‖≤B*‖w x‖)
    (herr : ∀x∈Metric.ball (0:Plane) 2,‖barPartial w x-b x‖≤E) :
    ∃ψ H : Plane → ℂ,CSmooth ψ ∧ CSmooth H ∧
      (∀x∈Metric.ball (0:Plane) 3,‖ψ x‖≤8*C*B) ∧
      (∀x∈Metric.ball (0:Plane) (3/2),barPartial H x=0) ∧
      (∀x∈Metric.ball (0:Plane) 3,
        ‖H x-Complex.exp (-ψ x)*w x‖≤8*C*(Real.exp (8*C*B)*(E+B*η))) := by
  let α : Plane → ℂ := fun x =>(similarityCutoff x : ℂ)*regularizedCoefficient w b η x
  have ha : CSmooth α := (csmooth_ofReal similarityCutoff.contDiff).mul (csmooth_regularizedCoefficient hw hb hη)
  have hac : HasCompactSupport α := (similarityCutoff.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have has : ∀x,3≤‖x‖ → α x=0 := by
    intro x hx
    have hz:=similarityCutoff.zero_of_le_dist (x:=x) (by
      change 9/4≤dist x 0
      simpa only [dist_zero_right] using (show (9/4:ℝ)≤‖x‖ by linarith))
    simp only [α,hz,Complex.ofReal_zero,zero_mul]
  have hab : ∀x,‖α x‖≤B := norm_cutoff_mul_le similarityCutoff hB
    (fun x hx =>norm_regularizedCoefficient_le hη hB (hbnd x hx))
  let ψ:=cauchyPotential α
  have hp : CSmooth ψ := csmooth_cauchyPotential ha hac
  have hpb : ∀x∈Metric.ball (0:Plane) 3,‖ψ x‖≤8*C*B :=
    fun x hx =>norm_cauchyPotential_le hC hB ha hac has (fun y _ =>hab y) hx
  let h : Plane → ℂ := fun x =>Complex.exp (-ψ x)*w x
  have hh : CSmooth h := hp.neg.cexp.mul hw
  have hηE : 0≤Real.exp (8*C*B)*(E+B*η) := by positivity
  have hdb : ∀x∈Metric.ball (0:Plane) 2,‖barPartial h x‖≤Real.exp (8*C*B)*(E+B*η) := by
    intro x hx
    have hx3 : x∈Metric.ball (0:Plane) 3 := Metric.ball_subset_ball (by norm_num) hx
    have hxa : x∈Metric.ball (0:Plane) (9/4) := Metric.ball_subset_ball (by norm_num) hx
    have hχ : similarityCutoff x=1 := similarityCutoff.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    have he : α x=regularizedCoefficient w b η x := by simp only [α,hχ,Complex.ofReal_one,one_mul]
    rw [show barPartial h x=Complex.exp (-ψ x)*(barPartial w x-α x*w x) from barPartial_similarity hw ha hac x,norm_mul,he]
    apply mul_le_mul (norm_exp_neg_le (hpb x hx3)) _ (norm_nonneg _) (Real.exp_pos _).le
    calc
      _ = ‖(barPartial w x-b x)+(b x-regularizedCoefficient w b η x*w x)‖ := by congr 1; ring
      _ ≤ ‖barPartial w x-b x‖+‖b x-regularizedCoefficient w b η x*w x‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (herr x hx) (norm_regularizedCoefficient_residual_le hη hB (hbnd x hxa))
  let R : Plane → ℂ := fun x =>(correctionCutoff x : ℂ)*barPartial h x
  have hr : CSmooth R := (csmooth_ofReal correctionCutoff.contDiff).mul (csmooth_barPartial hh)
  have hrc : HasCompactSupport R := (correctionCutoff.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have hrs : ∀x,3≤‖x‖ → R x=0 := by
    intro x hx
    have hz:=correctionCutoff.zero_of_le_dist (x:=x) (by
      change 7/4≤dist x 0
      simpa only [dist_zero_right] using (show (7/4:ℝ)≤‖x‖ by linarith))
    simp only [R,hz,Complex.ofReal_zero,zero_mul]
  have hrb : ∀x,‖R x‖≤Real.exp (8*C*B)*(E+B*η) :=
    norm_cutoff_mul_le correctionCutoff hηE (fun x hx =>hdb x (Metric.ball_subset_ball (by norm_num [correctionCutoff]) hx))
  let H : Plane → ℂ := fun x =>h x-cauchyPotential R x
  have hH : CSmooth H := hh.sub (csmooth_cauchyPotential hr hrc)
  refine ⟨ψ,H,hp,hH,hpb,?_,?_⟩
  · intro x hx
    have hχ : correctionCutoff x=1 := correctionCutoff.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    change barPartial (fun y =>h y-cauchyPotential R y) x=0
    rw [barPartial_sub hh (csmooth_cauchyPotential hr hrc),barPartial_cauchyPotential hr hrc]
    simp only [R,hχ,Complex.ofReal_one,one_mul,sub_self]
  · intro x hx
    have he : H x-Complex.exp (-ψ x)*w x= -cauchyPotential R x := by dsimp [H,h]; ring
    rw [he,norm_neg]
    exact norm_cauchyPotential_le hC hηE hr hrc hrs (fun y _ =>hrb y) hx

end SharpNodal.Profiles

noncomputable section
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
namespace SharpNodal.Profiles

lemma normal_family_fixed_disk {B : ℝ} (hB : 0≤B) {F : ℕ → ℂ → ℂ}
    (hF : ∀n,DifferentiableOn ℂ (F n) (ball 0 (3/2)))
    (hb : ∀n,∀z∈ball (0:ℂ) (3/2),‖F n z‖≤B) :
    ∃ H : ℂ → ℂ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      TendstoUniformlyOn (fun n =>F (σ n)) H atTop (closedBall 0 1) ∧
      DifferentiableOn ℂ H (ball 0 1) ∧ ∀z∈closedBall (0:ℂ) 1,‖H z‖≤B := by
  classical
  have hsub : closedBall (0:ℂ) 1 ⊆ ball 0 (3/2) := closedBall_subset_ball (by norm_num)
  have hd : ∀n,∀z∈closedBall (0:ℂ) 1,‖deriv (F n) z‖≤4*B := by
    intro n z hz
    have hs : closedBall z (1/4) ⊆ ball (0:ℂ) (3/2) := by
      intro w hw
      simp only [mem_ball,dist_zero_right]
      have hz' : ‖z‖≤1 := by simpa only [mem_closedBall,dist_zero_right] using hz
      have hw' : ‖w-z‖≤1/4 := by simpa only [mem_closedBall,dist_eq_norm] using hw
      have ht:=norm_add_le (w-z) z
      have hh : ‖w‖≤‖w-z‖+‖z‖ := by simpa only [sub_add_cancel] using ht
      linarith
    have hh:=Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ)<1/4)
      ((hF n).diffContOnCl_ball hs) (fun w hw =>hb n w (hs (sphere_subset_closedBall hw)))
    convert hh using 1 <;> first | rfl | ring
  let K : ℝ≥0:=⟨4*B,by positivity⟩
  have hl : ∀n,LipschitzOnWith K (F n) (closedBall 0 1) := by
    intro n
    exact (convex_closedBall (0:ℂ) 1).lipschitzOnWith_of_nnnorm_deriv_le
      (fun z hz =>(hF n).differentiableAt (isOpen_ball.mem_nhds (hsub hz))) (fun z hz =>hd n z hz)
  let X:=closedBall (0:ℂ) 1
  let G : ℕ → X →ᵇ ℂ := fun n =>BoundedContinuousFunction.mkOfCompact
    ⟨fun z => F n z,((hF n).continuousOn.mono hsub).domRestrict⟩
  have hlG : ∀n,LipschitzWith K (G n) := fun n x y =>hl n x.property y.property
  have hc:=BoundedContinuousFunction.arzela_ascoli (closedBall (0:ℂ) B) (isCompact_closedBall 0 B)
    (range G) (by
      rintro f x ⟨n,rfl⟩
      exact (mem_closedBall_zero_iff).mpr (hb n x (hsub x.property)))
    ((LipschitzWith.uniformEquicontinuous (fun f : range G => (f.1 : X → ℂ)) K (by
      rintro ⟨f,n,rfl⟩; exact hlG n)).equicontinuous)
  obtain ⟨g,_,σ,hσ,hconv⟩:=hc.tendsto_subseq (fun n =>subset_closure (mem_range_self n))
  let H : ℂ → ℂ:=fun z =>if hz:z∈X then g ⟨z,hz⟩ else 0
  have hrestrict : ∀z:X,H z=g z := by intro z; simp only [H,dite_eq_left z.property]
  have hunif : TendstoUniformlyOn (fun n =>F (σ n)) H atTop X := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have hh:=BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv
    change TendstoUniformly (fun n (z:X) => F (σ n) z) g atTop at hh
    simpa only [Function.comp_def,hrestrict] using hh
  refine ⟨H,σ,hσ,hunif,?_,?_⟩
  · exact (hunif.tendstoLocallyUniformlyOn.mono ball_subset_closedBall).differentiableOn
      (Eventually.of_forall (fun n =>(hF (σ n)).mono (ball_subset_ball (by norm_num)))) isOpen_ball
  · intro z hz
    exact le_of_tendsto (hunif.tendsto_at hz |>.norm) (Eventually.of_forall (fun n =>hb (σ n) z (hsub hz)))

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma norm_exp_sub_one_le_exp_norm (z : ℂ) :
    ‖Complex.exp z-1‖≤Real.exp ‖z‖-1 := by
  simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z 1

theorem sequence_similarity {C B E W : ℝ} (hC : NewtonControl C)
    (hB : 0≤B) (hE : 0≤E) (hW : 0≤W)
    {r : ℕ → ℝ} (hr : ∀n,0 ≤ r n ∧ r n≤1) (hrt : Tendsto r atTop (𝓝 0))
    {w b : ℕ → Plane → ℂ} (hw : ∀n,CSmooth (w n)) (hb : ∀n,CSmooth (b n))
    (hbb : ∀n,∀x∈Metric.ball (0:Plane) (9/4),‖b n x‖≤B*‖w n x‖)
    (herr : ∀n,∀x∈Metric.ball (0:Plane) 2,‖barPartial (w n) x-b n x‖≤E*r n)
    (hwb : ∀n,∀x∈Metric.ball (0:Plane) (3/2),‖w n x‖≤W)
    {wlim : Plane → ℂ}
    (hwt : ∀x∈Metric.closedBall (0:Plane) 1,Tendsto (fun n =>w n x) atTop (𝓝 (wlim x))) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (Metric.ball 0 1) ∧
      ∀x∈Metric.closedBall (0:Plane) 1,
        ‖H (planeToComplex x)-wlim x‖≤(Real.exp (8*C*B)-1)*‖wlim x‖ := by
  classical
  let η : ℕ → ℝ:=fun n =>(1/2)^(n+1)
  have hη : ∀n,0<η n := by intro n; positivity
  have hηb : ∀n,η n≤1 := by intro n; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hηt : Tendsto η atTop (𝓝 0) := by
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  choose ψ HH hp hH hpb hz he using fun n => approximate_similarity hC hB
    (mul_nonneg hE (hr n).1) (hη n) (hw n) (hb n) (hbb n) (herr n)
  let R : ℕ → ℝ:=fun n =>8*C*(Real.exp (8*C*B)*(E*r n+B*η n))
  have hR : ∀n,0≤R n := by intro n; dsimp [R]; have:=hC.1; have:=(hr n).1; have:=(hη n).le; positivity
  have hRt : Tendsto R atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      (((hrt.const_mul E).add (hηt.const_mul B)).const_mul (Real.exp (8*C*B))).const_mul (8*C)
  have hRbound : ∀n,R n≤8*C*Real.exp (8*C*B)*(E+B) := by
    intro n
    have hC0 : 0≤C := le_trans (by norm_num) hC.1
    dsimp [R]
    rw [←mul_assoc]
    gcongr
    · exact mul_le_of_le_one_right hE (hr n).2
    · exact mul_le_of_le_one_right hB (hηb n)
  let F : ℕ → ℂ → ℂ:=fun n z =>HH n (complexToPlane z)
  have hFd : ∀n,DifferentiableOn ℂ (F n) (Metric.ball 0 (3/2)) := by
    intro n z hz'
    have hx : complexToPlane z∈Metric.ball (0:Plane) (3/2) := by
      simpa only [Metric.mem_ball,dist_zero_right,LinearIsometryEquiv.norm_map] using hz'
    have ht:=holomorphic_of_barPartial_eq_zero ((hH n).differentiable (by simp) |>.differentiableAt) (hz n (complexToPlane z) hx)
    simpa only [F,planeToComplex,LinearIsometryEquiv.symm_apply_apply] using ht.differentiableWithinAt
  let M : ℝ:=Real.exp (8*C*B)*W+8*C*Real.exp (8*C*B)*(E+B)
  have hM : 0≤M := by dsimp [M]; have:=hC.1; positivity
  have hFb : ∀n,∀z∈Metric.ball (0:ℂ) (3/2),‖F n z‖≤M := by
    intro n z hz'
    have hx : complexToPlane z∈Metric.ball (0:Plane) (3/2) := by
      simpa only [Metric.mem_ball,dist_zero_right,LinearIsometryEquiv.norm_map] using hz'
    have hx3 : complexToPlane z∈Metric.ball (0:Plane) 3 := Metric.ball_subset_ball (by norm_num) hx
    calc
      _ ≤ ‖Complex.exp (-ψ n (complexToPlane z))*w n (complexToPlane z)‖+R n := by
        exact (norm_le_norm_add_norm_sub' (F n z) (Complex.exp (-ψ n (complexToPlane z))*w n (complexToPlane z))).trans
          (add_le_add le_rfl (he n _ hx3))
      _ ≤ Real.exp (8*C*B)*W+8*C*Real.exp (8*C*B)*(E+B) := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul (norm_exp_neg_le (hpb n _ hx3)) (hwb n _ hx)
          (norm_nonneg _) (Real.exp_pos _).le) (hRbound n)
  obtain ⟨H,σ,hσ,hconv,hHol,_⟩:=normal_family_fixed_disk hM hFd hFb
  refine ⟨H,hHol,?_⟩
  intro x hx
  have hx3 : x∈Metric.ball (0:Plane) 3 := Metric.closedBall_subset_ball (by norm_num) hx
  have hew : ∀n,‖HH n x-w n x‖≤(Real.exp (8*C*B)-1)*‖w n x‖+R n := by
    intro n
    have hrem : ‖Complex.exp (-ψ n x)-1‖≤Real.exp (8*C*B)-1 :=
      (norm_exp_sub_one_le_exp_norm _).trans (by gcongr; simpa only [norm_neg] using hpb n x hx3)
    calc
      _ = ‖(Complex.exp (-ψ n x)-1)*w n x+(HH n x-Complex.exp (-ψ n x)*w n x)‖ := by congr 1; ring
      _ ≤ ‖(Complex.exp (-ψ n x)-1)*w n x‖+‖HH n x-Complex.exp (-ψ n x)*w n x‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_right hrem (norm_nonneg _)) (he n x hx3)
  have hxp : planeToComplex x∈Metric.closedBall (0:ℂ) 1 := by
    simpa only [Metric.mem_closedBall,dist_zero_right,LinearIsometryEquiv.norm_map] using hx
  have htH : Tendsto (fun n =>HH (σ n) x) atTop (𝓝 (H (planeToComplex x))) := by
    simpa only [F,planeToComplex,LinearIsometryEquiv.apply_symm_apply] using hconv.tendsto_at hxp
  have htw := (hwt x hx).comp hσ.tendsto_atTop
  have htr := hRt.comp hσ.tendsto_atTop
  have hle:=le_of_tendsto_of_tendsto (htH.sub htw |>.norm)
    ((htw.norm.const_mul (Real.exp (8*C*B)-1)).add htr) (Eventually.of_forall (fun n =>hew (σ n)))
  simpa only [add_zero] using hle

end SharpNodal.Profiles

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_HolomorphicGradient
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

namespace SharpNodal.Profiles
open Carleman

lemma partial_quotient {U φ : Plane → ℝ} {x : Plane}
    (hU : DifferentiableAt ℝ U x) (hφ : DifferentiableAt ℝ φ x) (hne : φ x≠0)
    (i : Fin 2) :
    coordPartial (fun y =>U y/φ y) i x=
      (coordPartial U i x*φ x-U x*coordPartial φ i x)/(φ x)^2 := by
  have hi := (hasDerivAt_inv hne).comp_hasFDerivAt x hφ.hasFDerivAt
  have hp := hU.hasFDerivAt.mul hi
  simp only [Function.comp_def] at hp
  unfold coordPartial
  simp only [div_eq_mul_inv]
  have he:=hp.fderiv
  change fderiv ℝ (fun y =>U y*(φ y)⁻¹) x=_ at he
  rw [he]
  simp only [add_apply,smul_apply,smul_eq_mul]
  field_simp [hne]
  ring

lemma abs_partial_le_norm_gradient (v : Plane → ℝ) (i : Fin 2) (x : Plane) :
    |coordPartial v i x|≤‖complexGradient v x‖ := by
  fin_cases i
  · simpa [complexGradient] using Complex.abs_re_le_norm (complexGradient v x)
  · simpa [complexGradient] using Complex.abs_im_le_norm (complexGradient v x)

lemma norm_gradient_le (v : Plane → ℝ) (x : Plane) :
    ‖complexGradient v x‖≤|coordPartial v 0 x|+|coordPartial v 1 x| := by
  exact (norm_sub_le _ _).trans (by simp [Complex.norm_real])

lemma csmooth_conductivityDrift {U φ : Plane → ℝ} (hU : Smooth U)
    (hφ : Smooth φ) (hne : ∀x,φ x≠0) : CSmooth (conductivityDrift U φ) := by
  apply csmooth_ofReal
  exact (ContDiff.sum (fun i _ =>((smooth_partial hφ i).div hφ hne).mul
    (smooth_partial (hU.div hφ hne) i))).neg

lemma conductivityDrift_bound {U φ : Plane → ℝ} {a d : ℝ} (ha : 0<a) (hd : 0≤d)
    {x : Plane} (hφ : a≤φ x) (hder : ∀i,|coordPartial φ i x|≤d) :
    ‖conductivityDrift U φ x‖≤(2*d/a)*‖complexGradient (fun y =>U y/φ y) x‖ := by
  rw [conductivityDrift,Complex.norm_real,Real.norm_eq_abs,abs_neg]
  calc
    _ ≤ ∑i : Fin 2,|coordPartial φ i x/φ x*coordPartial (fun y =>U y/φ y) i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_i : Fin 2,(d/a)*‖complexGradient (fun y =>U y/φ y) x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_div,abs_of_pos (ha.trans_le hφ)]
      exact mul_le_mul (div_le_div₀ hd (hder i) ha hφ)
        (abs_partial_le_norm_gradient _ i x) (abs_nonneg _) (div_nonneg hd ha.le)
    _ = _ := by simp only [Fin.sum_univ_two]; ring

lemma quotient_barPartial_error {U φ : Plane → ℝ} (hU : Smooth U) (hφ : Smooth φ)
    (hne : ∀x,φ x≠0) {q r : Plane → ℝ} {x : Plane}
    (hUE : euclideanLaplacian U x+q x*U x=0)
    (hφE : euclideanLaplacian φ x+q x*φ x=r x) :
    barPartial (complexGradient (fun y =>U y/φ y)) x-conductivityDrift U φ x=
      (-(r x*U x/(2*(φ x)^2)) : ℝ) := by
  have hv : Smooth (fun y =>U y/φ y) := hU.div hφ hne
  rw [barPartial_gradient hv]
  have he:=quotient_laplacian hU hφ hne hUE hφE
  rw [←Complex.ofReal_ofNat (n:=2),←Complex.ofReal_div,he]
  simp only [conductivityDrift,Complex.ofReal_sub,sub_sub_cancel_left]
  push_cast
  field_simp [hne x]

lemma quotient_partial_bound {U φ : Plane → ℝ} {x : Plane} {K d : ℝ}
    (hK : 0≤K) (hd : 0≤d) (hU : DifferentiableAt ℝ U x)
    (hφ : DifferentiableAt ℝ φ x) (hφb : 1/2≤φ x)
    (hval : |U x|≤K) (hderU : ∀i,|coordPartial U i x|≤K)
    (hderφ : ∀i,|coordPartial φ i x|≤d) (i : Fin 2) :
    |coordPartial (fun y =>U y/φ y) i x|≤2*K+4*K*d := by
  have hpos : 0<φ x := by linarith
  rw [partial_quotient hU hφ hpos.ne' i]
  have he : (coordPartial U i x*φ x-U x*coordPartial φ i x)/(φ x)^2=
      coordPartial U i x/φ x-U x*coordPartial φ i x/(φ x)^2 := by field_simp
  rw [he]
  apply (abs_sub _ _).trans
  simp only [abs_div,abs_mul,abs_pow,abs_of_pos hpos]
  have h1 : |coordPartial U i x|/φ x≤2*K := by
    have ht:=div_le_div₀ hK (hderU i) (by norm_num : (0:ℝ)<1/2) hφb
    linarith only [ht]
  have h2 : |U x| * |coordPartial φ i x|/(φ x)^2≤4*K*d := by
    have hs : (1/4:ℝ)≤(φ x)^2 := by nlinarith
    have ht:=div_le_div₀ (mul_nonneg hK hd) (mul_le_mul hval (hderφ i) (abs_nonneg _) hK)
      (by norm_num : (0:ℝ)<1/4) hs
    linarith only [ht]
  exact add_le_add h1 h2

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

namespace SmallPotential
variable {C ε δ : ℝ} {q : Plane → ℝ} (h : SmallPotential C ε δ q)
include h

lemma δ_lt : δ<1 := by have:=h.δ_le; linarith
lemma ratio_nonneg : 0 ≤ δ/(1-δ) := div_nonneg h.δ_nonneg (by have:=h.δ_lt; linarith)
lemma ratio_le : δ/(1-δ) ≤ 1 := (div_le_iff₀ (by have:=h.δ_lt; linarith)).mpr (by have:=h.δ_le; linarith)

lemma approx_lower (n : ℕ) (x : Plane) : 1/2 ≤ positiveApprox q n x :=
  positiveApprox_lower h.control h.ε_nonneg h.δ_nonneg h.δ_le h.small
    h.smooth h.compact h.support h.bound n x

lemma approx_smooth (n : ℕ) : Smooth (positiveApprox q n) := smooth_positiveApprox h.smooth h.compact n

lemma approx_ne (n : ℕ) (x : Plane) : positiveApprox q n x≠0 := by have:=h.approx_lower n x; linarith

lemma approx_partial_bound (n : ℕ) {x : Plane} (hx : x∈Metric.ball (0:Plane) (5/2)) (i : Fin 2) :
    |coordPartial (positiveApprox q n) i x| ≤ δ/(1-δ) := by
  rw [positiveApprox_partial hx]
  exact (multiplierApprox_bounds h.control h.ε_nonneg h.δ_nonneg h.δ_lt h.small
    h.smooth h.compact h.support h.bound n (Metric.ball_subset_ball (by norm_num) hx)).2 i

lemma limit_lower {x : Plane} (hx : x∈Metric.ball (0:Plane) 3) :
    1/2 ≤ multiplierLimit q x := by
  have he := (multiplierLimit_bounds h.control h.ε_nonneg h.δ_nonneg h.δ_lt h.small
    h.smooth h.compact h.support h.bound hx).1
  have hb : δ/(1-δ) ≤ 1/2 := (div_le_iff₀ (by have:=h.δ_lt; linarith)).mpr (by have:=h.δ_le; linarith)
  have := (abs_le.mp (he.trans hb)).1
  linarith

lemma limit_differentiable {x : Plane} (hx : x∈Metric.ball (0:Plane) 3) :
    DifferentiableAt ℝ (multiplierLimit q) x :=
  (multiplierLimit_hasFDerivAt h.control h.ε_nonneg h.δ_nonneg h.δ_lt h.small
    h.smooth h.compact h.support h.bound hx).differentiableAt

lemma approx_converges {x : Plane} (hx : x∈Metric.ball (0:Plane) (5/2)) :
    Tendsto (fun n =>positiveApprox q n x) atTop (𝓝 (multiplierLimit q x)) ∧
    ∀i,Tendsto (fun n =>coordPartial (positiveApprox q n) i x) atTop
      (𝓝 (coordPartial (multiplierLimit q) i x)) := by
  obtain ⟨hv,hd⟩ := multiplierLimit_convergence h.control h.ε_nonneg h.δ_nonneg h.δ_lt h.small
    h.smooth h.compact h.support h.bound
  have hx3 : x∈Metric.ball (0:Plane) 3 := Metric.ball_subset_ball (by norm_num) hx
  constructor
  · simpa only [positiveApprox_eq hx] using hv.tendsto_at hx3
  · intro i
    have he:=((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.tendsto _).comp (hd.tendsto_at hx3)
    change Tendsto (fun n=>coordPartial (multiplierApprox q n) i x) atTop
      (𝓝 (coordPartial (multiplierLimit q) i x)) at he
    simp_rw [positiveApprox_partial hx]
    exact he

lemma quotient_gradient_converges {U : Plane → ℝ} (hU : Smooth U) {x : Plane}
    (hx : x∈Metric.ball (0:Plane) (5/2)) :
    Tendsto (fun n =>complexGradient (fun y =>U y/positiveApprox q n y) x) atTop
      (𝓝 (complexGradient (fun y =>U y/multiplierLimit q y) x)) := by
  obtain ⟨hv,hd⟩:=h.approx_converges hx
  have hx3 : x∈Metric.ball (0:Plane) 3 := Metric.ball_subset_ball (by norm_num) hx
  have hne : multiplierLimit q x≠0 := by have:=h.limit_lower hx3; linarith
  have hpart (i : Fin 2) :
      Tendsto (fun n =>coordPartial (fun y =>U y/positiveApprox q n y) i x) atTop
        (𝓝 (coordPartial (fun y =>U y/multiplierLimit q y) i x)) := by
    simp only [partial_quotient (hU.differentiable (by simp) |>.differentiableAt)
      ((h.approx_smooth _).differentiable (by simp) |>.differentiableAt) (h.approx_ne _ x),
      partial_quotient (hU.differentiable (by simp) |>.differentiableAt) (h.limit_differentiable hx3) hne]
    exact ((hv.const_mul _).sub ((hd i).const_mul _)).div (hv.pow 2) (pow_ne_zero _ hne)
  exact (Complex.continuous_ofReal.tendsto _ |>.comp (hpart 0)).sub
    ((Complex.continuous_ofReal.tendsto _ |>.comp (hpart 1)).const_mul Complex.I)

lemma approx_equation (n : ℕ) {x : Plane} (hx : x∈Metric.ball (0:Plane) (5/2)) :
    euclideanLaplacian (positiveApprox q n) x+q x*positiveApprox q n x=q x*neumannTerm q n x :=
  positiveApprox_equation h.smooth h.compact n hx

lemma term_bound (n : ℕ) {x : Plane} (hx : x∈Metric.ball (0:Plane) 3) :
    |neumannTerm q n x| ≤ δ^n :=
  (neumannTerm_bounds h.control h.ε_nonneg h.δ_nonneg h.small
    h.smooth h.compact h.support h.bound n x hx).1

theorem holomorphic_gradient {U : Plane → ℝ} (hU : Smooth U)
    (hUE : ∀x∈Metric.ball (0:Plane) (5/2),euclideanLaplacian U x+q x*U x=0)
    {K : ℝ} (hK : 0 ≤ K)
    (hUb : ∀x∈Metric.ball (0:Plane) 3,|U x| ≤ K ∧ ∀i,|coordPartial U i x| ≤ K) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (Metric.ball 0 1) ∧
      ∀x∈Metric.closedBall (0:Plane) 1,
        ‖H (planeToComplex x)-complexGradient (fun y =>U y/multiplierLimit q y) x‖ ≤
        (Real.exp (8*C*(4*δ/(1-δ)))-1)*‖complexGradient (fun y =>U y/multiplierLimit q y) x‖ := by
  let φ:=positiveApprox q
  let v : ℕ → Plane → ℝ:=fun n x =>U x/φ n x
  let w : ℕ → Plane → ℂ:=fun n =>complexGradient (v n)
  let b : ℕ → Plane → ℂ:=fun n =>conductivityDrift U (φ n)
  have hv : ∀n,Smooth (v n) := fun n =>hU.div (h.approx_smooth n) (h.approx_ne n)
  have hbb : ∀n,∀x∈Metric.ball (0:Plane) (9/4),‖b n x‖ ≤ (4*δ/(1-δ))*‖w n x‖ := by
    intro n x hx
    have hx' : x∈Metric.ball (0:Plane) (5/2) := Metric.ball_subset_ball (by norm_num) hx
    have he:=conductivityDrift_bound (U:=U) (φ:=φ n) (by norm_num : (0:ℝ)<1/2)
      h.ratio_nonneg (h.approx_lower n x) (h.approx_partial_bound n hx')
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [b,w,v,φ]; congr 1; ring
  have herr : ∀n,∀x∈Metric.ball (0:Plane) 2,‖barPartial (w n) x-b n x‖ ≤ (2*ε*K)*δ^n := by
    intro n x hx
    have hx' : x∈Metric.ball (0:Plane) (5/2) := Metric.ball_subset_ball (by norm_num) hx
    have hx3 : x∈Metric.ball (0:Plane) 3 := Metric.ball_subset_ball (by norm_num) hx
    have he:=quotient_barPartial_error (r:=fun x=>q x*neumannTerm q n x) hU (h.approx_smooth n) (h.approx_ne n) (hUE x hx') (h.approx_equation n hx')
    change ‖barPartial (complexGradient (fun y =>U y/positiveApprox q n y)) x-conductivityDrift U (positiveApprox q n) x‖ ≤ _
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_neg,abs_div,abs_mul,abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*(positiveApprox q n x)^2)]
    have hsq : (1/2:ℝ) ≤ 2*(positiveApprox q n x)^2 := by have:=h.approx_lower n x; nlinarith
    have ht:=div_le_div₀ (mul_nonneg (mul_nonneg h.ε_nonneg (pow_nonneg h.δ_nonneg n)) hK)
      (mul_le_mul (mul_le_mul (h.bound x hx3) (h.term_bound n hx3) (abs_nonneg _) h.ε_nonneg)
        (hUb x hx3).1 (abs_nonneg _) (mul_nonneg h.ε_nonneg (pow_nonneg h.δ_nonneg n)))
      (by norm_num : (0:ℝ)<1/2) hsq
    linarith only [ht]
  have hwb : ∀n,∀x∈Metric.ball (0:Plane) (3/2),‖w n x‖ ≤ 12*K := by
    intro n x hx
    have hx' : x∈Metric.ball (0:Plane) (5/2) := Metric.ball_subset_ball (by norm_num) hx
    have hx3 : x∈Metric.ball (0:Plane) 3 := Metric.ball_subset_ball (by norm_num) hx
    have hp (i : Fin 2) : |coordPartial (v n) i x| ≤ 6*K := by
      have ht:=quotient_partial_bound hK (by norm_num : (0:ℝ) ≤ 1)
        (hU.differentiable (by simp) |>.differentiableAt)
        ((h.approx_smooth n).differentiable (by simp) |>.differentiableAt)
        (h.approx_lower n x) (hUb x hx3).1 (hUb x hx3).2
        (fun i =>(h.approx_partial_bound n hx' i).trans h.ratio_le) i
      linarith only [ht]
    exact (norm_gradient_le (v n) x).trans (by have:=hp 0; have:=hp 1; linarith)
  exact sequence_similarity h.control (div_nonneg (mul_nonneg (by norm_num) h.δ_nonneg) (by have:=h.δ_lt; linarith))
    (by have:=h.ε_nonneg; positivity) (by positivity)
    (fun n =>⟨pow_nonneg h.δ_nonneg _,pow_le_one₀ h.δ_nonneg h.δ_lt.le⟩)
    (tendsto_pow_atTop_nhds_zero_of_lt_one h.δ_nonneg h.δ_lt)
    (fun n =>csmooth_gradient (hv n))
    (fun n =>csmooth_conductivityDrift hU (h.approx_smooth n) (h.approx_ne n))
    hbb herr hwb (fun x hx =>h.quotient_gradient_converges hU (Metric.closedBall_subset_ball (by norm_num) hx))

end SmallPotential
end SharpNodal.Profiles

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_NodalGraphs
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

namespace SharpNodal.Holomorphic

lemma blaschke_eq_inv (R : ℝ) (a z : ℂ) :
    blaschke R a z=(Complex.canonicalFactor R a z)⁻¹ := by
  simp [blaschke,Complex.canonicalFactor,inv_div]

lemma blaschke_denom_ne {R : ℝ} {a z : ℂ} (hR : 0<R)
    (ha : a∈ball 0 R) (hz : z∈closedBall 0 R) : (R:ℂ)^2-conj a*z≠0 := by
  have ha' : ‖a‖<R := mem_ball_zero_iff.mp ha
  have hz' : ‖z‖≤R := mem_closedBall_zero_iff.mp hz
  apply sub_ne_zero.mpr
  intro he
  have ht:=congrArg norm he
  have hm : ‖a‖*‖z‖<R^2 := by nlinarith [mul_le_mul_of_nonneg_left hz' (norm_nonneg a)]
  simp only [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR,norm_mul,norm_conj] at ht
  linarith

lemma blaschke_analytic {R : ℝ} {a : ℂ} (hR : 0<R) (ha : a∈ball 0 R) :
    AnalyticOnNhd ℂ (blaschke R a) (closedBall 0 R) := by
  intro z hz
  exact (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).div
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (blaschke_denom_ne hR ha hz)

lemma blaschke_norm_sphere {R : ℝ} {a z : ℂ} (ha : a∈ball 0 R) (hz : z∈sphere 0 R) :
    ‖blaschke R a z‖=1 := by
  rw [blaschke_eq_inv,norm_inv,Complex.norm_canonicalFactor_eval_circle_eq_one ha hz,inv_one]

lemma blaschke_norm_le {R : ℝ} {a z : ℂ} (hR : 0<R) (ha : a∈ball 0 R)
    (hz : z∈closedBall 0 R) : ‖blaschke R a z‖≤1 := by
  have ha' : ‖a‖<R := mem_ball_zero_iff.mp ha
  have hz' : ‖z‖≤R := mem_closedBall_zero_iff.mp hz
  have he : ‖(R:ℂ)^2-conj a*z‖^2-‖(R:ℂ)*(z-a)‖^2=
      (R^2-‖a‖^2)*(R^2-‖z‖^2) := by
    simp only [←Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      pow_two,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.conj_re,Complex.conj_im]
    ring
  have hba : 0≤R^2-‖a‖^2 := by nlinarith [norm_nonneg a]
  have hbz : 0≤R^2-‖z‖^2 := by nlinarith [norm_nonneg z]
  have hn : ‖(R:ℂ)*(z-a)‖≤‖(R:ℂ)^2-conj a*z‖ := by nlinarith [mul_nonneg hba hbz,norm_nonneg ((R:ℂ)*(z-a)),norm_nonneg ((R:ℂ)^2-conj a*z)]
  rw [blaschke,norm_div]
  exact (div_le_one₀ (norm_pos_iff.mpr (blaschke_denom_ne hR ha hz))).mpr hn

lemma blaschke_ne_zero {R : ℝ} {a z : ℂ} (hR : 0<R) (ha : a∈ball 0 R)
    (hz : z∈closedBall 0 R) (hne : z≠a) : blaschke R a z≠0 :=
  div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (sub_ne_zero.mpr hne))
    (blaschke_denom_ne hR ha hz)

lemma blaschke_logDeriv {R : ℝ} {a z : ℂ} (hR : 0<R) (ha : a∈ball 0 R)
    (hz : z∈closedBall 0 R) (hne : z≠a) :
    deriv (blaschke R a) z/blaschke R a z=
      (z-a)⁻¹+conj a/((R:ℂ)^2-conj a*z) := by
  have hd:=((hasDerivAt_id z).sub_const a).const_mul (R:ℂ)
  have he:=(hasDerivAt_const z ((R:ℂ)^2)).sub ((hasDerivAt_id z).const_mul (conj a))
  have hh:=hd.div he (blaschke_denom_ne hR ha hz)
  change HasDerivAt (blaschke R a) _ z at hh
  rw [hh.deriv,blaschke]
  dsimp only [Pi.sub_apply,id_eq]
  field_simp [blaschke_denom_ne hR ha hz,sub_ne_zero.mpr hne,Complex.ofReal_ne_zero.mpr hR.ne']
  ring

lemma codiscrete_analytic_eq {f g : ℂ → ℂ} {R : ℝ} (hR : 0<R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (he : f=ᶠ[codiscreteWithin (closedBall 0 R)] g) : EqOn f g (closedBall 0 R) := by
  intro z hz
  have hc : Preperfect (closedBall (0:ℂ) R) := by
    rw [←closure_ball (0:ℂ) hR.ne']
    exact isOpen_ball.perfect_closure.2
  have he' := (hf z hz).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
    (hg z hz).meromorphicAt hz hc he
  exact tendsto_nhds_unique_of_eventuallyEq (hf z hz).continuousAt.continuousWithinAt
    (hg z hz).continuousAt.continuousWithinAt he'

end SharpNodal.Holomorphic

noncomputable section
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
namespace SharpNodal.Holomorphic

lemma analytic_max_ball {f : ℂ → ℂ} {R M : ℝ} (hR : 0<R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hb : ∀z∈sphere 0 R,‖f z‖≤M) : ∀z∈closedBall 0 R,‖f z‖≤M := by
  have hd : DiffContOnCl ℂ f (ball 0 R) := hf.differentiableOn.diffContOnCl_ball subset_rfl
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
    (fun z hz =>hb z (by simpa only [frontier_ball (0:ℂ) hR.ne'] using hz))
  simpa only [closure_ball (0:ℂ) hR.ne'] using hz

lemma finite_blaschke_factorization {f : ℂ → ℂ} {R M : ℝ} (hR : 0<R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0≠0)
    (hb : ∀z∈sphere 0 R,‖f z‖≤M) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      (∀a∈S,a∈ball 0 R ∧ 0 < m a) ∧
      (∀a,(m a:ℤ)=divisor f (ball 0 R) a) ∧
      AnalyticOnNhd ℂ g (closedBall 0 R) ∧ (∀z∈ball 0 R,g z≠0) ∧
      (∀z∈closedBall 0 R,f z=(∏a∈S,blaschke R a z^m a)*g z) ∧
      (∀z∈closedBall 0 R,‖g z‖≤M) ∧ ‖f 0‖≤‖g 0‖ := by
  classical
  have hzero : (0:ℂ)∈closedBall 0 R := mem_closedBall_self hR.le
  have horder : ∀u : closedBall (0:ℂ) R,meromorphicOrderAt f u≠⊤ := by
    apply (hf.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall (isConnected_closedBall hR.le)).mp
    refine ⟨⟨0,hzero⟩,?_⟩
    rw [(hf 0 hzero).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0]
    simp
  obtain ⟨g,D⟩:=hf.meromorphicOn.exists_canonicalDecomp horder
  have hg : AnalyticOnNhd ℂ g (closedBall 0 R) := by
    apply D.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd.mp
    intro z
    have hp:=(hf.mono sphere_subset_closedBall).divisor_nonneg z
    change 0≤divisor g (closedBall 0 R) z
    rwa [D.divisor_eq_divisor hR]
  let d:=divisor f (ball 0 R)
  have hdn : ∀a,0≤d a := (hf.mono ball_subset_closedBall).divisor_nonneg
  have hfin : d.support.Finite := hf.meromorphicOn.divisor_ball_support_finite
  let S:=hfin.toFinset
  let m : ℂ → ℕ:=fun a =>(d a).toNat
  have hcast : ∀a,(m a:ℤ)=d a := fun a =>Int.toNat_of_nonneg (hdn a)
  have hSmem : ∀a∈S,a∈ball 0 R ∧ 0 < m a := by
    intro a ha
    have hdne : d a≠0 := by simpa only [S,Finite.mem_toFinset,Function.mem_support] using ha
    refine ⟨d.supportWithinDomain (by simpa only [Function.mem_support] using hdne),?_⟩
    have hpos : 0<d a := lt_of_le_of_ne (hdn a) (Ne.symm hdne)
    dsimp [m]; omega
  let P : ℂ → ℂ:=fun z =>∏a∈S,blaschke R a z^m a
  have hP : AnalyticOnNhd ℂ P (closedBall 0 R) := by
    intro z hz
    exact S.analyticAt_fun_prod (fun a ha =>(blaschke_analytic hR (hSmem a ha).1 z hz).pow _)
  have heP : (∏ᶠa,Complex.canonicalFactor R a^(-d a))=P := by
    have hs : (fun a =>Complex.canonicalFactor R a^(-d a)).mulSupport ⊆ d.support := by
      intro a
      contrapose
      simp only [Function.mem_support,not_not,Function.mem_mulSupport]
      intro he
      simp [he]
    rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ hs hfin]
    ext z
    simp only [Finset.prod_apply,Pi.pow_apply,P,S]
    apply Finset.prod_congr rfl
    intro a ha
    rw [←hcast a,zpow_neg,zpow_natCast,←inv_pow,←blaschke_eq_inv]
  have he : EqOn f (fun z =>P z*g z) (closedBall 0 R) := by
    apply codiscrete_analytic_eq hR hf (hP.mul hg)
    filter_upwards [D.eventuallyEq] with z hz
    change f z = ((∏ᶠa,Complex.canonicalFactor R a^(-d a)) z)*g z at hz
    simpa only [heP] using hz
  have hbP : ∀z∈sphere 0 R,‖P z‖=1 := by
    intro z hz
    simp only [P,norm_prod,norm_pow]
    exact Finset.prod_eq_one (fun a ha =>by rw [blaschke_norm_sphere (hSmem a ha).1 hz,one_pow])
  have hbG : ∀z∈closedBall 0 R,‖g z‖≤M := by
    apply analytic_max_ball hR hg
    intro z hz
    have he':=congrArg norm (he (sphere_subset_closedBall hz))
    rw [norm_mul,hbP z hz,one_mul] at he'
    exact he'.symm.trans_le (hb z hz)
  refine ⟨S,m,g,hSmem,hcast,hg,D.ne_zero,he,hbG,?_⟩
  rw [he hzero,norm_mul]
  have hPb : ‖P 0‖≤1 := by
    simp only [P,norm_prod,norm_pow]
    exact Finset.prod_le_one (fun a _ =>pow_nonneg (norm_nonneg _) _) (fun a ha =>pow_le_one₀ (norm_nonneg _) (blaschke_norm_le hR (hSmem a ha).1 hzero))
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hPb (norm_nonneg (g 0))

end SharpNodal.Holomorphic
noncomputable section
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
namespace SharpNodal.Holomorphic

lemma exists_holomorphic_log {g : ℂ → ℂ} {R : ℝ} (hR : 0<R)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hne : ∀z∈ball 0 R,g z≠0) :
    ∃ L : ℂ → ℂ,DifferentiableOn ℂ L (ball 0 R) ∧
      (∀z∈ball 0 R,Complex.exp (L z)=g z) ∧
      ∀z∈ball 0 R,deriv L z=deriv g z/g z := by
  have hc : IsSimplyConnected (ball (0:ℂ) R) := by
    let _:= (convex_ball (0:ℂ) R).contractibleSpace (nonempty_ball.mpr hR)
    change SimplyConnectedSpace (ball (0:ℂ) R)
    infer_instance
  obtain ⟨L,hLc,he⟩:=Complex.exists_continuousOn_eqOn_exp_comp hc isOpen_ball hg.continuousOn (by
    rintro ⟨z,hz,hzero⟩
    exact hne z hz hzero)
  have hd : ∀z∈ball 0 R,HasDerivAt L (deriv g z/g z) z := by
    intro z hz
    have hcomp : Complex.exp ∘ L=ᶠ[𝓝 z] g := Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) (fun _ hw =>he hw)
    have ht:=HasDerivAt.of_comp_left (hLc.continuousAt (isOpen_ball.mem_nhds hz))
      (Complex.hasDerivAt_exp (L z)) (hg.differentiableAt (isOpen_ball.mem_nhds hz) |>.hasDerivAt)
      (Complex.exp_ne_zero _) hcomp
    simpa only [show Complex.exp (L z)=g z from he hz] using ht
  exact ⟨L,fun z hz =>(hd z hz).differentiableAt.differentiableWithinAt,he,fun z hz =>(hd z hz).deriv⟩

end SharpNodal.Holomorphic
noncomputable section
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
namespace SharpNodal.Profiles
open Carleman

lemma plane_norm_le_abs (v : Plane) : ‖v‖ ≤ |v 0|+|v 1| := by
  calc
    ‖v‖ = ‖v 0 • (EuclideanSpace.single 0 1 : Plane)+v 1 • (EuclideanSpace.single 1 1 : Plane)‖ := by rw [←plane_basis_expansion]
    _ ≤ ‖v 0 • (EuclideanSpace.single 0 1 : Plane)‖+‖v 1 • (EuclideanSpace.single 1 1 : Plane)‖ := norm_add_le _ _
    _ = _ := by simp [norm_smul,Real.norm_eq_abs]

lemma plane_map_expansion (L : Plane →L[ℝ] ℝ) (v : Plane) :
    L v=v 0*L ((EuclideanSpace.single 0 1 : Plane))+v 1*L ((EuclideanSpace.single 1 1 : Plane)) := by
  conv_lhs => rw [plane_basis_expansion v]
  simp

end SharpNodal.Profiles

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Divisors
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

namespace SharpNodal.Holomorphic

lemma zeroWeight_pos {S : Finset ℂ} {m : ℂ → ℕ} {B : ℝ} (hB : 0<B) (z : ℂ) :
    0<zeroWeight S m B z := by
  have hs : 0≤∑a∈S,(m a:ℝ)*‖z-a‖⁻¹ := Finset.sum_nonneg (fun a _ =>by positivity)
  dsimp [zeroWeight]; linarith

lemma zeroWeight_term_le {S : Finset ℂ} {m : ℂ → ℕ} {B : ℝ} (hB : 0≤B)
    (z : ℂ) {a : ℂ} (ha : a∈S) : (m a:ℝ)*‖z-a‖⁻¹≤zeroWeight S m B z := by
  have ht:=Finset.single_le_sum (f:=fun a =>(m a:ℝ)*‖z-a‖⁻¹) (fun a _=>by positivity) ha
  dsimp [zeroWeight]; linarith

lemma zeroWeight_radius {S : Finset ℂ} {m : ℂ → ℕ} {B : ℝ} (hB : 0≤B)
    {z : ℂ} (hz : ∀a∈S,z≠a) (hm : ∀a∈S,0 < m a)
    {a : ℂ} (ha : a∈S) : 1≤zeroWeight S m B z*‖z-a‖ := by
  have ht:=zeroWeight_term_le (m:=m) hB z ha
  have hn : 0<‖z-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hz a ha))
  have he:=mul_le_mul_of_nonneg_right ht hn.le
  rw [mul_assoc,inv_mul_cancel₀ hn.ne',mul_one] at he
  have hm' : (1:ℝ)≤ m a := by exact_mod_cast (hm a ha)
  linarith

lemma zeroWeight_local_comparison {S : Finset ℂ} {m : ℂ → ℕ} {B : ℝ} (hB : 0<B)
    {z w : ℂ} (hz : ∀a∈S,z≠a) (hm : ∀a∈S,0 < m a)
    (hw : ‖w-z‖≤1/(4*zeroWeight S m B z)) :
    (∀a∈S,w≠a) ∧ zeroWeight S m B z/2≤zeroWeight S m B w ∧
      zeroWeight S m B w≤2*zeroWeight S m B z := by
  have hW:=zeroWeight_pos (S:=S) (m:=m) hB z
  have hd (a : ℂ) (ha : a∈S) : ‖w-z‖≤‖z-a‖/4 := by
    have ht:=zeroWeight_radius hB.le hz hm ha
    have he : 1/(4*zeroWeight S m B z)≤‖z-a‖/4 := by
      apply (div_le_iff₀ (by positivity : 0<4*zeroWeight S m B z)).mpr
      nlinarith
    exact hw.trans he
  have hdist (a : ℂ) (ha : a∈S) : ‖z-a‖/2≤‖w-a‖ ∧ ‖w-a‖≤2*‖z-a‖ := by
    have ht:=norm_add_le (w-z) (z-a)
    rw [sub_add_sub_cancel] at ht
    have ht':=norm_sub_norm_le (z-a) (w-a)
    rw [sub_sub_sub_cancel_right,norm_sub_rev z w] at ht'
    have he:=hd a ha
    constructor <;> linarith [norm_nonneg (z-a)]
  have hn (a : ℂ) (ha : a∈S) : 0<‖w-a‖ := by
    have hp : 0<‖z-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hz a ha))
    linarith [(hdist a ha).1]
  refine ⟨fun a ha =>sub_ne_zero.mp (norm_pos_iff.mp (hn a ha)),?_,?_⟩
  · have hs : (∑a∈S,(m a:ℝ)*‖z-a‖⁻¹)≤2*∑a∈S,(m a:ℝ)*‖w-a‖⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a ha
      have hp : 0<‖z-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hz a ha))
      have ht : ‖z-a‖⁻¹≤2*‖w-a‖⁻¹ := by
        rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ hp (hn a ha)]
        simpa only [one_mul] using (hdist a ha).2
      nlinarith [mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (m a))]
    dsimp [zeroWeight]; linarith
  · have hs : (∑a∈S,(m a:ℝ)*‖w-a‖⁻¹)≤2*∑a∈S,(m a:ℝ)*‖z-a‖⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a ha
      have hp : 0<‖z-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hz a ha))
      have ht : ‖w-a‖⁻¹≤2*‖z-a‖⁻¹ := by
        rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ (hn a ha) hp]
        have :=(hdist a ha).1
        linarith
      nlinarith [mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (m a))]
    dsimp [zeroWeight]; linarith

end SharpNodal.Holomorphic

noncomputable section
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
namespace SharpNodal.Holomorphic

lemma local_divisor_sum_bound {f : ℂ → ℂ} {M : ℝ} (hM : 1≤M)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (2/3))) (h0 : f 0≠0)
    (hb : ∀z∈sphere 0 (2/3),‖f z‖≤M)
    (S : Finset ℂ) (m : ℂ → ℕ) (hS : ∀a∈S,a∈ball 0 (1/2))
    (hpos : ∀a∈S,0 < m a) (hm : ∀a,(m a:ℤ)=divisor f (ball 0 (1/2)) a) :
    (∑a∈S,(m a:ℝ))≤Real.log (M/‖f 0‖)/Real.log (4/3) := by
  have hf' :=hf.mono (closedBall_subset_closedBall (by norm_num : (1/2:ℝ)≤2/3))
  have hle : (∑a∈S,(m a:ℤ))≤∑ᶠa,divisor f (closedBall 0 (1/2)) a := by
    have he : ∀a∈S,(m a:ℤ)=divisor f (closedBall 0 (1/2)) a := by
      intro a ha
      rw [hf'.meromorphicOn.divisor_apply (ball_subset_closedBall (hS a ha)),
        ←(hf'.mono ball_subset_closedBall).meromorphicOn.divisor_apply (hS a ha),hm a]
    rw [Finset.sum_congr rfl he]
    let T:=((divisor f (closedBall 0 (1/2))).finiteSupport (isCompact_closedBall ..)).toFinset
    rw [finsum_eq_sum_of_support_subset _ (s:=T) (by simp [T])]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro a ha
      simp only [T,Finite.mem_toFinset,Function.mem_support]
      rw [←he a ha]
      exact_mod_cast (hpos a ha).ne'
    · intro a _ _
      exact hf'.divisor_nonneg a
  have hfJ : AnalyticOnNhd ℂ f (closedBall 0 |(2/3:ℝ)|) :=by norm_num; exact hf
  have hj:=hfJ.sum_divisor_le (r:=1/2) (R:=2/3) (by norm_num) (by norm_num) hM h0
    (by simpa only [abs_of_pos (by norm_num : (0:ℝ)<2/3)] using hb)
  rw [abs_of_pos (by norm_num : (0:ℝ)<1/2)] at hj
  norm_num at hj
  have hle' : (∑a∈S,(m a:ℝ))≤(∑ᶠa,divisor f (closedBall 0 (1/2)) a : ℤ) := by exact_mod_cast hle
  exact hle'.trans hj

end SharpNodal.Holomorphic

noncomputable section
open scoped Topology
open Set Metric Complex

noncomputable section
open scoped Topology
open Set Metric
namespace SharpNodal.Holomorphic

lemma small_variation {H : ℂ → ℂ} {c : ℂ} {r K : ℝ} (hr : 0 ≤ r) (hK : 0≤K)
    (hsmall : K*r≤1/4)
    (hH : ∀z∈closedBall c r,DifferentiableAt ℂ H z)
    (hd : ∀z∈closedBall c r,‖deriv H z‖≤K*‖H z‖) :
    ∀z∈closedBall c r,‖H z-H c‖≤2*K*r*‖H c‖ := by
  have hcont : ContinuousOn (fun z =>‖H z‖) (closedBall c r) :=
    (show ContinuousOn H (closedBall c r) from fun z hz =>(hH z hz).continuousAt.continuousWithinAt).norm
  obtain ⟨p,hp,hmax⟩:=isCompact_closedBall c r |>.exists_isMaxOn
    ⟨c,mem_closedBall_self hr⟩ hcont
  have hb (z : ℂ) (hz : z∈closedBall c r) : ‖deriv H z‖≤K*‖H p‖ :=
    (hd z hz).trans (mul_le_mul_of_nonneg_left (hmax hz) hK)
  have hmv (z : ℂ) (hz : z∈closedBall c r) : ‖H z-H c‖≤K*‖H p‖*r := by
    exact (Convex.norm_image_sub_le_of_norm_deriv_le hH hb (convex_closedBall c r)
      (mem_closedBall_self hr) hz).trans (mul_le_mul_of_nonneg_left
      (by simpa only [dist_eq_norm] using mem_closedBall.mp hz) (mul_nonneg hK (norm_nonneg _)))
  have hpn : ‖H p‖≤2*‖H c‖ := by
    have ht:=norm_sub_norm_le (H p) (H c)
    have hh:=hmv p hp
    nlinarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg (H p)),norm_nonneg (H c)]
  intro z hz
  calc
    _ ≤ K*‖H p‖*r :=hmv z hz
    _ ≤ 2*K*r*‖H c‖ := by nlinarith [mul_le_mul_of_nonneg_left hpn (mul_nonneg hK hr)]

end SharpNodal.Holomorphic

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_GradientCones
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

namespace SharpNodal.Profiles
open Carleman

lemma plane_norm_le_pair (v : Plane) (i j : Fin 2) (hij : i≠j) :
    ‖v‖≤|v i|+|v j| := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact plane_norm_le_abs v
  · change ‖v‖≤|v 1|+|v 0|
    rw [add_comm]; exact plane_norm_le_abs v
  · exact False.elim (hij rfl)

lemma plane_map_pair (L : Plane →L[ℝ] ℝ) (v : Plane) (i j : Fin 2) (hij : i≠j) :
    L v=v i*L (EuclideanSpace.single i 1)+v j*L (EuclideanSpace.single j 1) := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact plane_map_expansion L v
  · change L v=v 1*L (EuclideanSpace.single 1 1)+v 0*L (EuclideanSpace.single 0 1)
    rw [add_comm]; exact plane_map_expansion L v
  · exact False.elim (hij rfl)

lemma nodal_graph_distance_pair {v : Plane → ℝ} {c : Plane} {r : ℝ}
    (hv : ∀x∈ball c r,DifferentiableAt ℝ v x)
    (L : Plane →L[ℝ] ℝ) {a : ℝ} (ha : 0<a) (i j : Fin 2) (hij : i≠j)
    (h0 : a ≤ |L ((EuclideanSpace.single i 1 : Plane))|)
    (h1 : |L ((EuclideanSpace.single j 1 : Plane))| ≤ 2*a)
    (hder : ∀x∈ball c r,‖fderiv ℝ v x-L‖ ≤ a/4)
    {x y : Plane} (hx : x∈ball c r) (hy : y∈ball c r) (hvx : v x=0) (hvy : v y=0) :
    dist x y ≤ 4*dist (x j) (y j) := by
  have he:=(convex_ball c r).norm_image_sub_le_of_norm_fderiv_le' hv hder hx hy
  simp only [hvx,hvy,sub_self,zero_sub,norm_neg,Real.norm_eq_abs] at he
  let d:=y-x
  have hd : ‖d‖ ≤ |d i|+|d j| := plane_norm_le_pair d i j hij
  have hm : |d i*L ((EuclideanSpace.single i 1 : Plane))| ≤ |L d|+|d j*L ((EuclideanSpace.single j 1 : Plane))| := by
    have hh := abs_sub (L d) (d j*L ((EuclideanSpace.single j 1 : Plane)))
    rw [plane_map_pair L d i j hij,add_sub_cancel_right] at hh
    simpa only [←plane_map_pair L d i j hij] using hh
  rw [abs_mul,abs_mul] at hm
  have he' : |L d| ≤ a/4*‖d‖ := he
  have hfirst:=mul_le_mul_of_nonneg_left h0 (abs_nonneg (d i))
  have hsecond:=mul_le_mul_of_nonneg_left h1 (abs_nonneg (d j))
  have hh : |d i| ≤ 3*|d j| := by nlinarith [mul_le_mul_of_nonneg_left hd ha.le]
  have htt : ‖d‖ ≤ 4*|d j| := by linarith
  simpa only [d,dist_eq_norm,PiLp.sub_apply,Real.norm_eq_abs,norm_sub_rev,abs_sub_comm] using htt

lemma nodal_graph_length_pair {v : Plane → ℝ} {c : Plane} {r : ℝ}
    (hv : ∀x∈ball c r,DifferentiableAt ℝ v x)
    (L : Plane →L[ℝ] ℝ) {a : ℝ} (ha : 0<a) (i j : Fin 2) (hij : i≠j)
    (h0 : a ≤ |L ((EuclideanSpace.single i 1 : Plane))|)
    (h1 : |L ((EuclideanSpace.single j 1 : Plane))| ≤ 2*a)
    (hder : ∀x∈ball c r,‖fderiv ℝ v x-L‖ ≤ a/4) :
    Measure.hausdorffMeasure 1 {x | x∈ball c r ∧ v x=0} ≤ ENNReal.ofReal (8*r) := by
  let S : Set Plane:={x | x∈ball c r ∧ v x=0}
  let proj : S → ℝ:=fun x =>(x.val) j
  have hAnti : AntilipschitzWith 4 proj := AntilipschitzWith.of_le_mul_dist (fun x y =>by
    exact nodal_graph_distance_pair hv L ha i j hij h0 h1 hder x.property.1 y.property.1 x.property.2 y.property.2)
  have hi : Isometry (Subtype.val : S → Plane) := isometry_subtype_coe
  have hIm : Subtype.val '' (Set.univ : Set S)=S := by ext x; simp
  have hproj : proj '' (Set.univ : Set S) ⊆ Icc (c j-r) (c j+r) := by
    rintro _ ⟨x,_,rfl⟩
    have hxc : |x.val j-c j| ≤ r := by
      have ht:=(plane_component_norm_le (x.val-c) j).trans (le_of_lt (mem_ball.mp x.property.1))
      simpa only [PiLp.sub_apply,dist_eq_norm] using ht
    exact ⟨by linarith [(abs_le.mp hxc).1],by linarith [(abs_le.mp hxc).2]⟩
  calc
    Measure.hausdorffMeasure 1 S = Measure.hausdorffMeasure 1 (Set.univ : Set S) := by
      have he:=hi.hausdorffMeasure_image (d:=1) (Or.inl (by norm_num)) Set.univ
      rw [hIm] at he
      exact he
    _ ≤ (4:ℝ≥0∞)^ (1:ℝ)*Measure.hausdorffMeasure 1 (proj '' Set.univ) := hAnti.le_hausdorffMeasure_image (by norm_num) _
    _ ≤ (4:ℝ≥0∞)*Measure.hausdorffMeasure 1 (Icc (c j-r) (c j+r)) := by
      rw [ENNReal.rpow_one]; exact mul_le_mul_right (measure_mono hproj) _
    _ = ENNReal.ofReal (8*r) := by
      rw [hausdorffMeasure_real,Real.volume_Icc]
      rw [show c j+r-(c j-r)=2*r by ring]
      rw [←ENNReal.ofReal_ofNat 4,←ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring

lemma gradient_diff_component {v : Plane → ℝ} (x y : Plane) (i : Fin 2) :
    |coordPartial v i x-coordPartial v i y|≤‖complexGradient v x-complexGradient v y‖ := by
  fin_cases i
  · simpa [complexGradient] using Complex.abs_re_le_norm (complexGradient v x-complexGradient v y)
  · change |coordPartial v 1 x-coordPartial v 1 y|≤_
    have he : (complexGradient v x-complexGradient v y).im=-(coordPartial v 1 x-coordPartial v 1 y) := by
      simp only [complexGradient,Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re]
      ring
    simpa only [he,abs_neg] using Complex.abs_im_le_norm (complexGradient v x-complexGradient v y)

lemma nodal_length_gradient_cone {v : Plane → ℝ} {c : Plane} {r : ℝ}
    (hv : ∀x∈ball c r,DifferentiableAt ℝ v x)
    (hne : complexGradient v c≠0)
    (hgrad : ∀x∈ball c r,‖complexGradient v x-complexGradient v c‖≤‖complexGradient v c‖/16) :
    Measure.hausdorffMeasure 1 {x | x∈ball c r ∧ v x=0} ≤ ENNReal.ofReal (8*r) := by
  let a:=‖complexGradient v c‖/2
  have ha : 0<a := half_pos (norm_pos_iff.mpr hne)
  have hder : ∀x∈ball c r,‖fderiv ℝ v x-fderiv ℝ v c‖≤a/4 := by
    intro x hx
    have hh:=plane_clm_norm_le_two (fderiv ℝ v x-fderiv ℝ v c)
      (show 0≤‖complexGradient v c‖/16 by positivity) (fun i =>by
        simpa only [sub_apply,coordPartial,Real.norm_eq_abs] using
          (gradient_diff_component x c i).trans (hgrad x hx))
    dsimp [a]
    linarith
  have hN:=norm_gradient_le v c
  have h0:=abs_partial_le_norm_gradient v 0 c
  have h1:=abs_partial_le_norm_gradient v 1 c
  by_cases h : a≤|coordPartial v 0 c|
  · exact nodal_graph_length_pair hv (fderiv ℝ v c) ha 0 1 (by decide) h
      (by change |coordPartial v 1 c|≤2*a; dsimp [a]; linarith) hder
  · apply nodal_graph_length_pair hv (fderiv ℝ v c) ha 1 0 (by decide) _ _ hder
    · change a≤|coordPartial v 1 c|
      dsimp [a] at *; linarith
    · change |coordPartial v 0 c|≤2*a
      dsimp [a]; linarith

end SharpNodal.Profiles

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Vitali
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

namespace SharpNodal

lemma vitali_measure_bound {α : Type*} [MetricSpace α] [SeparableSpace α]
    [MeasurableSpace α] [BorelSpace α] (ν μ : Measure α) (S D : Set α)
    (r : α → ℝ) {R : ℝ} (hr : ∀x∈S,0 < r x) (hb : ∀x∈S,r x≤R)
    (hD : ∀x∈S,ball x (r x)⊆D) (C : ℝ≥0∞)
    (hlocal : ∀x∈S,ν (S∩ball x (4*r x))≤C*μ (ball x (r x))) :
    ν S≤C*μ D := by
  obtain ⟨T,hTS,hdis,hcover⟩:=Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    S id r R hb 4 (by norm_num)
  have hcount : T.Countable := hdis.countable_of_isOpen (fun _ _=>isOpen_ball)
    (fun x hx=>nonempty_ball.mpr (hr x (hTS hx)))
  let _ : Countable T :=hcount.to_subtype
  have hc : S⊆⋃x : T,S∩ball x.val (4*r x.val) := by
    intro x hx
    obtain ⟨y,hy,hyc⟩:=hcover x hx
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hx,hyc (mem_ball_self (hr x hx))⟩
  have hpd : Pairwise (Disjoint on (fun x : T=>ball x.val (r x.val))) := by
    intro x y hne
    exact hdis x.property y.property (fun he=>hne (Subtype.ext he))
  calc
    ν S ≤ ν (⋃x : T,S∩ball x.val (4*r x.val)) :=measure_mono hc
    _ ≤ ∑'x : T,ν (S∩ball x.val (4*r x.val)) :=measure_iUnion_le _
    _ ≤ ∑'x : T,C*μ (ball x.val (r x.val)) :=ENNReal.tsum_le_tsum (fun x=>hlocal x.val (hTS x.property))
    _ = C*(∑'x : T,μ (ball x.val (r x.val))) :=ENNReal.tsum_mul_left
    _ = C*μ (⋃x : T,ball x.val (r x.val)) :=by rw [measure_iUnion hpd (fun _=>measurableSet_ball)]
    _ ≤ C*μ D :=mul_le_mul_right (measure_mono (iUnion_subset (fun (x : T)=>hD x.val (hTS x.property)))) _

end SharpNodal

noncomputable section
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
namespace SharpNodal.Profiles

lemma inverse_norm_integrableOn_ball (R : ℝ) :
    IntegrableOn (fun x : Plane =>‖x‖⁻¹) (ball (0:Plane) R) := by
  rw [integrableOn_fun_norm_addHaar]
  simp only [finrank_euclideanSpace_fin,Nat.reduceSub,pow_one,smul_eq_mul]
  have hi : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioo 0 R) := integrableOn_const (by simp)
  exact hi.congr_fun
    (fun r hr=>by rw [mul_inv_cancel₀ (ne_of_gt hr.1)]) measurableSet_Ioo

lemma integral_inverse_norm_ball {R : ℝ} (hR : 0≤R) :
    (∫x in ball (0:Plane) R,‖x‖⁻¹)=2*Real.pi*R := by
  rw [plane_radial_ball_integral (fun r=>r⁻¹) R]
  have he : (∫r in Ioo (0:ℝ) R,r*r⁻¹)=R := by
    rw [setIntegral_congr_fun measurableSet_Ioo (fun r hr=>mul_inv_cancel₀ (ne_of_gt hr.1))]
    simp [hR]
  rw [he]

lemma inverse_translate_integrable_bound {a : Plane} (ha : ‖a‖<1/2) :
    IntegrableOn (fun x : Plane=>‖x-a‖⁻¹) (ball (0:Plane) 1) ∧
      (∫x in ball (0:Plane) 1,‖x-a‖⁻¹)≤4*Real.pi := by
  let F : Plane → ℝ :=(ball (0:Plane) 2).indicator (fun x=>‖x‖⁻¹)
  have hi : Integrable F :=(inverse_norm_integrableOn_ball 2).integrable_indicator measurableSet_ball
  have hit : Integrable (fun x=>F (x-a)) :=
    (measurePreserving_sub_right volume a).integrable_comp hi.aestronglyMeasurable |>.mpr hi
  have he (x : Plane) (hx : x∈ball (0:Plane) 1) : ‖x-a‖⁻¹=F (x-a) := by
    have hn : ‖x-a‖<2 := by
      have hh:=norm_sub_le x a
      have hx':=mem_ball_zero_iff.mp hx
      linarith
    dsimp [F]
    rw [indicator_of_mem (show x-a∈ball (0:Plane) 2 from mem_ball_zero_iff.mpr hn)]
  have hin : IntegrableOn (fun x : Plane=>‖x-a‖⁻¹) (ball (0:Plane) 1) :=
    hit.integrableOn.congr_fun (fun x hx=>(he x hx).symm) measurableSet_ball
  refine ⟨hin,?_⟩
  calc
    _ = ∫x in ball (0:Plane) 1,F (x-a) :=setIntegral_congr_fun measurableSet_ball he
    _ ≤ ∫x,F (x-a) :=integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall (fun x=>indicator_nonneg (fun y _=>by positivity) _)) hit
    _ = ∫x,F x :=integral_sub_right_eq_self F a
    _ = ∫x in ball (0:Plane) 2,‖x‖⁻¹ :=integral_indicator measurableSet_ball
    _ = 4*Real.pi :=by rw [integral_inverse_norm_ball (by norm_num)]; ring

lemma complex_difference_norm (x : Plane) (a : ℂ) :
    ‖planeToComplex x-a‖=‖x-complexToPlane a‖ := by
  have he:=planeToComplex.norm_map (x-complexToPlane a)
  simpa only [map_sub,planeToComplex,LinearIsometryEquiv.symm_apply_apply] using he

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
namespace SharpNodal.Profiles
open Holomorphic

lemma weightMeasure_unit_bound (S : Finset ℂ) (m : ℂ → ℕ) {B : ℝ} (hB : 0<B)
    (hS : ∀a∈S,a∈ball 0 (1/2)) :
    weightMeasure S m B (ball (0:Plane) 1) ≤ ENNReal.ofReal (Real.pi*B+4*Real.pi*∑a∈S,(m a:ℝ)) := by
  have hk (a : ℂ) (ha : a∈S) := inverse_translate_integrable_bound
    (a:=complexToPlane a) (by simpa only [complexToPlane.norm_map] using mem_ball_zero_iff.mp (hS a ha))
  have hi : IntegrableOn (fun x : Plane=>zeroWeight S m B (planeToComplex x)) (ball (0:Plane) 1) := by
    simp only [zeroWeight,complex_difference_norm]
    exact (integrableOn_const (C:=B)).add (integrable_finsetSum S (fun a ha =>(hk a ha).1.const_mul _))
  have hnn : 0≤ᵐ[volume.restrict (ball (0:Plane) 1)] (fun x=>zeroWeight S m B (planeToComplex x)) :=
    Eventually.of_forall (fun x=>(zeroWeight_pos hB _).le)
  rw [weightMeasure,withDensity_apply _ measurableSet_ball,←ofReal_integral_eq_lintegral_ofReal hi hnn]
  apply ENNReal.ofReal_le_ofReal
  simp only [zeroWeight,complex_difference_norm]
  rw [integral_add (integrableOn_const (C:=B) (μ:=volume) (s:=ball (0:Plane) 1)) (integrable_finsetSum S (fun a ha=>(hk a ha).1.const_mul _)),
    integral_const,integral_finsetSum S (fun a ha=>(hk a ha).1.const_mul _)]
  simp only [integral_const_mul,Measure.restrict_apply_univ,measureReal_def,EuclideanSpace.volume_ball_fin_two,
    ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal Real.pi_pos.le,smul_eq_mul]
  apply add_le_add le_rfl
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun a ha=>by nlinarith [mul_le_mul_of_nonneg_left (hk a ha).2 (Nat.cast_nonneg (m a))])

lemma weightMeasure_local_lower (S : Finset ℂ) (m : ℂ → ℕ) {B : ℝ} (hB : 1≤B)
    (hm : ∀a∈S,0 < m a) {c : Plane} (hc : ∀a∈S,planeToComplex c≠a) :
    ENNReal.ofReal (1/(2097152*zeroWeight S m B (planeToComplex c))) ≤
      weightMeasure S m B (ball c (1/(1024*zeroWeight S m B (planeToComplex c)))) := by
  let W:=zeroWeight S m B (planeToComplex c)
  let r:=1/(1024*W)
  have hW : 0<W:=zeroWeight_pos (by linarith : 0<B) _
  have hr : 0 < r:=by dsimp [r]; positivity
  have hw (x : Plane) (hx : x∈ball c r) : W/2≤zeroWeight S m B (planeToComplex x) := by
    apply (zeroWeight_local_comparison (by linarith : 0<B) hc hm (w:=planeToComplex x) ?_).2.1
    rw [←map_sub,planeToComplex.norm_map]
    have hd : ‖x-c‖ < r:=by simpa only [dist_eq_norm] using mem_ball.mp hx
    apply hd.le.trans
    change r≤1/(4*W)
    dsimp [r]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  have he : ENNReal.ofReal (W/2)*volume (ball c r) ≤ weightMeasure S m B (ball c r) := by
    rw [weightMeasure,withDensity_apply _ measurableSet_ball,←Measure.restrict_apply_univ (μ:=volume) (s:=ball c r),←lintegral_const]
    exact lintegral_mono_ae (by filter_upwards [ae_restrict_mem measurableSet_ball] with x hx; exact ENNReal.ofReal_le_ofReal (hw x hx))
  have hvol : volume (ball c r)=ENNReal.ofReal (Real.pi*r^2) := by
    rw [EuclideanSpace.volume_ball_fin_two,←ENNReal.ofReal_pow hr.le,←ENNReal.ofReal_mul (sq_nonneg r)]
    congr 1; ring
  rw [hvol,←ENNReal.ofReal_mul (by positivity)] at he
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) he
  change 1/(2097152*W)≤W/2*(Real.pi*r^2)
  dsimp [r]
  have hpi : 1≤Real.pi:=by linarith [Real.pi_gt_three]
  field_simp
  nlinarith

end SharpNodal.Profiles

end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_HolomorphicLength
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

namespace SharpNodal.Holomorphic
lemma zero_free_logDeriv_bound_wide {g : ℂ → ℂ} {M : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 (1/2)))
    (hne : ∀z∈ball 0 (1/2),g z≠0)
    (hb : ∀z∈ball 0 (1/2),‖g z‖≤M) :
    ∀z∈closedBall (0:ℂ) (9/20),‖deriv g z/g z‖≤
      2000*(1+Real.log (M/‖g 0‖)) := by
  have hzero : (0:ℂ)∈ball 0 (1/2) := mem_ball_self (by norm_num)
  have hg0 : 0<‖g 0‖ := norm_pos_iff.mpr (hne 0 hzero)
  have hM : 0<M := hg0.trans_le (hb 0 hzero)
  have hratio : 1≤M/‖g 0‖ := (le_div_iff₀ hg0).mpr (by simpa using hb 0 hzero)
  let B:=1+Real.log (M/‖g 0‖)
  have hB : 0<B := by dsimp [B]; have:=Real.log_nonneg hratio; linarith
  obtain ⟨L,hL,hLe,hLd⟩:=exists_holomorphic_log (by norm_num : (0:ℝ)<1/2) hg hne
  let F : ℂ → ℂ:=fun z=>L z-L 0
  have hF : DifferentiableOn ℂ F (ball 0 (1/2)) := hL.sub_const _
  have hRe : ∀z∈ball 0 (1/2),(F z).re≤B := by
    intro z hz
    have he:=(Complex.norm_exp (L z)).symm
    rw [hLe z hz] at he
    have he0:=(Complex.norm_exp (L 0)).symm
    rw [hLe 0 hzero] at he0
    have hl : (L z).re=Real.log ‖g z‖ := by rw [←he,Real.log_exp]
    have hl0 : (L 0).re=Real.log ‖g 0‖ := by rw [←he0,Real.log_exp]
    dsimp [F,B]
    rw [hl,hl0,Real.log_div hM.ne' hg0.ne']
    have ht:=Real.log_le_log (norm_pos_iff.mpr (hne z hz)) (hb z hz)
    linarith
  have hnorm : ∀z∈closedBall (0:ℂ) (19/40),‖F z‖≤38*B := by
    intro z hz
    have hz' : z∈ball (0:ℂ) (1/2) := closedBall_subset_ball (by norm_num) hz
    have he:=Complex.borelCaratheodory_zero hB hF (fun z hz =>hRe z hz)
      (by norm_num : (0:ℝ)<1/2) hz' (by simp [F])
    have hzn : ‖z‖≤19/40 := mem_closedBall_zero_iff.mp hz
    have hpos : 0<(1/2:ℝ)-‖z‖ := by linarith
    apply he.trans
    apply (div_le_iff₀ hpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hzn hB.le]
  intro z hz
  have hz' : z∈ball (0:ℂ) (1/2) := closedBall_subset_ball (by norm_num) hz
  have hsub : closedBall z (1/40) ⊆ closedBall (0:ℂ) (19/40) := by
    intro w hw
    have ht:=dist_triangle w z (0:ℂ)
    have hw':=mem_closedBall.mp hw
    have hz'':=mem_closedBall.mp hz
    exact mem_closedBall.mpr (by linarith)
  have hsub' : closedBall z (1/40) ⊆ ball (0:ℂ) (1/2) := hsub.trans (closedBall_subset_ball (by norm_num))
  have hd : DiffContOnCl ℂ F (ball z (1/40)) := (hF.mono hsub').diffContOnCl_ball subset_rfl
  have he:=Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ)<1/40) hd
    (fun w hw =>hnorm w (hsub (sphere_subset_closedBall hw)))
  have hder : deriv F z=deriv g z/g z := by
    rw [deriv_sub_const,hLd z hz']
  rw [hder] at he
  dsimp [B] at he ⊢
  nlinarith [Real.log_nonneg hratio]

lemma blaschke_logDeriv_bound_wide {a z : ℂ} (ha : a∈ball 0 (1/2))
    (hz : z∈closedBall 0 (9/20)) (hne : z≠a) :
    ‖logDeriv (blaschke (1/2) a) z‖≤‖z-a‖⁻¹+20 := by
  rw [logDeriv_apply,blaschke_logDeriv (by norm_num) ha
    (closedBall_subset_closedBall (by norm_num) hz) hne]
  apply (norm_add_le _ _).trans
  rw [norm_inv,norm_div,norm_conj]
  gcongr
  have ha' : ‖a‖<1/2 :=mem_ball_zero_iff.mp ha
  have hz' : ‖z‖≤9/20 :=mem_closedBall_zero_iff.mp hz
  have hden : (1/40:ℝ)≤‖((1/2:ℝ):ℂ)^2-conj a*z‖ := by
    have he:=norm_sub_norm_le (((1/2:ℝ):ℂ)^2) (conj a*z)
    norm_num [norm_mul,norm_conj] at he
    norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,div_pow,one_pow] at *
    nlinarith [mul_le_mul ha'.le hz' (norm_nonneg z) (by norm_num : (0:ℝ)≤1/2)]
  apply (div_le_iff₀ (by linarith : 0<‖((1/2:ℝ):ℂ)^2-conj a*z‖)).mpr
  linarith

lemma factor_logDeriv_bound_wide {f g : ℂ → ℂ} {M : ℝ} (S : Finset ℂ) (m : ℂ → ℕ)
    (hS : ∀a∈S,a∈ball 0 (1/2))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 (1/2)))
    (hne : ∀z∈ball 0 (1/2),g z≠0)
    (he : ∀z∈closedBall 0 (1/2),f z=(∏a∈S,blaschke (1/2) a z^m a)*g z)
    (hb : ∀z∈closedBall 0 (1/2),‖g z‖≤M) {z : ℂ}
    (hz : z∈closedBall 0 (9/20)) (hza : ∀a∈S,z≠a) :
    ‖logDeriv f z‖≤2000*(1+Real.log (M/‖g 0‖))+
      ∑a∈S,(m a:ℝ)*(‖z-a‖⁻¹+20) := by
  have hz' : z∈ball (0:ℂ) (1/2) :=closedBall_subset_ball (by norm_num) hz
  have hd (a : ℂ) (ha : a∈S) : DifferentiableAt ℂ (blaschke (1/2) a) z :=
    (blaschke_analytic (by norm_num) (hS a ha) z (ball_subset_closedBall hz')).differentiableAt
  have hn (a : ℂ) (ha : a∈S) : blaschke (1/2) a z≠0 :=
    blaschke_ne_zero (by norm_num) (hS a ha) (ball_subset_closedBall hz') (hza a ha)
  have hev : f=ᶠ[𝓝 z] (fun w =>(∏a∈S,blaschke (1/2) a w^m a)*g w) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hz') (fun w hw=>he w (ball_subset_closedBall hw))
  rw [show logDeriv f z=logDeriv (fun w =>(∏a∈S,blaschke (1/2) a w^m a)*g w) z from by
    rw [logDeriv_apply,logDeriv_apply,hev.deriv_eq,hev.eq_of_nhds]]
  rw [logDeriv_mul (f:=fun w =>∏a∈S,blaschke (1/2) a w^m a) (g:=g) z (Finset.prod_ne_zero_iff.mpr (fun a ha=>pow_ne_zero _ (hn a ha)))
    (hne z hz') (DifferentiableAt.fun_finsetProd (𝕜:=ℂ) (fun a ha =>(hd a ha).pow _))
    (hg z (ball_subset_closedBall hz')).differentiableAt]
  rw [logDeriv_prod (f:=fun a w=>blaschke (1/2) a w^m a) (fun a ha=>pow_ne_zero _ (hn a ha)) (fun a ha=>(hd a ha).pow _)]
  apply (norm_add_le _ _).trans
  rw [add_comm]
  apply add_le_add
  · exact zero_free_logDeriv_bound_wide (hg.mono ball_subset_closedBall).differentiableOn hne
      (fun w hw=>hb w (ball_subset_closedBall hw)) z hz
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a ha
    rw [logDeriv_fun_pow (hd a ha),norm_mul,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (blaschke_logDeriv_bound_wide (hS a ha) hz (hza a ha)) (Nat.cast_nonneg _)

lemma exists_zeroWeight_wide {H : ℂ → ℂ} {M : ℝ} (hM : 1≤M)
    (hH : AnalyticOnNhd ℂ H (closedBall 0 (2/3))) (h0 : H 0≠0)
    (hb : ∀z∈closedBall 0 (2/3),‖H z‖≤M) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ) (B : ℝ),
      (∀a∈S,a∈ball 0 (1/2) ∧ 0 < m a) ∧ 1≤B ∧
      B+∑a∈S,(m a:ℝ)≤(2001+21/Real.log (4/3))*(1+Real.log (M/‖H 0‖)) ∧
      (∀z∈closedBall 0 (9/20),(∀a∈S,z≠a) → H z≠0) ∧
      (∀z∈closedBall 0 (9/20),(∀a∈S,z≠a) → ‖logDeriv H z‖≤zeroWeight S m B z) := by
  obtain ⟨S,m,g,hS,hm,hg,hgne,he,hbg,hg0⟩:=finite_blaschke_factorization
    (by norm_num : (0:ℝ)<1/2) (hH.mono (closedBall_subset_closedBall (by norm_num))) h0
    (fun z hz=>hb z ((sphere_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))) hz))
  have hf0 : 0<‖H 0‖:=norm_pos_iff.mpr h0
  have hg0' : 0<‖g 0‖:=norm_pos_iff.mpr (hgne 0 (mem_ball_self (by norm_num)))
  have hl : 0≤Real.log (M/‖H 0‖) := Real.log_nonneg ((le_div_iff₀ hf0).mpr (by simpa using hb 0 (mem_closedBall_self (by norm_num))))
  have hlg : Real.log (M/‖g 0‖)≤Real.log (M/‖H 0‖) := Real.log_le_log (div_pos (by linarith) hg0')
    (div_le_div_of_nonneg_left (by linarith) hf0 hg0)
  have hN:=local_divisor_sum_bound hM hH h0 (fun z hz=>hb z (sphere_subset_closedBall hz))
    S m (fun a ha=>(hS a ha).1) (fun a ha=>(hS a ha).2) hm
  have hlog : 0<Real.log (4/3) := Real.log_pos (by norm_num)
  let L:=1+Real.log (M/‖H 0‖)
  let B:=2001*L+20*∑a∈S,(m a:ℝ)
  have ha : 0≤∑a∈S,(m a:ℝ) :=Finset.sum_nonneg (fun _ _ =>Nat.cast_nonneg _)
  have hn : ∑a∈S,(m a:ℝ)≤L/Real.log (4/3) := hN.trans (div_le_div_of_nonneg_right (by dsimp[L]; linarith) hlog.le)
  refine ⟨S,m,B,hS,?_,?_,?_,?_⟩
  · dsimp [B,L]; linarith
  · dsimp [B]
    have hh:=mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ)≤21)
    dsimp [L] at *
    nlinarith [show 21*((1+Real.log (M/‖H 0‖))/Real.log (4/3))=(21/Real.log (4/3))*(1+Real.log (M/‖H 0‖)) by ring]
  · intro z hz hza
    rw [he z (closedBall_subset_closedBall (by norm_num) hz)]
    apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (fun a ha=>pow_ne_zero _ (blaschke_ne_zero
        (by norm_num) (hS a ha).1 (closedBall_subset_closedBall (by norm_num) hz) (hza a ha)))
    · exact hgne z (closedBall_subset_ball (by norm_num) hz)
  · intro z hz hza
    apply (factor_logDeriv_bound_wide S m (fun a ha=>(hS a ha).1) hg hgne he hbg hz hza).trans
    dsimp [zeroWeight,B,L]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib,←Finset.sum_mul]
    linarith

end SharpNodal.Holomorphic

namespace SharpNodal.Profiles
open Holomorphic Carleman
lemma holomorphic_gradient_local_length_wide {H : ℂ → ℂ} {v : Plane → ℝ}
    (S : Finset ℂ) (m : ℂ → ℕ) {B : ℝ} (hB : 1≤B)
    (hm : ∀a∈S,0 < m a)
    (hH : DifferentiableOn ℂ H (ball 0 1))
    (hHne : ∀z∈closedBall 0 (9/20),(∀a∈S,z≠a) → H z≠0)
    (hHd : ∀z∈closedBall 0 (9/20),(∀a∈S,z≠a) → ‖logDeriv H z‖≤zeroWeight S m B z)
    (hv : ∀x∈ball (0:Plane) 1,DifferentiableAt ℝ v x)
    (hcomp : ∀x∈ball (0:Plane) 1,‖complexGradient v x-H (planeToComplex x)‖≤‖H (planeToComplex x)‖/1024)
    {c : Plane} (hc : c∈ball (0:Plane) (2/5)) (hca : ∀a∈S,planeToComplex c≠a) :
    Measure.hausdorffMeasure 1 {x | x∈ball c (4/(1024*zeroWeight S m B (planeToComplex c))) ∧ v x=0}
      ≤ ENNReal.ofReal (32/(1024*zeroWeight S m B (planeToComplex c))) := by
  let W:=zeroWeight S m B (planeToComplex c)
  let R:=4/(1024*W)
  have hWp : 0<W:=zeroWeight_pos (by linarith : 0<B) _
  have hW : 1≤W := by
    have hs : 0≤∑a∈S,(m a:ℝ)*‖planeToComplex c-a‖⁻¹:=Finset.sum_nonneg (fun a _=>by positivity)
    dsimp [W,zeroWeight]; linarith
  have hR : 0<R:=by dsimp [R]; positivity
  have hRbd : R≤1/256 := by dsimp [R]; apply (div_le_iff₀ (by positivity)).mpr; nlinarith
  have hKR : (2*W)*R≤1/4 := by dsimp [R]; field_simp; norm_num
  have hphasebd : 2*(2*W)*R=1/64 := by dsimp [R]; field_simp; ring
  have hball (z : ℂ) (hz : z∈closedBall (planeToComplex c) R) : z∈closedBall 0 (9/20) := by
    have hd:=mem_closedBall.mp hz
    have hc':‖planeToComplex c‖<2/5 :=by simpa only [planeToComplex.norm_map] using mem_ball_zero_iff.mp hc
    have ht:=norm_add_le (z-planeToComplex c) (planeToComplex c)
    rw [sub_add_cancel] at ht
    rw [dist_eq_norm] at hd
    exact mem_closedBall_zero_iff.mpr (by linarith)
  have hball1 (x : Plane) (hx : x∈ball c R) : x∈ball (0:Plane) 1 := by
    have hz : planeToComplex x∈closedBall (planeToComplex c) R :=by
      rw [mem_closedBall,planeToComplex.dist_map]
      exact (mem_ball.mp hx).le
    have ht:=mem_closedBall_zero_iff.mp (hball _ hz)
    rw [planeToComplex.norm_map] at ht
    exact mem_ball_zero_iff.mpr (by linarith)
  have hw (z : ℂ) (hz : z∈closedBall (planeToComplex c) R) :=
    zeroWeight_local_comparison (by linarith :0<B) hca hm (w:=z) (by
      apply (show ‖z-planeToComplex c‖≤R by simpa only [dist_eq_norm] using mem_closedBall.mp hz).trans
      change R≤1/(4*W)
      dsimp [R]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith)
  have hdiff (z : ℂ) (hz : z∈closedBall (planeToComplex c) R) : DifferentiableAt ℂ H z :=
    hH.differentiableAt (isOpen_ball.mem_nhds (closedBall_subset_ball (by norm_num) (hball z hz)))
  have hd (z : ℂ) (hz : z∈closedBall (planeToComplex c) R) : ‖deriv H z‖≤(2*W)*‖H z‖ := by
    have he:=hHd z (hball z hz) (hw z hz).1
    have hn:=norm_pos_iff.mpr (hHne z (hball z hz) (hw z hz).1)
    rw [logDeriv_apply,norm_div] at he
    exact ((div_le_iff₀ hn).mp he).trans (mul_le_mul_of_nonneg_right (hw z hz).2.2 (norm_nonneg _))
  have hphase:=small_variation hR.le (by positivity) hKR hdiff hd
  rw [hphasebd] at hphase
  have hc1 : c∈ball (0:Plane) 1:=ball_subset_ball (by norm_num) hc
  have hp0:=hphase _ (mem_closedBall_self hR.le)
  have hHc:=hHne _ (hball _ (mem_closedBall_self hR.le)) hca
  have hccomp:=hcomp c hc1
  have hnwc : 0<‖complexGradient v c‖ := by
    have ht:=norm_sub_norm_le (H (planeToComplex c)) (complexGradient v c)
    rw [norm_sub_rev] at ht
    have hpos:=norm_pos_iff.mpr hHc
    linarith
  have hg : ∀x∈ball c R,‖complexGradient v x-complexGradient v c‖≤‖complexGradient v c‖/16 := by
    intro x hx
    have hz : planeToComplex x∈closedBall (planeToComplex c) R :=by
      rw [mem_closedBall,planeToComplex.dist_map]; exact (mem_ball.mp hx).le
    have hph:=hphase _ hz
    have hxcomp:=hcomp x (hball1 x hx)
    have ht:=norm_sub_norm_le (H (planeToComplex x)) (H (planeToComplex c))
    have ht':=norm_sub_norm_le (H (planeToComplex c)) (complexGradient v c)
    rw [norm_sub_rev] at ht'
    have htri:=norm_add_le (complexGradient v x-H (planeToComplex x))
      (H (planeToComplex x)-H (planeToComplex c)+(H (planeToComplex c)-complexGradient v c))
    have htri':=norm_add_le (H (planeToComplex x)-H (planeToComplex c)) (H (planeToComplex c)-complexGradient v c)
    rw [norm_sub_rev (H (planeToComplex c))] at htri'
    have he : complexGradient v x-H (planeToComplex x)+(H (planeToComplex x)-H (planeToComplex c)+(H (planeToComplex c)-complexGradient v c))=complexGradient v x-complexGradient v c := by ring
    rw [he] at htri
    nlinarith [norm_nonneg (H (planeToComplex c))]
  have hlen:=nodal_length_gradient_cone (fun x hx=>hv x (hball1 x hx)) (norm_pos_iff.mp hnwc) hg
  convert hlen using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [R,W]
  congr 1
  ring

lemma nodal_length_of_weight_wide {H : ℂ → ℂ} {v : Plane → ℝ}
    (S : Finset ℂ) (m : ℂ → ℕ) {B : ℝ} (hB : 1≤B)
    (hS : ∀a∈S,a∈ball 0 (1/2) ∧ 0 < m a)
    (hH : DifferentiableOn ℂ H (ball 0 1))
    (hHne : ∀z∈closedBall 0 (9/20),(∀a∈S,z≠a) → H z≠0)
    (hHd : ∀z∈closedBall 0 (9/20),(∀a∈S,z≠a) → ‖logDeriv H z‖≤zeroWeight S m B z)
    (hv : ∀x∈ball (0:Plane) 1,DifferentiableAt ℝ v x)
    (hcomp : ∀x∈ball (0:Plane) 1,‖complexGradient v x-H (planeToComplex x)‖≤‖H (planeToComplex x)‖/1024) :
    Measure.hausdorffMeasure 1 {x | x∈ball (0:Plane) (2/5) ∧ v x=0}
      ≤ ENNReal.ofReal (65536*(Real.pi*B+4*Real.pi*∑a∈S,(m a:ℝ))) := by
  classical
  let K : Set Plane:=planeToComplex ⁻¹' (S : Set ℂ)
  let Z : Set Plane:={x | x∈ball (0:Plane) (2/5) ∧ v x=0}
  let T:=Z\K
  let W : Plane → ℝ:=fun x=>zeroWeight S m B (planeToComplex x)
  let r : Plane → ℝ:=fun x=>1/(1024*W x)
  have hWp (x : Plane) : 0<W x:=zeroWeight_pos (by linarith :0<B) _
  have hW (x : Plane) : 1≤W x := by
    have hs : 0≤∑a∈S,(m a:ℝ)*‖planeToComplex x-a‖⁻¹ :=Finset.sum_nonneg (fun _ _=>by positivity)
    dsimp [W,zeroWeight]; linarith
  have hr (x : Plane) : 0 < r x:=by have hp:=hWp x; dsimp [r]; positivity
  have hrb (x : Plane) : r x≤1/1024 := by
    have hp:=hWp x
    dsimp [r]; apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [hW x]
  have hca (x : Plane) (hx : x∈T) (a : ℂ) (ha : a∈S) : planeToComplex x≠a := by
    intro he; exact hx.2 (by change planeToComplex x∈S; simpa only [he] using ha)
  have hD (x : Plane) (hx : x∈T) : ball x (r x)⊆ball (0:Plane) 1 := by
    intro y hy
    have hx' : ‖x‖<2/5:=mem_ball_zero_iff.mp hx.1.1
    have hy' : ‖y-x‖ < r x:=by simpa only [dist_eq_norm] using mem_ball.mp hy
    have ht:=norm_add_le (y-x) x
    rw [sub_add_cancel] at ht
    exact mem_ball_zero_iff.mpr (by linarith [hrb x])
  have hlocal (x : Plane) (hx : x∈T) : Measure.hausdorffMeasure 1 (T∩ball x (4*r x))≤
      (65536:ℝ≥0∞)*weightMeasure S m B (ball x (r x)) := by
    have hlen:=holomorphic_gradient_local_length_wide S m hB (fun a ha=>(hS a ha).2) hH hHne hHd hv hcomp hx.1.1 (hca x hx)
    have hlow:=weightMeasure_local_lower S m hB (fun a ha=>(hS a ha).2) (hca x hx)
    have he : 4*r x=4/(1024*W x):=by dsimp [r]; ring
    have hs : T∩ball x (4*r x)⊆{y | y∈ball x (4/(1024*W x)) ∧ v y=0} :=by
      intro y hy; exact ⟨he ▸ hy.2,hy.1.1.2⟩
    apply (measure_mono hs).trans (hlen.trans ?_)
    have hconst : ENNReal.ofReal (32/(1024*W x))=(65536:ℝ≥0∞)*ENNReal.ofReal (1/(2097152*W x)) :=by
      rw [←ENNReal.ofReal_ofNat 65536,←ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    rw [hconst]
    exact mul_le_mul_right hlow _
  have hbound:=vitali_measure_bound (Measure.hausdorffMeasure 1) (weightMeasure S m B) T (ball (0:Plane) 1) r
    (R:=1/1024) (fun x _=>hr x) (fun x _=>hrb x) hD 65536 hlocal
  have hkfin : K.Finite:=S.finite_toSet.preimage planeToComplex.injective.injOn
  have : NullSingletonClass (Measure.hausdorffMeasure (X:=Plane) 1):=Measure.nullSingletonClass_hausdorff Plane (by norm_num)
  have hK : Measure.hausdorffMeasure 1 K=0:=hkfin.measure_zero _
  have hZ : Z⊆T∪K:=fun x hx=>by by_cases h : x∈K; exact Or.inr h; exact Or.inl ⟨hx,h⟩
  calc
    Measure.hausdorffMeasure 1 Z ≤ Measure.hausdorffMeasure 1 T+Measure.hausdorffMeasure 1 K :=measure_union_le _ _ |>.trans' (measure_mono hZ)
    _ ≤ (65536:ℝ≥0∞)*weightMeasure S m B (ball (0:Plane) 1) := by simpa only [hK,add_zero] using hbound
    _ ≤ (65536:ℝ≥0∞)*ENNReal.ofReal (Real.pi*B+4*Real.pi*∑a∈S,(m a:ℝ)) :=
      mul_le_mul_right (weightMeasure_unit_bound S m (by linarith) (fun a ha=>(hS a ha).1)) _
    _ = _ :=by rw [←ENNReal.ofReal_ofNat 65536,←ENNReal.ofReal_mul (by norm_num)]

lemma nodal_length_holomorphic_comparison_wide {H : ℂ → ℂ} {v : Plane → ℝ} {M : ℝ}
    (hM : 1≤M) (hH : DifferentiableOn ℂ H (ball 0 1)) (hH0 : H 0≠0)
    (hb : ∀z∈closedBall 0 (2/3),‖H z‖≤M)
    (hv : ∀x∈ball (0:Plane) 1,DifferentiableAt ℝ v x)
    (hcomp : ∀x∈ball (0:Plane) 1,‖complexGradient v x-H (planeToComplex x)‖≤‖H (planeToComplex x)‖/1024) :
    Measure.hausdorffMeasure 1 {x | x∈ball (0:Plane) (2/5) ∧ v x=0} ≤
      ENNReal.ofReal ((65536*4*Real.pi*(2001+21/Real.log (4/3)))*(1+Real.log (M/‖H 0‖))) := by
  have han : AnalyticOnNhd ℂ H (closedBall 0 (2/3)) := by
    intro z hz
    exact hH.analyticAt (isOpen_ball.mem_nhds (closedBall_subset_ball (by norm_num) hz))
  obtain ⟨S,m,B,hS,hB,hBN,hne,hd⟩:=exists_zeroWeight_wide hM han hH0 hb
  apply (nodal_length_of_weight_wide S m hB hS hH hne hd hv hcomp).trans
  apply ENNReal.ofReal_le_ofReal
  have hp:=Real.pi_pos
  have hmul:=mul_le_mul_of_nonneg_left hBN (by positivity : 0≤65536*4*Real.pi)
  nlinarith

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

lemma rconv_comm_real (f g : Plane → ℝ) : rconv f g=rconv g f := by
  funext x
  rw [rconv_eq,rconv_swap]
  simp only [mul_comm]

lemma harmonic_parametrix {h : Plane → ℝ} (hh : Smooth h) (hc : HasCompactSupport h)
    (he : ∀x∈Metric.ball (0:Plane) 2,euclideanLaplacian h x=0) :
    ∀x∈Metric.ball (0:Plane) (7/4),h x= -(2*Real.pi)⁻¹*rconv h parametrixKernel x := by
  intro x hx
  have hn : ‖x‖<7/4:=by simpa only [Metric.mem_ball,dist_zero_right] using hx
  have hz : rconv logParametrix (euclideanLaplacian h) x=0 := by
    rw [rconv_eq]
    apply integral_eq_zero_of_ae
    filter_upwards [] with y
    change logParametrix y*euclideanLaplacian h (x-y)=0
    by_cases hy : (1/4:ℝ)≤‖y‖
    · rw [logParametrix_zero hy,zero_mul]
    · rw [he (x-y) (by
        apply mem_ball_zero_iff.mpr
        have ht:=norm_sub_le x y
        have hy':=lt_of_not_ge hy
        linarith),mul_zero]
  have hi:=laplacian_parametrix_convolution hh hc x
  rw [laplacian_rconv integrable_logParametrix hh hc,hz,rconv_comm_real parametrixKernel h] at hi
  field_simp
  linarith

lemma integral_norm_bounded_ball {f : Plane → ℝ} {R B : ℝ}
    (_hf : Integrable f) (_hB : 0≤B)
    (hs : ∀x,R≤‖x‖ → f x=0) (hb : ∀x,|f x|≤B) :
    (∫x,‖f x‖)≤volume.real (Metric.ball (0:Plane) R)*B := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0:Plane) R)):=⟨by simp only [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  have he : (fun x=>‖f x‖)=(Metric.ball (0:Plane) R).indicator (fun x=>‖f x‖) := by
    funext x
    by_cases hx : x∈Metric.ball (0:Plane) R
    · simp [hx]
    · have hz:=hs x (by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx)
      simp [hx,hz]
  rw [he,integral_indicator measurableSet_ball]
  calc
    _ ≤ ∫_x in Metric.ball (0:Plane) R,B := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun x=>norm_nonneg _))
        (integrable_const _)
      exact Eventually.of_forall (fun x=>by simpa only [Real.norm_eq_abs] using hb x)
    _ = _ := by simp [Measure.real,smul_eq_mul]

lemma harmonic_gradient_bound : ∃C : ℝ,0≤C ∧ ∀(h : Plane → ℝ),Smooth h →
    (∀x∈Metric.ball (0:Plane) (9/4),euclideanLaplacian h x=0) →
    ∀B : ℝ,0≤B → (∀x∈Metric.ball (0:Plane) (5/2),|h x|≤B) →
    ∀x∈Metric.ball (0:Plane) 1,∀i,|coordPartial h i x|≤C*B := by
  let χ : ContDiffBump (0:Plane):=⟨9/4,5/2,by norm_num,by norm_num⟩
  have hcK:=compact_parametrixKernel
  choose D hD using fun i : Fin 2 =>
    (smooth_partial smooth_parametrixKernel i).continuous.norm.bddAbove_range_of_hasCompactSupport (compact_partial hcK i).norm
  let A:=∑i : Fin 2,max 0 (D i)
  have hA : 0≤A:=Finset.sum_nonneg (fun _ _=>le_max_left _ _)
  have hAb (i : Fin 2) (x : Plane) : ‖coordPartial parametrixKernel i x‖≤A := by
    exact ((hD i (mem_range_self x)).trans (le_max_right _ _)).trans
      (Finset.single_le_sum (fun j _=>le_max_left (0:ℝ) (D j)) (Finset.mem_univ i))
  refine ⟨|(2*Real.pi)⁻¹| *A*volume.real (Metric.ball (0:Plane) (5/2)),by positivity,?_⟩
  intro h hh he B hB hb x hx i
  let g : Plane → ℝ:=fun x=>χ x*h x
  have hg : Smooth g:=χ.contDiff.mul hh
  have hcg : HasCompactSupport g:=χ.hasCompactSupport.mul_right
  have hig : Integrable g:=hg.continuous.integrable_of_hasCompactSupport hcg
  have hge : ∀x∈Metric.ball (0:Plane) (9/4),g=ᶠ[𝓝 x]h := by
    intro x hx
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    have ho : χ y=1:=χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    simp only [g,ho,one_mul]
  have hgb : ∀y,|g y|≤B := by
    intro y
    by_cases hy : y∈Metric.ball (0:Plane) (5/2)
    · dsimp [g]; rw [abs_mul,abs_of_nonneg χ.nonneg]
      exact (mul_le_mul_of_nonneg_right χ.le_one (abs_nonneg _)).trans (by simpa using hb y hy)
    · have hz : χ y=0:=χ.zero_of_le_dist (by simpa only [χ,Metric.mem_ball,dist_zero_right,not_lt] using hy)
      simpa [g,hz] using hB
  have hgs : ∀y,(5/2:ℝ)≤‖y‖ → g y=0 := by
    intro y hy
    have hz : χ y=0:=χ.zero_of_le_dist (by simpa only [χ,dist_zero_right] using hy)
    simp [g,hz]
  have hrep:=harmonic_parametrix hg hcg (fun y hy=>by
    rw [laplacian_germ (hge y (Metric.ball_subset_ball (by norm_num) hy))]
    exact he y (Metric.ball_subset_ball (by norm_num) hy))
  have heq : h=ᶠ[𝓝 x](fun y=> -(2*Real.pi)⁻¹*rconv g parametrixKernel y) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball (by norm_num : (1:ℝ)≤7/4) hx)] with y hy
    rw [←hrep y hy]
    exact ((hge y (Metric.ball_subset_ball (by norm_num) hy)).self_of_nhds).symm
  rw [partial_germ heq,partial_const_mul (smooth_rconv hig smooth_parametrixKernel hcK),
    partial_rconv hig smooth_parametrixKernel hcK,abs_mul,abs_neg]
  have hbconv:=norm_rconv_le hig (smooth_partial smooth_parametrixKernel i).continuous
    (compact_partial hcK i) (hAb i) x
  have hi:=integral_norm_bounded_ball hig hB hgs hgb
  have he' := mul_le_mul_of_nonneg_left (hbconv.trans (mul_le_mul_of_nonneg_left hi hA)) (abs_nonneg ((2*Real.pi)⁻¹))
  simpa only [Real.norm_eq_abs,mul_assoc] using he'

lemma small_potential_gradient_bound : ∃A : ℝ,1≤A ∧
    ∀{C ε δ : ℝ} {q : Plane → ℝ}, SmallPotential C ε δ q →
    ∀{U : Plane → ℝ},Smooth U →
    (∀x∈Metric.ball (0:Plane) (5/2),euclideanLaplacian U x+q x*U x=0) →
    ∀S : ℝ,0≤S → (∀x∈Metric.ball (0:Plane) (5/2),|U x|≤S) →
    ∀x∈Metric.ball (0:Plane) 1,∀i,|coordPartial U i x|≤A*S := by
  obtain ⟨D,hD,hDb⟩:=harmonic_gradient_bound
  refine ⟨2*D+1,by linarith,?_⟩
  intro C ε δ q h U hU hUE S hS hUb x hx i
  let χ : ContDiffBump (0:Plane):=⟨9/4,5/2,by norm_num,by norm_num⟩
  let f : Plane → ℝ:=fun y=>χ y*(q y*U y)
  have hf : Smooth f:=χ.contDiff.mul (h.smooth.mul hU)
  have hcf : HasCompactSupport f:=χ.hasCompactSupport.mul_right
  have hfs : ∀y,3≤‖y‖ → f y=0 := by
    intro y hy
    have hz : χ y=0:=χ.zero_of_le_dist (by dsimp [χ]; rw [dist_zero_right]; linarith)
    simp [f,hz]
  have hfb : ∀y∈Metric.ball (0:Plane) 3,|f y|≤ε*S := by
    intro y hy
    by_cases hy' : y∈Metric.ball (0:Plane) (5/2)
    · dsimp [f]; rw [abs_mul,abs_mul,abs_of_nonneg χ.nonneg]
      exact (mul_le_mul_of_nonneg_right χ.le_one (by positivity)).trans (by
        simpa using mul_le_mul (h.bound y hy) (hUb y hy') (abs_nonneg _) h.ε_nonneg)
    · have hz : χ y=0:=χ.zero_of_le_dist (by simpa only [χ,Metric.mem_ball,dist_zero_right,not_lt] using hy')
      have hn : 0≤ε*S:=mul_nonneg h.ε_nonneg hS
      simpa [f,hz] using hn
  have hn:=h.control.2 f hf hcf (ε*S) (mul_nonneg h.ε_nonneg hS) hfs hfb
  let v : Plane → ℝ:=fun y=>U y+newtonPotential f y
  have hv : Smooth v:=hU.add (smooth_newtonPotential hf hcf)
  have he : ∀y∈Metric.ball (0:Plane) (9/4),euclideanLaplacian v y=0 := by
    intro y hy
    rw [laplacian_add hU (smooth_newtonPotential hf hcf),laplacian_newtonPotential hf hcf]
    have ho : χ y=1:=χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    simpa only [f,ho,one_mul] using hUE y (Metric.ball_subset_ball (by norm_num) hy)
  have hδ:=h.δ_le
  have hsm:=mul_le_mul_of_nonneg_right h.small hS
  have hδS:=mul_le_mul_of_nonneg_right hδ hS
  have hb : ∀y∈Metric.ball (0:Plane) (5/2),|v y|≤2*S := by
    intro y hy
    have ht:=(hn y (Metric.ball_subset_ball (by norm_num) hy)).1
    have hsum:=abs_add_le (U y) (newtonPotential f y)
    have hu:=hUb y hy
    dsimp [v]; nlinarith
  have hd:=hDb v hv he (2*S) (by positivity) hb x hx i
  have hx3 : x∈Metric.ball (0:Plane) 3:=Metric.ball_subset_ball (by norm_num) hx
  have hnp:=(hn x hx3).2 i
  have hvp : coordPartial v i x=coordPartial U i x+coordPartial (newtonPotential f) i x :=
    partial_add hU (smooth_newtonPotential hf hcf) i x
  have hu : coordPartial U i x=coordPartial v i x-coordPartial (newtonPotential f) i x:=by linarith
  rw [hu]
  have ht:=abs_sub (coordPartial v i x) (coordPartial (newtonPotential f) i x)
  nlinarith

namespace SmallPotential
variable {C ε δ : ℝ} {q : Plane → ℝ} (h : SmallPotential C ε δ q)
include h
lemma limit_upper {x : Plane} (hx : x∈Metric.ball (0:Plane) 3) : multiplierLimit q x≤2 := by
  have he:=multiplierLimit_bounds h.control h.ε_nonneg h.δ_nonneg h.δ_lt h.small h.smooth h.compact h.support h.bound hx
  have hb:=h.ratio_le
  have ht:=(abs_le.mp he.1).2
  linarith
lemma limit_partial_bound {x : Plane} (hx : x∈Metric.ball (0:Plane) 3) (i : Fin 2) :
    |coordPartial (multiplierLimit q) i x|≤1 :=
  ((multiplierLimit_bounds h.control h.ε_nonneg h.δ_nonneg h.δ_lt h.small h.smooth h.compact h.support h.bound hx).2 i).trans h.ratio_le
lemma quotient_differentiable {U : Plane → ℝ} (hU : Smooth U) {x : Plane}
    (hx : x∈Metric.ball (0:Plane) 3) : DifferentiableAt ℝ (fun y=>U y/multiplierLimit q y) x := by
  have hUd : DifferentiableAt ℝ U x:=(hU.differentiable (by simp)).differentiableAt
  have hne : multiplierLimit q x≠0:=by have:=h.limit_lower hx; linarith
  convert! hUd.mul ((h.limit_differentiable hx).inv hne) using 1
  all_goals try with_reducible_and_instances rfl
end SmallPotential
end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
namespace SharpNodal.Profiles
open Carleman
lemma gradient_anchor {v : Plane → ℝ} (hv : ∀x∈ball (0:Plane) (1/4),DifferentiableAt ℝ v x)
    {y z : Plane} (hy : y∈ball (0:Plane) (1/4)) (hz : z∈ball (0:Plane) (1/4))
    (hvz : v z=0) (hvy : 1/2≤|v y|) :
    ∃p∈ball (0:Plane) (1/4),1/2≤‖complexGradient v p‖ := by
  by_contra hn
  push Not at hn
  have hder : ∀x∈ball (0:Plane) (1/4),‖fderiv ℝ v x‖≤1 := by
    intro x hx
    have hbound:=fderiv_norm_le_two (by norm_num : (0:ℝ)≤1/2) x
      (fun i =>(abs_partial_le_norm_gradient v i x).trans (hn x hx).le)
    norm_num at hbound
    exact hbound
  have he:=(convex_ball (0:Plane) (1/4)).norm_image_sub_le_of_norm_fderiv_le
    hv hder hz hy
  rw [hvz,sub_zero,Real.norm_eq_abs,one_mul] at he
  have ht:=norm_sub_le y z
  have hy':=mem_ball_zero_iff.mp hy
  have hz':=mem_ball_zero_iff.mp hz
  linarith

lemma partial_rescale_differentiable {v : Plane → ℝ} {p x : Plane} {r : ℝ}
    (hv : DifferentiableAt ℝ v (rescaleMap p r x)) (i : Fin 2) :
    coordPartial (v∘rescaleMap p r) i x=r*coordPartial v i (rescaleMap p r x) := by
  have h:=hv.hasFDerivAt.comp x (((hasFDerivAt_id (𝕜:=ℝ) x).const_smul r).const_add p)
  change fderiv ℝ (v∘rescaleMap p r) x _=_
  have he : fderiv ℝ (v∘rescaleMap p r) x=
    (fderiv ℝ v (rescaleMap p r x)).comp (r • ContinuousLinearMap.id ℝ Plane) := by
    simpa only [Function.comp_def,rescaleMap,Pi.smul_apply,id_eq] using h.fderiv
  rw [he]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,map_smul,smul_eq_mul,coordPartial]

lemma gradient_rescale_differentiable {v : Plane → ℝ} {p x : Plane} {r : ℝ}
    (hv : DifferentiableAt ℝ v (rescaleMap p r x)) :
    complexGradient (v∘rescaleMap p r) x=(r:ℂ)*complexGradient v (rescaleMap p r x) := by
  simp only [complexGradient,partial_rescale_differentiable hv]
  push_cast; ring

lemma rescaleMap_lipschitz (p : Plane) {r : ℝ} (hr : 0 ≤ r) :
    LipschitzWith (Real.toNNReal r) (rescaleMap p r) := by
  apply LipschitzWith.of_dist_le'
  intro x y
  simp only [rescaleMap,dist_add_left,dist_smul₀,Real.norm_eq_abs,abs_of_nonneg hr,le_refl]

lemma small_nodal_length_of_translated {v : Plane → ℝ} {p : Plane} (hp : p∈ball (0:Plane) (1/4)) :
    Measure.hausdorffMeasure 1 {x | x∈ball (0:Plane) (1/60) ∧ v x=0} ≤
      Measure.hausdorffMeasure 1 {x | x∈ball (0:Plane) (2/5) ∧ (v∘rescaleMap p (3/4)) x=0} := by
  let T:={x | x∈ball (0:Plane) (2/5) ∧ (v∘rescaleMap p (3/4)) x=0}
  have hs : {x | x∈ball (0:Plane) (1/60) ∧ v x=0}⊆rescaleMap p (3/4) '' T := by
    intro x hx
    let y : Plane :=(4/3:ℝ) • (x-p)
    have he : rescaleMap p (3/4) y=x := by dsimp [rescaleMap,y]; rw [smul_smul]; norm_num
    refine ⟨y,⟨?_,?_⟩,he⟩
    · apply mem_ball_zero_iff.mpr
      have ht:=norm_sub_le x p
      have hx':=mem_ball_zero_iff.mp hx.1
      have hp':=mem_ball_zero_iff.mp hp
      dsimp [y]; rw [norm_smul]; norm_num
      linarith
    · simpa only [Function.comp_apply,he] using hx.2
  have hlen:=(rescaleMap_lipschitz p (by norm_num : (0:ℝ)≤3/4)).hausdorffMeasure_image_le (d:=1) (by norm_num) T
  simp only [ENNReal.rpow_one] at hlen
  apply (measure_mono hs).trans (hlen.trans ?_)
  apply mul_le_of_le_one_left'
  change (↑(Real.toNNReal (3/4:ℝ)) : ℝ≥0∞)≤1
  norm_num
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

namespace SharpNodal.Profiles
open Carleman
lemma smooth_C1_bounded_ball {U : Plane → ℝ} (hU : Smooth U) (R : ℝ) :
    ∃K : ℝ,0≤K ∧ ∀x∈ball (0:Plane) R,|U x|≤K ∧ ∀i,|coordPartial U i x|≤K := by
  obtain ⟨B,hB⟩:=(isCompact_closedBall (0:Plane) R).exists_bound_of_continuousOn hU.continuous.continuousOn
  choose D hD using fun i : Fin 2 =>(isCompact_closedBall (0:Plane) R).exists_bound_of_continuousOn
    (smooth_partial hU i).continuous.continuousOn
  let K:=max 0 B+∑i : Fin 2,max 0 (D i)
  have hs : 0≤∑i : Fin 2,max 0 (D i):=Finset.sum_nonneg (fun _ _=>le_max_left _ _)
  refine ⟨K,add_nonneg (le_max_left _ _) hs,?_⟩
  intro x hx
  have hm:=ball_subset_closedBall hx
  constructor
  · exact (hB x hm).trans (by dsimp [K]; simpa only [Real.norm_eq_abs] using (le_max_right (0:ℝ) B).trans (le_add_of_nonneg_right hs))
  · intro i
    apply (hD i x hm).trans
    apply (le_max_right (0:ℝ) (D i)).trans
    exact (Finset.single_le_sum (fun j _=>le_max_left (0:ℝ) (D j)) (Finset.mem_univ i)).trans (le_add_of_nonneg_left (le_max_left _ _))

lemma recenter_inner_maps {p : Plane} (hp : p∈ball (0:Plane) (1/4)) {x : Plane}
    (hx : x∈closedBall (0:Plane) 1) : rescaleMap p (3/4) x∈ball (0:Plane) 1 := by
  apply mem_ball_zero_iff.mpr
  have hp':=mem_ball_zero_iff.mp hp
  have hx':=mem_closedBall_zero_iff.mp hx
  have ht:=norm_add_le p ((3/4:ℝ) • x)
  rw [norm_smul] at ht
  norm_num at ht
  dsimp [rescaleMap]; linarith

lemma planeToComplex_rescale (p x : Plane) (r : ℝ) :
    planeToComplex (rescaleMap p r x)=planeToComplex p+(r:ℂ)*planeToComplex x := by
  simp only [rescaleMap,map_add,map_smul,Complex.real_smul]

theorem normalized_small_potential_length_oai : ∃L : ℝ,0<L ∧
    ∀{C ε δ : ℝ} {q : Plane → ℝ},SmallPotential C ε δ q →
    Real.exp (8*C*(4*δ/(1-δ)))-1≤1/2048 →
    ∀{U : Plane → ℝ},Smooth U →
    (∀x∈ball (0:Plane) (5/2),euclideanLaplacian U x+q x*U x=0) →
    ∀S : ℝ,1≤S → (∀x∈ball (0:Plane) (5/2),|U x|≤S) →
    (∃y∈ball (0:Plane) (1/4),1≤|U y|) →
    Measure.hausdorffMeasure 1 {x | x∈ball (0:Plane) (1/60) ∧ U x=0}≤
      ENNReal.ofReal (L*(1+Real.log S)) := by
  obtain ⟨A,hA,hAb⟩:=small_potential_gradient_bound
  let L₀:=65536*4*Real.pi*(2001+21/Real.log (4/3))
  have hL₀ : 0<L₀:=by dsimp [L₀]; have:=Real.log_pos (by norm_num : (1:ℝ)<4/3); positivity
  have hAP : 0<A:=by linarith
  have hlogA : 0≤Real.log (128*A):=Real.log_nonneg (by linarith)
  refine ⟨L₀*(1+Real.log (128*A)),mul_pos hL₀ (by linarith),?_⟩
  intro C ε δ q h hη U hU hUE S hS hUb hanchor
  have hSp : 0<S:=by linarith
  have hlogS : 0≤Real.log S:=Real.log_nonneg hS
  by_cases hz : ∃z∈ball (0:Plane) (1/60),U z=0
  swap
  · have he : {x | x∈ball (0:Plane) (1/60) ∧ U x=0}=∅:=by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx; exact hz ⟨x,hx.1,hx.2⟩
    rw [he,measure_empty]; exact bot_le
  obtain ⟨z,hz,hUz⟩:=hz
  obtain ⟨y,hy,hUy⟩:=hanchor
  let v : Plane → ℝ:=fun x=>U x/multiplierLimit q x
  have hv : ∀x∈ball (0:Plane) 3,DifferentiableAt ℝ v x := fun x hx=>h.quotient_differentiable hU hx
  have hvz : v z=0:=by simp [v,hUz]
  have hvy : 1/2≤|v y| := by
    have hy3 : y∈ball (0:Plane) 3:=ball_subset_ball (by norm_num) hy
    have hlow:=h.limit_lower hy3
    have hupp:=h.limit_upper hy3
    dsimp [v]; rw [abs_div,abs_of_pos (by linarith : 0 < multiplierLimit q y)]
    apply (le_div_iff₀ (by linarith : 0 < multiplierLimit q y)).mpr
    linarith
  obtain ⟨p,hp,hpgrad⟩:=gradient_anchor (fun x hx=>hv x (ball_subset_ball (by norm_num) hx))
    hy (ball_subset_ball (by norm_num) hz) hvz hvy
  obtain ⟨K,hK,hKb⟩:=smooth_C1_bounded_ball hU 3
  obtain ⟨H,hH,hHclose⟩:=h.holomorphic_gradient hU hUE hK hKb
  have hc (x : Plane) (hx : x∈ball (0:Plane) 1) :
      ‖H (planeToComplex x)-complexGradient v x‖≤‖complexGradient v x‖/2048 := by
    exact (hHclose x (ball_subset_closedBall hx)).trans (by dsimp [v]; nlinarith [norm_nonneg (complexGradient v x)])
  have hnorms (x : Plane) (hx : x∈ball (0:Plane) 1) :
      ‖complexGradient v x‖≤2*‖H (planeToComplex x)‖ ∧
      ‖H (planeToComplex x)‖≤2*‖complexGradient v x‖ := by
    have hd:=hc x hx
    have h1:=norm_sub_norm_le (H (planeToComplex x)) (complexGradient v x)
    have h2:=norm_sub_norm_le (complexGradient v x) (H (planeToComplex x))
    rw [norm_sub_rev (complexGradient v x)] at h2
    constructor <;> linarith [norm_nonneg (complexGradient v x)]
  have hvgrad (x : Plane) (hx : x∈ball (0:Plane) 1) : ‖complexGradient v x‖≤12*(A*S) := by
    have hx3 : x∈ball (0:Plane) 3:=ball_subset_ball (by norm_num) hx
    have hAS : 0≤A*S:=mul_nonneg hAP.le hSp.le
    have hpbound (i : Fin 2) : |coordPartial v i x|≤6*(A*S) := by
      have hu : |U x|≤A*S := (hUb x (ball_subset_ball (by norm_num) hx)).trans (by nlinarith)
      have ht:=quotient_partial_bound hAS (by norm_num : (0:ℝ)≤1)
        (hU.differentiable (by simp) |>.differentiableAt) (h.limit_differentiable hx3)
        (h.limit_lower hx3) hu (hAb h hU hUE S hSp.le hUb x hx) (h.limit_partial_bound hx3) i
      dsimp [v]; linarith only [ht]
    exact (norm_gradient_le v x).trans (by have:=hpbound 0; have:=hpbound 1; linarith)
  have hbH (x : Plane) (hx : x∈ball (0:Plane) 1) : ‖H (planeToComplex x)‖≤24*A*S := by
    have:= (hnorms x hx).2
    have:=hvgrad x hx
    linarith
  let T : ℂ → ℂ:=fun w=>planeToComplex p+(3/4:ℂ)*w
  let G : ℂ → ℂ:=fun w=>(3/4:ℂ)*H (T w)
  let w : Plane → ℝ:=v∘rescaleMap p (3/4)
  have hT (a : ℂ) (ha : a∈ball (0:ℂ) 1) : T a∈ball (0:ℂ) 1 := by
    apply mem_ball_zero_iff.mpr
    have hn:=norm_add_le (planeToComplex p) ((3/4:ℂ)*a)
    rw [LinearIsometryEquiv.norm_map,norm_mul] at hn
    norm_num at hn
    have hp':=mem_ball_zero_iff.mp hp
    have ha':=mem_ball_zero_iff.mp ha
    dsimp [T]; linarith
  have hG : DifferentiableOn ℂ G (ball 0 1) := by
    intro a ha
    have hd' : DifferentiableAt ℂ H (T a):=hH.differentiableAt (isOpen_ball.mem_nhds (hT a ha))
    exact ((hd'.comp a (by dsimp [T]; fun_prop)).const_mul (3/4:ℂ)).differentiableWithinAt
  have hp1 : p∈ball (0:Plane) 1:=ball_subset_ball (by norm_num) hp
  have hGp : 3/16≤‖G 0‖ := by
    have he:=(hnorms p hp1).1
    dsimp [G,T]
    rw [mul_zero,add_zero,norm_mul]
    norm_num
    linarith
  have hG0 : G 0≠0:=norm_pos_iff.mp (by linarith : 0<‖G 0‖)
  have hbG : ∀a∈closedBall (0:ℂ) (2/3),‖G a‖≤24*A*S := by
    intro a ha
    have hTa:=hT a (closedBall_subset_ball (by norm_num) ha)
    have ht:=hbH (complexToPlane (T a)) (by
      apply mem_ball_zero_iff.mpr
      simpa only [LinearIsometryEquiv.norm_map] using mem_ball_zero_iff.mp hTa)
    rw [planeToComplex,LinearIsometryEquiv.symm_apply_apply] at ht
    dsimp [G]
    rw [norm_mul]; norm_num
    nlinarith [norm_nonneg (H (T a))]
  have hw : ∀x∈ball (0:Plane) 1,DifferentiableAt ℝ w x := by
    intro x hx
    have ht:=recenter_inner_maps hp (ball_subset_closedBall hx)
    exact (hv _ (ball_subset_ball (by norm_num) ht)).comp x ((smooth_rescaleMap p (3/4)).differentiable (by simp) |>.differentiableAt)
  have hwc : ∀x∈ball (0:Plane) 1,‖complexGradient w x-G (planeToComplex x)‖≤‖G (planeToComplex x)‖/1024 := by
    intro x hx
    have ht:=recenter_inner_maps hp (ball_subset_closedBall hx)
    have hdiff:=gradient_rescale_differentiable (r:=3/4) (hv _ (ball_subset_ball (by norm_num) ht))
    have he : T (planeToComplex x)=planeToComplex (rescaleMap p (3/4) x):=by
      dsimp [T]
      simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using (planeToComplex_rescale p x (3/4)).symm
    change ‖complexGradient (v∘rescaleMap p (3/4)) x-(3/4:ℂ)*H (T (planeToComplex x))‖≤_
    rw [hdiff,he,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_ofNat,←mul_sub,norm_mul]
    change _≤‖(3/4:ℂ)*H (T (planeToComplex x))‖/1024
    rw [he,norm_mul]
    norm_num
    have hclose:=hc _ ht
    rw [norm_sub_rev] at hclose
    have hnorm:=(hnorms _ ht).1
    linarith
  have hM : 1≤24*A*S:=by nlinarith
  have hlen:=nodal_length_holomorphic_comparison_wide hM hG hG0 hbG hw hwc
  have hlen':=small_nodal_length_of_translated (v:=v) hp
  have he : {x | x∈ball (0:Plane) (1/60) ∧ U x=0}={x | x∈ball (0:Plane) (1/60) ∧ v x=0} := by
    ext x
    by_cases hx : x∈ball (0:Plane) (1/60)
    · have hne : multiplierLimit q x≠0:=by have:=h.limit_lower (ball_subset_ball (by norm_num : (1/60:ℝ)≤3) hx); linarith
      simp only [Set.mem_ofPred_eq, hx, true_and, v, div_eq_zero_iff, hne, or_false]
    · simp only [Set.mem_ofPred_eq,hx,false_and]
  rw [he]
  apply (hlen'.trans hlen).trans
  apply ENNReal.ofReal_le_ofReal
  have hlg : Real.log ((24*A*S)/‖G 0‖)≤Real.log (128*A)+Real.log S := by
    rw [←Real.log_mul (by positivity : 128*A≠0) hSp.ne']
    apply Real.log_le_log (div_pos (by positivity) (norm_pos_iff.mpr hG0))
    apply (div_le_iff₀ (norm_pos_iff.mpr hG0)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hGp (by positivity : 0≤128*A*S)]
  change L₀*(1+Real.log ((24*A*S)/‖G 0‖))≤_
  have hle:=mul_le_mul_of_nonneg_left hlg hL₀.le
  nlinarith [mul_nonneg hlogA hlogS,mul_nonneg hL₀.le (mul_nonneg hlogA hlogS)]
end SharpNodal.Profiles

end

end OAI
end

theorem solution : type_of% @OAI.SharpNodal.Profiles.normalized_small_potential_length_oai := @OAI.SharpNodal.Profiles.normalized_small_potential_length_oai
