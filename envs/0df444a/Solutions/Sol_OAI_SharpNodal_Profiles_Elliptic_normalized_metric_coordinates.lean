-- Prove2me | solution 1 for OAI.SharpNodal.Profiles.Elliptic.normalized_metric_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:21:08.986611+00:00
-- url     : https://prove2.me/submissions/7eb3219c-7d52-4d98-84f0-71538f1aecce

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

lemma integrable_mul_compact_left {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport f) : Integrable (fun x => f x * g x) := by
  exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_right

lemma integral_partial_mul {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport f) (i : Fin 2) :
    (∫ x, coordPartial f i x * g x) = -(∫ x, f x * coordPartial g i x) := by
  simpa only [mul_comm] using integral_mul_partial hg hf hc i

lemma integral_sum_mul {ι : Type*} (s : Finset ι) {f : ι → Plane → ℝ} {g : Plane → ℝ}
    (hf : ∀ i ∈ s, Smooth (f i)) (hg : Smooth g) (hc : HasCompactSupport g) :
    (∫ x, (∑ i ∈ s, f i x) * g x) = ∑ i ∈ s, ∫ x, f i x * g x := by
  simp_rw [Finset.sum_mul]
  exact integral_finsetSum s fun i hi => integrable_mul_compact_right (hf i hi) hg hc


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

lemma integral_laplacian_mul {v : Plane → ℝ} (hv : Smooth v) (hc : HasCompactSupport v) :
    (∫ x, euclideanLaplacian v x * v x) =
      -(∑ i : Fin 2, ∫ x, coordPartial v i x * coordPartial v i x) := by
  unfold euclideanLaplacian
  rw [integral_sum_mul Finset.univ (fun i _ => smooth_partial (smooth_partial hv i) i) hv hc,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_partial_mul (smooth_partial hv i) hv (compact_partial hc i) i

lemma l2sq_nonneg (f : Plane → ℝ) : 0 ≤ l2sq f :=
  integral_nonneg fun x => mul_self_nonneg (f x)

lemma l2sq_add {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    l2sq (fun x => f x + g x) = l2sq f + l2sq g + 2 * (∫ x, f x * g x) := by
  have hI₁ := integrable_mul_compact_left hf hf hcf
  have hI₂ := integrable_mul_compact_left hg hg hcg
  have hI₃ := integrable_mul_compact_left hf hg hcf
  unfold l2sq
  calc
    _ = ∫ x, (f x * f x + g x * g x) + 2 * (f x * g x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := by
      rw [integral_add (f := fun x => f x * f x + g x * g x)
        (hI₁.add hI₂) (hI₃.const_mul 2), integral_add hI₁ hI₂, integral_const_mul]

lemma l2sq_const_mul (f : Plane → ℝ) (c : ℝ) :
    l2sq (fun x => c * f x) = c^2 * l2sq f := by
  unfold l2sq
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

lemma pairing_sq_le {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    (∫ x, f x * g x)^2 ≤ l2sq f * l2sq g := by
  have hquad (t : ℝ) : 0 ≤ l2sq f * (t * t) + (2 * (∫ x, f x * g x)) * t + l2sq g := by
    have h := l2sq_nonneg (fun x => t * f x + g x)
    rw [l2sq_add (contDiff_const.mul hf) hg hcf.mul_left hcg, l2sq_const_mul] at h
    simp_rw [mul_assoc] at h
    rw [integral_const_mul] at h
    nlinarith only [h]
  have h := discrim_le_zero hquad
  unfold discrim at h
  nlinarith only [h]


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Energy
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

lemma l2norm_nonneg (f : Plane → ℝ) : 0 ≤ l2norm f := Real.sqrt_nonneg _

lemma l2norm_sq (f : Plane → ℝ) : (l2norm f)^2 = l2sq f :=
  Real.sq_sqrt (l2sq_nonneg f)

lemma partial_tsupport_subset (f : Plane → ℝ) (i : Fin 2) :
    tsupport (coordPartial f i) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)


end Carleman
end SharpNodal

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Normalization
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

lemma l2sq_coefficient_mul_le {a f : Plane → ℝ} {C : ℝ}
    (ha : Smooth a) (hf : Smooth f) (hc : HasCompactSupport f)
    (hC : 0 ≤ C) (hb : ∀ x ∈ tsupport f, |a x| ≤ C) :
    l2sq (fun x => a x * f x) ≤ C ^ 2 * l2sq f := by
  have hIf := integrable_mul_compact_left hf hf hc
  have hI : Integrable (fun x => (a x * f x) * (a x * f x)) :=
    integrable_mul_compact_left (ha.mul hf) (ha.mul hf) hc.mul_left
  calc
    _ ≤ ∫ x, C ^ 2 * (f x * f x) := by
      apply integral_mono hI (hIf.const_mul (C ^ 2))
      intro x
      by_cases hx : f x = 0
      · simp only [hx, mul_zero, le_refl]
      · have haC := (sq_le_sq₀ (abs_nonneg (a x)) hC).mpr (hb x (subset_closure hx))
        rw [sq_abs] at haC
        have h := mul_le_mul_of_nonneg_right haC (mul_self_nonneg (f x))
        nlinarith only [h]
    _ = _ := integral_const_mul _ _


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

lemma compact_logParametrix : HasCompactSupport logParametrix := by
  apply HasCompactSupport.intro (isCompact_closedBall (0:Plane) (1/4:ℝ))
  intro x hx
  have hh : (1/4:ℝ)<‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx
  exact logParametrix_zero hh.le

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
-- module Solutions.OAIQ4_Nl.NodalLength_AffineError
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

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma volume_unit_disk_real : volume.real (Metric.ball (0:Plane) 1)=Real.pi := by
  simp [measureReal_def,EuclideanSpace.volume_ball_fin_two,ENNReal.toReal_ofReal Real.pi_pos.le]

end SharpNodal.Profiles

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

end SharpNodal.Profiles

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Elliptic
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

namespace SharpNodal.Profiles
open Carleman

lemma l2norm_add_le {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    l2norm (fun x=>f x+g x)≤l2norm f+l2norm g := by
  have hp:=pairing_sq_le hf hg hcf hcg
  have ha:=l2norm_sq f
  have hb:=l2norm_sq g
  have hc:=l2norm_sq (fun x=>f x+g x)
  rw [l2sq_add hf hg hcf hcg] at hc
  have hh : (∫x,f x*g x)≤l2norm f*l2norm g := by
    have hp' : (∫x,f x*g x)^2≤(l2norm f*l2norm g)^2:=by rw [mul_pow,ha,hb]; exact hp
    nlinarith only [hp',mul_nonneg (l2norm_nonneg f) (l2norm_nonneg g)]
  nlinarith [l2norm_nonneg (fun x=>f x+g x),l2norm_nonneg f,l2norm_nonneg g]

lemma l2norm_const_mul (f : Plane → ℝ) (c : ℝ) :
    l2norm (fun x=>c*f x)=|c| *l2norm f := by
  unfold l2norm
  rw [l2sq_const_mul,Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq_eq_abs]

lemma memLp_smooth_compact {f : Plane → ℝ} (hf : Smooth f) (hc : HasCompactSupport f) : MemLp f 2 := by
  apply (memLp_two_iff_integrable_sq hf.continuous.aestronglyMeasurable).mpr
  simpa only [pow_two] using integrable_mul_compact_left hf hf hc

lemma kernel_global_L2_bound {f g : Plane → ℝ} (hf : MemLp f 2) (hg : MemLp g 2) (x : Plane) :
    |rconv f g x|≤l2norm f*l2norm g := by
  have hh:=integral_abs_mul_le_sqrt hf (hg.comp_measurePreserving ((volume : Measure Plane).measurePreserving_sub_left x))
  simp only [Function.comp_apply] at hh
  rw [integral_sub_left_eq_self (fun y=>g y^2) volume x] at hh
  simpa only [rconv_eq,l2norm,l2sq,pow_two] using hh

lemma rconv_support_bound {f g : Plane → ℝ} {r s : ℝ}
    (hf : ∀x,r≤‖x‖ → f x=0) (hg : ∀x,s≤‖x‖ → g x=0)
    {x : Plane} (hx : r+s≤‖x‖) : rconv f g x=0 := by
  rw [rconv_eq]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : r≤‖y‖
  · simp [hf y hy]
  · have hz : s≤‖x-y‖:=by have:=norm_sub_le x y; have h:=norm_add_le (x-y) y; rw [sub_add_cancel] at h; linarith
    simp [hg (x-y) hz]

lemma l2norm_support_bound {f : Plane → ℝ} (hf : Smooth f) (hc : HasCompactSupport f)
    {B : ℝ} (hB : 0≤B) (hb : ∀x,|f x|≤B) (hs : ∀x,1≤‖x‖ → f x=0) :
    l2norm f≤2*B := by
  have he : (fun x=>f x*f x)=(ball (0:Plane) 1).indicator (fun x=>f x*f x) := by
    funext x
    by_cases hx : x∈ball (0:Plane) 1
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,hs x (by simpa only [mem_ball_zero_iff,not_lt] using hx),zero_mul]
  have hi : l2sq f≤Real.pi*B^2 := by
    rw [l2sq,he,integral_indicator measurableSet_ball]
    have hh:=integral_mono_ae ((integrable_mul_compact_left hf hf hc).integrableOn)
      (integrableOn_const (C:=B^2) (s:=ball (0:Plane) 1) measure_ball_ne_top)
      (Eventually.of_forall (fun x=>show f x*f x≤B^2 by have:=hb x; nlinarith [sq_abs (f x),abs_nonneg (f x)]))
    have hv : (volume.restrict (ball (0:Plane) 1)).real univ=Real.pi := by
      rw [measureReal_def,Measure.restrict_apply_univ]
      exact volume_unit_disk_real
    simpa only [integral_const,hv,smul_eq_mul] using hh
  nlinarith [l2norm_sq f,l2norm_nonneg f,Real.pi_lt_four,sq_nonneg B]

lemma smooth_localNewton {g : Plane → ℝ} (hg : Smooth g) (hc : HasCompactSupport g) :
    Smooth (localNewton g) := contDiff_const.mul (smooth_rconv integrable_logParametrix hg hc)

lemma compact_localNewton {g : Plane → ℝ} (hc : HasCompactSupport g) :
    HasCompactSupport (localNewton g) :=
  (compact_logParametrix.convolution (ContinuousLinearMap.mul ℝ ℝ) hc).mul_left

lemma localNewton_partial {g : Plane → ℝ} (hg : Smooth g) (hc : HasCompactSupport g) (i : Fin 2) :
    coordPartial (localNewton g) i=localNewton (coordPartial g i) := by
  funext x
  change coordPartial (fun y=>(2*Real.pi)⁻¹*rconv logParametrix g y) i x=(2*Real.pi)⁻¹*rconv logParametrix (coordPartial g i) x
  rw [partial_const_mul (smooth_rconv integrable_logParametrix hg hc),partial_rconv integrable_logParametrix hg hc]

lemma laplacian_localNewton {g : Plane → ℝ} (hg : Smooth g) (hc : HasCompactSupport g) (x : Plane) :
    euclideanLaplacian (localNewton g) x=g x+(2*Real.pi)⁻¹*rconv parametrixKernel g x := by
  change euclideanLaplacian (fun y=>(2*Real.pi)⁻¹*rconv logParametrix g y) x=_
  rw [laplacian_const_mul (smooth_rconv integrable_logParametrix hg hc)]
  dsimp only
  rw [laplacian_parametrix_convolution hg hc]
  field_simp

lemma parametrixKernel_inner {x : Plane} (hx : ‖x‖<1/8) : parametrixKernel x=0 := by
  have he : parametrixCorrection=ᶠ[𝓝 x](fun _=>0) := by
    filter_upwards [continuous_norm.continuousAt.eventually (eventually_lt_nhds hx)] with y hy
    have hχ : parametrixCutoff y=1:=parametrixCutoff.one_of_mem_closedBall (by simpa only [parametrixCutoff,mem_closedBall_zero_iff] using hy.le)
    simp only [parametrixCorrection,hχ,sub_self,zero_mul]
  rw [parametrixKernel,laplacian_germ he]
  simp only [euclideanLaplacian,show coordPartial (fun _ : Plane=>(0:ℝ))=(fun _ _=>0) by funext i z; simp [coordPartial]]
  simp

lemma localNewton_equation {g : Plane → ℝ} (hg : Smooth g) (hc : HasCompactSupport g)
    (hs : ∀x,(1/64:ℝ)≤‖x‖ → g x=0) {x : Plane} (hx : ‖x‖<1/64) :
    euclideanLaplacian (localNewton g) x=g x := by
  rw [laplacian_localNewton hg hc]
  suffices rconv parametrixKernel g x=0 by simp [this]
  rw [rconv_eq]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : (1/64:ℝ)≤‖x-y‖
  · simp [hs _ hy]
  · have hny : ‖y‖<1/8:=by
      have hh:=norm_sub_le x (x-y)
      rw [sub_sub_cancel] at hh
      linarith
    simp [parametrixKernel_inner hny]

lemma l2sq_hessian_cross {f : Plane → ℝ} (hf : Smooth f) (hc : HasCompactSupport f) :
    (∫x,coordPartial (coordPartial f 0) 0 x*coordPartial (coordPartial f 1) 1 x)=
      l2sq (coordPartial (coordPartial f 0) 1) := by
  rw [integral_partial_mul (smooth_partial hf 0) (smooth_partial (smooth_partial hf 1) 1) (compact_partial hc 0) 0]
  have he : coordPartial (coordPartial (coordPartial f 1) 1) 0=
      coordPartial (coordPartial (coordPartial f 0) 1) 1 := by
    funext x
    rw [partial_partial (smooth_partial hf 1) 1 0]
    congr 1
    funext y
    exact partial_partial hf 1 0 y
  rw [he,integral_mul_partial (smooth_partial hf 0) (smooth_partial (smooth_partial hf 0) 1)
    (compact_partial (compact_partial hc 0) 1) 1,neg_neg]
  rfl

lemma l2sq_hessian_identity {f : Plane → ℝ} (hf : Smooth f) (hc : HasCompactSupport f) :
    l2sq (euclideanLaplacian f)=l2sq (coordPartial (coordPartial f 0) 0)+
      l2sq (coordPartial (coordPartial f 1) 1)+2*l2sq (coordPartial (coordPartial f 0) 1) := by
  have he : euclideanLaplacian f=(fun x=>coordPartial (coordPartial f 0) 0 x+coordPartial (coordPartial f 1) 1 x):=by
    funext x; simp only [euclideanLaplacian,Fin.sum_univ_two]
  rw [he,l2sq_add (smooth_partial (smooth_partial hf 0) 0) (smooth_partial (smooth_partial hf 1) 1)
    (compact_partial (compact_partial hc 0) 0) (compact_partial (compact_partial hc 1) 1),l2sq_hessian_cross hf hc]

lemma l2norm_hessian_le {f : Plane → ℝ} (hf : Smooth f) (hc : HasCompactSupport f) (i j : Fin 2) :
    l2norm (coordPartial (coordPartial f i) j)≤l2norm (euclideanLaplacian f) := by
  apply Real.sqrt_le_sqrt
  have hh:=l2sq_hessian_identity hf hc
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta,Fin.isValue,Fin.mk_one]
  · linarith [l2sq_nonneg (coordPartial (coordPartial f 1) 1),l2sq_nonneg (coordPartial (coordPartial f 0) 1)]
  · linarith [l2sq_nonneg (coordPartial (coordPartial f 0) 0),l2sq_nonneg (coordPartial (coordPartial f 1) 1),l2sq_nonneg (coordPartial (coordPartial f 0) 1)]
  · rw [show coordPartial (coordPartial f 1) 0=coordPartial (coordPartial f 0) 1 from funext (partial_partial hf 1 0)]
    linarith [l2sq_nonneg (coordPartial (coordPartial f 0) 0),l2sq_nonneg (coordPartial (coordPartial f 1) 1),l2sq_nonneg (coordPartial (coordPartial f 0) 1)]
  · linarith [l2sq_nonneg (coordPartial (coordPartial f 0) 0),l2sq_nonneg (coordPartial (coordPartial f 0) 1)]

lemma l2norm_gradient_le {f : Plane → ℝ} (hf : Smooth f) (hc : HasCompactSupport f) (i : Fin 2) :
    l2norm (coordPartial f i)≤l2norm f+l2norm (euclideanLaplacian f) := by
  have hh:=l2sq_nonneg (fun x=>euclideanLaplacian f x+f x)
  rw [l2sq_add (smooth_laplacian hf) hf (compact_laplacian hc) hc,integral_laplacian_mul hf hc] at hh
  have hi : l2sq (coordPartial f i)≤∑j:Fin 2,l2sq (coordPartial f j):=
    Finset.single_le_sum (fun j _=>l2sq_nonneg (coordPartial f j)) (Finset.mem_univ i)
  change 0≤l2sq (euclideanLaplacian f)+l2sq f+2*(-∑j:Fin 2,l2sq (coordPartial f j)) at hh
  have hx:=mul_nonneg (l2norm_nonneg f) (l2norm_nonneg (euclideanLaplacian f))
  nlinarith [l2norm_sq f,l2norm_sq (euclideanLaplacian f),l2norm_sq (coordPartial f i),
    l2norm_nonneg f,l2norm_nonneg (euclideanLaplacian f),l2norm_nonneg (coordPartial f i),
    l2sq_nonneg f,l2sq_nonneg (euclideanLaplacian f)]

lemma memLp_logParametrix : MemLp logParametrix 2 :=
  (memLp_two_iff_integrable_sq (parametrixCutoff.continuous.measurable.mul measurable_id.norm.log |>.aestronglyMeasurable)).mpr integrable_logParametrix_sq

lemma localNewton_L2_bounds : ∃C:ℝ,1≤C ∧ ∀g:Plane → ℝ, Smooth g → HasCompactSupport g →
    (∀x,(1/64:ℝ)≤‖x‖ → g x=0) →
    l2norm (localNewton g)≤C*l2norm g ∧
    (∀i,l2norm (coordPartial (localNewton g) i)≤C*l2norm g) ∧
    (∀i j,l2norm (coordPartial (coordPartial (localNewton g) i) j)≤C*l2norm g) ∧
    (∀x,|localNewton g x|≤C*l2norm g) := by
  let c : ℝ := (2*Real.pi)⁻¹
  let B : ℝ := 2*c*l2norm logParametrix
  let D : ℝ := 1+2*c*l2norm parametrixKernel
  have hc : 0 < c:=inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  have hB : 0≤B:=mul_nonneg (by positivity) (l2norm_nonneg _)
  have hD : 1≤D:=by dsimp [D]; nlinarith [l2norm_nonneg parametrixKernel]
  refine ⟨1+B+D,by linarith,?_⟩
  intro g hg hcomp hs
  have hm:=memLp_smooth_compact hg hcomp
  have hkg:=smooth_rconv (smooth_parametrixKernel.continuous.integrable_of_hasCompactSupport compact_parametrixKernel) hg hcomp
  have hcKg : HasCompactSupport (rconv parametrixKernel g) :=compact_parametrixKernel.convolution (ContinuousLinearMap.mul ℝ ℝ) hcomp
  have hQcg : HasCompactSupport (rconv logParametrix g) :=compact_logParametrix.convolution (ContinuousLinearMap.mul ℝ ℝ) hcomp
  have hQ : l2norm (rconv logParametrix g)≤2*(l2norm logParametrix*l2norm g) := by
    apply l2norm_support_bound (smooth_rconv integrable_logParametrix hg hcomp) hQcg (mul_nonneg (l2norm_nonneg _) (l2norm_nonneg _))
      (kernel_global_L2_bound memLp_logParametrix hm)
    intro x hx
    exact rconv_support_bound (fun y hy=>logParametrix_zero hy) hs (by linarith)
  have hK : l2norm (rconv parametrixKernel g)≤2*(l2norm parametrixKernel*l2norm g) := by
    apply l2norm_support_bound hkg hcKg (mul_nonneg (l2norm_nonneg _) (l2norm_nonneg _))
      (kernel_global_L2_bound (memLp_smooth_compact smooth_parametrixKernel compact_parametrixKernel) hm)
    intro x hx
    exact rconv_support_bound (r:=1/3) (fun y hy=>parametrixKernel_zero (by linarith)) hs (by linarith)
  have h0 : l2norm (localNewton g)≤B*l2norm g := by
    change l2norm (fun x=>c*rconv logParametrix g x)≤_
    rw [l2norm_const_mul,abs_of_pos hc]
    dsimp [B,c] at *
    nlinarith
  have hL : l2norm (euclideanLaplacian (localNewton g))≤D*l2norm g := by
    rw [funext (laplacian_localNewton hg hcomp)]
    have hh:=l2norm_add_le hg (contDiff_const.mul hkg) hcomp hcKg.mul_left (f:=g) (g:=fun x=>c*rconv parametrixKernel g x)
    rw [l2norm_const_mul,abs_of_pos hc] at hh
    dsimp [D,c] at *
    nlinarith
  have h1 (i) : l2norm (coordPartial (localNewton g) i)≤(B+D)*l2norm g :=
    (l2norm_gradient_le (smooth_localNewton hg hcomp) (compact_localNewton hcomp) i).trans (by nlinarith)
  have h2 (i j) : l2norm (coordPartial (coordPartial (localNewton g) i) j)≤D*l2norm g :=
    (l2norm_hessian_le (smooth_localNewton hg hcomp) (compact_localNewton hcomp) i j).trans hL
  refine ⟨h0.trans ?_,fun i=>(h1 i).trans ?_,fun i j=>(h2 i j).trans ?_,?_⟩
  · nlinarith [l2norm_nonneg g]
  · nlinarith [l2norm_nonneg g]
  · nlinarith [l2norm_nonneg g]
  · intro x
    have hh:=kernel_global_L2_bound memLp_logParametrix hm x
    change |c*rconv logParametrix g x|≤_
    rw [abs_mul,abs_of_pos hc]
    have hh':=mul_le_mul_of_nonneg_left hh hc.le
    dsimp [B] at *
    nlinarith [mul_nonneg hc.le (mul_nonneg (l2norm_nonneg logParametrix) (l2norm_nonneg g)), l2norm_nonneg g]

namespace Elliptic

lemma good_partial {f} (hf : Good f) (i) : Good (coordPartial f i) := by
  refine ⟨smooth_partial hf.1 i,compact_partial hf.2.1 i,?_⟩
  intro x hx
  have hsub : tsupport f⊆closedBall (0:Plane) (1/64) := by
    apply closure_minimal ?_ isClosed_closedBall
    intro y hy
    exact mem_closedBall_zero_iff.mpr (le_of_lt (lt_of_not_ge (fun hh=>hy (hf.2.2 y hh))))
  by_cases hstrict : (1/64:ℝ)<‖x‖
  · apply image_eq_zero_of_notMem_tsupport
    intro h
    have := hsub (partial_tsupport_subset f i h)
    rw [mem_closedBall_zero_iff] at this
    linarith
  · have he : ‖x‖=(1/64:ℝ):=le_antisymm (le_of_not_gt hstrict) hx
    have hv : ∀ᶠy in 𝓝[>] (1:ℝ),coordPartial f i (y • x)=0 := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      apply image_eq_zero_of_notMem_tsupport
      intro h
      have hmem:=hsub (partial_tsupport_subset f i h)
      rw [mem_closedBall_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos (by exact lt_trans zero_lt_one hy),he] at hmem
      have hy' : 1<y:=hy
      linarith
    have ht0 : Continuous (fun y:ℝ=>y • x):=continuous_id.smul continuous_const
    have ht : Tendsto (fun y:ℝ=>coordPartial f i (y • x)) (𝓝[>] 1) (𝓝 (coordPartial f i x)) := by
      have ht' : ContinuousAt (fun y:ℝ=>coordPartial f i (y • x)) 1 := ((smooth_partial hf.1 i).continuous.comp ht0).continuousAt
      simpa only [one_smul] using ht'.tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi (1:ℝ)))
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hv.mono (fun _ h=>h.symm)))

lemma smooth_jet {f} (hf : Good f) (α : Kind) : Smooth (jet f α) := by
  rcases α with ⟨j,i⟩; cases j with
  |none=>exact smooth_partial (smooth_localNewton hf.1 hf.2.1) i
  |some j=>exact smooth_partial (smooth_partial (smooth_localNewton hf.1 hf.2.1) j) i

lemma compact_jet {f} (hf : Good f) (α : Kind) : HasCompactSupport (jet f α) := by
  rcases α with ⟨j,i⟩; cases j with
  |none=>exact compact_partial (compact_localNewton hf.2.1) i
  |some j=>exact compact_partial (compact_partial (compact_localNewton hf.2.1) j) i

lemma partial_jet {f} (hf : Good f) (α : Kind) (k) :
    coordPartial (jet f α) k=jet (coordPartial f k) α := by
  have hN:=smooth_localNewton hf.1 hf.2.1
  rcases α with ⟨j,i⟩; cases j with
  |none=>
    change coordPartial (coordPartial (localNewton f) i) k=coordPartial (localNewton (coordPartial f k)) i
    rw [←localNewton_partial hf.1 hf.2.1 k]
    exact funext (partial_partial hN i k)
  |some j=>
    change coordPartial (coordPartial (coordPartial (localNewton f) j) i) k=coordPartial (coordPartial (localNewton (coordPartial f k)) j) i
    rw [←localNewton_partial hf.1 hf.2.1 k]
    funext x
    rw [partial_partial (smooth_partial hN j) i k]
    congr 1
    exact funext (partial_partial hN j k)

lemma smooth_operator {a f} (ha : ∀α,Good (a α)) (hf : Good f) : Smooth (operator a f) :=
  ContDiff.sum (fun α _=>(ha α).1.mul (smooth_jet hf α))

lemma compact_fun_sum {ι : Type*} {s : Finset ι} {f : ι → Plane → ℝ}
    (hf : ∀i∈s,HasCompactSupport (f i)) : HasCompactSupport (fun x=>∑i∈s,f i x) := by
  simpa only [Finset.sum_fn] using HasCompactSupport.finset_sum hf

lemma compact_operator {a f} (ha : ∀α,Good (a α)) : HasCompactSupport (operator a f) := by
  apply compact_fun_sum
  intro α _
  exact (ha α).2.1.mul_right

lemma supported_operator {a f} (ha : ∀α,Good (a α)) : Supported (operator a f) := by
  intro x hx
  apply Finset.sum_eq_zero
  intro α _
  rw [(ha α).2.2 x hx,zero_mul]

lemma good_operator {a f} (ha : ∀α,Good (a α)) (hf : Good f) : Good (operator a f) :=
  ⟨smooth_operator ha hf,compact_operator ha,supported_operator ha⟩

lemma partial_sum {ι : Type*} (s : Finset ι) {f : ι → Plane → ℝ}
    (hf : ∀i∈s,Smooth (f i)) (j : Fin 2) (x : Plane) :
    coordPartial (fun y=>∑i∈s,f i y) j x=∑i∈s,coordPartial (f i) j x := by
  unfold coordPartial
  rw [fderiv_fun_sum (fun i hi=>(hf i hi).differentiable (by simp) |>.differentiableAt),sum_apply]

lemma partial_operator {a f} (ha : ∀α,Good (a α)) (hf : Good f) (i) :
    coordPartial (operator a f) i=(fun x=>operator a (coordPartial f i) x+operator (fun α=>coordPartial (a α) i) f x) := by
  funext x
  change coordPartial (fun y=>∑α,a α y*jet f α y) i x=_
  rw [partial_sum _ (fun α _=>(ha α).1.mul (smooth_jet hf α))]
  simp_rw [partial_mul (ha _).1 (smooth_jet hf _),partial_jet hf]
  simp only [operator,Finset.sum_add_distrib]
  ring

lemma l2norm_mul_le {a f : Plane → ℝ} (ha : Smooth a) (hf : Smooth f) (hc : HasCompactSupport f)
    {C : ℝ} (hC : 0≤C) (hb : ∀x,|a x|≤C) : l2norm (fun x=>a x*f x)≤C*l2norm f := by
  have hh:=l2sq_coefficient_mul_le ha hf hc hC (fun x _=>hb x)
  have hp:=mul_nonneg hC (l2norm_nonneg f)
  nlinarith [l2norm_sq (fun x=>a x*f x),l2norm_sq f,l2norm_nonneg (fun x=>a x*f x)]

lemma l2norm_sum_le {ι : Type*} (s : Finset ι) {f : ι → Plane → ℝ}
    (hf : ∀i∈s,Smooth (f i)) (hc : ∀i∈s,HasCompactSupport (f i)) :
    l2norm (fun x=>∑i∈s,f i x)≤∑i∈s,l2norm (f i) := by
  classical
  induction s using Finset.induction_on with
  |empty=>simp [l2norm,l2sq]
  |@insert a s ha ih=>
    simp only [Finset.sum_insert ha]
    apply (l2norm_add_le (hf a (Finset.mem_insert_self a s))
      (ContDiff.sum (fun i hi=>hf i (Finset.mem_insert_of_mem hi))) (hc a (Finset.mem_insert_self a s))
      (compact_fun_sum (fun i hi=>hc i (Finset.mem_insert_of_mem hi)))).trans
    exact add_le_add_right (ih (fun i hi=>hf i (Finset.mem_insert_of_mem hi)) (fun i hi=>hc i (Finset.mem_insert_of_mem hi))) _

lemma operator_L2_bound {C : ℝ}
    (hC : ∀g,Good g → ∀α,l2norm (jet g α)≤C*l2norm g)
    {a f} (ha : ∀α,Good (a α)) (hf : Good f) {b : Kind → ℝ}
    (hb0 : ∀α,0≤b α) (hb : ∀α x,|a α x|≤b α) :
    l2norm (operator a f)≤(∑α,b α)*C*l2norm f := by
  apply (l2norm_sum_le Finset.univ (fun α _=>(ha α).1.mul (smooth_jet hf α))
    (fun α _=>(compact_jet hf α).mul_left)).trans
  calc
    (∑α,l2norm (fun x=>a α x*jet f α x))≤∑α,b α*(C*l2norm f):=by
      apply Finset.sum_le_sum
      intro α _
      exact (l2norm_mul_le (ha α).1 (smooth_jet hf α) (compact_jet hf α) (hb0 α) (hb α)).trans
        (mul_le_mul_of_nonneg_left (hC f hf α) (hb0 α))
    _ = _ := by rw [←Finset.sum_mul]; ring

lemma operator_L2_bounded {C : ℝ} (hC0 : 0≤C)
    (hC : ∀g,Good g → ∀α,l2norm (jet g α)≤C*l2norm g)
    {a} (ha : ∀α,Good (a α)) : ∃B:ℝ,0≤B ∧ ∀f,Good f → l2norm (operator a f)≤B*l2norm f := by
  have h (α) : ∃b:ℝ,0≤b ∧ ∀x,|a α x|≤b := by
    obtain ⟨b,hb⟩:=(ha α).1.continuous.norm.bddAbove_range_of_hasCompactSupport (ha α).2.1.norm
    refine ⟨max b 0,le_max_right _ _,?_⟩
    intro x
    have hh : |a α x|≤b:=by simpa only [Real.norm_eq_abs] using hb (mem_range_self x)
    exact hh.trans (le_max_left _ _)
  choose b hb0 hb using h
  exact ⟨(∑α,b α)*C,mul_nonneg (Finset.sum_nonneg (fun α _=>hb0 α)) hC0,fun f hf=>operator_L2_bound hC ha hf hb0 hb⟩

lemma SNorm_nonneg (n : ℕ) (f : Plane → ℝ) : 0≤SNorm n f := by
  induction n generalizing f with
  |zero=>exact l2norm_nonneg f
  |succ n ih=>exact add_nonneg (ih f) (Finset.sum_nonneg (fun i _=>ih _))

lemma SNorm_le_succ (n : ℕ) (f : Plane → ℝ) : SNorm n f≤SNorm (n+1) f := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=>SNorm_nonneg n _))

lemma SNorm_partial_le (n : ℕ) (f : Plane → ℝ) (i : Fin 2) : SNorm n (coordPartial f i)≤SNorm (n+1) f := by
  exact (Finset.single_le_sum (fun j _=>SNorm_nonneg n (coordPartial f j)) (Finset.mem_univ i)).trans
    (le_add_of_nonneg_left (SNorm_nonneg n f))

lemma SNorm_add_le (n : ℕ) {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport f) (hd : HasCompactSupport g) :
    SNorm n (fun x=>f x+g x)≤SNorm n f+SNorm n g := by
  induction n generalizing f g with
  |zero=>exact l2norm_add_le hf hg hc hd
  |succ n ih=>
    change SNorm n (fun x=>f x+g x)+(∑i:Fin 2,SNorm n (coordPartial (fun x=>f x+g x) i))≤_
    have he (i) : coordPartial (fun x=>f x+g x) i=(fun x=>coordPartial f i x+coordPartial g i x):=by
      funext x
      exact partial_add hf hg i x
    simp_rw [he]
    have hh:=Finset.sum_le_sum (fun i (_:i∈(Finset.univ:Finset (Fin 2)))=>
      ih (smooth_partial hf i) (smooth_partial hg i) (compact_partial hc i) (compact_partial hd i))
    have hh0:=ih hf hg hc hd
    simp only [Finset.sum_add_distrib] at hh
    dsimp only [SNorm]
    linarith

lemma operator_SNorm_bounded {C : ℝ} (hC0 : 0≤C)
    (hC : ∀g,Good g → ∀α,l2norm (jet g α)≤C*l2norm g)
    (n : ℕ) {a} (ha : ∀α,Good (a α)) :
    ∃B:ℝ,0≤B ∧ ∀f,Good f → SNorm n (operator a f)≤B*SNorm n f := by
  induction n generalizing a with
  |zero=>exact operator_L2_bounded hC0 hC ha
  |succ n ih=>
    obtain ⟨B,hB,hbound⟩:=ih ha
    have hga (i : Fin 2) : ∀α,Good (coordPartial (a α) i):=fun α=>good_partial (ha α) i
    have hi (i : Fin 2) := ih (hga i)
    choose D hD hdb using hi
    refine ⟨B+∑i,D i,add_nonneg hB (Finset.sum_nonneg (fun i _=>hD i)),?_⟩
    intro f hf
    have hb0:=hbound f hf
    have hb (i : Fin 2) : SNorm n (coordPartial (operator a f) i)≤
        B*SNorm n (coordPartial f i)+D i*SNorm n f := by
      rw [partial_operator ha hf]
      exact (SNorm_add_le n (smooth_operator ha (good_partial hf i)) (smooth_operator (hga i) hf)
        (compact_operator ha) (compact_operator (hga i))).trans
        (add_le_add (hbound _ (good_partial hf i)) (hdb i f hf))
    calc
      SNorm (n+1) (operator a f)≤B*SNorm n f+∑i,(B*SNorm n (coordPartial f i)+D i*SNorm n f):=
        add_le_add hb0 (Finset.sum_le_sum (fun i _=>hb i))
      _ = B*SNorm (n+1) f+(∑i,D i)*SNorm n f:=by simp only [SNorm,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]; ring
      _ ≤ (B+∑i,D i)*SNorm (n+1) f := by
        have := mul_le_mul_of_nonneg_left (SNorm_le_succ n f) (Finset.sum_nonneg (s:=Finset.univ) (fun i _=>hD i))
        nlinarith

lemma operator_SNorm_leading {C r : ℝ} (hC0 : 0≤C)
    (hC : ∀g,Good g → ∀α,l2norm (jet g α)≤C*l2norm g)
    {a} (ha : ∀α,Good (a α))
    (hbase : ∀f,Good f → l2norm (operator a f) ≤ r*l2norm f) (n : ℕ) :
    ∃B:ℝ,0≤B ∧ ∀f,Good f → SNorm (n+1) (operator a f) ≤ r*SNorm (n+1) f+B*SNorm n f := by
  induction n with
  |zero=>
    have hi (i : Fin 2) := operator_L2_bounded hC0 hC (fun α=>good_partial (ha α) i)
    choose B hB hb using hi
    refine ⟨∑i,B i,Finset.sum_nonneg (fun i _=>hB i),?_⟩
    intro f hf
    have hh (i : Fin 2) : l2norm (coordPartial (operator a f) i) ≤ r*l2norm (coordPartial f i)+B i*l2norm f:=by
      rw [partial_operator ha hf]
      exact (l2norm_add_le (smooth_operator ha (good_partial hf i)) (smooth_operator (fun α=>good_partial (ha α) i) hf)
        (compact_operator ha) (compact_operator (fun α=>good_partial (ha α) i))).trans
        (add_le_add (hbase _ (good_partial hf i)) (hb i f hf))
    have hsum:=Finset.sum_le_sum (fun i (_:i∈(Finset.univ:Finset (Fin 2)))=>hh i)
    simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul] at hsum
    have h0:=hbase f hf
    dsimp only [SNorm]
    nlinarith
  |succ n ih=>
    obtain ⟨B,hB,hbound⟩:=ih
    have hd (i : Fin 2) := operator_SNorm_bounded hC0 hC (n+1) (fun α=>good_partial (ha α) i)
    choose D hD hdb using hd
    refine ⟨B+∑i,D i,add_nonneg hB (Finset.sum_nonneg (fun i _=>hD i)),?_⟩
    intro f hf
    have h0:=hbound f hf
    have hh (i : Fin 2) : SNorm (n+1) (coordPartial (operator a f) i)≤
        r*SNorm (n+1) (coordPartial f i)+B*SNorm n (coordPartial f i)+D i*SNorm (n+1) f := by
      rw [partial_operator ha hf]
      exact (SNorm_add_le (n+1) (smooth_operator ha (good_partial hf i))
        (smooth_operator (fun α=>good_partial (ha α) i) hf) (compact_operator ha)
        (compact_operator (fun α=>good_partial (ha α) i))).trans
        (add_le_add (hbound _ (good_partial hf i)) (hdb i f hf))
    have hsum:=Finset.sum_le_sum (fun i (_:i∈(Finset.univ:Finset (Fin 2)))=>hh i)
    simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul] at hsum
    change SNorm (n+1) (operator a f)+(∑i:Fin 2,SNorm (n+1) (coordPartial (operator a f) i))≤_
    have he : SNorm (n+1) f=SNorm n f+∑i:Fin 2,SNorm n (coordPartial f i):=rfl
    change _ ≤ r*(SNorm (n+1) f+∑i:Fin 2,SNorm (n+1) (coordPartial f i))+(B+∑i,D i)*SNorm (n+1) f
    calc
      _ ≤ (r*SNorm (n+1) f+B*SNorm n f)+
          (r*(∑i:Fin 2,SNorm (n+1) (coordPartial f i))+B*(∑i:Fin 2,SNorm n (coordPartial f i))+(∑i,D i)*SNorm (n+1) f) := add_le_add h0 hsum
      _ = _ := by rw [he]; ring

lemma good_iterate {a f} (ha : ∀α,Good (a α)) (hf : Good f) (n : ℕ) : Good (iterate a f n) := by
  induction n with
  |zero=>exact hf
  |succ n ih=>exact good_operator ha ih

lemma iterate_SNorm_decay {C : ℝ} (hC0 : 0≤C)
    (hC : ∀g,Good g → ∀α,l2norm (jet g α)≤C*l2norm g)
    {a f} (ha : ∀α,Good (a α)) (hf : Good f)
    (hbase : ∀g,Good g → l2norm (operator a g)≤(1/4)*l2norm g) (m : ℕ) :
    ∃B:ℝ,0≤B ∧ ∀n,SNorm m (iterate a f n)≤B*(1/2:ℝ)^n := by
  induction m with
  |zero=>
    refine ⟨l2norm f,l2norm_nonneg f,?_⟩
    intro n
    induction n with
    |zero=>simp [iterate,SNorm]
    |succ n ih=>
      have hh:=hbase _ (good_iterate ha hf n)
      change l2norm (operator a (iterate a f n))≤_
      change l2norm (iterate a f n)≤_ at ih
      rw [pow_succ]
      nlinarith [mul_nonneg (l2norm_nonneg f) (pow_nonneg (by norm_num : (0:ℝ)≤1/2) n)]
  |succ m ih=>
    obtain ⟨D,hD,hd⟩:=ih
    obtain ⟨E,hE,he⟩:=operator_SNorm_leading hC0 hC ha hbase m
    let B:=SNorm (m+1) f+4*E*D
    have hB : 0≤B:=add_nonneg (SNorm_nonneg _ _) (by positivity)
    refine ⟨B,hB,?_⟩
    intro n
    induction n with
    |zero=>simp only [iterate,pow_zero,mul_one]; dsimp [B]; nlinarith
    |succ n ih=>
      have hh:=he _ (good_iterate ha hf n)
      have hd':=mul_le_mul_of_nonneg_left (hd n) hE
      change SNorm (m+1) (operator a (iterate a f n))≤_
      rw [pow_succ]
      have hp : 0≤(1/2:ℝ)^n:=by positivity
      have hhB : 4*E*D≤B:=by dsimp [B]; linarith [SNorm_nonneg (m+1) f]
      have hhB':=mul_le_mul_of_nonneg_right hhB hp
      nlinarith

lemma wordPartial_append (w v : List (Fin 2)) (f : Plane → ℝ) :
    wordPartial (w++v) f=wordPartial w (wordPartial v f) := by
  induction w with
  |nil=>rfl
  |cons i w ih=>simp only [List.cons_append,wordPartial,ih]

lemma good_wordPartial {f} (hf : Good f) (w) : Good (wordPartial w f) := by
  induction w with
  |nil=>exact hf
  |cons i w ih=>exact good_partial ih i

lemma SNorm_wordPartial_le (f : Plane → ℝ) (w) (n : ℕ) :
    SNorm n (wordPartial w f)≤SNorm (n+w.length) f := by
  induction w generalizing n with
  |nil=>simp only [wordPartial,List.length_nil,add_zero,le_refl]
  |cons i w ih=>
    exact (SNorm_partial_le n (wordPartial w f) i).trans (by simpa only [List.length_cons,Nat.add_right_comm,Nat.add_assoc,Nat.add_comm 1 w.length] using ih (n+1))

lemma wordPartial_newton {f} (hf : Good f) (w) :
    wordPartial w (localNewton f)=localNewton (wordPartial w f) := by
  induction w with
  |nil=>rfl
  |cons i w ih=>
    rw [wordPartial,ih,localNewton_partial (good_wordPartial hf w).1 (good_wordPartial hf w).2.1]
    rfl

lemma half_summable (B : ℝ) : Summable (fun n:ℕ=>B*(1/2:ℝ)^n) :=
  (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)).mul_left B

lemma Regular.summable {f} (hf : Regular f) (x : Plane) : Summable (fun n=>f n x) := by
  obtain ⟨B,_,hB⟩:=hf.bound []
  exact .of_norm_bounded (half_summable B) (fun n=>by simpa only [wordPartial,Real.norm_eq_abs] using hB n x)

lemma Regular.partial {f} (hf : Regular f) (i) : Regular (fun n=>coordPartial (f n) i) := by
  refine ⟨fun n=>smooth_partial (hf.smooth n) i,?_⟩
  intro w
  obtain ⟨B,hB,hb⟩:=hf.bound (w++[i])
  refine ⟨B,hB,?_⟩
  simpa only [wordPartial_append,wordPartial] using hb

lemma Regular.derivative_bound {f} (hf : Regular f) :
    ∃B:ℝ,0≤B ∧ ∀n x,‖fderiv ℝ (f n) x‖≤B*(1/2:ℝ)^n := by
  have h (i : Fin 2) := hf.bound [i]
  choose B hB hb using h
  refine ⟨2*(B 0+B 1),mul_nonneg (by norm_num) (add_nonneg (hB 0) (hB 1)),?_⟩
  intro n x
  have hg : 0≤(B 0+B 1)*(1/2:ℝ)^n:=mul_nonneg (add_nonneg (hB 0) (hB 1)) (by positivity)
  have hh:=fderiv_norm_le_two hg x (fun i=>show |coordPartial (f n) i x|≤(B 0+B 1)*(1/2:ℝ)^n from by
    have hh:=hb i n x
    change |coordPartial (f n) i x|≤_ at hh
    fin_cases i <;> simp only [Fin.isValue,Fin.zero_eta,Fin.mk_one] at hh ⊢ <;> nlinarith [mul_nonneg (hB 0) (pow_nonneg (by norm_num : (0:ℝ)≤1/2) n),
      mul_nonneg (hB 1) (pow_nonneg (by norm_num : (0:ℝ)≤1/2) n)])
  nlinarith

lemma Regular.hasFDeriv {f} (hf : Regular f) (x) :
    HasFDerivAt (fun y=>∑'n,f n y) (∑'n,fderiv ℝ (f n) x) x := by
  obtain ⟨B,_,hB⟩:=hf.derivative_bound
  exact hasFDerivAt_tsum (half_summable B) (fun n y=>(hf.smooth n).differentiable (by simp) |>.differentiableAt.hasFDerivAt)
    hB (hf.summable (0:Plane)) x

lemma Regular.partial_tsum {f} (hf : Regular f) (i) :
    coordPartial (fun x=>∑'n,f n x) i=(fun x=>∑'n,coordPartial (f n) i x) := by
  funext x
  unfold coordPartial
  rw [(hf.hasFDeriv x).fderiv]
  obtain ⟨B,_,hB⟩:=hf.derivative_bound
  have hs : Summable (fun n=>fderiv ℝ (f n) x):=.of_norm_bounded (half_summable B) (fun n=>hB n x)
  exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).map_tsum hs

lemma Regular.contDiff_tsum {f} (hf : Regular f) (m : ℕ) :
    ContDiff ℝ m (fun x=>∑'n,f n x) := by
  induction m generalizing f with
  |zero=>
    rw [Nat.cast_zero,contDiff_zero]
    obtain ⟨B,_,hB⟩:=hf.bound []
    exact continuous_tsum (fun n=>(hf.smooth n).continuous) (half_summable B)
      (fun n x=>by simpa only [wordPartial,Real.norm_eq_abs] using hB n x)
  |succ m ih=>
    rw [show ((m+1:ℕ):ℕ∞ω)=(m:ℕ∞ω)+1 by simp,contDiff_succ_iff_fderiv_apply]
    refine ⟨fun x=>(hf.hasFDeriv x).differentiableAt,by simp,?_⟩
    intro v
    have he : (fun x=>fderiv ℝ (fun y=>∑'n,f n y) x v)=
        (fun x=>(v 0)*(∑'n,coordPartial (f n) 0 x)+(v 1)*(∑'n,coordPartial (f n) 1 x)) := by
      funext x
      conv_lhs => rw [plane_basis_expansion v]
      rw [map_add,map_smul,map_smul]
      change (v 0)*coordPartial (fun y=>∑'n,f n y) 0 x+(v 1)*coordPartial (fun y=>∑'n,f n y) 1 x=_
      rw [hf.partial_tsum 0,hf.partial_tsum 1]
    rw [he]
    exact (contDiff_const.mul (ih (hf.partial 0))).add (contDiff_const.mul (ih (hf.partial 1)))

lemma Regular.smooth_tsum {f} (hf : Regular f) : Smooth (fun x=>∑'n,f n x) :=
  contDiff_infty.mpr (fun m=>hf.contDiff_tsum m)

lemma regular_newton_iterate {C : ℝ} (hC0 : 0≤C)
    (hCb : ∀g,Good g → ∀α,l2norm (jet g α)≤C*l2norm g)
    (hCs : ∀g,Good g → ∀x,|localNewton g x|≤C*l2norm g)
    {a f} (ha : ∀α,Good (a α)) (hf : Good f)
    (hbase : ∀g,Good g → l2norm (operator a g)≤(1/4)*l2norm g) :
    Regular (fun n=>localNewton (iterate a f n)) := by
  refine ⟨fun n=>smooth_localNewton (good_iterate ha hf n).1 (good_iterate ha hf n).2.1,?_⟩
  intro w
  obtain ⟨B,hB,hb⟩:=iterate_SNorm_decay hC0 hCb ha hf hbase w.length
  refine ⟨C*B,mul_nonneg hC0 hB,?_⟩
  intro n x
  rw [wordPartial_newton (good_iterate ha hf n)]
  have hh:=hCs _ (good_wordPartial (good_iterate ha hf n) w) x
  have hw : l2norm (wordPartial w (iterate a f n))≤SNorm w.length (iterate a f n) := by
    simpa only [SNorm,Nat.zero_add] using SNorm_wordPartial_le (iterate a f n) w 0
  exact hh.trans (by have := mul_le_mul_of_nonneg_left (hw.trans (hb n)) hC0; nlinarith only [this])

lemma Regular.regular_fieldJet {f} (hf : Regular f) (α : Kind) :
    Regular (fun n=>fieldJet (f n) α) := by
  rcases α with ⟨j,i⟩; cases j with
  |none=>exact hf.partial i
  |some j=>exact (hf.partial j).partial i

lemma Regular.fieldJet_tsum {f} (hf : Regular f) (α : Kind) :
    fieldJet (fun x=>∑'n,f n x) α=(fun x=>∑'n,fieldJet (f n) α x) := by
  rcases α with ⟨j,i⟩; cases j with
  |none=>exact hf.partial_tsum i
  |some j=>change coordPartial (coordPartial (fun x=>∑'n,f n x) j) i=_
           rw [hf.partial_tsum j,(hf.partial j).partial_tsum i]
           rfl

lemma Regular.differential_tsum {f} (hf : Regular f) (a) (x) :
    differential a (fun y=>∑'n,f n y) x=∑'n,differential a (f n) x := by
  simp only [differential,hf.fieldJet_tsum]
  rw [Summable.tsum_finsetSum (fun α (_ : α∈(Finset.univ : Finset Kind))=>
    ((hf.regular_fieldJet α).summable x).mul_left (a α x))]
  exact Finset.sum_congr rfl (fun α _=> (tsum_mul_left).symm)

lemma Regular.laplacian_tsum {f} (hf : Regular f) (x) :
    euclideanLaplacian (fun y=>∑'n,f n y) x=∑'n,euclideanLaplacian (f n) x := by
  simp only [euclideanLaplacian,hf.partial_tsum]
  simp_rw [fun i=> (hf.partial i).partial_tsum i]
  exact (Summable.tsum_finsetSum (fun i (_ : i∈(Finset.univ : Finset (Fin 2)))=>
    (((hf.partial i).partial i).summable x))).symm

lemma Regular.summable_laplacian {f} (hf : Regular f) (x) :
    Summable (fun n=>euclideanLaplacian (f n) x) := by
  exact summable_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 2)))=>(((hf.partial i).partial i).summable x))

lemma solution_equation {C : ℝ} (hC0 : 0≤C)
    (hCb : ∀g,Good g → ∀α,l2norm (jet g α)≤C*l2norm g)
    (hCs : ∀g,Good g → ∀x,|localNewton g x|≤C*l2norm g)
    {a f} (ha : ∀α,Good (a α)) (hf : Good f)
    (hbase : ∀g,Good g → l2norm (operator a g)≤(1/4)*l2norm g) :
    Smooth (solution a f) ∧ ∀x,‖x‖<1/64 →
      euclideanLaplacian (solution a f) x=f x+differential a (solution a f) x := by
  have hr:=regular_newton_iterate hC0 hCb hCs ha hf hbase
  refine ⟨hr.smooth_tsum,?_⟩
  intro x hx
  have he (n) : euclideanLaplacian (localNewton (iterate a f n)) x=iterate a f n x :=
    localNewton_equation (good_iterate ha hf n).1 (good_iterate ha hf n).2.1 (good_iterate ha hf n).2.2 hx
  have hs : Summable (fun n=>iterate a f n x):=by simpa only [he] using hr.summable_laplacian x
  change euclideanLaplacian (fun y=>∑'n,localNewton (iterate a f n) y) x=_
  rw [hr.laplacian_tsum]
  simp_rw [he]
  rw [hs.tsum_eq_zero_add]
  congr 1
  exact (hr.differential_tsum a x).symm

lemma operator_SNorm_one_contraction
    {a} (ha : ∀α,Good (a α))
    (h0 : ∀g,Good g → l2norm (operator a g)≤(1/12)*l2norm g)
    (h1 : ∀i g,Good g → l2norm (operator (fun α=>coordPartial (a α) i) g)≤(1/12)*l2norm g)
    {f} (hf : Good f) : SNorm 1 (operator a f)≤(1/4)*SNorm 1 f := by
  have hh (i : Fin 2) : l2norm (coordPartial (operator a f) i)≤
      (1/12)*l2norm (coordPartial f i)+(1/12)*l2norm f := by
    rw [partial_operator ha hf]
    exact (l2norm_add_le (smooth_operator ha (good_partial hf i))
      (smooth_operator (fun α=>good_partial (ha α) i) hf) (compact_operator ha)
      (compact_operator (fun α=>good_partial (ha α) i))).trans
      (add_le_add (h0 _ (good_partial hf i)) (h1 i f hf))
  have hb:=h0 f hf
  simp only [SNorm,Fin.sum_univ_two]
  nlinarith [hh 0,hh 1,l2norm_nonneg (coordPartial f 0),l2norm_nonneg (coordPartial f 1)]

lemma iterate_SNorm_one_decay {a f} (ha : ∀α,Good (a α)) (hf : Good f)
    (h1 : ∀g,Good g → SNorm 1 (operator a g)≤(1/4)*SNorm 1 g)
    (n : ℕ) : SNorm 1 (iterate a f n)≤SNorm 1 f*(1/2:ℝ)^n := by
  induction n with
    |zero=>simp [iterate]
    |succ n ih=>
      have hh:=h1 _ (good_iterate ha hf n)
      change SNorm 1 (operator a (iterate a f n))≤_
      rw [pow_succ]
      nlinarith [mul_nonneg (SNorm_nonneg 1 f) (pow_nonneg (by norm_num : (0:ℝ)≤1/2) n)]
lemma Regular.abs_partial_tsum_le {f} (hf : Regular f) (i : Fin 2) {B : ℝ}
    (hB : ∀n x,|coordPartial (f n) i x|≤B*(1/2:ℝ)^n) (x) :
    |coordPartial (fun y=>∑'n,f n y) i x|≤2*B := by
  rw [hf.partial_tsum]
  have hsum := (hf.partial i).summable x
  have hnorm := norm_tsum_le_tsum_norm hsum.norm
  have hbound := Summable.tsum_le_tsum (fun n=>hB n x) hsum.abs (half_summable B)
  rw [tsum_mul_left,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)] at hbound
  simp only [Real.norm_eq_abs] at hnorm
  norm_num at hbound
  linarith

lemma solution_gradient_bound {C : ℝ} (hC0 : 0≤C)
    (hCb : ∀g,Good g → ∀α,l2norm (jet g α)≤C*l2norm g)
    (hCs : ∀g,Good g → ∀x,|localNewton g x|≤C*l2norm g)
    {a f} (ha : ∀α,Good (a α)) (hf : Good f)
    (hbase : ∀g,Good g → l2norm (operator a g)≤(1/4)*l2norm g)
    (h1 : ∀g,Good g → SNorm 1 (operator a g)≤(1/4)*SNorm 1 g) :
    ∀i x,|coordPartial (solution a f) i x|≤2*C*SNorm 1 f := by
  have hr:=regular_newton_iterate hC0 hCb hCs ha hf hbase
  have hb := iterate_SNorm_one_decay ha hf h1
  intro i x
  have hbd (n y) : |coordPartial (localNewton (iterate a f n)) i y|≤(C*SNorm 1 f)*(1/2:ℝ)^n := by
    rw [localNewton_partial (good_iterate ha hf n).1 (good_iterate ha hf n).2.1]
    apply (hCs _ (good_partial (good_iterate ha hf n) i) y).trans
    have hw : l2norm (coordPartial (iterate a f n) i)≤SNorm 1 (iterate a f n):=SNorm_partial_le 0 _ i
    have := mul_le_mul_of_nonneg_left (hw.trans (hb n)) hC0
    nlinarith only [this]
  have hh := hr.abs_partial_tsum_le i hbd x
  change |coordPartial (solution a f) i x|≤_ at hh
  nlinarith only [hh]

end Elliptic
end SharpNodal.Profiles

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_MetricFamilies
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

namespace SharpNodal.Profiles
open Carleman
namespace Elliptic

lemma smooth_family_partial {F : ℝ → Plane → ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (i : Fin 2) :
    ContDiff ℝ ∞ (fun p : ℝ×Plane=>coordPartial (F p.1) i p.2) := by
  have hh : ContDiff ℝ ∞ (fun p : (ℝ×Plane)×Plane=>F p.1.1 p.2) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact (hh.fderiv contDiff_snd (by simp)).clm_apply contDiff_const

lemma smooth_family_wordPartial {F : ℝ → Plane → ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (w : List (Fin 2)) :
    ContDiff ℝ ∞ (fun p : ℝ×Plane=>wordPartial w (F p.1) p.2) := by
  induction w with
  |nil=>exact hF
  |cons i w ih=>exact smooth_family_partial (F:=fun t=>wordPartial w (F t)) ih i

lemma wordPartial_zero (w : List (Fin 2)) : wordPartial w (fun _=>0)=fun _=>0 := by
  induction w with
  |nil=>rfl
  |cons i w ih=>
    simp only [wordPartial,ih]
    funext x
    simp [coordPartial]

lemma uniform_family_small {F : ℝ → Plane → ℝ}
    (hF : Continuous (Function.uncurry F)) (hs : ∀t,Supported (F t))
    (h0 : F 0=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠt in 𝓝 (0:ℝ),∀x,|F t x|≤ε := by
  have hh : ∀ᶠt in 𝓝 (0:ℝ),∀x∈closedBall (0:Plane) (1/64),|F t x|<ε := by
    apply (isCompact_closedBall (0:Plane) (1/64)).eventually_forall_of_forall_eventually
    intro x _
    exact (hF.abs.continuousAt (x:=(0,x))).eventually (eventually_lt_nhds (by simpa only [Function.uncurry_apply_pair,h0,Pi.zero_apply,abs_zero] using hε))
  filter_upwards [hh] with t ht x
  by_cases hx : (1/64:ℝ)≤‖x‖
  · rw [hs t x hx,abs_zero]; exact hε.le
  · exact (ht x (mem_closedBall_zero_iff.mpr (le_of_not_ge hx))).le

lemma uniform_wordPartial_small {F : ℝ → Plane → ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (hg : ∀t,Good (F t))
    (h0 : F 0=0) (w : List (Fin 2)) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠt in 𝓝 (0:ℝ),∀x,|wordPartial w (F t) x|≤ε := by
  apply uniform_family_small (F:=fun t=>wordPartial w (F t)) (smooth_family_wordPartial hF w).continuous
    (fun t=>(good_wordPartial (hg t) w).2.2) _ hε
  rw [h0]; exact wordPartial_zero w

lemma good_flatCut {A : Plane → ℝ} (hA : Smooth A) (t : ℝ) : Good (flatCut A t) := by
  refine ⟨metricCutoff.contDiff.mul ((hA.comp ((contDiff_const (c:=t)).smul contDiff_id)).sub (contDiff_const (c:=A 0))),
    metricCutoff.hasCompactSupport.mul_right,?_⟩
  intro x hx
  simp only [flatCut,metricCutoff.zero_of_le_dist (by simpa only [metricCutoff,dist_zero_right] using hx),zero_mul]

lemma smooth_flatCut_family {A : Plane → ℝ} (hA : Smooth A) :
    ContDiff ℝ ∞ (Function.uncurry (flatCut A)) := by
  exact (metricCutoff.contDiff.comp contDiff_snd).mul
    ((hA.comp (contDiff_fst.smul contDiff_snd)).sub contDiff_const)

lemma flatCut_zero (A : Plane → ℝ) : flatCut A 0=0 := by
  funext x; simp [flatCut]

lemma flatCut_inner (A : Plane → ℝ) (t : ℝ) {x : Plane} (hx : ‖x‖≤1/128) :
    flatCut A t x=A (t • x)-A 0 := by
  rw [flatCut,metricCutoff.one_of_mem_closedBall (by simpa only [metricCutoff,mem_closedBall_zero_iff] using hx),one_mul]

lemma exists_small_flatCut {ι : Type*} [Fintype ι] (A : ι → Plane → ℝ)
    (hA : ∀i,Smooth (A i)) {ε : ℝ} (hε : 0<ε) :
    ∃t:ℝ,0<t ∧ t<1 ∧ ∀i,
      (∀x,|flatCut (A i) t x|≤ε) ∧
      (∀j x,|coordPartial (flatCut (A i) t) j x|≤ε) ∧
      (∀j k x,|coordPartial (coordPartial (flatCut (A i) t) j) k x|≤ε) := by
  have h0 (i) := uniform_wordPartial_small (smooth_flatCut_family (hA i))
    (good_flatCut (hA i)) (flatCut_zero (A i)) [] hε
  have h1 (i) (j : Fin 2) := uniform_wordPartial_small (smooth_flatCut_family (hA i))
    (good_flatCut (hA i)) (flatCut_zero (A i)) [j] hε
  have h2 (i) (j k : Fin 2) := uniform_wordPartial_small (smooth_flatCut_family (hA i))
    (good_flatCut (hA i)) (flatCut_zero (A i)) [k,j] hε
  have hh0 := eventually_all.mpr h0
  have hh1 := eventually_all.mpr (fun i=>eventually_all.mpr (h1 i))
  have hh2 := eventually_all.mpr (fun i=>eventually_all.mpr (fun j=>eventually_all.mpr (h2 i j)))
  have hh : ∀ᶠt in 𝓝[>] (0:ℝ),0<t ∧ t<1 ∧ ∀i,
      (∀x,|flatCut (A i) t x|≤ε) ∧ (∀j x,|coordPartial (flatCut (A i) t) j x|≤ε) ∧
      (∀j k x,|coordPartial (coordPartial (flatCut (A i) t) j) k x|≤ε) := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds hh0,nhdsWithin_le_nhds hh1,
      nhdsWithin_le_nhds hh2,nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with t ht h0 h1 h2 hlt
    exact ⟨ht,hlt,fun i=>⟨h0 i,h1 i,h2 i⟩⟩
  exact hh.exists

lemma good_neg {f : Plane → ℝ} (hf : Good f) : Good (fun x=> -f x) :=
  ⟨hf.1.neg,hf.2.1.neg,fun x hx=>by change -f x=0; rw [hf.2.2 x hx,neg_zero]⟩

lemma good_sum {ι : Type*} [Fintype ι] {f : ι → Plane → ℝ} (hf : ∀i,Good (f i)) :
    Good (fun x=>∑i,f i x) := by
  refine ⟨ContDiff.sum (fun i _=>(hf i).1),compact_fun_sum (fun i _=>(hf i).2.1),?_⟩
  intro x hx; exact Finset.sum_eq_zero (fun i _=>(hf i).2.2 x hx)

lemma good_coeffs {b} (hb : ∀i j,Good (b i j)) : ∀α,Good (coeffs b α) := by
  rintro ⟨j,i⟩; cases j with
  |none=>exact good_neg (good_sum (fun j=>good_partial (hb j i) j))
  |some j=>exact good_neg (hb i j)

lemma differential_coeffs {b u} (hb : ∀i j,Good (b i j)) (hu : Smooth u) (x) :
    differential (coeffs b) u x= -perturbation b u x := by
  have hi (i : Fin 2) : coordPartial (fun y=>∑j:Fin 2,b i j y*coordPartial u j y) i x=
      ∑j:Fin 2,(coordPartial (b i j) i x*coordPartial u j x+b i j x*coordPartial (coordPartial u j) i x) := by
    rw [partial_sum _ (fun j _=>(hb i j).1.mul (smooth_partial hu j))]
    exact Finset.sum_congr rfl (fun j _=>partial_mul (hb i j).1 (smooth_partial hu j) i x)
  unfold perturbation
  simp_rw [hi]
  simp only [differential,Fintype.sum_prod_type,Fintype.sum_option,Fin.sum_univ_two,coeffs,fieldJet]
  ring

lemma coeffs_bounds {b} (hb : ∀i j,Good (b i j)) {ε : ℝ} (hε : 0≤ε)
    (hb0 : ∀i j x,|b i j x|≤ε)
    (hb1 : ∀i j k x,|coordPartial (b i j) k x|≤ε)
    (hb2 : ∀i j k l x,|coordPartial (coordPartial (b i j) k) l x|≤ε) :
    (∀α x,|coeffs b α x|≤2*ε) ∧
    (∀k α x,|coordPartial (coeffs b α) k x|≤2*ε) := by
  constructor
  · rintro ⟨j,i⟩ x; cases j with
    |none=>
      simp only [coeffs,abs_neg,Fin.sum_univ_two]
      exact (abs_add_le _ _).trans (by linarith [hb1 0 i 0 x,hb1 1 i 1 x])
    |some j=>simp only [coeffs,abs_neg]; exact (hb0 i j x).trans (by linarith)
  · rintro k ⟨j,i⟩ x; cases j with
    |none=>
      rw [coeffs,partial_neg (good_sum (fun j=>good_partial (hb j i) j)).1,
        partial_sum _ (fun j _=>smooth_partial (hb j i).1 j)]
      simp only [abs_neg,Fin.sum_univ_two]
      exact (abs_add_le _ _).trans (by linarith [hb2 0 i 0 k x,hb2 1 i 1 k x])
    |some j=>
      rw [coeffs,partial_neg (hb i j).1,abs_neg]
      exact (hb1 i j k x).trans (by linarith)

lemma good_l2_bound {f} (hf : Good f) {B : ℝ} (hB : 0≤B) (hb : ∀x,|f x|≤B) :
    l2norm f≤2*B :=
  l2norm_support_bound hf.1 hf.2.1 hB hb (fun x hx=>hf.2.2 x (by linarith))

lemma coeffs_source_bound {b} (hb : ∀i j,Good (b i j)) {ε : ℝ} (hε : 0≤ε)
    (h0 : ∀α x,|coeffs b α x|≤2*ε)
    (h1 : ∀k α x,|coordPartial (coeffs b α) k x|≤2*ε) :
    SNorm 1 (coeffs b (none,0))≤12*ε := by
  have hg := good_coeffs hb (none,0)
  have hh0:=good_l2_bound hg (by positivity) (h0 (none,0))
  have hh1 (i : Fin 2):=good_l2_bound (good_partial hg i) (by positivity) (h1 i (none,0))
  simp only [SNorm,Fin.sum_univ_two]
  linarith [hh1 0,hh1 1]

lemma operator_small {C ε : ℝ} (_hC : 1≤C) (hε : 0≤ε)
    (hsmall : 12*ε*C≤1/12)
    (hCb : ∀g,Good g → ∀α,l2norm (jet g α)≤C*l2norm g)
    {a} (ha : ∀α,Good (a α)) (hb : ∀α x,|a α x|≤2*ε) :
    ∀g,Good g → l2norm (operator a g)≤(1/12)*l2norm g := by
  intro g hg
  have hh:=operator_L2_bound hCb ha hg (fun _=>show 0≤2*ε by positivity) hb
  have he : (∑_α:Kind,2*ε)=12*ε := by simp [Kind,Fintype.card_prod]; ring
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hsmall (l2norm_nonneg g))

lemma smooth_coordinate (j : Fin 2) : Smooth (fun y:Plane=>y j) :=
  (EuclideanSpace.proj j : Plane →L[ℝ] ℝ).contDiff

lemma coordPartial_coordinate (j i : Fin 2) (x : Plane) :
    coordPartial (fun y:Plane=>y j) i x=if i=j then 1 else 0 := by
  unfold coordPartial
  change fderiv ℝ (EuclideanSpace.proj j : Plane →L[ℝ] ℝ) x (EuclideanSpace.single i 1)=_
  rw [(EuclideanSpace.proj j : Plane →L[ℝ] ℝ).fderiv]
  simp [eq_comm]

lemma laplacian_coordinate (j : Fin 2) (x : Plane) :
    euclideanLaplacian (fun y:Plane=>y j) x=0 := by
  simp only [euclideanLaplacian]
  apply Finset.sum_eq_zero
  intro i _
  rw [show coordPartial (fun y:Plane=>y j) i=(fun _=>if i=j then 1 else 0) by funext z; exact coordPartial_coordinate j i z]
  simp [coordPartial]

lemma perturbation_coordinate_add {b h} (hb : ∀i j,Good (b i j)) (hh : Smooth h) (x) :
    perturbation b (fun y=>y 0+h y) x=perturbation b h x-coeffs b (none,0) x := by
  have hp (j : Fin 2) : coordPartial (fun y:Plane=>y 0+h y) j=
      fun y=>(if j=0 then 1 else 0)+coordPartial h j y := by
    funext y
    rw [partial_add (smooth_coordinate 0) hh j y,coordPartial_coordinate]
  have he (i : Fin 2) : (fun y=>∑j:Fin 2,b i j y*coordPartial (fun y:Plane=>y 0+h y) j y)=
      (fun y=>b i 0 y+(∑j:Fin 2,b i j y*coordPartial h j y)) := by
    funext y; simp only [hp,Fin.sum_univ_two]; norm_num; ring
  simp only [perturbation,he,partial_add (hb _ _).1 (ContDiff.sum (fun j _=>(hb _ j).1.mul (smooth_partial hh j))),coeffs,sub_neg_eq_add]
  rw [Finset.sum_add_distrib,add_comm]

theorem small_metric_harmonic_coordinate : ∃ε:ℝ,0<ε ∧
    ∀b : Fin 2 → Fin 2 → Plane → ℝ,(∀i j,Good (b i j)) →
    (∀i j x,|b i j x|≤ε) →
    (∀i j k x,|coordPartial (b i j) k x|≤ε) →
    (∀i j k l x,|coordPartial (coordPartial (b i j) k) l x|≤ε) →
    ∃u:Plane → ℝ,Smooth u ∧ (∀x,1/2 ≤ coordPartial u 0 x) ∧
      ∀x,‖x‖<1/64 → euclideanLaplacian u x+perturbation b u x=0 := by
  obtain ⟨C,hC,hCb⟩:=localNewton_L2_bounds
  have hC0 : 0<C:=lt_of_lt_of_le zero_lt_one hC
  have hCj (g) (hg : Good g) (α : Kind) : l2norm (jet g α)≤C*l2norm g := by
    rcases α with ⟨j,i⟩; cases j with
    |none=>exact (hCb g hg.1 hg.2.1 hg.2.2).2.1 i
    |some j=>exact (hCb g hg.1 hg.2.1 hg.2.2).2.2.1 j i
  have hCs (g) (hg : Good g) := (hCb g hg.1 hg.2.1 hg.2.2).2.2.2
  let ε : ℝ := 1/(1000*C)
  have hε : 0<ε:=by dsimp [ε]; positivity
  have hεC : ε*C=1/1000:=by dsimp [ε]; field_simp
  refine ⟨ε,hε,?_⟩
  intro b hb hb0 hb1 hb2
  obtain ⟨h0,h1⟩:=coeffs_bounds hb hε.le hb0 hb1 hb2
  have hsmall : 12*ε*C≤1/12:=by nlinarith only [hεC]
  have hop := operator_small hC hε.le hsmall hCj (good_coeffs hb) h0
  have hop1 (i) := operator_small hC hε.le hsmall hCj
    (fun α=>good_partial (good_coeffs hb α) i) (h1 i)
  have hbase (g) (hg : Good g) : l2norm (operator (coeffs b) g)≤(1/4)*l2norm g :=
    (hop g hg).trans (by nlinarith [l2norm_nonneg g])
  let h:=solution (coeffs b) (coeffs b (none,0))
  have hhg:=good_coeffs hb (none,0)
  obtain ⟨hh,he⟩:=solution_equation hC0.le hCj hCs (good_coeffs hb) hhg hbase
  have hg := solution_gradient_bound hC0.le hCj hCs (good_coeffs hb) hhg hbase
    (fun g hgood=>operator_SNorm_one_contraction (good_coeffs hb) hop hop1 hgood)
  have hsrc:=coeffs_source_bound hb hε.le h0 h1
  have hgrad (x) : |coordPartial h 0 x|≤1/2 := by
    have hhh:=(hg 0 x).trans (mul_le_mul_of_nonneg_left hsrc (by positivity : 0≤2*C))
    change |coordPartial h 0 x|≤_ at hhh
    have hle : 2*C*(12*ε)≤1/2:=by nlinarith only [hεC]
    exact hhh.trans hle
  refine ⟨fun y=>y 0+h y,(smooth_coordinate 0).add hh,?_,?_⟩
  · intro x
    rw [partial_add (smooth_coordinate 0) hh,coordPartial_coordinate]
    simp only [ite_true]
    have := (abs_le.mp (hgrad x)).1
    linarith
  · intro x hx
    rw [laplacian_add (smooth_coordinate 0) hh,laplacian_coordinate,zero_add,
      perturbation_coordinate_add hb hh]
    have hhe:=he x hx
    rw [differential_coeffs hb hh] at hhe
    change euclideanLaplacian h x=_ at hhe
    linarith

lemma smooth_oneForm {p q : Plane → ℝ} (hp : Smooth p) (hq : Smooth q) :
    ContDiff ℝ ∞ (oneForm p q) :=
  (hp.smul contDiff_const).add (hq.smul contDiff_const)

lemma fderiv_apply_coords (f : Plane → ℝ) (x v : Plane) :
    fderiv ℝ f x v=v 0*coordPartial f 0 x+v 1*coordPartial f 1 x := by
  conv_lhs=>rw [plane_basis_expansion v]
  simp only [map_add,map_smul,smul_eq_mul,coordPartial]

lemma fderiv_oneForm {p q : Plane → ℝ} (hp : Smooth p) (hq : Smooth q) (x v w : Plane) :
    fderiv ℝ (oneForm p q) x v w=
      (v 0*coordPartial p 0 x+v 1*coordPartial p 1 x)*w 0+
      (v 0*coordPartial q 0 x+v 1*coordPartial q 1 x)*w 1 := by
  have hd:=((hp.differentiable (by simp)).differentiableAt.hasFDerivAt.smul_const
    (EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ)).add
    ((hq.differentiable (by simp)).differentiableAt.hasFDerivAt.smul_const
    (EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ)) (x:=x)
  rw [show fderiv ℝ (oneForm p q) x=_ from hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,
    smul_apply,smul_eq_mul,EuclideanSpace.coe_proj,fderiv_apply_coords]

lemma exists_smooth_primitive {p q : Plane → ℝ} (hp : Smooth p) (hq : Smooth q)
    {s : Set Plane} (hsc : Convex ℝ s) (hso : IsOpen s)
    (hc : ∀x∈s,coordPartial p 1 x=coordPartial q 0 x) :
    ∃v : Plane → ℝ,ContDiffOn ℝ ∞ v s ∧
      ∀x∈s,coordPartial v 0 x=p x ∧ coordPartial v 1 x=q x := by
  obtain ⟨v,hv⟩:=hsc.exists_forall_hasFDerivAt_of_fderiv_symmetric hso
    ((smooth_oneForm hp hq).differentiable (by simp)).differentiableOn (by
      intro x hx a b
      rw [fderiv_oneForm hp hq,fderiv_oneForm hp hq,hc x hx]
      ring)
  refine ⟨v,(contDiffOn_infty_iff_fderiv_of_isOpen hso).mpr ⟨fun x hx=>(hv x hx).differentiableAt.differentiableWithinAt,?_⟩,?_⟩
  · exact (smooth_oneForm hp hq).contDiffOn.congr (fun x hx=>(hv x hx).fderiv)
  · intro x hx
    simp [coordPartial,(hv x hx).fderiv,oneForm]

lemma smooth_metricFlux {b u} (hb : ∀i j,Good (b i j)) (hu : Smooth u) (i) :
    Smooth (metricFlux b u i) :=
  (smooth_partial hu i).add (ContDiff.sum (fun j _=>(hb i j).1.mul (smooth_partial hu j)))

lemma divergence_metricFlux {b u} (hb : ∀i j,Good (b i j)) (hu : Smooth u) (x) :
    coordPartial (metricFlux b u 0) 0 x+coordPartial (metricFlux b u 1) 1 x=
      euclideanLaplacian u x+perturbation b u x := by
  have hi (i : Fin 2) := partial_add (smooth_partial hu i)
    (ContDiff.sum (s:=Finset.univ) (fun j _=>(hb i j).1.mul (smooth_partial hu j))) i x
  unfold metricFlux
  rw [hi 0,hi 1]
  simp only [euclideanLaplacian,perturbation,Fin.sum_univ_two]
  ring

lemma metric_conjugate {b u} (hb : ∀i j,Good (b i j)) (hu : Smooth u)
    (hPDE : ∀x∈ball (0:Plane) (1/64),euclideanLaplacian u x+perturbation b u x=0) :
    ∃v : Plane → ℝ,ContDiffOn ℝ ∞ v (ball 0 (1/64)) ∧
      ∀x∈ball (0:Plane) (1/64),
        coordPartial v 0 x= -metricFlux b u 1 x ∧ coordPartial v 1 x=metricFlux b u 0 x := by
  apply exists_smooth_primitive (smooth_metricFlux hb hu 1).neg (smooth_metricFlux hb hu 0)
    (convex_ball _ _) isOpen_ball
  intro x hx
  rw [partial_neg (smooth_metricFlux hb hu 1)]
  have he:=divergence_metricFlux hb hu x
  rw [hPDE x hx] at he
  linarith

lemma metricFlux_positive {b u} {ε : ℝ} (hε : ε<1/4)
    (hb : ∀i j x,|b i j x|≤ε) {x : Plane} (hu : 1/2 ≤ coordPartial u 0 x) :
    0 < coordPartial u 0 x*metricFlux b u 0 x+coordPartial u 1 x*metricFlux b u 1 x := by
  let a:=coordPartial u 0 x
  let c:=coordPartial u 1 x
  have hε0 : 0≤ε:= (abs_nonneg _).trans (hb 0 0 x)
  have he (i j : Fin 2) (r s : ℝ) : -(ε * |r| * |s|) ≤ r*b i j x*s := by
    have hh:=mul_le_mul_of_nonneg_left (hb i j x) (abs_nonneg r)
    have hhh:=mul_le_mul_of_nonneg_right hh (abs_nonneg s)
    rw [← abs_mul,← abs_mul] at hhh
    simpa only [mul_comm ε |r|] using (abs_le.mp hhh).1
  have h00:=he 0 0 a a
  have h01:=he 0 1 a c
  have h10:=he 1 0 c a
  have h11:=he 1 1 c c
  have ha : 0<a:=by dsimp [a]; linarith
  have hab : |a|=a:=abs_of_pos ha
  have hc2 : |c|^2=c^2:=sq_abs c
  have hh : 2*a*|c|≤a^2+c^2:=by nlinarith only [sq_nonneg (a-|c|),hc2]
  have hee : ε*(2*a*|c|)≤ε*(a^2+c^2):=mul_le_mul_of_nonneg_left hh hε0
  simp only [metricFlux,Fin.sum_univ_two]
  change 0<a*(a+(b 0 0 x*a+b 0 1 x*c))+c*(c+(b 1 0 x*a+b 1 1 x*c))
  rw [hab] at h00 h01 h10
  nlinarith only [h00,h01,h10,h11,hee,congrArg (fun r:ℝ=>ε*r) hc2,mul_pos (show 0<1-2*ε by linarith) (show 0<a^2+c^2 by positivity)]

lemma smoothOn_coordMap {u v : Plane → ℝ} {s : Set Plane}
    (hu : ContDiffOn ℝ ∞ u s) (hv : ContDiffOn ℝ ∞ v s) : ContDiffOn ℝ ∞ (coordMap u v) s :=
  (hu.smul contDiffOn_const).add (hv.smul contDiffOn_const)

lemma hasFDerivAt_coordMap {u v : Plane → ℝ} {x : Plane}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    HasFDerivAt (coordMap u v)
      ((fderiv ℝ u x).smulRight (EuclideanSpace.single 0 1)+(fderiv ℝ v x).smulRight (EuclideanSpace.single 1 1)) x :=
  (hu.hasFDerivAt.smul_const _).add (hv.hasFDerivAt.smul_const _)

lemma plane_clm_injective (L : Plane →L[ℝ] Plane)
    (hd : L (EuclideanSpace.single 0 1) 0*L (EuclideanSpace.single 1 1) 1-
      L (EuclideanSpace.single 1 1) 0*L (EuclideanSpace.single 0 1) 1≠0) : Function.Injective L := by
  intro x y he
  have hxy (z : Plane) (i : Fin 2) : L z i=z 0*L (EuclideanSpace.single 0 1) i+z 1*L (EuclideanSpace.single 1 1) i := by
    conv_lhs=>rw [plane_basis_expansion z]
    simp
  have h (i : Fin 2) : x 0*L (EuclideanSpace.single 0 1) i+x 1*L (EuclideanSpace.single 1 1) i=
      y 0*L (EuclideanSpace.single 0 1) i+y 1*L (EuclideanSpace.single 1 1) i := by
    rw [← hxy x i,← hxy y i,he]
  have h0 : (L (EuclideanSpace.single 0 1) 0*L (EuclideanSpace.single 1 1) 1-
      L (EuclideanSpace.single 1 1) 0*L (EuclideanSpace.single 0 1) 1)*(x 0-y 0)=0 := by
    linear_combination L (EuclideanSpace.single 1 1) 1*h 0-L (EuclideanSpace.single 1 1) 0*h 1
  have h1 : (L (EuclideanSpace.single 0 1) 0*L (EuclideanSpace.single 1 1) 1-
      L (EuclideanSpace.single 1 1) 0*L (EuclideanSpace.single 0 1) 1)*(x 1-y 1)=0 := by
    linear_combination L (EuclideanSpace.single 0 1) 0*h 1-L (EuclideanSpace.single 0 1) 1*h 0
  have hx0:=sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hd)
  have hx1:=sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hd)
  ext i; fin_cases i <;> assumption

lemma local_smooth_diffeomorph {F : Plane → Plane} {s : Set Plane} {x : Plane}
    (hso : IsOpen s) (hx : x∈s) (hF : ContDiffOn ℝ ∞ F s)
    (hi : ∀y∈s,Function.Injective (fderiv ℝ F y)) :
    ∃e : OpenPartialHomeomorph Plane Plane, (e : Plane → Plane)=F ∧ x∈e.source ∧ e.source⊆s ∧
      ContDiffOn ℝ ∞ (e : Plane → Plane) e.source ∧ ContDiffOn ℝ ∞ (e.symm : Plane → Plane) e.target := by
  let L (y : Plane) (hy : y∈s) : Plane ≃L[ℝ] Plane:=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ F y).toLinearMap (hi y hy)).toContinuousLinearEquiv
  have hD (y : Plane) (hy : y∈s) : HasFDerivAt F (L y hy : Plane →L[ℝ] Plane) y :=
    (hF.contDiffAt (hso.mem_nhds hy)).differentiableAt (by simp) |>.hasFDerivAt
  let e₀ := (hF.contDiffAt (hso.mem_nhds hx)).toOpenPartialHomeomorph F (hD x hx) (by simp)
  let e:=e₀.restr s
  have hs : e.source=e₀.source∩s:=e₀.restr_source' s hso
  have he : (e : Plane → Plane)=F:=rfl
  have hsub : e.source⊆s:=by rw [hs]; exact inter_subset_right
  refine ⟨e,he,?_,hsub,?_,?_⟩
  · rw [hs]; exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _,hx⟩
  · rw [he]; exact hF.mono hsub
  · intro y hy
    have hy' := hsub (e.map_target hy)
    apply (e.contDiffAt_symm hy (show HasFDerivAt (e : Plane → Plane) (L (e.symm y) hy') (e.symm y) from by rw [he]; exact hD _ hy')
      (by rw [he]; exact hF.contDiffAt (hso.mem_nhds hy'))).contDiffWithinAt

lemma coordMap_injective_derivative {u v : Plane → ℝ} {x : Plane}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hd : coordPartial u 0 x*coordPartial v 1 x-coordPartial u 1 x*coordPartial v 0 x≠0) :
    Function.Injective (fderiv ℝ (coordMap u v) x) := by
  apply plane_clm_injective
  rw [(hasFDerivAt_coordMap hu hv).fderiv]
  simpa [coordPartial] using hd

theorem normalized_metric_coordinates_oai (A : Fin 2 → Fin 2 → Plane → ℝ)
    (hA : ∀i j,Smooth (A i j)) (hA0 : ∀i j,A i j 0=if i=j then 1 else 0) :
    ∃(t : ℝ) (u v : Plane → ℝ) (e : OpenPartialHomeomorph Plane Plane),
      0<t ∧ t<1 ∧ Smooth u ∧ ContDiffOn ℝ ∞ v (ball (0:Plane) (1/64)) ∧
      (e : Plane → Plane)=coordMap u v ∧ (0:Plane)∈e.source ∧
      e.source⊆ball (0:Plane) (1/128) ∧
      ContDiffOn ℝ ∞ (e : Plane → Plane) e.source ∧
      ContDiffOn ℝ ∞ (e.symm : Plane → Plane) e.target ∧
      (∀x∈ball (0:Plane) (1/128),
        coordPartial v 0 x= -(∑j:Fin 2,A 1 j (t • x)*coordPartial u j x) ∧
        coordPartial v 1 x= ∑j:Fin 2,A 0 j (t • x)*coordPartial u j x) ∧
      (∀x∈ball (0:Plane) (1/128),
        ∑i:Fin 2,coordPartial (fun y=>∑j:Fin 2,A i j (t • y)*coordPartial u j y) i x=0) ∧
      (∀x∈ball (0:Plane) (1/128),
        0 < coordPartial u 0 x*coordPartial v 1 x-coordPartial u 1 x*coordPartial v 0 x) := by
  obtain ⟨ε,hε,hcoord⟩:=small_metric_harmonic_coordinate
  let δ:=min ε (1/8)
  have hδ : 0<δ:=lt_min hε (by norm_num)
  obtain ⟨t,ht,ht1,hb⟩:=exists_small_flatCut (fun ij:Fin 2×Fin 2=>A ij.1 ij.2) (fun ij=>hA ij.1 ij.2) hδ
  let b:=fun i j=>flatCut (A i j) t
  have hbg : ∀i j,Good (b i j):=fun i j=>good_flatCut (hA i j) t
  have hb0 (i j x) : |b i j x|≤δ:=(hb (i,j)).1 x
  have hb1 (i j k x) : |coordPartial (b i j) k x|≤ε:=((hb (i,j)).2.1 k x).trans (min_le_left _ _)
  have hb2 (i j k l x) : |coordPartial (coordPartial (b i j) k) l x|≤ε:=((hb (i,j)).2.2 k l x).trans (min_le_left _ _)
  obtain ⟨u,hu,hug,hPDE⟩:=hcoord b hbg (fun i j x=>(hb0 i j x).trans (min_le_left _ _)) hb1 hb2
  obtain ⟨v,hv,hvc⟩:=metric_conjugate hbg hu (fun x hx=>hPDE x (mem_ball_zero_iff.mp hx))
  have hsmall : δ<1/4:=lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hdet (x) (hx : x∈ball (0:Plane) (1/64)) :
      0 < coordPartial u 0 x*coordPartial v 1 x-coordPartial u 1 x*coordPartial v 0 x := by
    rw [(hvc x hx).1,(hvc x hx).2]
    simpa only [mul_neg,sub_neg_eq_add] using metricFlux_positive hsmall hb0 (hug x)
  have hF:=smoothOn_coordMap hu.contDiffOn hv
  have hsub : ball (0:Plane) (1/128)⊆ball (0:Plane) (1/64):=ball_subset_ball (by norm_num)
  obtain ⟨e,he,he0,hes,hef,hei⟩:=local_smooth_diffeomorph isOpen_ball (mem_ball_self (by norm_num : (0:ℝ)<1/128))
    (hF.mono hsub) (fun x hx=>coordMap_injective_derivative (hu.differentiable (by simp) x)
      ((hv.contDiffAt (isOpen_ball.mem_nhds (hsub hx))).differentiableAt (by simp)) (hdet x (hsub hx)).ne')
  have hflux (i : Fin 2) (x : Plane) (hx : x∈ball (0:Plane) (1/128)) :
      metricFlux b u i x=∑j:Fin 2,A i j (t • x)*coordPartial u j x := by
    have heq (j) : b i j x=A i j (t • x)-(if i=j then 1 else 0) := by
      change flatCut (A i j) t x = _
      rw [flatCut_inner _ _ (mem_ball_zero_iff.mp hx).le,hA0]
    simp only [metricFlux,heq,Fin.sum_univ_two]
    fin_cases i <;> norm_num <;> ring
  refine ⟨t,u,v,e,ht,ht1,hu,hv,he,he0,hes,hef,hei,?_,?_,fun x hx=>hdet x (hsub hx)⟩
  · intro x hx
    rw [← hflux 1 x hx,← hflux 0 x hx]
    exact hvc x (hsub hx)
  · intro x hx
    have heq (i : Fin 2) : metricFlux b u i=ᶠ[𝓝 x]fun y=>∑j:Fin 2,A i j (t • y)*coordPartial u j y := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy; exact hflux i y hy
    have hd (i : Fin 2) := congrArg (fun L:Plane →L[ℝ] ℝ=>L (EuclideanSpace.single i 1)) (heq i).fderiv_eq
    have hzero := (divergence_metricFlux hbg hu x).trans (hPDE x (mem_ball_zero_iff.mp (hsub hx)))
    have hz : (∑i:Fin 2,coordPartial (metricFlux b u i) i x)=0 := by
      simpa only [Fin.sum_univ_two] using hzero
    convert hz using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    exact (hd i).symm

end Elliptic
end SharpNodal.Profiles

end

end OAI
end

theorem solution : type_of% @OAI.SharpNodal.Profiles.Elliptic.normalized_metric_coordinates_oai := @OAI.SharpNodal.Profiles.Elliptic.normalized_metric_coordinates_oai
