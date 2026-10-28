-- Prove2me | solution 1 for OAI.SharpNodal.Geometry.normalized_frequency_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:17:43.673809+00:00
-- url     : https://prove2.me/submissions/d76d4c5e-d2fd-45a1-b843-8d44e8ac0759

import Mathlib
import Definitions.Def_NodalLength
import Definitions.Def_OAIQ4Nl000
import Theorems.Thm_OAI_SharpNodal_Geometry_exists_isothermal_chart
import Theorems.Thm_OAI_SharpNodal_Geometry_laplaceBeltrami_in_chart

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

lemma partial_const (c : ℝ) (i : Fin 2) (x : Plane) :
    coordPartial (fun _ => c) i x = 0 := by simp [coordPartial]


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
namespace SharpNodal.Profiles
open Carleman

lemma smooth_radiusSquare (x₀ : Plane) : Smooth (radiusSquare x₀) :=
  (contDiff_id.sub contDiff_const).norm_sq ℝ

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma smooth_centeredQuadratic (A : BilinearForm) (x₀ : Plane) :
    Smooth (centeredQuadratic A x₀) := by
  exact contDiff_const.mul ((contDiff_const.clm_apply (contDiff_id.sub contDiff_const)).clm_apply
    (contDiff_id.sub contDiff_const))

lemma hasFDerivAt_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ x : Plane) : HasFDerivAt (centeredQuadratic A x₀) (A (x-x₀)) x := by
  have ht := (hasFDerivAt_id (𝕜:=ℝ) x).sub_const x₀
  have hAt : HasFDerivAt (fun y => A (y-x₀)) A x := by
    convert! A.hasFDerivAt.comp x ht using 1
    all_goals try with_reducible_and_instances rfl
  convert! (hAt.clm_apply ht).const_mul (1/2:ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul, id_eq]
  rw [hA y (x-x₀)]
  ring

lemma fderiv_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A) (x₀ : Plane) :
    fderiv ℝ (centeredQuadratic A x₀) = fun x => A (x-x₀) :=
  funext fun x => (hasFDerivAt_centeredQuadratic hA x₀ x).fderiv

lemma partial_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ : Plane) (i : Fin 2) (x : Plane) :
    coordPartial (centeredQuadratic A x₀) i x=A (x-x₀) (EuclideanSpace.single i 1) := by
  rw [coordPartial, fderiv_centeredQuadratic hA]

lemma partial2_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ : Plane) (i j : Fin 2) (x : Plane) :
    coordPartial (coordPartial (centeredQuadratic A x₀) i) j x=
      A (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
  rw [show coordPartial (centeredQuadratic A x₀) i =
    fun y => A (y-x₀) (EuclideanSpace.single i 1) from funext (partial_centeredQuadratic hA x₀ i)]
  have ht := (hasFDerivAt_id (𝕜:=ℝ) x).sub_const x₀
  have hh : HasFDerivAt (fun y => A (y-x₀) (EuclideanSpace.single i 1))
      (A.flip (EuclideanSpace.single i 1)) x := by
    convert! (A.flip (EuclideanSpace.single i 1)).hasFDerivAt.comp x ht using 1
    all_goals try with_reducible_and_instances rfl
  simp only [coordPartial, hh.fderiv, ContinuousLinearMap.flip_apply]

lemma laplacian_centeredQuadratic {A : BilinearForm} (hA : SymmetricForm A)
    (x₀ x : Plane) : euclideanLaplacian (centeredQuadratic A x₀) x=
      ∑ i : Fin 2, A (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  simp only [euclideanLaplacian, partial2_centeredQuadratic hA]

lemma symmetric_hessian {f : Plane → ℝ} (hf : Smooth f) (x₀ : Plane) :
    SymmetricForm (fderiv ℝ (fderiv ℝ f) x₀) := by
  intro x y
  exact (hf.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞)≤⊤))).eq x y

lemma hessian_on_basis {f : Plane → ℝ} (hf : Smooth f) (x₀ : Plane) (i j : Fin 2) :
    fderiv ℝ (fderiv ℝ f) x₀ (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)=
      coordPartial (coordPartial f i) j x₀ := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by simp : (∞:ℕ∞ω)+1≤(∞:ℕ∞ω))).differentiable (by simp)
  unfold coordPartial
  rw [fderiv_clm_apply hdf.differentiableAt (differentiableAt_const _)]
  simp

lemma smooth_secondTaylorPolynomial (f : Plane → ℝ) (x₀ : Plane) :
    Smooth (secondTaylorPolynomial f x₀) :=
  (contDiff_const.add (contDiff_const.clm_apply (contDiff_id.sub contDiff_const))).add
    (smooth_centeredQuadratic _ _)

lemma secondTaylorPolynomial_self (f : Plane → ℝ) (x₀ : Plane) :
    secondTaylorPolynomial f x₀ x₀=f x₀ := by
  simp [secondTaylorPolynomial, centeredQuadratic]

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set
namespace SharpNodal.Profiles
open Carleman

lemma partial_clm_shift (L : Plane →L[ℝ] ℝ) (x₀ x : Plane) (i : Fin 2) :
    coordPartial (fun y => L (y-x₀)) i x=L (EuclideanSpace.single i 1) := by
  have hd : HasFDerivAt (fun y => L (y-x₀)) L x := by
    convert! L.hasFDerivAt.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).sub_const x₀) using 1
    all_goals try with_reducible_and_instances rfl
  simp only [coordPartial, hd.fderiv]

lemma partial_quadraticAffine {A : BilinearForm} (hA : SymmetricForm A)
    (c : ℝ) (L : Plane →L[ℝ] ℝ) (x₀ x : Plane) (i : Fin 2) :
    coordPartial (quadraticAffine c L A x₀) i x=
      L (EuclideanSpace.single i 1)+A (x-x₀) (EuclideanSpace.single i 1) := by
  have hL : Smooth (fun y => L (y-x₀)) :=
    contDiff_const.clm_apply (contDiff_id.sub contDiff_const)
  unfold quadraticAffine
  rw [partial_add (contDiff_const.add hL)
    (smooth_centeredQuadratic A x₀), partial_add contDiff_const hL, partial_const,
    partial_clm_shift, partial_centeredQuadratic hA, zero_add]

lemma laplacian_quadraticAffine {A : BilinearForm} (hA : SymmetricForm A)
    (c : ℝ) (L : Plane →L[ℝ] ℝ) (x₀ x : Plane) :
    euclideanLaplacian (quadraticAffine c L A x₀) x=formTrace A := by
  unfold euclideanLaplacian formTrace
  apply Finset.sum_congr rfl
  intro i _
  rw [show coordPartial (quadraticAffine c L A x₀) i =
    fun y => L (EuclideanSpace.single i 1)+coordPartial (centeredQuadratic A x₀) i y by
      ext y; rw [partial_quadraticAffine hA, partial_centeredQuadratic hA]]
  rw [partial_add contDiff_const (smooth_partial (smooth_centeredQuadratic A x₀) i),
    partial_const, zero_add, partial2_centeredQuadratic hA]

lemma innerForm_apply (x y : Plane) : innerForm x y=inner ℝ x y := rfl

lemma symmetric_innerForm : SymmetricForm innerForm := by
  intro x y
  exact real_inner_comm y x

lemma formTrace_innerForm : formTrace innerForm=2 := by
  simp [formTrace, innerForm_apply]

lemma formTrace_smul (c : ℝ) (A : BilinearForm) : formTrace (c • A)=c*formTrace A := by
  simp only [formTrace, smul_apply, smul_eq_mul, Finset.mul_sum]

lemma centeredQuadratic_inner_smul (δ : ℝ) (x₀ x : Plane) :
    centeredQuadratic ((2*δ) • innerForm) x₀ x=δ*‖x-x₀‖^2 := by
  simp only [centeredQuadratic, smul_apply, smul_eq_mul, innerForm_apply,
    real_inner_self_eq_norm_sq]
  ring

end SharpNodal.Profiles

end
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

namespace SharpNodal.Profiles
open Carleman

lemma laplacian_radiusSquare (x₀ x : Plane) : euclideanLaplacian (radiusSquare x₀) x=4 := by
  have heq : radiusSquare x₀=centeredQuadratic ((2:ℝ) • innerForm) x₀ := by
    ext y
    simpa only [radiusSquare,mul_one,one_mul] using (centeredQuadratic_inner_smul 1 x₀ y).symm
  have hs : SymmetricForm ((2:ℝ) • innerForm) := by
    intro y z
    simp only [smul_apply,smul_eq_mul,symmetric_innerForm y z]
  rw [heq,laplacian_centeredQuadratic hs]
  change formTrace ((2:ℝ) • innerForm)=4
  rw [formTrace_smul,formTrace_innerForm]
  norm_num

end SharpNodal.Profiles

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
-- module Solutions.OAIQ4_Nl.NodalLength_Distributional
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

namespace SharpNodal.Profiles
open Carleman

theorem uniform_secondTaylor_remainder {f : Plane → ℝ} (hf : Smooth f)
    (hc : HasCompactSupport f) : ∃ C : ℝ, 0≤C ∧ ∀ x y,
    |f (x+y)-secondTaylorPolynomial f x (x+y)|≤C*‖y‖^3 := by
  have hd : Continuous (iteratedFDeriv ℝ 3 f) :=
    (hf.iteratedFDeriv_right (i:=3) (m:=0) (by exact WithTop.coe_le_coe.mpr (le_top : (3:ℕ∞)≤⊤))).continuous
  obtain ⟨M,hM⟩ := hd.norm.bddAbove_range_of_hasCompactSupport (hc.iteratedFDeriv (𝕜:=ℝ) 3).norm
  refine ⟨max 0 M,le_max_left _ _,?_⟩
  intro x y
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (n:=2) (x:=x) (y:=y)
    (fun t _ => (hf.of_le (WithTop.coe_le_coe.mpr (le_top : (3:ℕ∞)≤⊤))).contDiffAt)
  have heq : f (x+y)-secondTaylorPolynomial f x (x+y)=
      (1/2:ℝ)*(∫ t in (0:ℝ)..1, (1-t)^2*iteratedFDeriv ℝ 3 f (x+t • y) (fun _ => y)) := by
    simp only [show (2+1:ℕ)=3 from rfl,Finset.sum_range_succ,Finset.sum_range_zero,
      Nat.factorial_zero,Nat.factorial_one,Nat.factorial_two,zero_add,Nat.cast_one,Nat.cast_ofNat,
      inv_one,iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,
      iteratedFDeriv_two_apply,smul_eq_mul] at ht
    dsimp only [secondTaylorPolynomial,centeredQuadratic]
    simp only [add_sub_cancel_left]
    linarith [ht]
  rw [heq,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have hi : |∫ t in (0:ℝ)..1, (1-t)^2*iteratedFDeriv ℝ 3 f (x+t • y) (fun _ => y)|
      ≤ max 0 M*‖y‖^3 := by
    rw [← Real.norm_eq_abs]
    have hb : ∀ t ∈ uIoc (0:ℝ) 1,
        ‖(1-t)^2*iteratedFDeriv ℝ 3 f (x+t • y) (fun _ => y)‖≤ max 0 M*‖y‖^3 := by
      intro t ht
      simp only [uIoc_of_le (by norm_num : (0:ℝ)≤1),mem_Ioc] at ht
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
      have hder := (iteratedFDeriv ℝ 3 f (x+t • y)).le_opNorm (fun _ => y)
      have hnorm : ‖iteratedFDeriv ℝ 3 f (x+t • y)‖≤ max 0 M := (hM (mem_range_self (x+t • y))).trans (le_max_right _ _)
      have hs : (1-t)^2≤1 := by nlinarith [ht.1,ht.2]
      calc
        (1-t)^2*|iteratedFDeriv ℝ 3 f (x+t • y) (fun _ => y)|
          ≤ 1*(max 0 M*‖y‖^3) := mul_le_mul hs (by simpa [Real.norm_eq_abs] using hder.trans (mul_le_mul_of_nonneg_right hnorm (by positivity))) (abs_nonneg _) (by positivity)
        _ = _ := one_mul _
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hpos : 0≤ max 0 M*‖y‖^3 := by positivity
  linarith
end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma planeCircleAverage_harmonic {f : Plane → ℝ} (hf : Smooth f)
    (hΔ : ∀x,euclideanLaplacian f x=0) (a : Plane) (r : ℝ) :
    planeCircleAverage f a r=f a := by
  have hg : ContDiff ℝ ∞ (f∘planeComplex.symm) :=
    hf.comp planeComplex.symm.toContinuousLinearEquiv.contDiff
  have hgΔ : ∀z,(Δ (f∘planeComplex.symm)) z=0 := by
    rw [laplacian_comp_isometry planeComplex.symm hf,← plane_laplacian_eq_mathlib hf]
    exact fun z => hΔ (planeComplex.symm z)
  have hh : HarmonicOnNhd (f∘planeComplex.symm) (Metric.closedBall (planeComplex a) |r|) := by
    intro z _
    refine ⟨hg.contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤)),?_⟩
    exact Filter.Eventually.of_forall hgΔ
  simpa only [planeCircleAverage,Function.comp_def,planeComplex.symm_apply_apply] using hh.circleAverage_eq

lemma planeCircleAverage_radiusSquare (a : Plane) (r : ℝ) :
    planeCircleAverage (radiusSquare a) a r=r^2 := by
  apply Real.circleAverage_const_on_circle
  intro z hz
  change ‖planeComplex.symm z-a‖^2=r^2
  rw [← dist_eq_norm,← planeComplex.symm_apply_apply a,planeComplex.symm.isometry.dist_eq]
  rw [Metric.mem_sphere.mp hz,sq_abs]

lemma planeCircleAverage_secondTaylor {f : Plane → ℝ} (hf : Smooth f) (a : Plane) (r : ℝ) :
    planeCircleAverage (secondTaylorPolynomial f a) a r=
      f a+(r^2/4)*euclideanLaplacian f a := by
  let T := secondTaylorPolynomial f a
  let L := euclideanLaplacian f a
  have hT : Smooth T := smooth_secondTaylorPolynomial f a
  have hL (x : Plane) : euclideanLaplacian T x=L := by
    change euclideanLaplacian (quadraticAffine (f a) (fderiv ℝ f a)
      (fderiv ℝ (fderiv ℝ f) a) a) x=euclideanLaplacian f a
    rw [laplacian_quadraticAffine (symmetric_hessian hf a)]
    unfold formTrace euclideanLaplacian
    apply Finset.sum_congr rfl
    intro i _
    exact hessian_on_basis hf a i i
  let q := fun x => T x+(-L/4)*radiusSquare a x
  have hq : Smooth q := hT.add (contDiff_const.mul (smooth_radiusSquare a))
  have hqΔ (x : Plane) : euclideanLaplacian q x=0 := by
    rw [show q=(fun x => T x+(-L/4)*radiusSquare a x) from rfl,
      laplacian_add hT (contDiff_const.mul (smooth_radiusSquare a)),
      laplacian_const_mul (smooth_radiusSquare a),hL]
    dsimp only
    rw [laplacian_radiusSquare]
    ring
  have havg := planeCircleAverage_harmonic hq hqΔ a r
  have hsplit : planeCircleAverage q a r=planeCircleAverage T a r+(-L/4)*r^2 := by
    unfold planeCircleAverage
    change Real.circleAverage (fun z => T (planeComplex.symm z)+(-L/4)*radiusSquare a (planeComplex.symm z)) _ r=_
    have h1 : CircleIntegrable (fun z => T (planeComplex.symm z)) (planeComplex a) r :=
      (hT.continuous.comp planeComplex.symm.continuous).continuousOn.circleIntegrable'
    have h2 : CircleIntegrable (fun z => (-L/4)*radiusSquare a (planeComplex.symm z)) (planeComplex a) r :=
      ((contDiff_const.mul (smooth_radiusSquare a) : Smooth (fun x => (-L/4)*radiusSquare a x)).continuous.comp planeComplex.symm.continuous).continuousOn.circleIntegrable'
    rw [Real.circleAverage_fun_add h1 h2]
    change _+Real.circleAverage ((-L/4) • (fun z => radiusSquare a (planeComplex.symm z))) (planeComplex a) r=_
    rw [Real.circleAverage_smul]
    change _+(-L/4)*planeCircleAverage (radiusSquare a) a r=_
    rw [planeCircleAverage_radiusSquare]
    rfl
  have hqa : q a=f a := by simp [q,T,secondTaylorPolynomial_self,radiusSquare]
  rw [hsplit,hqa] at havg
  change planeCircleAverage T a r=f a+r^2/4*L
  linarith
end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma planeCircleAverage_uniform_second_order {f : Plane → ℝ} (hf : Smooth f)
    (hc : HasCompactSupport f) : ∃ C : ℝ, 0≤C ∧ ∀ a r,
      |planeCircleAverage f a r-f a-(r^2/4)*euclideanLaplacian f a|≤C*|r|^3 := by
  obtain ⟨C,hC,hrem⟩ := uniform_secondTaylor_remainder hf hc
  refine ⟨C,hC,?_⟩
  intro a r
  let T := secondTaylorPolynomial f a
  have hT : Smooth T := smooth_secondTaylorPolynomial f a
  have he : planeCircleAverage f a r-f a-r^2/4*euclideanLaplacian f a =
    Real.circleAverage (fun z => f (planeComplex.symm z)-T (planeComplex.symm z)) (planeComplex a) r := by
    have h1 : CircleIntegrable (fun z => f (planeComplex.symm z)) (planeComplex a) r :=
      (hf.continuous.comp planeComplex.symm.continuous).continuousOn.circleIntegrable'
    have h2 : CircleIntegrable (fun z => T (planeComplex.symm z)) (planeComplex a) r :=
      (hT.continuous.comp planeComplex.symm.continuous).continuousOn.circleIntegrable'
    rw [Real.circleAverage_fun_sub h1 h2]
    change planeCircleAverage f a r-f a-r^2/4*euclideanLaplacian f a=
      planeCircleAverage f a r-planeCircleAverage (secondTaylorPolynomial f a) a r
    rw [planeCircleAverage_secondTaylor hf]
    ring
  rw [he]
  apply Real.abs_circleAverage_le_circleAverage_abs.trans
  apply Real.circleAverage_mono_on_of_le_circle
  · exact (((hf.continuous.sub hT.continuous).comp planeComplex.symm.continuous).abs).continuousOn.circleIntegrable'
  intro z hz
  have hr' : ‖planeComplex.symm z-a‖=|r| := by
    rw [← dist_eq_norm,← planeComplex.symm_apply_apply a,planeComplex.symm.isometry.dist_eq]
    exact Metric.mem_sphere.mp hz
  simpa only [Pi.abs_apply,add_sub_cancel,hr',T] using hrem a (planeComplex.symm z-a)

end SharpNodal.Profiles
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

noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma rconv_eq (f g : Plane → ℝ) (x : Plane) : rconv f g x=∫y,f y*g (x-y) := rfl
lemma rconv_swap (f g : Plane → ℝ) (x : Plane) : rconv f g x=∫y,f (x-y)*g y :=
  convolution_eq_swap (ContinuousLinearMap.mul ℝ ℝ)

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
-- module Solutions.OAIQ4_Nl.NodalLength_MetricFlux
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

namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic

lemma smoothAt_partial {f : Plane → ℝ} {x : Plane} (hf : ContDiffAt ℝ ∞ f x) (i : Fin 2) :
    ContDiffAt ℝ ∞ (coordPartial f i) x :=
  (hf.fderiv_right (by simp)).clm_apply contDiffAt_const
lemma partial_congr_nhds {f g : Plane → ℝ} {x : Plane} (h : f=ᶠ[𝓝 x]g) (i : Fin 2) :
    coordPartial f i x=coordPartial g i x := by unfold coordPartial; rw [h.fderiv_eq]

end SharpNodal.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_NormalizedCharts
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

namespace SharpNodal.Geometry
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M]
  [RiemannianBundle (fun x : M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

lemma smoothOn_pullback_metric {f : Plane → M} {s : Set Plane} (hs : IsOpen s)
    (hf : ContMDiffOn 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ f s) (v w : Plane) :
    ContDiffOn ℝ ∞ (fun y=>inner ℝ
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y v)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y w)) s := by
  have hc (a : Plane) : ContMDiff 𝓘(ℝ,Plane) (𝓘(ℝ,Plane)).tangent ∞
      (fun y:Plane=>(⟨y,a⟩ : TangentBundle 𝓘(ℝ,Plane) Plane)) := by
    intro y
    exact contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
  have ht:=hf.contMDiffOn_tangentMapWithin (m:=∞) (by simp) hs.uniqueMDiffOn
  have hv (a : Plane) : ContMDiffOn 𝓘(ℝ,Plane) (𝓘(ℝ,Plane)).tangent ∞
      (fun y=> (⟨f y,mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y a⟩ : TangentBundle 𝓘(ℝ,Plane) M)) s := by
    have hh:=ht.comp (hc a).contMDiffOn (show MapsTo (fun y:Plane=>(⟨y,a⟩ : TangentBundle 𝓘(ℝ,Plane) Plane)) s (Bundle.TotalSpace.proj ⁻¹' s) from fun _ hy=>hy)
    apply hh.congr
    intro y hy
    simp only [Function.comp_apply,tangentMapWithin,
      mfderivWithin_of_mem_nhds (I:=𝓘(ℝ,Plane)) (I':=𝓘(ℝ,Plane)) (f:=f) (hs.mem_nhds hy)]
  exact ((hv v).inner_bundle (hv w)).contDiffOn

lemma ChartSmooth.metric_smooth {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e)
    (i j : Fin 2) : ContDiffOn ℝ ∞ (fun y=>pullMetric (e.symm : Plane → M) y i j) e.target :=
  smoothOn_pullback_metric e.open_target he.2 _ _

end SharpNodal.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Isothermal
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

noncomputable section
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

noncomputable section
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma IsConformal.factor {e : OpenPartialHomeomorph M Plane} (he : IsConformal e)
    {y : Plane} (hy : y∈e.target) :
    0 < conformalFactor e y ∧ pullMetric (e.symm : Plane → M) y=
      conformalFactor e y • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨p,hp,hG⟩:=he.2 y hy
  have hf : conformalFactor e y=p:=by simp [conformalFactor,hG]
  exact ⟨hf.symm ▸ hp,by rwa [hf]⟩

lemma IsConformal.factor_smooth {e : OpenPartialHomeomorph M Plane} (he : IsConformal e) :
    ContDiffOn ℝ ∞ (conformalFactor e) e.target:=he.1.metric_smooth 0 0

lemma IsConformal.laplace {e : OpenPartialHomeomorph M Plane} (he : IsConformal e)
    {U : M → ℝ} (hU : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ) ∞ U) {y : Plane} (hy : y∈e.target) :
    laplaceBeltrami U (e.symm y)=euclideanLaplacian (U ∘ e.symm) y/conformalFactor e y := by
  rw [laplaceBeltrami_in_chart he.1 (e.map_target hy) hU,e.right_inv hy]
  let a:=fun z=>pullMetric (e.symm : Plane → M) z 0 0
  let b:=fun z=>pullMetric (e.symm : Plane → M) z 0 1
  let c:=fun z=>pullMetric (e.symm : Plane → M) z 1 1
  have hf0 : scalarFlux0 a b c (U ∘ e.symm)=ᶠ[𝓝 y]coordPartial (U ∘ e.symm) 0 := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    have hpos:=(he.factor hz).1
    have hG:=(he.factor hz).2
    dsimp [scalarFlux0,scalarDensity,a,b,c]
    rw [hG]
    norm_num [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    rw [← pow_two,Real.sqrt_sq hpos.le]
    exact mul_div_cancel_left₀ _ hpos.ne'
  have hf1 : scalarFlux1 a b c (U ∘ e.symm)=ᶠ[𝓝 y]coordPartial (U ∘ e.symm) 1 := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    have hpos:=(he.factor hz).1
    have hG:=(he.factor hz).2
    dsimp [scalarFlux1,scalarDensity,a,b,c]
    rw [hG]
    norm_num [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    rw [← pow_two,Real.sqrt_sq hpos.le]
    exact mul_div_cancel_left₀ _ hpos.ne'
  have hρ : scalarDensity a b c y=conformalFactor e y := by
    dsimp [scalarDensity,a,b,c]
    rw [(he.factor hy).2]
    norm_num [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    rw [← pow_two,Real.sqrt_sq (he.factor hy).1.le]
  change scalarLaplace a b c (U ∘ e.symm) y=_
  rw [scalarLaplace,partial_congr_nhds hf0,partial_congr_nhds hf1,hρ]
  simp only [euclideanLaplacian,Fin.sum_univ_two]

lemma IsConformal.eigenfunction {e : OpenPartialHomeomorph M Plane} (he : IsConformal e)
    {U : M → ℝ} (hU : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ) ∞ U) {lam : ℝ}
    (hPDE : ∀x,-laplaceBeltrami U x=lam*U x) :
    ContDiffOn ℝ ∞ (U ∘ e.symm) e.target ∧
      ∀y∈e.target,euclideanLaplacian (U ∘ e.symm) y+lam*conformalFactor e y*(U ∘ e.symm) y=0 := by
  refine ⟨(hU.comp_contMDiffOn he.1.2).contDiffOn,?_⟩
  intro y hy
  have h:=hPDE (e.symm y)
  rw [he.laplace hU hy] at h
  have hn:=(he.factor hy).1.ne'
  change -(euclideanLaplacian (U ∘ e.symm) y/conformalFactor e y)=lam*(U ∘ e.symm) y at h
  field_simp at h
  nlinarith

end SharpNodal.Geometry

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

noncomputable section
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

lemma IsConformal.exists_profile_ball {e : OpenPartialHomeomorph M Plane} (he : IsConformal e)
    {y : Plane} (hy : y∈e.target) : ∃r Cp : ℝ,0 < r ∧ 0≤Cp ∧
      closedBall y r⊆e.target ∧ volume (ball y r)≤1 ∧
      (∀z∈ball y r,|conformalFactor e z|≤Cp) ∧
      (∀i z,z∈ball y r → |coordPartial (conformalFactor e) i z|≤Cp) := by
  obtain ⟨t,ht,hball⟩:=Metric.isOpen_iff.mp e.open_target y hy
  let r:=min (t/2) (1/4)
  have hr : 0 < r:=lt_min (by positivity) (by norm_num)
  have hrt : r<t:=lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr4 : r≤1/4:=min_le_right _ _
  have hc : closedBall y r⊆e.target:=(closedBall_subset_ball hrt).trans hball
  have hp:=he.factor_smooth
  have hpi (i : Fin 2) : ContinuousOn (coordPartial (conformalFactor e) i) e.target := by
    intro z hz
    exact (smoothAt_partial (hp.contDiffAt (e.open_target.mem_nhds hz)) i).continuousAt.continuousWithinAt
  obtain ⟨B,hB⟩:=(isCompact_closedBall y r).exists_bound_of_continuousOn (hp.continuousOn.mono hc)
  obtain ⟨B0,hB0⟩:=(isCompact_closedBall y r).exists_bound_of_continuousOn ((hpi 0).mono hc)
  obtain ⟨B1,hB1⟩:=(isCompact_closedBall y r).exists_bound_of_continuousOn ((hpi 1).mono hc)
  let Cp:=|B|+|B0|+|B1|
  refine ⟨r,Cp,hr,by dsimp [Cp]; positivity,hc,?_,?_,?_⟩
  · rw [EuclideanSpace.volume_ball_fin_two,←ENNReal.ofReal_pow hr.le,←ENNReal.ofReal_mul (sq_nonneg r)]
    apply ENNReal.ofReal_le_one.mpr
    have hh:=Real.pi_lt_four
    nlinarith
  · intro z hz
    have hb:=hB z (ball_subset_closedBall hz)
    rw [Real.norm_eq_abs] at hb
    dsimp [Cp]; linarith [le_abs_self B,abs_nonneg B0,abs_nonneg B1]
  · intro i z hz
    fin_cases i
    · have hb:=hB0 z (ball_subset_closedBall hz)
      rw [Real.norm_eq_abs] at hb
      dsimp [Cp]; linarith [le_abs_self B0,abs_nonneg B,abs_nonneg B1]
    · have hb:=hB1 z (ball_subset_closedBall hz)
      rw [Real.norm_eq_abs] at hb
      dsimp [Cp]; linarith [le_abs_self B1,abs_nonneg B,abs_nonneg B0]

end SharpNodal.Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Eigenfunctions
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

noncomputable section
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory

noncomputable section
open scoped Topology ContDiff ENNReal Bundle
open Set Filter Metric MeasureTheory Bundle Manifold

noncomputable section
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

lemma laplaceBeltrami_const_mul {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ) ∞ u) (c : ℝ) (x : M) :
    laplaceBeltrami (fun z=>c*u z) x=c*laplaceBeltrami u x := by
  obtain ⟨e,hx,he⟩:=exists_isothermal_chart x
  have ht:=e.map_source hx
  have hs : ContDiffOn ℝ ∞ (u∘e.symm) e.target:=(hu.comp_contMDiffOn he.1.2).contDiffOn
  obtain ⟨f,r,hf,hr,-,heq⟩:=smooth_extension_near e.open_target ht hs
  have hg : f=ᶠ[𝓝 (e x)]u∘e.symm:=Eventually.mono (ball_mem_nhds _ hr) (fun z hz=>heq z hz)
  have hcg : (fun z=>c*f z)=ᶠ[𝓝 (e x)](fun z=>c*u (e.symm z)):=by filter_upwards [hg] with z hz; rw [hz]; rfl
  have hc : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ) ∞ (fun z=>c*u z) := contMDiff_const.mul hu
  rw [←e.left_inv hx,he.laplace hc ht,he.laplace hu ht]
  change euclideanLaplacian (fun z=>c*u (e.symm z)) (e x)/conformalFactor e (e x)=_
  rw [←laplacian_germ hcg,laplacian_const_mul hf]
  dsimp only
  rw [laplacian_germ hg]
  ring

lemma NormalizedEigen.neg {K : ℝ} {u : M → ℝ} (hu : NormalizedEigen K u) :
    NormalizedEigen K (fun x=> -u x) := by
  refine ⟨hu.smooth.neg,?_,?_,?_⟩
  · intro x
    have hh:=laplaceBeltrami_const_mul hu.smooth (-1) x
    simp only [neg_one_mul] at hh
    rw [hh,neg_neg]
    have he:=hu.equation x
    nlinarith
  · intro x; simpa only [abs_neg] using hu.bound x
  · obtain ⟨x,hx⟩:=hu.maximum; exact ⟨x,by simpa only [abs_neg] using hx⟩

end SharpNodal.Geometry

noncomputable section
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
namespace SharpNodal.Profiles
open Carleman
lemma compact_laplacian_min {f : Plane → ℝ} (hf : Smooth f) (hc : HasCompactSupport f)
    {x : Plane} (hmin : IsLocalMin f x) : 0≤euclideanLaplacian f x := by
  obtain ⟨C,hC,hCb⟩:=planeCircleAverage_uniform_second_order hf hc
  obtain ⟨r,hr,hrb⟩:=Metric.eventually_nhds_iff.mp hmin
  by_contra hn
  have hd : euclideanLaplacian f x<0:=lt_of_not_ge hn
  let t:=min (r/2) (-euclideanLaplacian f x/(8*(C+1)))
  have ht : 0<t:=lt_min (by positivity) (div_pos (neg_pos.mpr hd) (by positivity))
  have htr : t < r:=(min_le_left _ _).trans_lt (by linarith)
  have htD : 8*(C+1)*t≤-euclideanLaplacian f x := by
    have hh:=min_le_right (r/2) (-euclideanLaplacian f x/(8*(C+1)))
    have hh' := (le_div_iff₀ (by positivity : 0<8*(C+1))).mp hh
    dsimp [t]; nlinarith only [hh']
  have hm : f x≤planeCircleAverage f x t := by
    have hi : CircleIntegrable (f∘planeComplex.symm) (planeComplex x) t :=
      (hf.continuous.comp planeComplex.symm.continuous).continuousOn.circleIntegrable'
    have hh:=Real.circleAverage_mono (f₁:=fun _=>f x) (circleIntegrable_const _ _ _) hi (fun z hz=>by
      apply hrb
      have hz' : dist (planeComplex.symm z) x=t := by
        rw [←planeComplex.symm_apply_apply x,planeComplex.symm.isometry.dist_eq]
        simpa only [abs_of_pos ht] using mem_sphere.mp hz
      rw [hz']; exact htr)
    simpa only [Real.circleAverage_const,planeCircleAverage] using hh
  have he:=(abs_le.mp (hCb x t)).2
  rw [abs_of_pos ht] at he
  have hmul : t^2*(-euclideanLaplacian f x/4)≤t^2*(C*t) := by nlinarith only [he,hm]
  have hdel:=le_of_mul_le_mul_left hmul (sq_pos_of_pos ht)
  nlinarith

lemma laplacian_min {f : Plane → ℝ} (hf : Smooth f) {x : Plane}
    (hmin : IsLocalMin f x) : 0≤euclideanLaplacian f x := by
  let χ : ContDiffBump x:=⟨1,2,by norm_num,by norm_num⟩
  let g:=fun z=>χ z*f z
  have hg : Smooth g:=χ.contDiff.mul hf
  have hcg : HasCompactSupport g:=χ.hasCompactSupport.mul_right
  have he : g=ᶠ[𝓝 x]f := by
    filter_upwards [ball_mem_nhds x (by norm_num : (0:ℝ)<1)] with z hz
    simp only [g,χ.one_of_mem_closedBall (ball_subset_closedBall hz),one_mul]
  have hgm : IsLocalMin g x := by
    have hx : g x=f x:=he.self_of_nhds
    filter_upwards [hmin,he] with z hz hze
    rw [hx,hze]; exact hz
  rw [←laplacian_germ he]
  exact compact_laplacian_min hg hcg hgm

lemma laplacian_min_local {Ω : Set Plane} (hΩ : IsOpen Ω) {x : Plane} (hx : x∈Ω)
    {f : Plane → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hmin : IsLocalMin f x) :
    0≤euclideanLaplacian f x := by
  obtain ⟨g,r,hg,hr,-,heq⟩:=smooth_extension_near hΩ hx hf
  have he : g=ᶠ[𝓝 x]f:=Eventually.mono (ball_mem_nhds x hr) (fun z hz=>heq z hz)
  have hgm : IsLocalMin g x:=by
    filter_upwards [hmin,he] with z hz hez
    rw [he.self_of_nhds,hez]; exact hz
  rw [←laplacian_germ he]
  exact laplacian_min hg hgm
end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff Bundle
open Set Filter Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
lemma NormalizedEigen.exists_nonpos [CompactSpace M] {K : ℝ} {u : M → ℝ}
    (hu : NormalizedEigen K u) (hK : 0<K) : ∃x,u x≤0 := by
  let : Nonempty M:=⟨hu.maximum.choose⟩
  obtain ⟨x,-,hx⟩:=isCompact_univ.exists_isMinOn (Set.univ_nonempty) hu.smooth.continuous.continuousOn
  refine ⟨x,?_⟩
  obtain ⟨e,hxe,he⟩:=exists_isothermal_chart x
  have hye:=e.map_source hxe
  obtain ⟨hU,hPDE⟩:=he.eigenfunction hu.smooth hu.equation
  have hmin : IsLocalMin (u∘e.symm) (e x) := by
    filter_upwards [] with z
    simp only [Function.comp_apply,e.left_inv hxe]
    exact hx (mem_univ (e.symm z))
  have hd:=laplacian_min_local e.open_target hye hU hmin
  have hp:=(he.factor hye).1
  have heq:=hPDE (e x) hye
  simp only [Function.comp_apply,e.left_inv hxe] at heq
  have hh : K^2*conformalFactor e (e x)*u x≤0:=by linarith
  have hpos := mul_pos (sq_pos_of_pos hK) hp
  nlinarith only [hh,hpos]
end SharpNodal.Geometry

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_FrequencyGap
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

namespace SharpNodal.Profiles
open Carleman InnerProductSpace
lemma poissonKernel_bounds {w z : ℂ} (hw : ‖w‖<1/2) (hz : ‖z‖=1) :
    1/4≤poissonKernel 0 w z ∧ poissonKernel 0 w z≤4 := by
  have ht:=norm_sub_le z w
  have hl:=norm_sub_norm_le z w
  rw [hz] at ht hl
  have hdn : 0<‖z-w‖:=by linarith
  have hsqlo : 1/4≤‖z-w‖^2:=by nlinarith
  have hsqhi : ‖z-w‖^2≤9/4:=by nlinarith [norm_nonneg w,norm_nonneg (z-w)]
  simp only [poissonKernel_def,sub_zero,hz,one_pow]
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hdn)).mpr
    nlinarith [norm_nonneg w]
  · apply (div_le_iff₀ (sq_pos_of_pos hdn)).mpr
    nlinarith [sq_nonneg ‖w‖]

lemma harmonic_harnack {h : ℂ → ℝ} (hh : HarmonicOnNhd h (closedBall 0 1))
    (hn : ∀z∈sphere (0:ℂ) 1,0≤h z) {x y : ℂ}
    (hx : x∈ball 0 (1/2)) (hy : y∈ball 0 (1/2)) : h x≤16*h y := by
  have hcont:=hh.continuousOn.mono sphere_subset_closedBall
  have hcont' : ContinuousOn h (sphere 0 |(1:ℝ)|) := by simpa only [abs_one] using hcont
  have hi : CircleIntegrable h 0 1 := hcont'.circleIntegrable'
  have hker (w : ℂ) (hw:w∈ball 0 (1/2)) :
      CircleIntegrable (poissonKernel 0 w • h) 0 1 := by
    have hne (z : ℂ) (hz:z∈sphere 0 1) : z-w≠0 := by
      have hw':=mem_ball_zero_iff.mp hw
      have hz':=mem_sphere_zero_iff_norm.mp hz
      intro he
      have he':z=w:=sub_eq_zero.mp he
      rw [he'] at hz'; linarith
    apply ContinuousOn.circleIntegrable'
    simp only [abs_one]
    change ContinuousOn (poissonKernel 0 w * h) (sphere 0 1)
    apply ContinuousOn.mul _ hcont
    have hfun : poissonKernel 0 w = (fun z=>(‖z‖^2-‖w‖^2)/‖z-w‖^2) := by
      funext z; simp only [poissonKernel_def,sub_zero]
    rw [hfun]
    exact (continuous_norm.continuousOn.pow 2 |>.sub continuousOn_const).div
      ((continuous_id.sub continuous_const).norm.continuousOn.pow 2)
      (fun z hz=>pow_ne_zero _ (norm_ne_zero_iff.mpr (hne z hz)))
  have hb (w : ℂ) (hw:w∈ball 0 (1/2)) :
      (1/4)*h 0≤h w ∧ h w≤4*h 0 := by
    have hf : Real.circleAverage (poissonKernel 0 w * h) 0 1 = h w := by
      simpa only [smul_eq_mul] using hh.circleAverage_poissonKernel_smul (ball_subset_ball (by norm_num : (1/2:ℝ)≤1) hw)
    have hhabs : HarmonicOnNhd h (closedBall 0 |(1:ℝ)|) := by simpa only [abs_one] using hh
    have hm : Real.circleAverage h 0 1=h 0:=hhabs.circleAverage_eq
    constructor
    · have hi' : CircleIntegrable ((1/4:ℝ) • h) 0 1:=hi.smul (1/4)
      have he:=Real.circleAverage_mono hi' (hker w hw) (fun z hz=>by
        have hz' : ‖z‖=1:=by simpa using mem_sphere.mp hz
        exact mul_le_mul_of_nonneg_right (poissonKernel_bounds (mem_ball_zero_iff.mp hw) hz').1 (hn z (by simpa using hz)))
      simpa only [Real.circleAverage_smul,smul_eq_mul,hm,hf] using he
    · have hi' : CircleIntegrable ((4:ℝ) • h) 0 1:=hi.smul 4
      have he:=Real.circleAverage_mono (hker w hw) hi' (fun z hz=>by
        have hz' : ‖z‖=1:=by simpa using mem_sphere.mp hz
        exact mul_le_mul_of_nonneg_right (poissonKernel_bounds (mem_ball_zero_iff.mp hw) hz').2 (hn z (by simpa using hz)))
      simpa only [Real.circleAverage_smul,smul_eq_mul,hm,hf] using he
  have hxx:=(hb x hx).2
  have hyy:=(hb y hy).1
  linarith

lemma plane_harmonic_harnack {h : Plane → ℝ} (hh : Smooth h)
    (he : ∀z∈ball (0:Plane) 2,euclideanLaplacian h z=0)
    (hn : ∀z∈ball (0:Plane) 2,0≤h z) {x y : Plane}
    (hx:x∈ball 0 (1/2)) (hy:y∈ball 0 (1/2)) : h x≤16*h y := by
  let H:=h ∘ planeComplex.symm
  have hs : ContDiff ℝ ∞ H:=hh.comp planeComplex.symm.toContinuousLinearEquiv.contDiff
  have hh' : HarmonicOnNhd H (closedBall 0 1) := by
    intro z hz
    refine ⟨hs.contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤)),?_⟩
    have hz' : z∈ball (0:ℂ) 2:=closedBall_subset_ball (by norm_num) hz
    filter_upwards [isOpen_ball.mem_nhds hz'] with w hw
    rw [laplacian_comp_isometry planeComplex.symm hh,←plane_laplacian_eq_mathlib hh]
    exact he _ (by simpa only [mem_ball,dist_zero_right,planeComplex.symm.norm_map] using hw)
  have hpc (z : Plane) (hz:z∈ball 0 (1/2)) : planeComplex z∈ball (0:ℂ) (1/2) := by
    simpa only [mem_ball,dist_zero_right,planeComplex.norm_map] using hz
  simpa only [H,Function.comp_apply,planeComplex.symm_apply_apply] using
    harmonic_harnack hh' (fun z hz=>hn _ (by
      have hz':=sphere_subset_ball (by norm_num : (1:ℝ)<2) hz
      simpa only [mem_ball,dist_zero_right,planeComplex.symm.norm_map] using hz')) (hpc x hx) (hpc y hy)
end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
namespace SharpNodal.Profiles
open Carleman
lemma laplacian_sub {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g) (x : Plane) :
    euclideanLaplacian (fun z=>f z-g z) x=euclideanLaplacian f x-euclideanLaplacian g x := by
  have he : (fun z=>f z-g z)=(fun z=>f z+(-1)*g z) := by funext z; ring
  rw [he,laplacian_add hf (contDiff_const.mul hg),laplacian_const_mul hg]
  ring

lemma additive_harnack_unit : ∃D : ℝ,0<D ∧ ∀(U q : Plane → ℝ),
    ContDiffOn ℝ ∞ U (ball 0 3) → ContDiffOn ℝ ∞ q (ball 0 3) →
    (∀z∈ball (0:Plane) 3,euclideanLaplacian U z+q z*U z=0) →
    (∀z∈ball (0:Plane) 3,|U z|≤1) → ∀Q : ℝ,0≤Q →
    (∀z∈ball (0:Plane) 3,|q z|≤Q) →
    ∀x∈ball (0:Plane) (1/2),∀y∈ball (0:Plane) (1/2),
      1-U x≤16*(1-U y)+D*Q := by
  obtain ⟨C,hC,hCb⟩:=newton_operator_bounds
  refine ⟨34*C,by linarith,?_⟩
  intro U q hU hq he hUb Q hQ hqb x hx y hy
  obtain ⟨V,hV,-,hVe,-,-⟩:=bump_smoothOn_extension hU
  obtain ⟨P,hP,-,hPe,-,-⟩:=bump_smoothOn_extension hq
  let χ : ContDiffBump (0:Plane):=⟨9/4,5/2,by norm_num,by norm_num⟩
  let f : Plane → ℝ:=fun z=>χ z*(P z*V z)
  have hf : Smooth f:=χ.contDiff.mul (hP.mul hV)
  have hcf : HasCompactSupport f:=χ.hasCompactSupport.mul_right
  have hfs : ∀z,3≤‖z‖ → f z=0 := by
    intro z hz
    have hz':χ z=0:=χ.zero_of_le_dist (by dsimp [χ]; simpa only [dist_zero_right] using (show (5/2:ℝ)≤‖z‖ by linarith))
    simp [f,hz']
  have hfb : ∀z∈ball (0:Plane) 3,|f z|≤Q := by
    intro z hz
    by_cases hz' : z∈ball (0:Plane) (5/2)
    · have hz'' : z∈ball (0:Plane) (11/4):=ball_subset_ball (by norm_num) hz'
      have hvz:=hVe z hz''
      have hpz:=hPe z hz''
      have hh:=mul_le_mul (hqb z hz) (hUb z hz) (abs_nonneg _) hQ
      dsimp [f]
      rw [hpz.self_of_nhds,hvz.self_of_nhds,abs_mul,abs_mul,abs_of_nonneg χ.nonneg]
      calc
        _ ≤ 1*(|q z| * |U z|):=mul_le_mul_of_nonneg_right χ.le_one (by positivity)
        _ ≤ Q:=by simpa using hh
    · have hz0 : χ z=0:=χ.zero_of_le_dist (by simpa only [χ,mem_ball,dist_zero_right,not_lt] using hz')
      simpa [f,hz0] using hQ
  have hnb:=hCb f hf hcf Q hQ hfs hfb
  let N:=newtonPotential f
  have hN : Smooth N:=smooth_newtonPotential hf hcf
  let H : Plane → ℝ:=fun z=>1-(V z+N z)+C*Q
  have hH : Smooth H:=(contDiff_const.sub (hV.add hN)).add contDiff_const
  have hHE : ∀z∈ball (0:Plane) 2,euclideanLaplacian H z=0 := by
    intro z hz
    have hz11 : z∈ball (0:Plane) (11/4):=ball_subset_ball (by norm_num) hz
    have hz3 : z∈ball (0:Plane) 3:=ball_subset_ball (by norm_num) hz
    have hVE:=laplacian_germ (hVe z hz11)
    have hfz : f z=q z*U z:=by
      have hχ : χ z=1:=χ.one_of_mem_closedBall (ball_subset_closedBall (ball_subset_ball (by norm_num) hz))
      simp only [f,hχ,one_mul,(hPe z hz11).self_of_nhds,(hVe z hz11).self_of_nhds]
    rw [laplacian_add (contDiff_const.sub (hV.add hN)) contDiff_const,
      laplacian_const,add_zero,laplacian_sub contDiff_const (hV.add hN),laplacian_const,
      laplacian_add hV hN,laplacian_newtonPotential hf hcf,hVE,hfz]
    rw [he z hz3,sub_zero]
  have hHn : ∀z∈ball (0:Plane) 2,0≤H z := by
    intro z hz
    have hz3 : z∈ball (0:Plane) 3:=ball_subset_ball (by norm_num) hz
    have hz11 : z∈ball (0:Plane) (11/4):=ball_subset_ball (by norm_num) hz
    have hvz:=(hUb z hz3)
    have hnz:=(hnb z hz3).1
    have hvEq:=(hVe z hz11).self_of_nhds
    dsimp [H,N]; rw [hvEq]; linarith [le_abs_self (U z),le_abs_self (newtonPotential f z)]
  have hh:=plane_harmonic_harnack hH hHE hHn hx hy
  have hx3 : x∈ball (0:Plane) 3:=ball_subset_ball (by norm_num) hx
  have hy3 : y∈ball (0:Plane) 3:=ball_subset_ball (by norm_num) hy
  have hnx:=(hnb x hx3).1
  have hny:=(hnb y hy3).1
  have hvx:=(hVe x (ball_subset_ball (by norm_num) hx)).self_of_nhds
  have hvy:=(hVe y (ball_subset_ball (by norm_num) hy)).self_of_nhds
  dsimp [H,N] at hh
  rw [hvx,hvy] at hh
  have hnxl:=(abs_le.mp hnx).1
  have hnxu:=(abs_le.mp hnx).2
  have hnyl:=(abs_le.mp hny).1
  have hnyu:=(abs_le.mp hny).2
  nlinarith [show 0≤C*Q by positivity]
end SharpNodal.Profiles

noncomputable section
open scoped Topology
open Set Filter Metric
namespace SharpNodal.Geometry
lemma no_low_energy_sequence {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    {v : ℕ → X → ℝ} {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hv : ∀j x,0≤v j x) (hmin : ∀j,∃x,v j x=0) (hmax : ∀j,∃x,1≤v j x)
    (hlocal : ∀x:X,∃G : Set X,IsOpen G ∧ x∈G ∧ ∃D : ℝ,0≤D ∧
      ∀j,∀y∈G,∀z∈G,v j y≤16*v j z+D*ε j) : False := by
  choose x hx using hmin
  obtain ⟨a,-,φ,hφ,hconv⟩:=isCompact_univ.tendsto_subseq (fun j=>mem_univ (x j))
  let S : Set X:={y | Tendsto (fun j=>v (φ j) y) atTop (𝓝 0)}
  have heps : Tendsto (fun j=>ε (φ j)) atTop (𝓝 0):=hε.comp hφ.tendsto_atTop
  have hprop {G : Set X} {D : ℝ}
      (hb : ∀j,∀y∈G,∀z∈G,v j y≤16*v j z+D*ε j)
      {y z : X} (hy:y∈G) (hz:z∈G) (hs:z∈S) : y∈S := by
    have ht : Tendsto (fun j=>16*v (φ j) z+D*ε (φ j)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hs).add (tendsto_const_nhds.mul heps)
    exact squeeze_zero (fun j=>hv (φ j) y) (fun j=>hb (φ j) y hy z hz) ht
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨G,hG,hyG,D,-,hb⟩:=hlocal y
    exact Filter.mem_of_superset (hG.mem_nhds hyG) (fun z hz=>hprop hb hz hyG hy)
  have hScopen : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨G,hG,hyG,D,-,hb⟩:=hlocal y
    apply Filter.mem_of_superset (hG.mem_nhds hyG)
    intro z hz hzs
    exact hy (hprop hb hyG hz hzs)
  have ha : a∈S := by
    obtain ⟨G,hG,haG,D,-,hb⟩:=hlocal a
    have hGevent:=hconv.eventually (hG.mem_nhds haG)
    have hupper : ∀ᶠj in atTop,v (φ j) a≤D*ε (φ j) := by
      filter_upwards [hGevent] with j hj
      have hh:=hb (φ j) a haG (x (φ j)) hj
      simpa only [hx,mul_zero,zero_add] using hh
    apply squeeze_zero' (Eventually.of_forall fun j=>hv (φ j) a) hupper
    simpa using tendsto_const_nhds.mul heps
  have hSuniv : S=univ:=(show IsClopen S from ⟨by simpa only [compl_compl] using hScopen.isClosed_compl,hSopen⟩).eq_univ ⟨a,ha⟩
  choose z hz using hmax
  obtain ⟨b,-,ψ,hψ,hzconv⟩:=isCompact_univ.tendsto_subseq (fun j=>mem_univ (z (φ j)))
  obtain ⟨G,hG,hbG,D,-,hb⟩:=hlocal b
  have hbevent:=hzconv.eventually (hG.mem_nhds hbG)
  have hbS : b∈S:=by rw [hSuniv]; exact mem_univ b
  have hb0 : Tendsto (fun j=>v (φ (ψ j)) b) atTop (𝓝 0):=hbS.comp hψ.tendsto_atTop
  have ht : Tendsto (fun j=>16*v (φ (ψ j)) b+D*ε (φ (ψ j))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hb0).add (tendsto_const_nhds.mul (heps.comp hψ.tendsto_atTop))
  have hone : ∀ᶠj in atTop,(1:ℝ)≤16*v (φ (ψ j)) b+D*ε (φ (ψ j)) := by
    filter_upwards [hbevent] with j hj
    exact (hz (φ (ψ j))).trans (hb (φ (ψ j)) _ hj b hbG)
  have := ge_of_tendsto ht hone
  norm_num at this
end SharpNodal.Geometry

noncomputable section
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
lemma exists_additive_harnack (x : M) :
    ∃G : Set M,IsOpen G ∧ x ∈ G ∧ ∃D : ℝ,0 ≤ D ∧
      ∀K : ℝ,∀u : M → ℝ,NormalizedEigen K u →
      ∀y ∈ G,∀z ∈ G,1-u y ≤ 16*(1-u z)+D*K^2 := by
  obtain ⟨e,hxe,he⟩:=exists_isothermal_chart x
  have hy:=e.map_source hxe
  obtain ⟨r,Cp,hr,hCp,hclose,-,hpbound,-⟩:=he.exists_profile_ball hy
  obtain ⟨B,hB,hBb⟩:=additive_harnack_unit
  let s:=r/4
  have hs : 0 < s:=by dsimp [s]; positivity
  let F:=rescaleMap (e x) s
  have hFmap : MapsTo F (ball 0 3) (ball (e x) r) := by
    intro z hz
    change dist (e x+s • z) (e x) < r
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    have hz':=mem_ball_zero_iff.mp hz
    dsimp [s]; nlinarith
  have hFe : MapsTo F (ball 0 3) e.target:=fun z hz=>hclose (ball_subset_closedBall (hFmap hz))
  let G:=e.source∩e ⁻¹' ball (e x) (s/2)
  have hs2 : 0 < s/2:=by positivity
  refine ⟨G,e.isOpen_inter_preimage isOpen_ball,⟨hxe,mem_ball_self hs2⟩,B*s^2*Cp,by positivity,?_⟩
  intro K u hu y hyG z hzG
  let U:=u∘e.symm
  let V:=U∘F
  let q:=fun w=>s^2*K^2*conformalFactor e (F w)
  obtain ⟨hU,hUE⟩:=he.eigenfunction hu.smooth hu.equation
  have hV : ContDiffOn ℝ ∞ V (ball 0 3):=hU.comp (smooth_rescaleMap (e x) s).contDiffOn hFe
  have hq : ContDiffOn ℝ ∞ q (ball 0 3):=contDiffOn_const.mul (he.factor_smooth.comp (smooth_rescaleMap (e x) s).contDiffOn hFe)
  have hVE : ∀w ∈ ball (0:Plane) 3,euclideanLaplacian V w+q w*V w=0 := by
    intro w hw
    rw [laplacian_rescale_local e.open_target hU (e x) s w (hFe hw)]
    have hh:=hUE _ (hFe hw)
    dsimp [V,U,q,F] at *; nlinarith only [hh]
  have hVb : ∀w ∈ ball (0:Plane) 3,|V w| ≤ 1:=fun w _=>hu.bound _
  have hqb : ∀w ∈ ball (0:Plane) 3,|q w| ≤ s^2*K^2*Cp := by
    intro w hw
    dsimp [q]
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ s^2*K^2)]
    exact mul_le_mul_of_nonneg_left (hpbound _ (hFmap hw)) (by positivity)
  let Y:=s⁻¹ • (e y-e x)
  let Z:=s⁻¹ • (e z-e x)
  have hpoint {a : M} (ha:a ∈ G) : s⁻¹ • (e a-e x) ∈ ball (0:Plane) (1/2) := by
    rw [mem_ball_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
    have hh:=ha.2
    rw [mem_preimage,mem_ball,dist_eq_norm] at hh
    exact (inv_mul_lt_iff₀ hs).mpr (by nlinarith)
  have hvalue {a : M} (ha : a ∈ G) : V (s⁻¹ • (e a-e x))=u a := by
    dsimp [V,U,F,rescaleMap]
    rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul,add_sub_cancel,e.left_inv ha.1]
  have hh:=hBb V q hV hq hVE hVb _ (by positivity : 0 ≤ s^2*K^2*Cp) hqb Y (hpoint hyG) Z (hpoint hzG)
  rw [show V Y=u y from hvalue hyG,show V Z=u z from hvalue hzG] at hh
  nlinarith only [hh]

lemma normalized_frequency_gap_oai [CompactSpace M] [ConnectedSpace M] :
    ∃k₀ : ℝ,0 < k₀ ∧ ∀K : ℝ,0 < K → ∀u : M → ℝ,NormalizedEigen K u → k₀ ≤ K := by
  by_contra hn
  push Not at hn
  have hf (j : ℕ):=hn ((j+1:ℝ)⁻¹) (by positivity)
  choose K hK u hu hKsmall using hf
  have hkt : Tendsto K atTop (𝓝 0) := by
    apply squeeze_zero (fun j=>(hK j).le) (fun j=>(hKsmall j).le)
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun _=>le_add_of_nonneg_right (by norm_num)) tendsto_natCast_atTop_atTop)
  have hchoose (j : ℕ) : ∃v : M → ℝ,NormalizedEigen (K j) v ∧ (∃x,v x=1) ∧ ∃x,v x ≤ 0 := by
    obtain ⟨x,hx⟩:=(hu j).maximum
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hx with hx|hx
    · exact ⟨u j,hu j,⟨x,hx⟩,(hu j).exists_nonpos (hK j)⟩
    · refine ⟨fun y=> -u j y,(hu j).neg,⟨x,by linarith⟩,(hu j).neg.exists_nonpos (hK j)⟩
  choose v hv hvmax hvmin using hchoose
  apply no_low_energy_sequence (v:=fun j x=>1-v j x) (ε:=fun j=>(K j)^2)
  · simpa only [zero_pow (by decide : (2:ℕ)≠0)] using hkt.pow 2
  · intro j x; linarith [(le_abs_self (v j x)).trans ((hv j).bound x)]
  · intro j; obtain ⟨x,hx⟩:=hvmax j; exact ⟨x,by linarith⟩
  · intro j; obtain ⟨x,hx⟩:=hvmin j; exact ⟨x,by linarith⟩
  · intro x
    obtain ⟨G,hG,hx,D,hD,hDb⟩:=exists_additive_harnack x
    exact ⟨G,hG,hx,D,hD,fun j=>hDb (K j) (v j) (hv j)⟩
end SharpNodal.Geometry

end
end
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpNodal.Geometry.normalized_frequency_gap_oai.{u_1} := @OAI.SharpNodal.Geometry.normalized_frequency_gap_oai.{u_1}
