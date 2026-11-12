-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SurfacePairTranslationPatch.regularize_avoiding_points
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:11:01.605615+00:00
-- url     : https://prove2.me/submissions/def269c5-0e57-4332-b1c3-0e0a5d6f7e10

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI004
import Definitions.Def_OAIQ249SI005

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_OneFiberAugmentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A surjective linear map with a one-dimensional kernel admits one
additional linear coordinate with invertible derivative. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem one_fiber_linear_augmentation (hdimEF : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    (K : E →L[ℝ] F)
    (hK : Function.Surjective K) :
    ∃ ℓ : E →L[ℝ] ℝ, Function.Bijective (K.prod ℓ) := by
  have hdim : Module.finrank ℝ K.ker = 1 := by
    have h := K.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hK,finrank_top] at h
    omega
  let e : K.ker ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)
  obtain ⟨P,hP⟩ := K.ker.exists_isCompl
  let π : E →L[ℝ] K.ker := (K.ker.projectionOnto P hP).toContinuousLinearMap
  let ℓ : E →L[ℝ] ℝ := e.toContinuousLinearMap.comp π
  have hzero (x : E) (hx : K x = 0) (hℓ : ℓ x = 0) : x = 0 := by
    have hmem : x ∈ K.ker := hx
    have hπ : π x = ⟨x,hmem⟩ := by
      exact Submodule.projectionOnto_apply_of_mem_left hP hmem
    have he : e (⟨x,hmem⟩ : K.ker) = e 0 := by
      simpa only [ℓ,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,hπ,map_zero] using hℓ
    exact congrArg Subtype.val (e.injective he)
  have hi : Function.Injective (K.prod ℓ) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    · rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.fst hxy)
    · rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.snd hxy)
  refine ⟨ℓ,hi,?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (K.prod ℓ).toLinearMap) _).mp hi
  simpa using hdimEF

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_OneFiberChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth submersion coordinates with one-dimensional fibers. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem one_fiber_submersion_chart (hdimEF : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    {f : E → F}
    (hf : ContDiff ℝ ∞ f) (p : E)
    (hsurj : Function.Surjective (fderiv ℝ f p)) :
    ∃ e : OpenPartialHomeomorph E (F × ℝ), p ∈ e.source ∧
      (∀ x, (e x).1 = f x) ∧ ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨ℓ,hℓ⟩ := one_fiber_linear_augmentation hdimEF (fderiv ℝ f p) hsurj
  let L := ContinuousLinearEquiv.ofBijective ((fderiv ℝ f p).prod ℓ)
    (LinearMap.ker_eq_bot.mpr hℓ.1) (LinearMap.range_eq_top.mpr hℓ.2)
  let g : E → F × ℝ := fun x => (f x,ℓ x)
  have hg : ContDiff ℝ ∞ g := hf.prodMk ℓ.contDiff
  have hd : HasFDerivAt g L.toContinuousLinearMap p :=
    (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt.prodMk ℓ.hasFDerivAt
  let e₀ := hg.contDiffAt.toOpenPartialHomeomorph g hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let W : Set E := {x | IsUnit (L.symm.toContinuousLinearMap.comp (fderiv ℝ g x))}
  have hcont : Continuous (fun x => L.symm.toContinuousLinearMap.comp (fderiv ℝ g x)) :=
    continuous_const.clm_comp (hg.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hW : IsOpen W := Units.isOpen.preimage hcont
  have hpW : p ∈ W := by
    change IsUnit (L.symm.toContinuousLinearMap.comp (fderiv ℝ g p))
    rw [hd.fderiv]
    have heq : L.symm.toContinuousLinearMap.comp L.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ E := by
      apply ContinuousLinearMap.ext
      intro v
      exact L.symm_apply_apply v
    rw [heq]
    exact isUnit_one
  let e := e₀.restrOpen W hW
  have he : (e : E → F × ℝ) = g := rfl
  refine ⟨e,⟨hg.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),hpW⟩,
    (fun _ => rfl),?_,?_⟩
  · simpa only [he] using hg
  · intro y hy
    have hunit : IsUnit (L.symm.toContinuousLinearMap.comp (fderiv ℝ g (e.symm y))) :=
      (e.map_target hy).2
    obtain ⟨u,hu⟩ := hunit
    let D := (ContinuousLinearEquiv.ofUnit u).trans L
    have heq : D.toContinuousLinearMap = fderiv ℝ g (e.symm y) := by
      apply ContinuousLinearMap.ext
      intro v
      change L ((u : E →L[ℝ] E) v) = _
      rw [hu]
      exact L.apply_symm_apply _
    have hdy : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
      rw [he,heq]
      exact (hg.differentiable (by simp) _).hasFDerivAt
    exact (e.contDiffAt_symm hy hdy (by rw [he]; exact hg.contDiffAt)).contDiffWithinAt

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ScalarCoordinateAugmentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A regular scalar function can be completed to local coordinates. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem scalar_coordinate_augmentation (hdimEF : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    (K : E →L[ℝ] ℝ)
    (hK : Function.Surjective K) :
    ∃ ℓ : E →L[ℝ] F, Function.Bijective (K.prod ℓ) := by
  have hdim : Module.finrank ℝ K.ker = Module.finrank ℝ F := by
    have h := K.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hK,finrank_top] at h
    simp only [Module.finrank_self] at h
    omega
  let e : K.ker ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)
  obtain ⟨P,hP⟩ := K.ker.exists_isCompl
  let π : E →L[ℝ] K.ker := (K.ker.projectionOnto P hP).toContinuousLinearMap
  let ℓ : E →L[ℝ] F := e.toContinuousLinearMap.comp π
  have hzero (x : E) (hx : K x = 0) (hℓ : ℓ x = 0) : x = 0 := by
    have hmem : x ∈ K.ker := hx
    have hπ : π x = ⟨x,hmem⟩ := by
      exact Submodule.projectionOnto_apply_of_mem_left hP hmem
    have he : e (⟨x,hmem⟩ : K.ker) = e 0 := by
      simpa only [ℓ,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,hπ,map_zero] using hℓ
    exact congrArg Subtype.val (e.injective he)
  have hi : Function.Injective (K.prod ℓ) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    · rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.fst hxy)
    · rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.snd hxy)
  refine ⟨ℓ,hi,?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (K.prod ℓ).toLinearMap) _).mp hi
  simpa [add_comm] using hdimEF

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ScalarSubmersionChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar submersion coordinates in the dimensions needed for Sard reduction. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem scalar_submersion_chart (hdimEF : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (p : E)
    (hsurj : Function.Surjective (fderiv ℝ f p)) :
    ∃ e : OpenPartialHomeomorph E (ℝ × F), p ∈ e.source ∧
      (∀ x, (e x).1 = f x) ∧ ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨ℓ,hℓ⟩ := scalar_coordinate_augmentation hdimEF (fderiv ℝ f p) hsurj
  let L := ContinuousLinearEquiv.ofBijective ((fderiv ℝ f p).prod ℓ)
    (LinearMap.ker_eq_bot.mpr hℓ.1) (LinearMap.range_eq_top.mpr hℓ.2)
  let g : E → ℝ × F := fun x => (f x,ℓ x)
  have hg : ContDiff ℝ ∞ g := hf.prodMk ℓ.contDiff
  have hd : HasFDerivAt g L.toContinuousLinearMap p :=
    (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt.prodMk ℓ.hasFDerivAt
  let e₀ := hg.contDiffAt.toOpenPartialHomeomorph g hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let W : Set E := {x | IsUnit (L.symm.toContinuousLinearMap.comp (fderiv ℝ g x))}
  have hcont : Continuous (fun x => L.symm.toContinuousLinearMap.comp (fderiv ℝ g x)) :=
    continuous_const.clm_comp (hg.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hW : IsOpen W := Units.isOpen.preimage hcont
  have hpW : p ∈ W := by
    change IsUnit (L.symm.toContinuousLinearMap.comp (fderiv ℝ g p))
    rw [hd.fderiv]
    have heq : L.symm.toContinuousLinearMap.comp L.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ E := by
      apply ContinuousLinearMap.ext
      intro v
      exact L.symm_apply_apply v
    rw [heq]
    exact isUnit_one
  let e := e₀.restrOpen W hW
  have he : (e : E → ℝ × F) = g := rfl
  refine ⟨e,⟨hg.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),hpW⟩,
    (fun _ => rfl),?_,?_⟩
  · simpa only [he] using hg
  · intro y hy
    have hunit : IsUnit (L.symm.toContinuousLinearMap.comp (fderiv ℝ g (e.symm y))) :=
      (e.map_target hy).2
    obtain ⟨u,hu⟩ := hunit
    let D := (ContinuousLinearEquiv.ofUnit u).trans L
    have heq : D.toContinuousLinearMap = fderiv ℝ g (e.symm y) := by
      apply ContinuousLinearMap.ext
      intro v
      change L ((u : E →L[ℝ] E) v) = _
      rw [hu]
      exact L.apply_symm_apply _
    have hdy : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
      rw [he,heq]
      exact (hg.differentiable (by simp) _).hasFDerivAt
    exact (e.contDiffAt_symm hy hdy (by rw [he]; exact hg.contDiffAt)).contDiffWithinAt

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScalarFlatTaylor
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A cubic remainder estimate at a scalar flat second jet. This is the
low-dimensional flat-stratum estimate needed for double-locus regularity. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.scalarFirstNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.scalarFirstSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.scalarSecondNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.scalarSecondSpace
local instance scalarThirdNormed_r22319f_1 : NormedAddCommGroup (Base →L[ℝ] Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
local instance scalarThirdSpace_r22319f_1 : NormedSpace ℝ (Base →L[ℝ] Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
lemma scalar_flat_cubic_bound {f : Base → ℝ} (hf : ContDiff ℝ ∞ f)
    (x y : Base) (hfirst : fderiv ℝ f x = 0)
    (hsecond : fderiv ℝ (fderiv ℝ f) x = 0) {M : ℝ} (hM : 0 ≤ M)
    (hthird : ∀ z ∈ closedBall x ‖y-x‖,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ ≤ M) :
    ‖f y-f x‖ ≤ M*‖y-x‖^3 := by
  let d := ‖y-x‖
  have hd : 0 ≤ d := norm_nonneg _
  let B := closedBall x d
  have hx : x ∈ B := mem_closedBall_self hd
  have hy : y ∈ B := by simp only [B,d,mem_closedBall,dist_eq_norm,le_refl]
  have hD := hf.fderiv_right (m := ∞) (by simp)
  have hDD := hD.fderiv_right (m := ∞) (by simp)
  have hsecond_bound (z : Base) (hz : z ∈ B) :
      ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M*d := by
    have h := (convex_closedBall x d).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => hDD.differentiable (by simp) w) hthird hx hz
    rw [hsecond,sub_zero] at h
    apply h.trans
    exact mul_le_mul_of_nonneg_left (mem_closedBall.mp hz) hM
  have hfirst_bound (z : Base) (hz : z ∈ B) : ‖fderiv ℝ f z‖ ≤ (M*d)*d := by
    have h := (convex_closedBall x d).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => hD.differentiable (by simp) w) hsecond_bound hx hz
    rw [hfirst,sub_zero] at h
    apply h.trans
    exact mul_le_mul_of_nonneg_left (mem_closedBall.mp hz) (mul_nonneg hM hd)
  have h := (convex_closedBall x d).norm_image_sub_le_of_norm_fderiv_le
    (fun w _ => hf.differentiable (by simp) w) hfirst_bound hx hy
  calc
    _ ≤ (M*d*d)*‖y-x‖ := h
    _ = M*‖y-x‖^3 := by dsimp [d] <;> ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScalarFlatHolder
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flat second-jet stratum of a smooth scalar surface function has
locally cubic Hölder control. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology NNReal ENNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.holderFirstNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.holderFirstSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.holderSecondNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.holderSecondSpace
local instance holderThirdNormed_r22319f_1 : NormedAddCommGroup (Base →L[ℝ] Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
local instance holderThirdSpace_r22319f_1 : NormedSpace ℝ (Base →L[ℝ] Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
theorem scalarFlatTwo_local_holder {f : Base → ℝ} (hf : ContDiff ℝ ∞ f) (p : Base) :
    ∃ C : ℝ≥0, HolderOnWith C 3 f (scalarFlatTwo f ∩ ball p (1/4)) := by
  have hD := hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hDD := hD.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hc := hDD.continuous_fderiv (by simp)
  obtain ⟨M,hM⟩ := (isCompact_closedBall p 1).exists_bound_of_continuousOn hc.continuousOn
  let C : ℝ≥0 := ⟨max M 0,le_max_right _ _⟩
  refine ⟨C,?_⟩
  intro x hx y hy
  have hsub : closedBall y ‖x-y‖ ⊆ closedBall p 1 := by
    intro z hz
    have hzp := dist_triangle z y p
    have hxy := dist_triangle x p y
    have hz' : dist z y ≤ dist x y := by simpa only [mem_closedBall,dist_eq_norm] using hz
    have hxp : dist x p < 1/4 := hx.2
    have hyp : dist y p < 1/4 := hy.2
    rw [dist_comm p y] at hxy
    change dist z p ≤ 1
    linarith
  have hbound : ‖f x-f y‖ ≤ (C:ℝ)*‖x-y‖^3 :=
    scalar_flat_cubic_bound hf y x hy.1.1 hy.1.2 C.2 (fun z hz =>
      (hM z (hsub hz)).trans (le_max_left _ _))
  change edist (f x) (f y) ≤ (C : ℝ≥0∞)*edist x y ^ (3 : ℝ)
  rw [edist_dist,edist_dist,show (3 : ℝ) = (3 : ℕ) by norm_num,ENNReal.rpow_natCast]
  have he := ENNReal.ofReal_le_ofReal hbound
  rw [ENNReal.ofReal_mul (p := (C:ℝ)) C.2,
    ENNReal.ofReal_pow (norm_nonneg (x-y)) 3,ENNReal.ofReal_coe_nnreal] at he
  simpa only [dist_eq_norm] using he

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScalarFlatCriticalValues
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The image of the flat second-jet stratum of a smooth scalar surface
function is null. No Sard hypothesis is used. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology NNReal ENNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem scalarFlatTwo_image_dimH {f : Base → ℝ} (hf : ContDiff ℝ ∞ f) :
    dimH (f '' scalarFlatTwo f) ≤ (2 : ℝ≥0∞)/3 := by
  have hholder : dimH (f '' scalarFlatTwo f) ≤ dimH (scalarFlatTwo f)/(3 : ℝ≥0∞) := by
    apply dimH_image_le_of_locally_holder_on (by norm_num : (0 : ℝ≥0) < 3)
    intro p hp
    obtain ⟨C,hC⟩ := scalarFlatTwo_local_holder hf p
    refine ⟨C,scalarFlatTwo f ∩ ball p (1/4),?_,hC⟩
    exact inter_mem_nhdsWithin _ (ball_mem_nhds _ (by norm_num))
  have hdim : dimH (scalarFlatTwo f) ≤ (2 : ℝ≥0∞) := by
    have h := dimH_mono (subset_univ (scalarFlatTwo f))
    simpa [Base,Real.dimH_univ_pi_fin] using h
  exact hholder.trans (ENNReal.div_le_div_right hdim _)

theorem scalarFlatTwo_image_volume_zero {f : Base → ℝ} (hf : ContDiff ℝ ∞ f) :
    volume (f '' scalarFlatTwo f) = 0 := by
  have hd : dimH (f '' scalarFlatTwo f) < (1 : ℝ≥0∞) :=
    (scalarFlatTwo_image_dimH hf).trans_lt (by
      rw [ENNReal.div_lt_iff (Or.inl (by norm_num : (3 : ℝ≥0∞) ≠ 0)) (Or.inl (by simp))]
      norm_num)
  have hm := hausdorffMeasure_of_dimH_lt (d := (1 : ℝ≥0)) hd
  simpa using hm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalNullImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local null-image statements glue over a second countable domain. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem null_image_of_locally_null {X Y : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace Y] (μ : Measure Y)
    (f : X → Y) (s : Set X)
    (h : ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ μ (f '' (s ∩ U)) = 0) :
    μ (f '' s) = 0 := by
  choose U ho hm hn using fun x : s => h x x.property
  have hcover : s ⊆ ⋃ x : s, U x := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hm ⟨x,hx⟩⟩
  obtain ⟨A,hAc,hA⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover U ho hcover
  have hsub : f '' s ⊆ ⋃ x ∈ A, f '' (s ∩ U x) := by
    rintro y ⟨x,hx,rfl⟩
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hA hx)
    exact mem_iUnion₂.mpr ⟨i,hi,⟨x,⟨hx,hxi⟩,rfl⟩⟩
  exact measure_mono_null hsub ((measure_biUnion_null_iff hAc).mpr fun x _ => hn x)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScalarCriticalCurve
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Near a nonzero derivative, the zero set is a curve. The critical
values of a scalar function restricted to this curve are null. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem scalar_critical_curve_local_null {f g : Base → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (p : Base)
    (hdg : fderiv ℝ g p ≠ 0) :
    ∃ U : Set Base, IsOpen U ∧ p ∈ U ∧
      volume (f '' ({x | fderiv ℝ f x = 0 ∧ g x = 0} ∩ U)) = 0 := by
  have hs : Function.Surjective (fderiv ℝ g p) :=
    surjective_of_nonzero_of_finrank_eq_one (by simp : Module.finrank ℝ ℝ = 1)
      (show (fderiv ℝ g p).toLinearMap ≠ 0 from fun h => hdg (by ext x; exact congrArg (fun L => L x) h))
  obtain ⟨e,hpe,he,hsm,hinv⟩ := one_fiber_submersion_chart (by simp [Base]) hg p hs
  let τ : ℝ → ℝ × ℝ := fun t => (0,t)
  have hτ : ContDiff ℝ ∞ τ := contDiff_const.prodMk contDiff_id
  let h : ℝ → ℝ := f ∘ e.symm ∘ τ
  let S : Set ℝ := {t | τ t ∈ e.target ∧ fderiv ℝ f (e.symm (τ t)) = 0}
  have hh (t : ℝ) (ht : t ∈ S) : HasFDerivAt h (0 : ℝ →L[ℝ] ℝ) t := by
    have hi : DifferentiableAt ℝ e.symm (τ t) :=
      (hinv.contDiffAt (e.open_target.mem_nhds ht.1)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hf0 : HasFDerivAt f (0 : Base →L[ℝ] ℝ) (e.symm (τ t)) := by
      simpa only [ht.2] using (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (e.symm (τ t))).hasFDerivAt
    simpa only [ContinuousLinearMap.zero_comp] using
      hf0.comp t (hi.hasFDerivAt.comp t (hτ.differentiable (by simp) t).hasFDerivAt)
  have hn : volume (h '' S) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun _ => (0 : ℝ →L[ℝ] ℝ))
      (fun t ht => (hh t ht).hasFDerivWithinAt) (by simp)
  refine ⟨e.source,e.open_source,hpe,measure_mono_null ?_ hn⟩
  rintro y ⟨x,⟨hx,hxe⟩,rfl⟩
  have ht : τ ((e x).2) = e x := by
    apply Prod.ext
    · exact (he x |>.trans hx.2).symm
    · rfl
  refine ⟨(e x).2,?_,?_⟩
  · change τ ((e x).2) ∈ e.target ∧ fderiv ℝ f (e.symm (τ ((e x).2))) = 0
    rw [ht,e.left_inv hxe]
    exact ⟨e.map_source hxe,hx.1⟩
  · change f (e.symm (τ ((e x).2))) = f x
    rw [ht,e.left_inv hxe]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScalarNonflatCriticalValues
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonflat critical scalar jets lie on regular level curves of a
first derivative; one-dimensional critical-value nullity applies. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

local instance nonflatFirstNormed_r22319f_1 : NormedAddCommGroup (Base →L[ℝ] ℝ) := inferInstance
local instance nonflatFirstSpace_r22319f_1 : NormedSpace ℝ (Base →L[ℝ] ℝ) := inferInstance
local instance nonflatSecondNormed_r22319f_1 : NormedAddCommGroup (Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
local instance nonflatSecondSpace_r22319f_1 : NormedSpace ℝ (Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
theorem scalar_nonflat_critical_image_null {f : Base → ℝ} (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x ≠ 0}) = 0 := by
  apply null_image_of_locally_null
  intro p hp
  have hD := hf.fderiv_right (m := ∞) (by simp)
  obtain ⟨v,hv⟩ := DFunLike.ne_iff.mp hp.2
  obtain ⟨w,hw⟩ := DFunLike.ne_iff.mp (show (fderiv ℝ (fderiv ℝ f) p) v ≠ 0 by simpa using hv)
  let g : Base → ℝ := fun x => fderiv ℝ f x w
  have hg : ContDiff ℝ ∞ g := hD.clm_apply contDiff_const
  have hdg : fderiv ℝ g p ≠ 0 := by
    intro hz
    have hd := ((hD.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt.clm_apply
      (hasFDerivAt_const w p)).fderiv
    have he := congrArg (fun L : Base →L[ℝ] ℝ => L v) (hz.symm.trans hd)
    apply hw
    simpa only [add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,zero_apply,map_zero,add_zero,zero_add] using he.symm
  obtain ⟨U,hU,hpU,hn⟩ := scalar_critical_curve_local_null hf hg p hdg
  refine ⟨U,hU,hpU,measure_mono_null (image_mono ?_) hn⟩
  rintro x ⟨hx,hxU⟩
  exact ⟨⟨hx.1,by simp [g,hx.1]⟩,hxU⟩

theorem scalar_surface_critical_values_null {f : Base → ℝ} (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | fderiv ℝ f x = 0}) = 0 := by
  have hsub : {x | fderiv ℝ f x = 0} ⊆ scalarFlatTwo f ∪
      {x | fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x ≠ 0} := by
    intro x hx
    by_cases h : fderiv ℝ (fderiv ℝ f) x = 0
    · exact Or.inl ⟨hx,h⟩
    · exact Or.inr ⟨hx,h⟩
  apply measure_mono_null (image_mono hsub)
  rw [image_union]
  exact measure_union_null (scalarFlatTwo_image_volume_zero hf)
    (scalar_nonflat_critical_image_null hf)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalSardTransfer
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A global critical-value theorem also applies to smooth maps on open
coordinate domains, by a compactly supported local extension. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F]

theorem local_critical_values_null (μ : Measure F)
    (hglobal : ∀ f : E → F, ContDiff ℝ ∞ f →
      μ (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0)
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    μ (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  apply null_image_of_locally_null
  intro p hp
  obtain ⟨W,hW,hpW,hWU,g,hg,hgf⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := p)) hU (singleton_subset_iff.mpr hp.1) hf
  refine ⟨W,hW,hpW (mem_singleton p),measure_mono_null ?_ (hglobal g hg)⟩
  rintro y ⟨x,⟨hx,hxW⟩,rfl⟩
  have he : g =ᶠ[𝓝 x] f := Filter.eventuallyEq_iff_exists_mem.mpr ⟨W,hW.mem_nhds hxW,hgf⟩
  refine ⟨x,?_,hgf hxW⟩
  change ¬ Function.Surjective (fderiv ℝ g x)
  rw [he.fderiv_eq (𝕜 := ℝ)]
  exact hx.2

theorem scalar_surface_local_critical_values_null {f : JetPolynomial.Base → ℝ}
    {U : Set JetPolynomial.Base} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    volume (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  apply local_critical_values_null volume ?_ hU hf
  intro g hg
  apply measure_mono_null (image_mono ?_) (scalar_surface_critical_values_null hg)
  intro x hx
  by_contra hn
  exact hx (surjective_of_nonzero_of_finrank_eq_one
    (by simp : Module.finrank ℝ ℝ = 1)
    (show (fderiv ℝ g x).toLinearMap ≠ 0 from fun h => hn (by ext v; exact congrArg (fun L => L v) h)))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SliceDerivativeSurjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Surjectivity in split coordinates is equivalent to surjectivity of
the vertical derivative when the first component is the first coordinate. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem split_linear_surjective {K : (ℝ × E) →L[ℝ] (ℝ × F)}
    (hfirst : ∀ v, (K v).1 = v.1)
    (hvert : Function.Surjective (fun v : E => (K (0,v)).2)) :
    Function.Surjective K := by
  rintro ⟨a,y⟩
  obtain ⟨v,hv⟩ := hvert (y-(K (a,0)).2)
  refine ⟨(a,v),?_⟩
  apply Prod.ext
  · exact hfirst _
  · have h := congrArg Prod.snd (map_add K (a,0) (0,v))
    simp only [Prod.mk_add_mk,add_zero,zero_add,Prod.snd_add] at h
    dsimp only at hv
    rw [h,hv]
    abel

theorem slice_derivative_not_surjective {f : (ℝ × E) → ℝ × F} {U : Set (ℝ × E)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hfirst : ∀ z ∈ U, (f z).1 = z.1) (a : ℝ) (x : E) (hx : (a,x) ∈ U)
    (hcrit : ¬ Function.Surjective (fderiv ℝ f (a,x))) :
    ¬ Function.Surjective (fderiv ℝ (fun y : E => (f (a,y)).2) x) := by
  have hfd := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : (fun z => (f z).1) =ᶠ[𝓝 (a,x)] Prod.fst :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U,hU.mem_nhds hx,hfirst⟩
  have he' : (ContinuousLinearMap.fst ℝ ℝ F).comp (fderiv ℝ f (a,x)) =
      ContinuousLinearMap.fst ℝ ℝ E := by
    rw [← fderiv.fst hfd,he.fderiv_eq (𝕜 := ℝ),fderiv_fst]
  have hpair : HasFDerivAt (fun y : E => (a,y)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
    (hasFDerivAt_const a x).prodMk (hasFDerivAt_id x)
  have hv := ((hfd.hasFDerivAt.comp x hpair).snd).fderiv
  dsimp only [Function.comp_def] at hv
  intro hs
  apply hcrit
  apply split_linear_surjective (fun v => congrArg (fun L : (ℝ × E) →L[ℝ] ℝ => L v) he')
  intro y
  obtain ⟨v,hv'⟩ := hs y
  refine ⟨v,?_⟩
  rw [hv] at hv'
  exact hv'

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SplitSardCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fiberwise Sard nullity gives null critical images for split maps,
first on compact sets so measurability follows directly from continuity. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasureSpace F] [BorelSpace F] [SFinite (volume : Measure F)]

theorem split_sard_compact
    (hsard : ∀ (g : E → F) (V : Set E), IsOpen V → ContDiffOn ℝ ∞ g V →
      volume (g '' {x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ g x)}) = 0)
    {f : (ℝ × E) → ℝ × F} {U K : Set (ℝ × E)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hfirst : ∀ z ∈ U, (f z).1 = z.1)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hcrit : ∀ z ∈ K, ¬ Function.Surjective (fderiv ℝ f z)) :
    volume (f '' K) = 0 := by
  have him : IsCompact (f '' K) := hK.image_of_continuousOn (hf.continuousOn.mono hKU)
  apply Measure.measure_prod_null_of_ae_null him.measurableSet
  filter_upwards [] with a
  let g : E → F := fun x => (f (a,x)).2
  let V : Set E := {x | (a,x) ∈ U}
  have hV : IsOpen V := hU.preimage (continuous_const.prodMk continuous_id)
  have hg : ContDiffOn ℝ ∞ g V :=
    (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hx => hx)).snd
  apply measure_mono_null _ (hsard g V hV hg)
  rintro y ⟨z,hz,heq⟩
  have ha : z.1 = a := (hfirst z (hKU hz)).symm.trans (congrArg Prod.fst heq)
  have hz' : z = (a,z.2) := by ext <;> simp [ha]
  refine ⟨z.2,⟨?_,?_⟩,?_⟩
  · change (a,z.2) ∈ U
    rw [← hz']
    exact hKU hz
  · apply slice_derivative_not_surjective hU hf hfirst a z.2
    · rw [← hz']; exact hKU hz
    · rw [← hz']; exact hcrit z hz
  · change (f (a,z.2)).2 = y
    rw [← hz']
    exact congrArg Prod.snd heq

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CriticalSetClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-dimensional critical loci are closed. This supplies compact
exhaustions for the fiberwise critical-value argument. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem surjective_clm_open : IsOpen {K : E →L[ℝ] F | Function.Surjective K} := by
  rw [isOpen_iff_mem_nhds]
  intro K hK
  obtain ⟨R,hR⟩ := K.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hK)
  let R' : F →L[ℝ] E := R.toContinuousLinearMap
  have hKR : K.comp R' = ContinuousLinearMap.id ℝ F := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun L : F →ₗ[ℝ] F => L x) hR
  have hc : Continuous (fun L : E →L[ℝ] F => L.comp R') := continuous_id.clm_comp continuous_const
  have hn : ∀ᶠ L in 𝓝 K, IsUnit (L.comp R') := by
    change (fun L : E →L[ℝ] F => L.comp R') ⁻¹' {A | IsUnit A} ∈ 𝓝 K
    apply hc.continuousAt.preimage_mem_nhds
    apply Units.isOpen.mem_nhds
    rw [hKR]
    exact isUnit_one
  filter_upwards [hn] with L hL
  obtain ⟨u,hu⟩ := hL
  intro y
  refine ⟨R' ((↑u⁻¹ : F →L[ℝ] F) y),?_⟩
  have hval : L (R' ((↑u⁻¹ : F →L[ℝ] F) y)) =
      (↑u : F →L[ℝ] F) ((↑u⁻¹ : F →L[ℝ] F) y) := by rw [hu]; rfl
  rw [hval]
  change ((u : F →L[ℝ] F) * (↑u⁻¹ : F →L[ℝ] F)) y = y
  simp

theorem smooth_critical_set_closed {f : E → F} (hf : ContDiff ℝ ∞ f) :
    IsClosed {x | ¬ Function.Surjective (fderiv ℝ f x)} :=
  (surjective_clm_open.preimage (hf.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))).isClosed_compl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_RegularCoordinateSard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonzero first coordinate of the derivative reduces the critical
value problem by one source and one target dimension. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasureSpace G] [BorelSpace G] [SFinite (volume : Measure G)]

theorem regular_coordinate_critical_local_null
    (hdim : Module.finrank ℝ E = Module.finrank ℝ H + 1)
    (hsard : ∀ (g : H → G) (V : Set H), IsOpen V → ContDiffOn ℝ ∞ g V →
      volume (g '' {x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ g x)}) = 0)
    {f : E → ℝ × G} (hf : ContDiff ℝ ∞ f) (p : E)
    (hn : fderiv ℝ (fun x => (f x).1) p ≠ 0) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      volume (f '' ({x | ¬ Function.Surjective (fderiv ℝ f x)} ∩ U)) = 0 := by
  have hs : Function.Surjective (fderiv ℝ (fun x => (f x).1) p) :=
    surjective_of_nonzero_of_finrank_eq_one (by simp : Module.finrank ℝ ℝ = 1)
      (show (fderiv ℝ (fun x => (f x).1) p).toLinearMap ≠ 0 from
        fun h => hn (by ext v; exact congrArg (fun L => L v) h))
  obtain ⟨e,hpe,he,hec,hei⟩ := scalar_submersion_chart hdim hf.fst p hs
  obtain ⟨r,hr,hrsub⟩ := nhds_basis_closedBall.mem_iff.mp (e.open_source.mem_nhds hpe)
  let C := {x | ¬ Function.Surjective (fderiv ℝ f x)}
  let K := C ∩ closedBall p r
  have hK : IsCompact K := (isCompact_closedBall p r).inter_left (smooth_critical_set_closed hf)
  let ψ : (ℝ × H) → ℝ × G := f ∘ e.symm
  have hψ : ContDiffOn ℝ ∞ ψ e.target := hf.comp_contDiffOn hei
  have hψfirst (z : ℝ × H) (hz : z ∈ e.target) : (ψ z).1 = z.1 := by
    change (f (e.symm z)).1 = z.1
    rw [← he,e.right_inv hz]
  have hKe : IsCompact (e '' K) := hK.image hec.continuous
  have hKeT : e '' K ⊆ e.target := by
    rintro z ⟨x,hx,rfl⟩
    exact e.map_source (hrsub hx.2)
  have hcrit (z : ℝ × H) (hz : z ∈ e '' K) :
      ¬ Function.Surjective (fderiv ℝ ψ z) := by
    rcases hz with ⟨x,hx,rfl⟩
    have hxS := hrsub hx.2
    have heinv := (hei.contDiffAt (e.open_target.mem_nhds (e.map_source hxS))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hd := ((hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (e.symm (e x))).hasFDerivAt.comp (e x) heinv.hasFDerivAt).fderiv
    rw [e.left_inv hxS] at hd
    intro hsurj
    apply hx.1
    intro y
    obtain ⟨v,hv⟩ := hsurj y
    rw [hd] at hv
    exact ⟨fderiv ℝ e.symm (e x) v,hv⟩
  have hnul : volume (ψ '' (e '' K)) = 0 :=
    split_sard_compact hsard e.open_target hψ hψfirst hKe hKeT hcrit
  have heq : ψ '' (e '' K) = f '' K := by
    rw [← image_comp]
    apply image_congr
    intro x hx
    exact congrArg f (e.left_inv (hrsub hx.2))
  rw [heq] at hnul
  refine ⟨ball p r,isOpen_ball,mem_ball_self hr,measure_mono_null (image_mono ?_) hnul⟩
  intro x hx
  exact ⟨hx.1,ball_subset_closedBall hx.2⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TargetCoordinateChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonzero derivative has a nonzero scalar target coordinate, which
can be completed to a linear isomorphism of the target. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

theorem target_coordinate_choice (hdim : Module.finrank ℝ F = Module.finrank ℝ G + 1)
    (D : E →L[ℝ] F) (hD : D ≠ 0) :
    ∃ e : F ≃L[ℝ] (ℝ × G), (ContinuousLinearMap.fst ℝ ℝ G).comp
      (e.toContinuousLinearMap.comp D) ≠ 0 := by
  obtain ⟨v,hv⟩ := DFunLike.ne_iff.mp hD
  obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_eq_one ℝ (show D v ≠ 0 by simpa using hv)
  let L : F →L[ℝ] ℝ := ℓ.toContinuousLinearMap
  have hL : Function.Surjective L := by
    intro t
    refine ⟨t • D v,?_⟩
    change ℓ (t • D v) = t
    rw [map_smul,hℓ,smul_eq_mul,mul_one]
  obtain ⟨R,hR⟩ := scalar_coordinate_augmentation hdim L hL
  let e := ContinuousLinearEquiv.ofBijective (L.prod R)
    (LinearMap.ker_eq_bot.mpr hR.1) (LinearMap.range_eq_top.mpr hR.2)
  refine ⟨e,?_⟩
  intro hzero
  have hh := congrArg (fun A : E →L[ℝ] ℝ => A v) hzero
  change L (D v) = 0 at hh
  have hh' : L (D v) = 1 := hℓ
  linarith

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FlatFirstHolder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic control on the rank-zero stratum. In dimensions three to
 two and four to three it makes the critical image Hausdorff-null. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology NNReal ENNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.flatFirstNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.flatFirstSpace
local instance flatSecondNormed_r22319f_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance flatSecondSpace_r22319f_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
omit [FiniteDimensional ℝ E] in
lemma flat_first_quadratic_bound {f : E → F} (hf : ContDiff ℝ ∞ f)
    (x y : E) (hfirst : fderiv ℝ f x = 0) {M : ℝ} (hM : 0 ≤ M)
    (hsecond : ∀ z ∈ closedBall x ‖y-x‖, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M) :
    ‖f y-f x‖ ≤ M*‖y-x‖^2 := by
  let d := ‖y-x‖
  have hd : 0 ≤ d := norm_nonneg _
  let B := closedBall x d
  have hx : x ∈ B := mem_closedBall_self hd
  have hy : y ∈ B := by simp only [B,d,mem_closedBall,dist_eq_norm,le_refl]
  have hD := hf.fderiv_right (m := ∞) (by simp)
  have hfirst_bound (z : E) (hz : z ∈ B) : ‖fderiv ℝ f z‖ ≤ M*d := by
    have h := (convex_closedBall x d).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => hD.differentiable (by simp) w) hsecond hx hz
    rw [hfirst,sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using (mem_closedBall.mp hz)) hM)
  have h := (convex_closedBall x d).norm_image_sub_le_of_norm_fderiv_le
    (fun w _ => hf.differentiable (by simp) w) hfirst_bound hx hy
  calc
    _ ≤ (M*d)*‖y-x‖ := h
    _ = M*‖y-x‖^2 := by dsimp [d] <;> ring

theorem flat_first_local_holder {f : E → F} (hf : ContDiff ℝ ∞ f) (p : E) :
    ∃ C : ℝ≥0, HolderOnWith C 2 f ({x | fderiv ℝ f x = 0} ∩ ball p (1/4)) := by
  have hD := hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hc := hD.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨M,hM⟩ := (isCompact_closedBall p 1).exists_bound_of_continuousOn hc.continuousOn
  let C : ℝ≥0 := ⟨max M 0,le_max_right _ _⟩
  refine ⟨C,?_⟩
  intro x hx y hy
  have hsub : closedBall y ‖x-y‖ ⊆ closedBall p 1 := by
    intro z hz
    have hzp := dist_triangle z y p
    have hxy := dist_triangle x p y
    have hz' : dist z y ≤ dist x y := by simpa only [mem_closedBall,dist_eq_norm] using hz
    have hxp : dist x p < 1/4 := hx.2
    have hyp : dist y p < 1/4 := hy.2
    rw [dist_comm p y] at hxy
    change dist z p ≤ 1
    linarith
  have hbound : ‖f x-f y‖ ≤ (C:ℝ)*‖x-y‖^2 :=
    flat_first_quadratic_bound hf y x hy.1 C.2 (fun z hz =>
      (hM z (hsub hz)).trans (le_max_left _ _))
  change edist (f x) (f y) ≤ (C : ℝ≥0∞)*edist x y ^ (2 : ℝ)
  rw [edist_dist,edist_dist,show (2 : ℝ) = (2 : ℕ) by norm_num,ENNReal.rpow_natCast]
  have he := ENNReal.ofReal_le_ofReal hbound
  rw [ENNReal.ofReal_mul (p := (C:ℝ)) C.2,
    ENNReal.ofReal_pow (norm_nonneg (x-y)) 2,ENNReal.ofReal_coe_nnreal] at he
  simpa only [dist_eq_norm] using he

theorem flat_first_image_dimH {f : E → F} (hf : ContDiff ℝ ∞ f) :
    dimH (f '' {x | fderiv ℝ f x = 0}) ≤ (Module.finrank ℝ E : ℝ≥0∞)/2 := by
  have hholder : dimH (f '' {x | fderiv ℝ f x = 0}) ≤
      dimH {x | fderiv ℝ f x = 0}/(2 : ℝ≥0∞) := by
    apply dimH_image_le_of_locally_holder_on (by norm_num : (0 : ℝ≥0) < 2)
    intro p hp
    obtain ⟨C,hC⟩ := flat_first_local_holder hf p
    exact ⟨C,_,inter_mem_nhdsWithin _ (ball_mem_nhds _ (by norm_num)),hC⟩
  have hdim : dimH {x | fderiv ℝ f x = 0} ≤ (Module.finrank ℝ E : ℝ≥0∞) := by
    exact (dimH_mono (subset_univ _)).trans_eq (Real.dimH_univ_eq_finrank E)
  exact hholder.trans (ENNReal.div_le_div_right hdim _)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FlatFirstNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rank-zero stratum is null when half the domain dimension is
strictly below the target dimension. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology ENNReal NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem flat_first_image_null (μ : Measure F) [Measure.IsAddHaarMeasure μ]
    {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hdim : (Module.finrank ℝ E : ℝ≥0∞)/2 < Module.finrank ℝ F) :
    μ (f '' {x | fderiv ℝ f x = 0}) = 0 := by
  let : SecondCountableTopology F := inferInstance
  let : LocallyCompactSpace F := inferInstance
  let : SigmaFinite μ := inferInstance
  have hd : dimH (f '' {x | fderiv ℝ f x = 0}) < Module.finrank ℝ F :=
    (flat_first_image_dimH hf).trans_lt hdim
  have hd' : dimH (f '' {x | fderiv ℝ f x = 0}) <
      ((Module.finrank ℝ F : ℝ≥0) : ℝ≥0∞) := by
    simpa only [ENNReal.coe_natCast] using hd
  have hh' := hausdorffMeasure_of_dimH_lt (d := (Module.finrank ℝ F : ℝ≥0)) hd'
  have hh : μH[(Module.finrank ℝ F : ℝ)] (f '' {x | fderiv ℝ f x = 0}) = 0 := by
    simpa only [NNReal.coe_natCast] using hh'
  have hμ : μ ≪ (μH[(Module.finrank ℝ F : ℝ)] : Measure F) :=
    Measure.absolutelyContinuous_isAddHaarMeasure μ (μH[(Module.finrank ℝ F : ℝ)] : Measure F)
  exact hμ hh

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LinearEquivNullImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear coordinate changes preserve null sets, including between the
finite-dimensional models used in the Sard argument. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]

theorem linear_equiv_null_image (e : E ≃L[ℝ] F)
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (ν : Measure F) [Measure.IsAddHaarMeasure ν]
    {s : Set E} (hs : μ s = 0) : ν (e '' s) = 0 := by
  have hm : ν.map e.symm ≪ μ :=
    Measure.absolutelyContinuous_isAddHaarMeasure (ν.map e.symm) μ
  have hz := hm hs
  have he : MeasurableEmbedding (e.symm : F → E) := e.symm.toHomeomorph.measurableEmbedding
  rw [he.map_apply] at hz
  simpa only [e.image_eq_preimage_symm] using hz

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SardDimensionStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The single dimension-reduction step needed to pass from the proved
scalar surface Sard statement to the three- and four-dimensional pair
charts. All hypotheses of the lower-dimensional statement are explicit. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E H F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [MeasureSpace G] [BorelSpace G] [Measure.IsAddHaarMeasure (volume : Measure G)]

theorem sard_dimension_step
    (hdomain : Module.finrank ℝ E = Module.finrank ℝ H + 1)
    (htarget : Module.finrank ℝ F = Module.finrank ℝ G + 1)
    (hsmall : (Module.finrank ℝ E : ℝ≥0∞)/2 < Module.finrank ℝ F)
    (hsard : ∀ (g : H → G) (V : Set H), IsOpen V → ContDiffOn ℝ ∞ g V →
      volume (g '' {x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ g x)}) = 0)
    {f : E → F} (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  let C : Set E := {x | ¬ Function.Surjective (fderiv ℝ f x) ∧ fderiv ℝ f x ≠ 0}
  have hC : volume (f '' C) = 0 := by
    apply null_image_of_locally_null
    intro p hp
    obtain ⟨e,he⟩ := target_coordinate_choice htarget (fderiv ℝ f p) hp.2
    let g : E → ℝ × G := e ∘ f
    have hg : ContDiff ℝ ∞ g := e.contDiff.comp hf
    have hd (x : E) : fderiv ℝ g x = e.toContinuousLinearMap.comp (fderiv ℝ f x) :=
      (e.hasFDerivAt.comp x (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasFDerivAt).fderiv
    have hgp : fderiv ℝ (fun x => (g x).1) p ≠ 0 := by
      rw [fderiv.fst (hg.differentiable (by simp) p),hd]
      exact he
    obtain ⟨U,hU,hpU,hnull⟩ := regular_coordinate_critical_local_null hdomain hsard hg p hgp
    have hbad (x : E) (hx : ¬ Function.Surjective (fderiv ℝ f x)) :
        ¬ Function.Surjective (fderiv ℝ g x) := by
      intro hs
      apply hx
      intro y
      obtain ⟨v,hv⟩ := hs (e y)
      rw [hd] at hv
      exact ⟨v,e.injective hv⟩
    have him : volume (e '' (f '' (C ∩ U))) = 0 := by
      apply measure_mono_null _ hnull
      rintro y ⟨z,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨x,⟨hbad x hx.1.1,hx.2⟩,rfl⟩
    refine ⟨U,hU,hpU,?_⟩
    let : Measure.IsAddHaarMeasure (volume : Measure (ℝ × G)) := by
      change Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure G))
      exact Measure.prod.instIsAddHaarMeasure _ _
    have hh := linear_equiv_null_image e.symm (volume : Measure (ℝ × G)) (volume : Measure F) him
    simpa only [e.symm_image_image] using hh
  have hzero := flat_first_image_null volume hf hsmall
  apply measure_mono_null (image_mono (show {x | ¬ Function.Surjective (fderiv ℝ f x)} ⊆
      {x | fderiv ℝ f x = 0} ∪ C from ?_))
  · rw [image_union]
    exact measure_union_null hzero hC
  · intro x hx
    by_cases h : fderiv ℝ f x = 0
    · exact Or.inl h
    · exact Or.inr ⟨hx,h⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PairChartSard
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precise one-excess-dimension Sard instances for global double
curves: three to two, then four to three. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem three_two_critical_values_null {f : (Fin 3 → ℝ) → ℝ × ℝ}
    (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  apply sard_dimension_step (H := Base) (G := ℝ) (by simp [Base]) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) ?_
    (fun _ _ hV hg => scalar_surface_local_critical_values_null hV hg) hf
  simp only [Module.finrank_fin_fun,Module.finrank_prod,Module.finrank_self]
  norm_num only [Nat.cast_add,Nat.cast_one]
  rw [ENNReal.div_lt_iff (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0)) (Or.inl (by simp))]
  norm_num

theorem three_two_local_critical_values_null {f : (Fin 3 → ℝ) → ℝ × ℝ}
    {U : Set (Fin 3 → ℝ)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    volume (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 :=
  local_critical_values_null volume (fun _ hf => three_two_critical_values_null hf) hU hf

theorem pair_chart_critical_values_null {f : (Base × Base) → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  apply sard_dimension_step (H := Fin 3 → ℝ) (G := ℝ × ℝ)
    (by simp [Base]) (by simp [ProjectionTarget]) ?_
    (fun _ _ hV hg => three_two_local_critical_values_null hV hg) hf
  have hE : Module.finrank ℝ (Base × Base) = 4 := by simp [Base]
  have hF : Module.finrank ℝ (ProjectionTarget 3) = 3 := by simp [ProjectionTarget]
  rw [hE,hF]
  rw [ENNReal.div_lt_iff (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0)) (Or.inl (by simp))]
  norm_num

theorem pair_chart_local_critical_values_null {f : (Base × Base) → ProjectionTarget 3}
    {U : Set (Base × Base)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    volume (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 :=
  local_critical_values_null volume (fun _ hf => pair_chart_critical_values_null hf) hU hf

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowerDimensionalImage
attribute [-simp] _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_one _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The triple-radius exceptional set is null. Extend a map from two to
three coordinates constantly in the final coordinate and apply the proved
fixed-dimensional Jacobian null-image theorem. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace ClosedSurfaceR4.PublishedInputs

local instance tripleVolumeHaar : (volume : Measure (Plane × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem smooth_surface_image_volume_zero (f : Plane → Plane × ℝ)
    (hf : ContDiff ℝ ∞ f) : volume (Set.range f) = 0 := by
  let g : Plane × ℝ → Plane × ℝ := fun x => f x.1
  have hg : ContDiff ℝ ∞ g := hf.comp contDiff_fst
  have hdet (x : Plane × ℝ) : LinearMap.det (fderiv ℝ g x).toLinearMap = 0 := by
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq, LinearMap.ker_eq_bot]
    intro hinj
    have hd : fderiv ℝ g x = (fderiv ℝ f x.1).comp (ContinuousLinearMap.fst ℝ Plane ℝ) := by
      change fderiv ℝ (f ∘ (Prod.fst : Plane × ℝ → Plane)) x = _
      rw [fderiv_comp x (hf.differentiable (by simp) x.1) differentiableAt_fst, fderiv_fst]
    have hzero : fderiv ℝ g x (0,1) = fderiv ℝ g x 0 := by
      rw [hd]
      simp
    have he := congrArg Prod.snd (hinj hzero)
    exact one_ne_zero he
  have hnull : volume (g '' (univ : Set (Plane × ℝ))) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun x => fderiv ℝ g x)
    · intro x _
      exact (hg.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt
    · intro x _
      exact hdet x
  have he : g '' (univ : Set (Plane × ℝ)) = Set.range f := by
    ext y
    constructor
    · rintro ⟨x,_,rfl⟩
      exact ⟨x.1,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨(x,0),mem_univ _,rfl⟩
  rwa [he] at hnull

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_EuclideanSurfaceImageNull
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_one _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth two-dimensional images in three-space are null, in the
actual coordinate models used by the surface perturbations. -/
noncomputable section
open Set MeasureTheory Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance instIsAddHaarMeasureProdPlaneRealVolume : (volume : Measure (Plane × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem euclidean_surface_image_null (f : Base → ProjectionTarget 3) (hf : ContDiff ℝ ∞ f) :
    volume (range f) = 0 := by
  let L : Plane ≃L[ℝ] Base := ContinuousLinearEquiv.ofFinrankEq (by simp [Base])
  let T : ProjectionTarget 3 ≃L[ℝ] Plane × ℝ := ContinuousLinearEquiv.ofFinrankEq (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hnull := PublishedInputs.smooth_surface_image_volume_zero (T ∘ f ∘ L)
    (T.contDiff.comp (hf.comp L.contDiff))
  have hnull' := linear_equiv_null_image T.symm volume volume hnull
  have he : T.symm '' range (T ∘ f ∘ L) = range f := by
    ext y
    constructor
    · rintro ⟨z,⟨x,rfl⟩,rfl⟩
      exact ⟨L x,by simp⟩
    · rintro ⟨x,rfl⟩
      exact ⟨T (f x),⟨L.symm x,by simp⟩,by simp⟩
  rwa [he] at hnull'

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RegularPairAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A regular translation can simultaneously avoid an additional null set
of parameter values. This refines the proved local Sard selection. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem exists_regular_pair_translation_avoiding_null {f g : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (U V : Set Base) (hU : IsOpen U) (hV : IsOpen V)
    (A : Set (ProjectionTarget 3)) (hA : IsOpen A) (hAn : A.Nonempty)
    (N : Set (ProjectionTarget 3)) (hN : volume N = 0) :
    ∃ a ∈ A, a ∉ N ∧ ∀ x ∈ U, ∀ y ∈ V, f x-g y = a →
      Function.Surjective (fderiv ℝ (fun z : Base × Base => f z.1-g z.2) (x,y)) := by
  let h : Base × Base → ProjectionTarget 3 := fun z => f z.1-g z.2
  let B := h '' {z | z ∈ U ×ˢ V ∧ ¬ Function.Surjective (fderiv ℝ h z)}
  have hh : ContDiff ℝ ∞ h := (hf.comp contDiff_fst).sub (hg.comp contDiff_snd)
  have hB : volume B = 0 := pair_chart_local_critical_values_null (hU.prod hV) hh.contDiffOn
  have hnull : volume (B ∪ N) = 0 := measure_union_null hB hN
  have hae : ∀ᵐ a ∂volume, a ∉ B ∪ N := by
    simp only [ae_iff,not_not]
    exact hnull
  obtain ⟨a,haA,ha⟩ := (Measure.dense_of_ae hae).inter_open_nonempty A hA hAn
  refine ⟨a,haA,(fun h => ha (Or.inr h)),?_⟩
  intro x hx y hy he
  by_contra hn
  exact ha (Or.inl ⟨(x,y),⟨⟨hx,hy⟩,hn⟩,he⟩)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FinitePointPairAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrarily small transverse translations remove every coincidence
that uses one of finitely many prescribed points on either coordinate patch. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem exists_small_transverse_translation_avoiding_points {f g : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (U V : Set Base) (hU : IsOpen U) (hV : IsOpen V)
    (S T : Set Base) (hS : S.Finite) (hT : T.Finite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ProjectionTarget 3, ‖a‖ < ε ∧
      ∀ x ∈ U, ∀ y ∈ V, f x+a = g y → x ∉ S ∧ y ∉ T ∧
        Function.Surjective (fderiv ℝ (fun z : Base × Base => f z.1-g z.2) (x,y)) := by
  let N₁ : Set (ProjectionTarget 3) := ⋃ s ∈ S, range (fun y => f s-g y)
  let N₂ : Set (ProjectionTarget 3) := ⋃ t ∈ T, range (fun x => f x-g t)
  have hN₁ : volume N₁ = 0 := (measure_biUnion_null_iff hS.countable).mpr
    (fun s _ => euclidean_surface_image_null _ (contDiff_const.sub hg))
  have hN₂ : volume N₂ = 0 := (measure_biUnion_null_iff hT.countable).mpr
    (fun t _ => euclidean_surface_image_null _ (hf.sub contDiff_const))
  obtain ⟨α,hα,havoid,hreg⟩ := exists_regular_pair_translation_avoiding_null hf hg U V hU hV
    (Metric.ball 0 ε) Metric.isOpen_ball ⟨0,Metric.mem_ball_self hε⟩
    (N₁ ∪ N₂) (measure_union_null hN₁ hN₂)
  refine ⟨-α,?_,?_⟩
  · simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hα
  · intro x hx y hy heq
    have hval : f x-g y = α := by
      apply sub_eq_iff_eq_add.mpr
      calc
        f x = (f x + -α) + α := by abel
        _ = g y + α := by rw [heq]
        _ = α + g y := add_comm _ _
    refine ⟨?_,?_,hreg x hx y hy hval⟩
    · intro hxS
      exact havoid (Or.inl (mem_iUnion₂.mpr ⟨x,hxS,y,hval⟩))
    · intro hyT
      exact havoid (Or.inr (mem_iUnion₂.mpr ⟨y,hyT,x,hval⟩))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceCompactRepresentative
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth representatives on a fixed compact part of a surface chart.
The compact chart region can be chosen before the surface map. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem surface_compact_representative {f : M → W}
    (hf : ContMDiff planeModel 𝓘(ℝ,W) ∞ f) (p : M)
    {K : Set M} (hK : IsCompact K) (hKp : K ⊆ (chart p).source) :
    ∃ F : Base → W, ContDiff ℝ ∞ F ∧ EqOn f (F ∘ chart p) K := by
  have hlocal : ContDiffOn ℝ ∞ (f ∘ (chart p).symm) (chart p).target :=
    (hf.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  have hKc : IsCompact ((chart p) '' K) :=
    hK.image_of_continuousOn ((chart p).continuousOn.mono hKp)
  have hKT : (chart p) '' K ⊆ (chart p).target := by
    rintro z ⟨x,hx,rfl⟩
    exact (chart p).map_source (hKp hx)
  obtain ⟨U,hU,hKU,hUT,F,hF,hFF⟩ := CollarVelocity.compact_smooth_extension
    hKc (chart p).open_target hKT hlocal
  refine ⟨F,hF,?_⟩
  intro x hx
  change f x = F (chart p x)
  rw [hFF (hKU ⟨x,hx,rfl⟩)]
  change f x = f ((chart p).symm (chart p x))
  rw [(chart p).left_inv (hKp hx)]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SurfacePairPointAvoidance
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual chart translations can avoid prescribed finite surface points while
retaining transversality at all remaining coincidences. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_pair_patch_translation_avoiding_points (p q : M)
    {f : M → ProjectionTarget 3} {χ : M → ℝ}
    {F G : Base → ProjectionTarget 3} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    (hUp : U ⊆ (chart p).source) (hVq : V ⊆ (chart q).source)
    (heF : EqOn f (F ∘ chart p) U) (heG : EqOn f (G ∘ chart q) V)
    (hχU : EqOn χ 1 U) (hχV : EqOn χ 0 V)
    (S T : Set M) (hS : S.Finite) (hT : T.Finite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ProjectionTarget 3, ‖a‖ < ε ∧ ∀ x ∈ U, ∀ y ∈ V,
      surfaceTranslation f χ a x = surfaceTranslation f χ a y →
      x ∉ S ∧ y ∉ T ∧ Function.Surjective (surfacePairDerivative (surfaceTranslation f χ a) x y) := by
  obtain ⟨a,ha,hreg⟩ := exists_small_transverse_translation_avoiding_points hF hG
    ((chart p) '' U) ((chart q) '' V)
    ((chart p).isOpen_image_of_subset_source hU hUp)
    ((chart q).isOpen_image_of_subset_source hV hVq)
    ((chart p) '' S) ((chart q) '' T) (hS.image _) (hT.image _) hε
  refine ⟨a,ha,?_⟩
  intro x hx y hy hxy
  have he₁ : surfaceTranslation f χ a =ᶠ[𝓝 x] (fun z => F z+a) ∘ chart p := by
    filter_upwards [hU.mem_nhds hx] with z hz
    simp only [surfaceTranslation,hχU hz,Pi.one_apply,one_smul,Function.comp_apply,heF hz]
  have he₂ : surfaceTranslation f χ a =ᶠ[𝓝 y] G ∘ chart q := by
    filter_upwards [hV.mem_nhds hy] with z hz
    simp only [surfaceTranslation,hχV hz,Pi.zero_apply,zero_smul,add_zero,heG hz]
  have hval : F (chart p x)+a = G (chart q y) := by
    exact he₁.self_of_nhds.symm.trans (hxy.trans he₂.self_of_nhds)
  obtain ⟨hxS,hyT,ht⟩ := hreg (chart p x) ⟨x,hx,rfl⟩ (chart q y) ⟨y,hy,rfl⟩ hval
  refine ⟨(fun h => hxS ⟨x,h,rfl⟩),(fun h => hyT ⟨y,h,rfl⟩),?_⟩
  apply (surface_pair_coordinate_regular_iff p q (hUp hx) (hVq hy)
    (hF.add contDiff_const) hG he₁ he₂).mpr
  have heq : (fun z : Base × Base => (F z.1+a)-G z.2) =
      (fun z : Base × Base => (F z.1-G z.2)+a) := by
    funext z
    abel
  change Function.Surjective (fderiv ℝ (fun z : Base × Base => (F z.1+a)-G z.2) _)
  rw [heq,fderiv_add_const]
  exact ht

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FixedPairPointAvoidance
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed cutoff patches also remove coincidences at prescribed finite points. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SurfacePairTranslationPatch

theorem regularize_avoiding_points_oai {p q : M} (P : SurfacePairTranslationPatch p q)
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (S T : Set M) (hS : S.Finite) (hT : T.Finite) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ProjectionTarget 3, ‖a‖ < ε ∧ ∀ x ∈ P.U, ∀ y ∈ P.V,
      surfaceTranslation f P.χ a x = surfaceTranslation f P.χ a y →
      x ∉ S ∧ y ∉ T ∧ Function.Surjective (surfacePairDerivative (surfaceTranslation f P.χ a) x y) := by
  obtain ⟨F,hF,heF⟩ := surface_compact_representative hf p isClosed_closure.isCompact P.sourceU
  obtain ⟨G,hG,heG⟩ := surface_compact_representative hf q isClosed_closure.isCompact P.sourceV
  exact surface_pair_patch_translation_avoiding_points p q hF hG P.openU P.openV
    (fun x hx => P.sourceU (subset_closure hx)) (fun y hy => P.sourceV (subset_closure hy))
    (heF.mono subset_closure) (heG.mono subset_closure) P.oneOn P.zeroOn S T hS hT hε

end SurfacePairTranslationPatch
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SurfacePairTranslationPatch.regularize_avoiding_points_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SurfacePairTranslationPatch.regularize_avoiding_points_oai.{u_1}
