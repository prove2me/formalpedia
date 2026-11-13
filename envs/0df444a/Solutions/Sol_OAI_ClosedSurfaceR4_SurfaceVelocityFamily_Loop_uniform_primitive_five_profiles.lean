-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_five_profiles
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:51:04.125223+00:00
-- url     : https://prove2.me/submissions/299eb674-5eda-4d0d-a7cc-da57ae4135ee

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_uniform_longitudinal_profile
import Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_uniform_mixed_profile
import Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_uniform_scaled_longitudinal_profile
import Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_uniform_transverse_profiles

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicPrimitive
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The normalized periodic antiderivative used by the finite periodic expansion.
The primitive is constructed by integration, followed by subtraction of its
mean.  The period is one, matching `UnitAddCircle`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicPrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem rawPrimitive_hasDerivAt {f : ℝ → E} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (rawPrimitive f) (f x) x :=
  (hf.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem primitive_hasDerivAt {f : ℝ → E} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (primitive f) (f x) x :=
  (rawPrimitive_hasDerivAt hf x).sub_const _

end ClosedSurfaceR4.PeriodicPrimitive

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPeriodicCalculus
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical periodic primitives and angular derivatives in a smooth family. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.SmoothPeriodicCalculus

open CovarianceCorrector PeriodicPrimitive PeriodicCalculus

variable {A E : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma derivativeFamily_hasDerivAt (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period))) (p : A) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F p (s : Period)) (derivativeFamily F hF p (t : Period)) t :=
  angle_hasDerivAt hF p t

end ClosedSurfaceR4.SmoothPeriodicCalculus

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic differentiation and integration on an open parameter domain. -/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicCalculus

open CovarianceCorrector SmoothPeriodicCalculus

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma angleOn_hasDerivAt (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    {p : P} (hp : p ∈ S) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F p (s : Period)) (angleOn F S hS hF p (t : Period)) t := by
  rw [angleOn, bundleOn_apply _ _ _ _ _ hp]
  exact angle_hasDerivAt hS hF hp t

lemma slowOn_apply (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (v : P) {p : P} (hp : p ∈ S) (t : ℝ) :
    slowOn F S hS hF v p (t : Period) =
      slowDerivative (fun z : P × ℝ => F z.1 (z.2 : Period)) v (p, t) :=
  bundleOn_apply _ _ _ _ _ hp t

variable [FiniteDimensional ℝ P] [CompleteSpace E]

lemma primitiveOn_apply (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) {p : P} (hp : p ∈ S) (t : ℝ) :
    primitiveOn F S hS hF hm p (t : Period) =
      PeriodicPrimitive.primitive (fun s => F p (s : Period)) t :=
  bundleOn_apply _ _ _ _ _ hp t

lemma primitiveOn_hasDerivAt (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) {p : P} (hp : p ∈ S) (t : ℝ) :
    HasDerivAt (fun s : ℝ => primitiveOn F S hS hF hm p (s : Period)) (F p (t : Period)) t := by
  simp only [primitiveOn_apply F S hS hF hm hp]
  exact PeriodicPrimitive.primitive_hasDerivAt ((F p).continuous.comp (AddCircle.continuous_mk' 1)) t

end ClosedSurfaceR4.LocalPeriodicCalculus

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFamilies
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.vectorMean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xTangent_zero _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yTangent_zero _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth periodic coefficient families on the actual open geometric domain.
Values outside that domain are fixed at zero, so equality only needs checking inside. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable (O : TopologicalSpace.Opens A) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {O E}
namespace Family

lemma angle_hasDerivAt (F : Family O E) {p : A} (hp : p ∈ O) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.val p (s : Period)) (F.angle.val p (t : Period)) t := by
  rw [angle, ofLocal_apply _ _ hp]
  exact angleOn_hasDerivAt F.val O O.isOpen F.smooth hp t

@[simp] lemma slow_apply (F : Family O E) (v : A) {p : A} (hp : p ∈ O) (t : ℝ) :
    (F.slow v).val p (t : Period) =
      SmoothPeriodicCalculus.slowDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) v (p, t) := by
  rw [slow, ofLocal_apply _ _ hp, slowOn_apply _ _ _ _ _ hp]

variable [FiniteDimensional ℝ A] [CompleteSpace E]

lemma primitive_angle (F : Family O E) (hm : ∀ p ∈ O, average (F.val p) = 0) :
    (F.primitive hm).angle = F := by
  ext p hp t
  refine Quotient.inductionOn' t ?_
  intro x
  have hd := (F.primitive hm).angle_hasDerivAt hp x
  have he : (fun s : ℝ => (F.primitive hm).val p (s : Period)) =
      fun s : ℝ => primitiveOn F.val O O.isOpen F.smooth hm p (s : Period) := by
    funext s
    exact ofLocal_apply _ _ hp _
  rw [he] at hd
  exact hd.unique (primitiveOn_hasDerivAt _ _ _ _ _ hp x)

end Family
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFastEvaluation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual fast-phase differentiation on an admissible chart domain. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion.Family
open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {O : TopologicalSpace.Opens A}

lemma angle_apply (F : Family O E) {p : A} (hp : p ∈ O) (t : ℝ) :
    F.angle.val p (t : Period) =
      angleDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) (p, t) := by
  rw [angle, ofLocal_apply _ _ hp]
  exact LocalPeriodicCalculus.bundleOn_apply _ _ _ _ _ hp t

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicExpansionInit
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial coefficient and transverse cancellation on the admissible domain. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

namespace Geometry
variable {v : A} (g : Geometry (E := E) O v)

omit [FiniteDimensional ℝ E] in
lemma initial_angle : g.initial.angle = g.V - g.V.vectorMean :=
  Family.primitive_angle _ _

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactAnsatzAsymptotics
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact, fixed-coefficient asymptotics of the finite periodic ansatz. -/

noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion
open CovarianceCorrector WeightedEstimates

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma directionalMap_smooth {F : A → E} (hF : ContDiff ℝ ∞ F) (v : A) :
    ContDiff ℝ ∞ (directionalMap F v) :=
  (hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalAnsatzProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading jets of the supported local ansatz are the geometric profiles
of the initial periodic primitive. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector
open PeriodicExpansion (directionalMap)

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {O : TopologicalSpace.Opens A}

lemma global_angle_eq_local (W : PeriodicExpansion.Family A E) (U : Family O E)
    (hW : W.val = U.val) {p : A} (hp : p ∈ O) (t : Period) :
    W.angle.val p t = U.angle.val p t := by
  refine Quotient.inductionOn' t ?_
  intro s
  rw [PeriodicExpansion.Family.angle_apply,Family.angle_apply U hp,hW]

namespace Geometry

variable [FiniteDimensional ℝ A] [CompleteSpace E]
  {dy : A} (g : Geometry (E := E) O dy)

/-- The leading angular correction is the mean-zero velocity primitive. -/
lemma initial_global_angle (W : PeriodicExpansion.Family A E)
    (hW : W.val = g.initial.val) {p : A} (hp : p ∈ O) (t : Period) :
    W.angle.val p t = g.V.val p t-average (g.V.val p) := by
  rw [global_angle_eq_local W g.initial hW hp,g.initial_angle]
  simp only [Family.sub_apply,Family.vectorMean_apply]

/-- Adding the leading angular correction to the old longitudinal derivative
gives precisely the prescribed velocity profile `X`. -/
lemma initial_global_longitudinal {F : A → E} (W : PeriodicExpansion.Family A E)
    (hW : W.val = g.initial.val) (dx : A)
    (hX : ∀ p ∈ O, fderiv ℝ F p dx = g.X₀ p+average (g.V.val p))
    {p : A} (hp : p ∈ O) (t : Period) :
    directionalMap F dx p+W.angle.val p t = g.longitudinal.val p t := by
  rw [g.initial_global_angle W hW hp]
  change fderiv ℝ F p dx+(g.V.val p t-average (g.V.val p)) = _
  rw [hX p hp]
  simp only [longitudinal,Family.add_apply,Family.constant_apply _ _ hp]
  abel

/-- The second angular derivative of the primitive is the angular derivative
of the actual velocity loop, including its normalization by the mean. -/
lemma initial_global_angle_angle (W : PeriodicExpansion.Family A E)
    (hW : W.val = g.initial.val) {p : A} (hp : p ∈ O) (t : Period) :
    W.angle.angle.val p t = g.V.angle.val p t := by
  refine Quotient.inductionOn' t ?_
  intro s
  have hd := SmoothPeriodicCalculus.derivativeFamily_hasDerivAt
    W.angle.val W.angle.smooth p s
  change HasDerivAt (fun r : ℝ => W.angle.val p (r : Period))
    (W.angle.angle.val p (s : Period)) s at hd
  have he : (fun r : ℝ => W.angle.val p (r : Period)) =
      fun r : ℝ => g.V.val p (r : Period)-average (g.V.val p) :=
    funext (fun r => g.initial_global_angle W hW hp (r : Period))
  rw [he] at hd
  exact hd.unique ((g.V.angle_hasDerivAt hp s).sub_const _)

/-- Slow differentiation of the actual leading profile gives `X_y`, rather
than a separately supplied approximation. -/
lemma initial_global_longitudinal_slow {F : A → E} (hF : ContDiff ℝ ∞ F)
    (W : PeriodicExpansion.Family A E) (hW : W.val = g.initial.val) (dx : A)
    (hX : ∀ p ∈ O, fderiv ℝ F p dx = g.X₀ p+average (g.V.val p))
    {p : A} (hp : p ∈ O) (s : ℝ) :
    directionalMap (directionalMap F dx) dy p+
      (W.angle.slow dy).val p (s : Period) =
        (g.longitudinal.slow dy).val p (s : Period) := by
  have he : (fun q : A => directionalMap F dx q+W.angle.val q (s : Period)) =ᶠ[𝓝 p]
      fun q : A => g.longitudinal.val q (s : Period) := by
    filter_upwards [O.isOpen.mem_nhds hp] with q hq
    exact g.initial_global_longitudinal W hW dx hX hq _
  have hd := congrArg (fun L : A →L[ℝ] E => L dy) he.fderiv_eq
  have hs : ContDiff ℝ ∞ (fun q : A => W.angle.val q (s : Period)) :=
    W.angle.smooth.comp (contDiff_id.prodMk contDiff_const)
  rw [fderiv_fun_add (f := directionalMap F dx)
    (g := fun q : A => W.angle.val q (s : Period))
    ((PeriodicExpansion.directionalMap_smooth hF dx).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)
    (hs.differentiable (by simp) p)] at hd
  simp only [add_apply] at hd
  rw [PeriodicExpansion.Family.slow_apply,Family.slow_apply _ _ hp,
    ← SmoothPeriodicCalculus.fderiv_slice W.angle.smooth,
    ← LocalPeriodicCalculus.fderiv_slice O.isOpen g.longitudinal.smooth hp]
  exact hd

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicCoefficientProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit finite coefficient bounds for the varying-map version of the
periodic derivative estimates. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector
variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {O : TopologicalSpace.Opens A}

lemma global_slow_eq_local_of_eqOn (W : PeriodicExpansion.Family A E) (U : Family O E)
    (hW : ∀ p ∈ O, ∀ t : Period, W.val p t = U.val p t)
    (v : A) {p : A} (hp : p ∈ O) (t : Period) :
    (W.slow v).val p t = (U.slow v).val p t := by
  refine Quotient.inductionOn' t ?_
  intro s
  rw [PeriodicExpansion.Family.slow_apply,Family.slow_apply U v hp]
  have he : (fun z : A × ℝ => W.val z.1 (z.2 : Period)) =ᶠ[nhds (p,s)]
      (fun z => U.val z.1 (z.2 : Period)) := by
    filter_upwards [(O.isOpen.prod isOpen_univ).mem_nhds ⟨hp,mem_univ s⟩] with z hz
    exact hW z.1 hz.1 (z.2 : Period)
  exact congrArg (fun L : (A × ℝ) →L[ℝ] E => L (v,0)) he.fderiv_eq

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SecondCoefficientProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Second coefficient derivatives agree with the local represented jets,
even when only their germs agree after the first derivative. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector JetPolynomial

lemma global_angle_eq_local_of_eqOn {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {O : TopologicalSpace.Opens A}
    (W : PeriodicExpansion.Family A E) (U : Family O E)
    (hW : ∀ p ∈ O, ∀ t : Period, W.val p t = U.val p t)
    {p : A} (hp : p ∈ O) (t : Period) : W.angle.val p t = U.angle.val p t := by
  refine Quotient.inductionOn' t ?_
  intro s
  rw [PeriodicExpansion.Family.angle_apply,Family.angle_apply U hp]
  have he : (fun z : A × ℝ => W.val z.1 (z.2 : Period)) =ᶠ[nhds (p,s)]
      (fun z => U.val z.1 (z.2 : Period)) := by
    filter_upwards [(O.isOpen.prod isOpen_univ).mem_nhds ⟨hp,mem_univ s⟩] with z hz
    exact hW z.1 hz.1 (z.2 : Period)
  exact congrArg (fun L : (A × ℝ) →L[ℝ] E => L (0,1)) he.fderiv_eq

lemma global_coefficientDerivative_eq_local {S : TopologicalSpace.Opens Base}
    (W : PeriodicExpansion.Family Base JetVelocityCoordinates.Euclidean)
    (U : Family S JetVelocityCoordinates.Euclidean)
    (hW : ∀ p ∈ S, ∀ t : Period, W.val p t = U.val p t)
    (k : Fin 3) {p : Base} (hp : p ∈ S) (t : Period) :
    (globalCoefficientDerivative W k).val p t =
      (VectorExpression.coefficientFamilyDerivative U k).val p t := by
  fin_cases k
  · exact global_slow_eq_local_of_eqOn W U hW _ hp t
  · exact global_slow_eq_local_of_eqOn W U hW _ hp t
  · exact global_angle_eq_local_of_eqOn W U hW hp t

lemma global_second_coefficientDerivative_eq_local {S : TopologicalSpace.Opens Base}
    (W : PeriodicExpansion.Family Base JetVelocityCoordinates.Euclidean)
    (U : Family S JetVelocityCoordinates.Euclidean) (hW : W.val = U.val)
    (k j : Fin 3) {p : Base} (hp : p ∈ S) (t : Period) :
    (globalCoefficientDerivative (globalCoefficientDerivative W k) j).val p t =
      (VectorExpression.coefficientFamilyDerivative
        (VectorExpression.coefficientFamilyDerivative U k) j).val p t := by
  apply global_coefficientDerivative_eq_local _ _ _ j hp t
  intro q hq r
  exact global_coefficientDerivative_eq_local W U (by intro q _ t; rw [hW]) k hq r

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceVelocityFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert a geometric second-jet velocity loop into the exact family of
Euclidean data used by the supported finite periodic recursion. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector
open LocalPeriodicExpansion LocalPeriodicCalculus
local notation "ι" => JetVelocityCoordinates.toEuclidean

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

lemma euclideanVelocity_mean {J : LowJet} (hJ : J ∈ O) :
    average (l.euclideanVelocity J) = ι (normal J) := by
  rw [average, ← PeriodicPrimitive.integral_lift_eq_haar]
  simp only [l.euclideanVelocity_apply hJ]
  have hi : IntervalIntegrable (fun t => l.velocity (J, t)) MeasureTheory.volume 0 1 :=
    (smooth_slice O.isOpen l.smoothVelocity hJ).continuous.intervalIntegrable 0 1
  exact (JetVelocityCoordinates.toEuclidean.toContinuousLinearMap.intervalIntegral_comp_comm hi).trans
    (congrArg ι (l.mean J hJ))

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceVelocityIdentities
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xTangent_zero _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yTangent_zero _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading metric and support of the actual second-jet family. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector
open LocalPeriodicExpansion
local notation "ι" => JetVelocityCoordinates.toEuclidean

lemma first_slot {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (i : Fin 2) (p : JetPolynomial.Base) :
    slot (![1, 2] i) (lowJet G p) = fderiv ℝ G p (coordinateVector i) := by
  funext a
  have he := congrArg (fun L : JetPolynomial.Base →L[ℝ] ℝ => L (coordinateVector i))
    (fderiv_apply (hG.differentiable (by simp) p) a)
  calc
    _ = fderiv ℝ (fun q => G q a) p (coordinateVector i) := by fin_cases i <;> rfl
    _ = _ := he

lemma euclidean_first_derivative {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (i : Fin 2) (p : JetPolynomial.Base) :
    fderiv ℝ (fun q => ι (G q)) p (coordinateVector i) =
      ι (slot (![1, 2] i) (lowJet G p)) := by
  have hd := (JetVelocityCoordinates.toEuclidean.hasFDerivAt.comp p
    (hG.differentiable (by simp) p).hasFDerivAt).fderiv
  calc
    _ = ι (fderiv ℝ G p (coordinateVector i)) :=
      congrArg (fun L : JetPolynomial.Base →L[ℝ] Euclidean => L (coordinateVector i)) hd
    _ = _ := congrArg ι (first_slot hG i p).symm

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

variable {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O)

lemma geometry_velocity {p : JetPolynomial.Base} (hp : p ∈ S) :
    (l.geometry G hG hGO).V.val p = l.euclideanVelocity (lowJet G p) := by
  apply ContinuousMap.ext
  intro t
  change (Family.ofLocal (fun q => l.euclideanVelocity (lowJet G q)) _).val p t = _
  exact Family.ofLocal_apply _ _ hp t

lemma geometry_mean {p : JetPolynomial.Base} (hp : p ∈ S) :
    average ((l.geometry G hG hGO).V.val p) = ι (normal (lowJet G p)) := by
  rw [l.geometry_velocity hG hGO hp]
  exact l.euclideanVelocity_mean (hGO hp)

lemma geometry_dx {p : JetPolynomial.Base} (hp : p ∈ S) :
    fderiv ℝ (fun q => ι (G q)) p (coordinateVector 0) =
      (l.geometry G hG hGO).X₀ p + average ((l.geometry G hG hGO).V.val p) := by
  rw [euclidean_first_derivative hG, l.geometry_mean hG hGO hp]
  change ι (slot 1 (lowJet G p)) = ι (tangent (lowJet G p)) + ι (normal (lowJet G p))
  rw [← map_add]
  congr 1
  dsimp [tangent]
  abel

lemma geometry_dy (p : JetPolynomial.Base) :
    fderiv ℝ (fun q => ι (G q)) p (coordinateVector 1) = (l.geometry G hG hGO).Y p :=
  euclidean_first_derivative hG 1 p

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_UniformPrimitiveProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All five actual derivative profiles share a loss fixed before the slow
map. The leading profiles are the geometric velocity and its derivatives. -/
noncomputable section
open Set
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem uniform_primitive_five_profiles_oai {S : TopologicalSpace.Opens JetPolynomial.Base}
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hx : ℓ (coordinateVector 0) = 1) (hy : ℓ (coordinateVector 1) = 0) :
    ∃ loss : ℕ, ∀ B : ℝ, 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (hGQ : MapsTo (lowJet G) S Q),
      ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s ((2*n+2)+2) B (lowJet G) →
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U i).val y.1 (y.2 : Period))) →
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
        U 0 = (l.geometry G hG (fun _ hp => hQO (hGQ hp))).initial →
      ∀ p ∈ S,
        let g := l.geometry G hG (fun _ hp => hQO (hGQ hp))
        let t : Period := ((ℓ p/z : ℝ) : Period)
        ‖primitiveJetProfile (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
            U ℓ (n+1) z) z p-
          ![g.longitudinal.val p t,g.Y p,g.C p,
            (g.longitudinal.slow (coordinateVector 1)).val p t,g.V.angle.val p t]‖ ≤ D*z/s^loss := by
  obtain ⟨lx,hxb⟩ := l.uniform_longitudinal_profile (S := S) hQ hQO n ℓ hx
  obtain ⟨ly,hyb⟩ := l.uniform_transverse_profiles (S := S) hQ hQO n ℓ hy
  obtain ⟨lm,hmb⟩ := l.uniform_mixed_profile (S := S) hQ hQO n ℓ hx hy
  obtain ⟨la,hab⟩ := l.uniform_scaled_longitudinal_profile (S := S) hQ hQO n ℓ hx
  let loss := max (max lx ly) (max lm la)
  refine ⟨loss,?_⟩
  intro B hB
  obtain ⟨Dx,hDx,hxbound⟩ := hxb B hB
  obtain ⟨Dy,hDy,hybound⟩ := hyb B hB
  obtain ⟨Dm,hDm,hmbound⟩ := hmb B hB
  obtain ⟨Da,hDa,habound⟩ := hab B hB
  let D := Dx+Dy+Dm+Da
  have hD : 0 ≤ D := by dsimp [D] <;> positivity
  refine ⟨D,hD,?_⟩
  intro G hG hGQ s z hz hzs hs1 hb U hU hrep hinit p hp
  have hs : 0 < s := hz.trans_le hzs
  have hbound (C : ℝ) (hC : 0 ≤ C) (hCD : C ≤ D) (d : ℕ) (hd : d ≤ loss) :
      C*z/s^d ≤ D*z/s^loss := by
    exact (div_le_div_of_nonneg_left (mul_nonneg hC hz.le) (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 hd)).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCD hz.le) (pow_nonneg hs.le _))
  have hxd : lx ≤ loss := (le_max_left lx ly).trans (le_max_left _ _)
  have hyd : ly ≤ loss := (le_max_right lx ly).trans (le_max_left _ _)
  have hmd : lm ≤ loss := (le_max_left lm la).trans (le_max_right _ _)
  have had : la ≤ loss := (le_max_right lm la).trans (le_max_right _ _)
  have hxerr := (hxbound G hG hGQ s z hz hzs hs1 hb U hU hrep p hp).trans
    (hbound Dx hDx (by dsimp [D] <;> linarith) lx hxd)
  obtain ⟨hyerr,hyyerr⟩ := hybound G hG hGQ s z hz hzs hs1 hb U hU hrep p hp
  have hdy := hbound Dy hDy (by dsimp [D] <;> linarith) ly hyd
  replace hyerr := hyerr.trans hdy
  replace hyyerr := hyyerr.trans hdy
  have hmerr := (hmbound G hG hGQ s z hz hzs hs1 hb U hU hrep p hp).trans
    (hbound Dm hDm (by dsimp [D] <;> linarith) lm hmd)
  have haerr := (habound G hG hGQ s z hz hzs hs1 hb U hU hrep p hp).trans
    (hbound Da hDa (by dsimp [D] <;> linarith) la had)
  let F := fun q => JetVelocityCoordinates.toEuclidean (G q)
  have hFs : ContDiff ℝ ∞ F := JetVelocityCoordinates.toEuclidean.contDiff.comp hG
  have hGO : MapsTo (lowJet G) S O := fun _ hq => hQO (hGQ hq)
  let g := l.geometry G hG hGO
  let W := globalCoefficients U hU
  have hW : (W 0).val = g.initial.val := by
    change (U 0).val = g.initial.val
    rw [hinit]
  have hx0 := g.initial_global_longitudinal (W 0) hW (coordinateVector 0)
    (fun q hq => l.geometry_dx hG hGO hq) hp ((ℓ p/z : ℝ) : Period)
  rw [global_angle_eq_local (W 0) (U 0) rfl hp] at hx0
  change PeriodicExpansion.directionalMap F (coordinateVector 0) p+
    (U 0).angle.fastValue ℓ z p = g.longitudinal.val p ((ℓ p/z : ℝ) : Period) at hx0
  rw [hx0] at hxerr
  have hy0 : PeriodicExpansion.directionalMap F (coordinateVector 1) =ᶠ[𝓝 p] g.Y := by
    filter_upwards [S.isOpen.mem_nhds hp] with q hq
    exact l.geometry_dy hG hGO q
  have hyy0 : PeriodicExpansion.directionalMap
      (PeriodicExpansion.directionalMap F (coordinateVector 1)) (coordinateVector 1) p = g.C p :=
    (congrArg (fun L : JetPolynomial.Base →L[ℝ] Euclidean => L (coordinateVector 1))
      hy0.fderiv_eq).trans (g.derivativeY p hp)
  rw [hy0.eq_of_nhds] at hyerr
  rw [hyy0] at hyyerr
  have hm0 := g.initial_global_longitudinal_slow hFs (W 0) hW (coordinateVector 0)
    (fun q hq => l.geometry_dx hG hGO hq) hp (ℓ p/z)
  rw [global_slow_eq_local_of_eqOn (W 0).angle (U 0).angle
    (fun q hq t => global_angle_eq_local (W 0) (U 0) rfl hq t) (coordinateVector 1) hp] at hm0
  change PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap F (coordinateVector 0))
    (coordinateVector 1) p+((U 0).angle.slow (coordinateVector 1)).fastValue ℓ z p = _ at hm0
  rw [hm0] at hmerr
  have ha0 := g.initial_global_angle_angle (W 0) hW hp ((ℓ p/z : ℝ) : Period)
  have haLocal : (W 0).angle.angle.val p ((ℓ p/z : ℝ) : Period) =
      (U 0).angle.angle.val p ((ℓ p/z : ℝ) : Period) :=
    global_second_coefficientDerivative_eq_local (W 0) (U 0) rfl 2 2 hp _
  rw [haLocal] at ha0
  change (U 0).angle.angle.fastValue ℓ z p = _ at ha0
  rw [ha0] at haerr
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (mul_nonneg hD hz.le) (pow_nonneg hs.le _))).mpr
  intro k
  fin_cases k
  · exact hxerr
  · exact hyerr
  · exact hyyerr
  · exact hmerr
  · exact haerr

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_five_profiles_oai := @OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_five_profiles_oai
