-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:48:03.984642+00:00
-- url     : https://prove2.me/submissions/66776013-d183-4cd4-946a-200cda31db68

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_polynomial_charted_metric_mean_family

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma WeightedBound.const_smul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ}
    {m : ℕ} {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℝ) :
    WeightedBound U s m (|a| * C) (fun x => a • f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul, Real.norm_eq_abs]
  calc
    _ = |a| * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (abs_nonneg _)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneCoordinates
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading and restoring global tensors in the two real coordinates used
by the charted oscillatory solver. The bounds preserve derivative order. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates RealModes
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadSectionNormed
local instance planeReadSectionSpace_r665030_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRestore_sub (f g : A.centers → SmallModes.Base → Tensor) :
    A.tensorPlaneRestore (f-g) = A.tensorPlaneRestore f - A.tensorPlaneRestore g := by
  funext p
  simp only [tensorPlaneRestore, Pi.sub_apply, map_sub, bundleRestore, smul_sub,
    Finset.sum_sub_distrib]

variable [CompactSpace M]

lemma tensorPlaneRead_smooth (i : A.centers) {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContDiff ℝ ∞ (A.tensorPlaneRead i u) :=
  (A.tensorChartRead_smooth i hu).comp planeCoordinateIsometry.symm.contDiff

lemma tensorPlaneRestore_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : A.centers → SmallModes.Base → Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (f i)) →
      (∀ i, _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C (f i)) →
      A.TensorWeightedBound s m (D*C) (A.tensorPlaneRestore f) := by
  obtain ⟨D,hD,hd⟩ := A.bundle_restoration_bound A.tensorTriv A.tensorTriv_domain m
  refine ⟨D * ‖fiberFromThree‖, mul_nonneg hD (norm_nonneg _), ?_⟩
  intro f s C hs hs1 hC hf hb
  have hh := hd (fun i y => fiberFromThree (f i (planeCoordinateIsometry y))) s
    (‖fiberFromThree‖ * C) hs hs1 (mul_nonneg (norm_nonneg _) hC)
    (fun i => fiberFromThree.contDiff.comp ((hf i).comp planeCoordinateIsometry.contDiff))
    (fun i => (weightedBound_comp_isometry planeCoordinateIsometry (hf i) (hb i)).linear
      uniqueDiffOn_univ hs.le ((hf i).comp planeCoordinateIsometry.contDiff).contDiffOn fiberFromThree)
  have hout : A.TensorWeightedBound s m (D * (‖fiberFromThree‖ * C))
      (A.tensorPlaneRestore f) := hh
  convert hout using 1
  all_goals try with_reducible_and_instances rfl
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FixedMeanSubstitution
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mean correction for one fixed operator with derivative loss.
The smallness threshold is uniform in the operator; no infinite-dimensional
inverse or convergence of a derivative-losing iteration is asserted. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteMean
open WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma rescaledMean_self {η : ℝ} (hη : η ≠ 0) (A : (E → F) → E → F) :
    rescaledMean η A η = A := by
  funext f
  simp only [rescaledMean, div_self hη, one_smul]

lemma rescaledMean_bounds {U : Set E} (hU : UniqueDiffOn ℝ U) {s : ℝ}
    {reference : E → F} {r η : ℝ} {L : ℕ} (hη : 0 < η)
    (A : (E → F) → E → F) (B K : ℕ → ℝ → ℝ)
    (hB : ∀ m C, 1 ≤ C → 1 ≤ B m C) (hK : ∀ m C, 1 ≤ C → 1 ≤ K m C)
    (hsm : ∀ f, ContDiffOn ℝ ∞ f U → InTrialBall U reference r f → ContDiffOn ℝ ∞ (A f) U)
    (hv : ∀ m C f, 1 ≤ C → ContDiffOn ℝ ∞ f U → InTrialBall U reference r f →
      WeightedBound U s (m + L) C f → WeightedBound U s m (η * B m C) (A f))
    (hd : ∀ m C D f g, 1 ≤ C → 0 ≤ D →
      ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
      InTrialBall U reference r f → InTrialBall U reference r g →
      WeightedBound U s (m + L) C f → WeightedBound U s (m + L) C g →
      WeightedBound U s (m + L) D (f - g) →
      WeightedBound U s m (K m C * η * D) (A f - A g)) :
    MeanBounds U s reference r L (rescaledMean η A) B K := by
  refine ⟨hB, hK, ?_, ?_, ?_⟩
  · intro θ _ _ f hf hb
    exact (hsm f hf hb).const_smul (θ / η)
  · intro θ hθ _ m C f hC hf hb hbf
    have hh := (hv m C f hC hf hb hbf).const_smul hU (hsm f hf hb) (θ / η)
    change WeightedBound U s m _ (rescaledMean η A θ f) at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [abs_of_pos (div_pos hθ hη)]
    field_simp
  · intro θ hθ _ m C D f g hC hD hf hg hb hc hbf hbg hbd
    have hh := (hd m C D f g hC hD hf hg hb hc hbf hbg hbd).const_smul hU
      ((hsm f hf hb).sub (hsm g hg hc)) (θ / η)
    have he : (θ / η) • (A f - A g) = rescaledMean η A θ f - rescaledMean η A θ g :=
      smul_sub _ _ _
    change WeightedBound U s m _ ((θ / η) • (A f - A g)) at hh
    rw [he] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [abs_of_pos (div_pos hθ hη)]
    field_simp

end ClosedSurfaceR4.FiniteMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialFiniteMeanFamily
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite local mean families retain polynomial majorants even when the
number of summands grows. The degree depends on the local estimate, not
on the number of charts. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.FiniteMean
open WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma MeanBounds.mono_majorants {U : Set E} {s r : ℝ} {reference : E → F}
    {L : ℕ} {T : ℝ → (E → F) → E → F} {B K B' K' : ℕ → ℝ → ℝ}
    (h : MeanBounds U s reference r L T B K)
    (hB : ∀ m C, 1 ≤ C → B m C ≤ B' m C)
    (hK : ∀ m C, 1 ≤ C → K m C ≤ K' m C) :
    MeanBounds U s reference r L T B' K' := by
  refine ⟨fun m C hC => (h.B_pos m C hC).trans (hB m C hC),
    fun m C hC => (h.K_pos m C hC).trans (hK m C hC), h.smooth, ?_, ?_⟩
  · intro η hη hη1 m C f hC hf hb hnorm
    exact (h.value η hη hη1 m C f hC hf hb hnorm).mono_const
      (mul_le_mul_of_nonneg_left (hB m C hC) hη.le)
  · intro η hη hη1 m C D f g hC hD hf hg hbf hbg hnf hng hnd
    exact (h.difference η hη hη1 m C D f g hC hD hf hg hbf hbg hnf hng hnd).mono_const
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hK m C hC) hη.le) hD)

end ClosedSurfaceR4.FiniteMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanTransport
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial majorants survive the read/restore operations in
an atlas. All dependence on transport constants stays in the profile. -/
noncomputable section
namespace ClosedSurfaceR4.PhaseMean
open RealModes

lemma polynomialMeanProfile_transport_bound (p : ℕ) {C G D E A : ℝ}
    (hC : 0 ≤ C) (hG : 1 ≤ G) (hD : 1 ≤ D) (hE : 0 ≤ E) (hA : 1 ≤ A) :
    max 1 (E*(C*(G+max 1 (D*A))^p)*D) ≤
      (1+C)*(1+G+D+E+max 1 A)^(2*p+2) := by
  let u := 1+G+D+E+max 1 A
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hDA : 1 ≤ D*A := one_le_mul_of_one_le_of_one_le hD hA
  have hu : 1 ≤ u := by dsimp [u]; rw [max_eq_right hA]; linarith
  have hGD : G+D ≤ u := by dsimp [u]; rw [max_eq_right hA]; linarith
  have hDu : D ≤ u := by dsimp [u]; rw [max_eq_right hA]; linarith
  have hEu : E ≤ u := by dsimp [u]; rw [max_eq_right hA]; linarith
  have hAu : A ≤ u := by dsimp [u]; rw [max_eq_right hA]; linarith
  have hbase : G+max 1 (D*A) ≤ u^2 := by
    rw [max_eq_right hDA]
    calc
      G+D*A ≤ (G+D)*A := by nlinarith
      _ ≤ u*u := mul_le_mul hGD hAu hA0 (zero_le_one.trans hu)
      _ = u^2 := by ring
  have hp : (G+max 1 (D*A))^p ≤ (u^2)^p :=
    pow_le_pow_left₀ (by positivity) hbase p
  have hED : E*D ≤ u^2 := by
    simpa only [pow_two] using mul_le_mul hEu hDu hD0 (zero_le_one.trans hu)
  have hb : E*(C*(G+max 1 (D*A))^p)*D ≤ C*u^(2*p+2) := by
    calc
      _ = C*(E*D)*(G+max 1 (D*A))^p := by ring
      _ ≤ C*(u^2)*(u^2)^p := mul_le_mul
        (mul_le_mul_of_nonneg_left hED hC) hp (by positivity) (by positivity)
      _ = C*u^(2*p+2) := by rw [← pow_mul, mul_assoc, ← pow_add, Nat.add_comm 2 (2*p)]
  have hone : 1 ≤ u^(2*p+2) := one_le_pow₀ hu
  apply max_le
  · nlinarith [pow_nonneg (zero_le_one.trans hu) (2*p+2)]
  · exact hb.trans (by nlinarith [pow_nonneg (zero_le_one.trans hu) (2*p+2)])

lemma polynomialMeanProfile_value_transport_bound (p : ℕ) {C G D E A : ℝ}
    (hC : 0 ≤ C) (hG : 1 ≤ G) (hD : 1 ≤ D) (hE : 0 ≤ E) (hA : 1 ≤ A) :
    max 1 (E*(C*(G+max 1 (D*A))^p)) ≤
      (1+C)*(1+G+D+E+max 1 A)^(2*p+2) := by
  have h : E*(C*(G+max 1 (D*A))^p) ≤ E*(C*(G+max 1 (D*A))^p)*D := by
    exact le_mul_of_one_le_right (by positivity) hD
  exact (max_le_max_left 1 h).trans
    (polynomialMeanProfile_transport_bound p hC hG hD hE hA)

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorAtlasMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global nonlinear mean is the finite restoration of the actual
local means evaluated on unweighted chart readings. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanFiberSpace
local instance atlasMeanDualAdd_r665030_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanFiberNormed
local instance atlasMeanSectionNormed_r665030_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasMeanSectionSpace_r665030_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma atlasMean_sub
    (μ : A.centers → (SmallModes.Base → Tensor) → SmallModes.Base → Tensor)
    (u v : ∀ x : M, CovariantTwoTensor x) :
    A.atlasMean μ u - A.atlasMean μ v = A.tensorPlaneRestore
      (fun i => μ i (A.tensorPlaneRead i u) - μ i (A.tensorPlaneRead i v)) :=
  (A.tensorPlaneRestore_sub _ _).symm

lemma tensorReadBallConstant_ball
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (f : Base → A.centers → TensorFiber) (r : ℝ) (hr : 0 ≤ r)
    (hf : ContDiff ℝ ∞ f) (hb : InTrialBall univ (A.tensorEncode reference) r f)
    (i : A.centers) :
    InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r)
      (A.tensorPlaneRead i (A.tensorDecode f)) :=
  (Classical.choose_spec A.tensorPlaneRead_decode_ball).2 reference href f r hr hf hb i

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorAtlasMeanExplicit
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The atlas mean estimate with its read and restore constants exposed. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.explicitAtlasMeanFiberSpace
local instance explicitAtlasMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.explicitAtlasMeanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.explicitAtlasMeanFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.explicitAtlasMeanFiberSpace
local instance explicitAtlasMeanSectionNormed_r665030_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance explicitAtlasMeanSectionSpace_r665030_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem atlasMean_majorants_explicit
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (L : ℕ) (B K : ℕ → ℝ → ℝ)
    (hB : ∀ m C, 1 ≤ C → 1 ≤ B m C) (hK : ∀ m C, 1 ≤ C → 1 ≤ K m C)
    (D E : ℕ → ℝ) (hD : ∀ m, 1 ≤ D m) (hE : ∀ m, 0 ≤ E m)
    (hd : ∀ m (i : A.centers) (f : Base → A.centers → TensorFiber) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C f →
      _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (D m*C) (A.tensorPlaneRead i (A.tensorDecode f)))
    (he : ∀ m (f : A.centers → SmallModes.Base → Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (f i)) →
      (∀ i, _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C (f i)) →
      A.TensorWeightedBound s m (E m*C) (A.tensorPlaneRestore f)) :
    ∀ r : ℝ, 0 ≤ r →
      (∀ f : Base → A.centers → TensorFiber, ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorEncode reference) r f → ∀ i : A.centers,
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r)
          (A.tensorPlaneRead i (A.tensorDecode f))) ∧ ∃ β κ : ℕ → ℝ → ℝ,
      β = (fun m C => max 1 (E m * B m (D (m+L)*C))) ∧
      κ = (fun m C => max 1 (E m * K m (D (m+L)*C) * D (m+L))) ∧
      ∀ {s : ℝ}, 0 < s → s ≤ 1 → ∀ η : ℝ, 0 < η →
      ∀ μ : A.centers → (SmallModes.Base → Tensor) → SmallModes.Base → Tensor,
      (∀ i f, ContDiff ℝ ∞ f → InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) f →
        ContDiff ℝ ∞ (μ i f)) →
      (∀ i m C f, 1 ≤ C → ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) f →
        _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s (m+L) C f → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (η * B m C) (μ i f)) →
      (∀ i m C D f g, 1 ≤ C → 0 ≤ D → ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) f →
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) g →
        _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s (m+L) C f → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s (m+L) C g →
        _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s (m+L) D (f-g) →
        _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (K m C * η * D) (μ i f - μ i g)) →
      MeanBounds univ s (A.tensorEncode reference) r L
        (rescaledMean η (A.tensorMeanOperator (A.atlasMean μ))) β κ := by
  classical
  have hball := A.tensorReadBallConstant_ball
  intro r hr
  let β : ℕ → ℝ → ℝ := fun m C => max 1 (E m * B m (D (m+L)*C))
  let κ : ℕ → ℝ → ℝ := fun m C => max 1 (E m * K m (D (m+L)*C) * D (m+L))
  refine ⟨(fun f hf hb i => hball reference href f r hr hf hb i),β,κ,rfl,rfl,?_⟩
  intro s hs hs1 η hη μ hsm hv hdiff
  have hb0 (f : Base → A.centers → TensorFiber) (hf : ContDiff ℝ ∞ f)
      (hb : InTrialBall univ (A.tensorEncode reference) r f) (i : A.centers) :=
    hball reference href f r hr hf hb i
  have hf0 (f : Base → A.centers → TensorFiber) (hf : ContDiff ℝ ∞ f) (i : A.centers) :=
    A.tensorPlaneRead_smooth i (A.tensorDecode_smooth hf)
  have hms (f : Base → A.centers → TensorFiber) (hf : ContDiff ℝ ∞ f)
      (hb : InTrialBall univ (A.tensorEncode reference) r f) :
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (A.atlasMean μ (A.tensorDecode f) x)) :=
    A.tensorPlaneRestore_smooth (fun i => hsm i _ (hf0 f hf i) (hb0 f hf hb i))
  apply rescaledMean_bounds uniqueDiffOn_univ hη
  · exact fun m C _ => le_max_left _ _
  · exact fun m C _ => le_max_left _ _
  · intro f hf hb
    exact (A.tensorEncode_smooth (hms f (contDiffOn_univ.mp hf) hb)).contDiffOn
  · intro m C f hC hf hb hbf
    have hfs := contDiffOn_univ.mp hf
    have hDC : 1 ≤ D (m+L)*C := one_le_mul_of_one_le_of_one_le (hD _) hC
    have hl (i : A.centers) := hv i m (D (m+L)*C) _ hDC (hf0 f hfs i) (hb0 f hfs hb i)
      (hd (m+L) i f s C hs hs1 (zero_le_one.trans hC) hfs hbf)
    have hg := he m (fun i => μ i (A.tensorPlaneRead i (A.tensorDecode f))) s
      (η * B m (D (m+L)*C)) hs hs1 (mul_nonneg hη.le (zero_le_one.trans (hB _ _ hDC)))
      (fun i => hsm i _ (hf0 f hfs i) (hb0 f hfs hb i)) hl
    have henc := A.tensorEncode_bound (hms f hfs hb) hs
      (mul_nonneg (hE m) (mul_nonneg hη.le (zero_le_one.trans (hB _ _ hDC)))) hg
    apply henc.mono_const
    calc
      _ = η * (E m * B m (D (m+L)*C)) := by ring
      _ ≤ η * β m C := mul_le_mul_of_nonneg_left (le_max_right _ _) hη.le
  · intro m C D' f g hC hD' hf hg hbf hbg hbf' hbg' hfg
    have hfs := contDiffOn_univ.mp hf
    have hgs := contDiffOn_univ.mp hg
    have hDC : 1 ≤ D (m+L)*C := one_le_mul_of_one_le_of_one_le (hD _) hC
    have hl (i : A.centers) := hdiff i m (D (m+L)*C) (D (m+L)*D') _ _ hDC
      (mul_nonneg (zero_le_one.trans (hD _)) hD') (hf0 f hfs i) (hf0 g hgs i)
      (hb0 f hfs hbf i) (hb0 g hgs hbg i)
      (hd (m+L) i f s C hs hs1 (zero_le_one.trans hC) hfs hbf')
      (hd (m+L) i g s C hs hs1 (zero_le_one.trans hC) hgs hbg')
      (by rw [← A.tensorPlaneRead_decode_sub]; exact
        hd (m+L) i (f-g) s D' hs hs1 hD' (hfs.sub hgs) hfg)
    have hnon : 0 ≤ K m (D (m+L)*C) * η * (D (m+L)*D') :=
      mul_nonneg (mul_nonneg (zero_le_one.trans (hK _ _ hDC)) hη.le)
        (mul_nonneg (zero_le_one.trans (hD _)) hD')
    have hb := he m (fun i => μ i (A.tensorPlaneRead i (A.tensorDecode f)) -
      μ i (A.tensorPlaneRead i (A.tensorDecode g))) s _ hs hs1 hnon
      (fun i => (hsm i _ (hf0 f hfs i) (hb0 f hfs hbf i)).sub
        (hsm i _ (hf0 g hgs i) (hb0 g hgs hbg i))) hl
    rw [← A.atlasMean_sub μ] at hb
    have hsec := (hms f hfs hbf).sub_section (hms g hgs hbg)
    have henc := A.tensorEncode_bound hsec hs (mul_nonneg (hE m) hnon) hb
    rw [A.tensorEncode_sub] at henc
    apply henc.mono_const
    calc
      _ = (E m * K m (D (m+L)*C) * D (m+L)) * η * D' := by ring
      _ ≤ κ m C * η * D' := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hη.le) hD'

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAtlasMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The atlas mean estimate with its read and restore constants exposed. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAtlasMeanFiberSpace
local instance polynomialAtlasMeanDualAdd_r665030_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAtlasMeanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAtlasMeanFiberNormed
local instance polynomialAtlasMeanSectionNormed_r665030_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialAtlasMeanSectionSpace_r665030_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem atlasMean_polynomial_majorants
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (L : ℕ) (p : ℕ → ℕ) (c G : ℕ → ℝ)
    (hc : ∀ m, 1 ≤ c m) (hG : ∀ m, 1 ≤ G m)
    (D E : ℕ → ℝ) (hD : ∀ m, 1 ≤ D m) (hE : ∀ m, 0 ≤ E m)
    (hd : ∀ m (i : A.centers) (f : Base → A.centers → TensorFiber) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C f →
      _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (D m*C) (A.tensorPlaneRead i (A.tensorDecode f)))
    (he : ∀ m (f : A.centers → SmallModes.Base → Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (f i)) →
      (∀ i, _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C (f i)) →
      A.TensorWeightedBound s m (E m*C) (A.tensorPlaneRestore f)) :
    ∀ r : ℝ, 0 ≤ r →
      (∀ f : Base → A.centers → TensorFiber, ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorEncode reference) r f → ∀ i : A.centers,
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r)
          (A.tensorPlaneRead i (A.tensorDecode f))) ∧
      ∀ {s : ℝ}, 0 < s → s ≤ 1 → ∀ η : ℝ, 0 < η →
      ∀ μ : A.centers → (SmallModes.Base → Tensor) → SmallModes.Base → Tensor,
      (∀ i f, ContDiff ℝ ∞ f → InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) f →
        ContDiff ℝ ∞ (μ i f)) →
      (∀ i m C f, 1 ≤ C → ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) f →
        _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s (m+L) C f → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (η * polynomialMeanProfile p c G m C) (μ i f)) →
      (∀ i m C D f g, 1 ≤ C → 0 ≤ D → ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) f →
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) g →
        _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s (m+L) C f → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s (m+L) C g →
        _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s (m+L) D (f-g) →
        _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (polynomialMeanProfile p c G m C * η * D) (μ i f - μ i g)) →
      MeanBounds univ s (A.tensorEncode reference) r L
        (rescaledMean η (A.tensorMeanOperator (A.atlasMean μ)))
        (polynomialMeanProfile (fun m => 2*p m+2) (fun m => 1+c m)
          (transportedMeanGeometry L G D E))
        (polynomialMeanProfile (fun m => 2*p m+2) (fun m => 1+c m)
          (transportedMeanGeometry L G D E)) := by
  have hB (m : ℕ) (C : ℝ) (_hC : 1 ≤ C) : 1 ≤ polynomialMeanProfile p c G m C := by
    apply one_le_mul_of_one_le_of_one_le (hc m)
    apply one_le_pow₀
    exact (hG m).trans (le_add_of_nonneg_right (zero_le_one.trans (le_max_left 1 C)))
  intro r hr
  obtain ⟨hball,β,κ,hβ,hκ,hm⟩ := A.atlasMean_majorants_explicit reference href L
    (polynomialMeanProfile p c G) (polynomialMeanProfile p c G) hB hB D E hD hE hd he r hr
  subst β κ
  refine ⟨hball,?_⟩
  intro s hs hs1 η hη μ hsm hv hdiff
  apply (hm hs hs1 η hη μ hsm hv hdiff).mono_majorants
  · intro m C hC
    simpa only [polynomialMeanProfile, transportedMeanGeometry] using
      polynomialMeanProfile_value_transport_bound (p m) (zero_le_one.trans (hc m))
        (hG m) (hD (m+L)) (hE m) hC
  · intro m C hC
    simpa only [polynomialMeanProfile, transportedMeanGeometry] using
      polynomialMeanProfile_transport_bound (p m) (zero_le_one.trans (hc m))
        (hG m) (hD (m+L)) (hE m) hC

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialBudgetMeanFamily
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the actual finite metric mean from one common bound on its
seven local budgets. The envelope records the derivative shift explicitly. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem polynomial_mean_family_from_budgets (q : ℕ) :
    ∃ (p : ℕ → ℕ) (C : ℕ → ℝ), (∀ m, 1 ≤ C m) ∧
    ∀ {ι : Type*} [Fintype ι] {n : ℕ} {P : Fin 3 → Fin n → Expression} {τ : ℝ}
      {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
      {K : ι → Compacts Base} {s : ℝ≥0}
      (c : ∀ i, PolynomialSolveData P 0 G hG (φ i) (K i) τ s)
      {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ∀ i, ChartedMeanData (c i) r ρ R reference),
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ H B : ℕ → ℝ, (∀ m, 1 ≤ H m) → (∀ m, 0 ≤ B m) →
      (∀ m, (Fintype.card ι : ℝ) ≤ H m ∧ ρ⁻¹ ≤ H m) →
      (∀ i m, (d i).budgets.inv m ≤ B m ∧ (d i).budgets.chi m ≤ B m ∧
        (d i).budgets.forms m ≤ B m ∧ (d i).budgets.pull m ≤ B m ∧
        (d i).budgets.psi m ≤ B m ∧ (d i).budgets.normal m ≤ B m ∧
        (d i).budgets.mode m ≤ B m) →
      ∀ δ : ℝ, 0 < δ → MeanBounds univ s reference r (q+2)
        (rescaledMean (τ/s) (chartedFamilyMean d hρ δ q))
        (polynomialMeanProfile p C (meanGeometryEnvelope q H B))
        (polynomialMeanProfile p C (meanGeometryEnvelope q H B)) := by
  obtain ⟨p,C,hC,hmean⟩ := polynomial_charted_metric_mean_family q
  refine ⟨p,C,hC,?_⟩
  intro ι _ n P τ G hG φ K s c r ρ R reference d hρ hτ hs hτs hs1 H B hH hB hHB hb δ hδ
  have henv (m : ℕ) : 1 ≤ meanGeometryEnvelope q H B m ∧
      H m ≤ meanGeometryEnvelope q H B m ∧
      B (m+q+2) ≤ meanGeometryEnvelope q H B m ∧
      B m ≤ meanGeometryEnvelope q H B m := by
    dsimp [meanGeometryEnvelope]
    have h₀ := hB m
    have h₁ := hB (m+q+2)
    have h₂ := hH m
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  apply hmean c d hρ hτ hs hτs hs1 (meanGeometryEnvelope q H B)
    (fun m => (henv m).1) (fun m => (hHB m).1.trans (henv m).2.1) _ δ hδ
  intro i m
  obtain ⟨hi,hχ,hQ,hpull,hψ,hn,hm⟩ := hb i (m+q+2)
  obtain ⟨_,hχ₀,_,hpull₀,_,_,_⟩ := hb i m
  exact ⟨(hHB m).2.trans (henv m).2.1,
    hi.trans (henv m).2.2.1,hQ.trans (henv m).2.2.1,
    hψ.trans (henv m).2.2.1,hm.trans (henv m).2.2.1,
    hn.trans (henv m).2.2.1,hχ₀.trans (henv m).2.2.2,hpull₀.trans (henv m).2.2.2⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialFiniteAtlasMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual atlas mean bounds with polynomial dependence on all local budgets
and on the number of cells in each chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates FiniteMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteMeanFiberSpace
local instance polynomialFiniteMeanDualAdd_r665030_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteMeanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteMeanFiberNormed
local instance polynomialFiniteMeanSectionNormed_r665030_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialFiniteMeanSectionSpace_r665030_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_finite_atlas_mean_oai (q : ℕ) :
    ∃ (p : ℕ → ℕ) (C D E : ℕ → ℝ),
      (∀ m, 1 ≤ C m) ∧ (∀ m, 1 ≤ D m) ∧ (∀ m, 0 ≤ E m) ∧
    ∀ (reference : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (reference x)) →
    ∀ r : ℝ, 0 ≤ r → ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
      {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
      {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
      {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
      {τ : ℝ} {s : ℝ≥0}
      {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
      {ρ R : ℝ}
      (d : ∀ i j, ChartedMeanData (c i j) (A.tensorReadBallConstant*r) ρ R (A.tensorPlaneRead i reference)),
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ H B : ℕ → ℝ, (∀ m, 1 ≤ H m) → (∀ m, 0 ≤ B m) →
      (∀ i m, (Fintype.card (ι i) : ℝ) ≤ H m ∧ ρ⁻¹ ≤ H m) →
      (∀ i j m, (d i j).budgets.inv m ≤ B m ∧ (d i j).budgets.chi m ≤ B m ∧
        (d i j).budgets.forms m ≤ B m ∧ (d i j).budgets.pull m ≤ B m ∧
        (d i j).budgets.psi m ≤ B m ∧ (d i j).budgets.normal m ≤ B m ∧
        (d i j).budgets.mode m ≤ B m) →
      ∀ δ : ℝ, 0 < δ → MeanBounds univ s (A.tensorEncode reference) r (q+2)
        (rescaledMean (τ/s) (A.tensorMeanOperator
          (A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q))))
        (polynomialMeanProfile (fun m => 2*p m+2) (fun m => 1+C m)
          (transportedMeanGeometry (q+2) (meanGeometryEnvelope q H B) D E))
        (polynomialMeanProfile (fun m => 2*p m+2) (fun m => 1+C m)
          (transportedMeanGeometry (q+2) (meanGeometryEnvelope q H B) D E)) := by
  classical
  obtain ⟨p,C,hC,hmean⟩ := polynomial_mean_family_from_budgets q
  choose D hD hd using A.tensorPlaneRead_decode_bound
  choose E hE he using A.tensorPlaneRestore_bound
  refine ⟨p,C,D,E,hC,hD,hE,?_⟩
  intro reference href r hr ι _ n P G hG φ K τ s c ρ R d hρ hτ hs hτs hs1 H B hH hB hHB hb δ hδ
  have henv (m : ℕ) : 1 ≤ meanGeometryEnvelope q H B m := by
    dsimp [meanGeometryEnvelope]
    linarith [hH m,hB m,hB (m+q+2)]
  have hlocal (i : A.centers) := hmean (c i) (d i) hρ hτ hs hτs hs1 H B hH hB (hHB i) (hb i) δ hδ
  have hg := (A.atlasMean_polynomial_majorants reference href (q+2) p C
    (meanGeometryEnvelope q H B) hC henv D E hD hE hd he r hr).2 (s := (s : ℝ))
  have hη : 0 < τ/(s : ℝ) := div_pos hτ hs
  have hη1 : τ/(s : ℝ) ≤ 1 := (div_le_one₀ hs).mpr hτs
  apply hg hs hs1 (τ/s) hη (fun i => chartedFamilyMean (d i) hρ δ q)
  · intro i f hf hball
    have hh := (hlocal i).smooth (τ/s) hη hη1 f hf.contDiffOn hball
    rw [rescaledMean_self hη.ne'] at hh
    exact contDiffOn_univ.mp hh
  · intro i m C₀ f hC₀ hf hball hbf
    have hh := (hlocal i).value (τ/s) hη hη1 m C₀ f hC₀ hf.contDiffOn hball hbf
    rwa [rescaledMean_self hη.ne'] at hh
  · intro i m C₀ D₀ f g hC₀ hD₀ hf hg hballf hballg hbf hbg hdiff
    have hh := (hlocal i).difference (τ/s) hη hη1 m C₀ D₀ f g hC₀ hD₀
      hf.contDiffOn hg.contDiffOn hballf hballg hbf hbg hdiff
    rwa [rescaledMean_self hη.ne'] at hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_mean_oai.{u_1, u_2} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_mean_oai.{u_1, u_2}
