-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_forced_increment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:47:12.550626+00:00
-- url     : https://prove2.me/submissions/662cc24e-04ab-41e4-be69-1ccbcd44ccae

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_atlas_increment_bound
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_global_quadratic_correction
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_finite_atlas_free
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_PolynomialSolveData_originalFreeSeed_bound

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
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



lemma WeightedBound.fderivWithin {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hs : 0 < s) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) (fderivWithin ℝ f U) := by
  intro j hj x hx
  rw [norm_iteratedFDerivWithin_fderivWithin hU hx]
  apply (le_div_iff₀ hs).2
  have hh := hb (j + 1) (Nat.add_le_add_right hj 1) x hx
  rw [pow_succ] at hh
  nlinarith

lemma WeightedBound.clm_apply_const {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : E → F →L[ℝ] G} (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s m C f) (v : F) :
    WeightedBound U s m (‖v‖ * C) (fun x => f x v) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (‖v‖ * ‖iteratedFDerivWithin ℝ j f U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_clm_apply_const (n := j) (N := ∞)
        (hf.contDiffWithinAt hx) hU hx (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ = ‖v‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg v)



lemma WeightedBound.comp {U : Set E} {V : Set F} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {s C D : ℝ} {m : ℕ} {f : E → F} {g : F → G} (hs : 0 < s) (hC : 1 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V) (hUV : MapsTo f U V)
    (hbf : WeightedBound U s m C f)
    (hbg : ∀ j ≤ m, ∀ x ∈ U, ‖iteratedFDerivWithin ℝ j g V (f x)‖ ≤ D) :
    WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (g ∘ f) := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  intro j hj x hx
  have hi (i : ℕ) (hi1 : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i f U x‖ ≤ (C / s) ^ i := by
    have hp : C ≤ C ^ i := by
      simpa only [pow_one] using pow_le_pow_right₀ hC hi1
    calc
      _ ≤ C / s ^ i := hbf.deriv_le hs (hij.trans hj) hx
      _ ≤ C ^ i / s ^ i := div_le_div_of_nonneg_right hp (pow_nonneg hs.le _)
      _ = _ := (div_pow C s i).symm
  have hn : (j : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  have hh := norm_iteratedFDerivWithin_comp_le hg hf hn hV hU hUV hx
    (fun i hij => hbg i (hij.trans hj) x hx) hi
  calc
    _ ≤ s ^ j * ((j.factorial : ℝ) * D * (C / s) ^ j) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = (j.factorial : ℝ) * D * C ^ j := by
      rw [div_pow]
      field_simp
    _ ≤ _ := by
      gcongr




lemma WeightedBound.congr {U : Set E} {s C : ℝ} {m : ℕ} {f g : E → F}
    (hf : WeightedBound U s m C f) (he : EqOn g f U) : WeightedBound U s m C g := by
  intro j hj x hx
  rw [iteratedFDerivWithin_congr he hx]
  exact hf j hj x hx

lemma WeightedBound.directional {U : Set E} (hU : IsOpen U) {s C : ℝ} {m : ℕ}
    {f : E → F} (hs : 0 < s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s (m + 1) C f) (v : E) :
    WeightedBound U s m (‖v‖ * (C / s)) (fun x => fderiv ℝ f x v) := by
  have hd := hb.fderivWithin hU.uniqueDiffOn hs
  have hdsm : ContDiffOn ℝ ∞ (_root_.fderivWithin ℝ f U) U :=
    hf.fderivWithin hU.uniqueDiffOn (by exact le_rfl)
  apply (hd.clm_apply_const hU.uniqueDiffOn hs.le hdsm v).congr
  intro x hx
  dsimp only
  rw [fderivWithin_of_isOpen hU hx]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ModeBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

section Quantitative
variable {n : ℕ}



lemma reducedConstant_nonneg (m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ reducedConstant m K := by
  unfold reducedConstant
  positivity

lemma errorConstant_nonneg (m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ errorConstant m K := by
  unfold errorConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (reducedConstant_nonneg m hK)) (by positivity)

lemma targetConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ targetConstant n m K := by
  unfold targetConstant
  positivity

lemma fullErrorConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ fullErrorConstant n m K :=
  mul_nonneg (mul_nonneg (by norm_num) (reducedConstant_nonneg m hK))
    (targetConstant_nonneg n (m + 1) hK)

lemma amplitudeConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ amplitudeConstant n m K := by
  unfold amplitudeConstant
  exact mul_nonneg (by positivity) (targetConstant_nonneg _ _ hK)

lemma initialConstant_nonneg (n m : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ initialConstant n m K := by
  unfold initialConstant
  exact add_nonneg (by positivity) (amplitudeConstant_nonneg _ _ hK)

end Quantitative
end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RootMean
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


lemma sqrt_difference {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    Real.sqrt u - Real.sqrt v = (u - v) * rootDifferenceCoefficient ![u, v] := by
  have hh : Real.sqrt u + Real.sqrt v ≠ 0 := ne_of_gt
    (add_pos (Real.sqrt_pos.2 hu) (Real.sqrt_pos.2 hv))
  dsimp [rootDifferenceCoefficient]
  rw [← div_eq_mul_inv]
  apply (eq_div_iff hh).2
  nlinarith [Real.sq_sqrt hu.le, Real.sq_sqrt hv.le]

end ClosedSurfaceR4.RootMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean
open Set

lemma weighted_coefficient {U V : Set Base} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {Q : Base → Tensor →L[ℝ] ℝ} {e : Base → Base} {A : Base → Tensor}
    {s J P C : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hJ : 1 ≤ J) (hP : 0 ≤ P)
    (hC : 0 ≤ C) (hQ : ContDiffOn ℝ ∞ Q V) (he : ContDiffOn ℝ ∞ e V)
    (heU : MapsTo e V U) (hA : ContDiffOn ℝ ∞ A U)
    (heB : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ V, ‖iteratedFDerivWithin ℝ j e V p‖ ≤ J)
    (hQB : WeightedBound V s m P Q) (hAB : WeightedBound U s m C A) :
    WeightedBound V s m ((2 ^ m * P * (m.factorial : ℝ) * J ^ m) * C)
      (coefficient Q e A) := by
  have hAe := hAB.comp_coordinates hV hU hs hs1 hJ hC he hA heU heB
  have hh := hQB.clm_apply hV hs.le hP (by positivity) hQ (hA.comp he heU) hAe
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  ring

lemma weighted_coefficient_difference {U V : Set Base} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {Q : Base → Tensor →L[ℝ] ℝ} {e : Base → Base} {A B : Base → Tensor}
    {s J P D : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hJ : 1 ≤ J) (hP : 0 ≤ P)
    (hD : 0 ≤ D) (hQ : ContDiffOn ℝ ∞ Q V) (he : ContDiffOn ℝ ∞ e V)
    (heU : MapsTo e V U) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (heB : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ V, ‖iteratedFDerivWithin ℝ j e V p‖ ≤ J)
    (hQB : WeightedBound V s m P Q) (hAB : WeightedBound U s m D (A - B)) :
    WeightedBound V s m ((2 ^ m * P * (m.factorial : ℝ) * J ^ m) * D)
      (fun p => coefficient Q e A p - coefficient Q e B p) := by
  apply (weighted_coefficient hU hV hs hs1 hJ hP hD hQ he heU (hA.sub hB) heB hQB hAB).congr
  intro p hp
  exact (map_sub (Q p) (A (e p)) (B (e p))).symm




end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




lemma WeightedBound.extend_support {U : Set E} (hU : IsOpen U) {f : E → F}
    (hfs : tsupport f ⊆ U) {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C f) : WeightedBound univ s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_univ]
  by_cases hxU : x ∈ U
  · rw [← iteratedFDerivWithin_of_isOpen j hU hxU]
    exact hb j hj x hxU
  · have hz : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hh => hxU (hfs hh))
    rw [(hz.iteratedFDeriv ℝ j).self_of_nhds]
    simpa using hC

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma WeightedBound.restrict_open {U : Set E} (hU : IsOpen U) {f : E → F}
    {s C : ℝ} {m : ℕ} (hb : WeightedBound univ s m C f) : WeightedBound U s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hU hx]
  simpa only [iteratedFDerivWithin_univ] using hb j hj x (mem_univ x)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldFreeIncrement
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local free oscillations as maps on the surface

The finite-mode construction takes place in coordinates. These lemmas
extend its supported output by zero on the surface, preserving smoothness
and support. This is the first globalization step for the small increments.
-/

noncomputable section

namespace ClosedSurfaceR4

open Set Manifold
open scoped ContDiff Topology
open SmallModes RealModes RootMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

/-- Extension by zero across a closed support lying inside the smooth chart. -/
theorem contMDiff_indicator_of_support {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {O S : Set M} {Z : M → V}
    (hO : IsOpen O) (hS : IsClosed S) (hSO : S ⊆ O)
    (hZ : ContMDiffOn planeModel 𝓘(ℝ, V) ∞ Z O)
    (hz : ∀ x ∈ O, x ∉ S → Z x = 0) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (O.indicator Z) ∧
      tsupport (O.indicator Z) ⊆ S := by
  classical
  have hs : tsupport (O.indicator Z) ⊆ S := by
    apply closure_minimal _ hS
    intro x hx
    by_contra hxS
    by_cases hxO : x ∈ O
    · exact hx (by rw [indicator_of_mem hxO, hz x hxO hxS])
    · exact hx (indicator_of_notMem hxO Z)
  refine ⟨contMDiff_of_tsupport (fun x hx => ?_), hs⟩
  have hxO : x ∈ O := hSO (hs hx)
  apply ((hZ x hxO).contMDiffAt (hO.mem_nhds hxO)).congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact indicator_of_mem hy Z

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smoothing maps on a closed surface, assembled from a fixed atlas. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma restore_smooth (p : M) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (chart p).source) {h : Base → V} (hh : ContDiff ℝ ∞ h) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (restore p χ h) := by
  apply (contMDiff_indicator_of_support (chart p).open_source
    (isClosed_tsupport χ) hs
    (hχ.contMDiffOn.smul (hh.contMDiff.comp_contMDiffOn (chart_smooth p))) ?_).1
  intro x _ hx
  change χ x • h (chart p x) = 0
  rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]

namespace SmoothingAtlas

variable (A : SmoothingAtlas M)

variable [CompactSpace M]

omit [CompactSpace M] in
lemma restore_localize (i : A.centers) (f : M → V) (x : M) :
    restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f) x =
      (A.weight i x) ^ 2 • f x := by
  by_cases hx : x ∈ (chart (i : M)).source
  · rw [restore, indicator_of_mem hx, localize_chart _ _ _ hx]
    by_cases hzero : A.weight i x = 0
    · simp only [hzero, zero_pow (by decide : 2 ≠ 0), zero_smul, smul_zero]
    · rw [A.outer_one i x (subset_tsupport _ hzero), one_smul]
  · have hz : A.weight i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.weight_support i h))
    simp only [restore, indicator_of_notMem hx, hz, zero_pow (by decide : 2 ≠ 0), zero_smul]

omit [CompactSpace M] in
lemma sum_restore_localize (f : M → V) :
    (∑ i : A.centers, restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f)) = f := by
  funext x
  simp only [Finset.sum_apply, A.restore_localize]
  rw [← Finset.sum_smul, A.partition, one_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalizedCompositionBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth cutoff and chart transition operators preserve weighted
norms with constants independent of the input and its scale. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set WeightedEstimates
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A compactly supported coordinate change costs a fixed constant in each
weighted derivative norm; it introduces no additional scale loss. -/
theorem compact_localized_composition_bound {O K : Set Base}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : tsupport χ ⊆ K)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedBound Set.univ s m C f →
      WeightedBound Set.univ s m (D * C) (fun x => χ x • f (T x)) := by
  obtain ⟨U, hU, hKU, hUO, hUc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  have hsub : U ⊆ O := subset_closure.trans hUO
  obtain ⟨A, hA, hbA⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hχ.contDiffOn m
  obtain ⟨B, hB, hbB⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hT m
  refine ⟨2 ^ m * A * ((m.factorial : ℝ) * B ^ m), by positivity, ?_⟩
  intro f s C hs hs1 hC hf hb
  have hTj : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j T U x‖ ≤ B := by
    intro j _ hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) T x :=
      (hT.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hO.mem_nhds (hsub hx))
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbB j hj x (subset_closure hx)
    rwa [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
  have hχb : WeightedBound U s m A χ := by
    intro j hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) χ x := (hχ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbA j hj x (subset_closure hx)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs.le hs1)).trans h
  have hc := hb.comp_coordinates hU.uniqueDiffOn uniqueDiffOn_univ hs hs1 hB hC
    (hT.mono hsub) hf.contDiffOn (fun _ _ => mem_univ _) hTj
  have hcomp : ContDiffOn ℝ ∞ (fun x => f (T x)) U :=
    hf.contDiffOn.comp (hT.mono hsub) (fun _ _ => mem_univ _)
  have hp := hχb.smul_real hU.uniqueDiffOn hs.le (zero_le_one.trans hA)
    (by positivity) hχ.contDiffOn hcomp hc
  have hlocal : ContDiffOn ℝ ∞ (fun x => χ x • f (T x)) U := hχ.contDiffOn.smul hcomp
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hx : x ∈ U
  · have ht : ContDiffAt ℝ (j : ℕ∞ω) (fun x => χ x • f (T x)) x :=
      (hlocal.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hU.mem_nhds hx)
    have h := hp j hj x hx
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have hxK : x ∉ K := fun hk => hx (hKU hk)
    have hxχ : x ∉ tsupport χ := fun hx' => hxK (hχK hx')
    have heq : (fun y => χ y • f (T y)) =ᶠ[𝓝 x] (fun _ => (0 : V)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_smul]
    have hd := (heq.iteratedFDeriv ℝ j).self_of_nhds
    rw [hd]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    positivity

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasWeightedBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-atlas weighted norms and bounds for the actual restoration operator. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [IsManifold planeModel ∞ M] in
lemma localize_sum {ι : Type*} (b : Finset ι) (p : M) (ψ : M → ℝ) (f : ι → M → V) :
    localize p ψ (∑ i ∈ b, f i) = fun x => ∑ i ∈ b, localize p ψ (f i) x := by
  funext x
  by_cases hx : x ∈ (chart p).target <;>
    simp [localize, hx, Finset.sum_apply, Finset.smul_sum]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasLinearMapBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed linear coordinate changes preserve the actual atlas norm. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V W : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma localize_clm (p : M) (χ : M → ℝ) (L : V →L[ℝ] W) (F : M → V) :
    localize p χ (L ∘ F) = L ∘ localize p χ F := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize,hx,map_smul]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma weightedBound_clm (L : V →L[ℝ] W) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) {s C : ℝ} {m : ℕ}
    (hs : 0 ≤ s) (hb : A.WeightedBound s m C F) :
    A.WeightedBound s m (‖L‖*C) (L ∘ F) := by
  intro i
  rw [localize_clm]
  exact (hb i).linear uniqueDiffOn_univ hs
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).contDiffOn L

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedWeightedSeminorm
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted derivative bounds as actual seminorms on smooth fields
with fixed compact support, for finite derivative-loss parametrix iteration. -/
noncomputable section
open TopologicalSpace
open scoped Distributions NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma supportedWeightedSeminorm_component {K : Compacts A} (s : ℝ≥0) (m j : ℕ)
    (hj : j ≤ m) (f : SupportedField (F := F) K) :
    (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤
      supportedWeightedSeminorm K s m f := by
  let q : ℕ → Seminorm ℝ (SupportedField (F := F) K) :=
    fun j => s ^ j • ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j
  have h : q j f ≤ (Finset.range (m + 1)).sup q f :=
    Seminorm.le_finset_sup_apply (show j ∈ Finset.range (m + 1) by simpa using hj)
  simpa only [q, supportedWeightedSeminorm, smul_apply, NNReal.smul_def,
    NNReal.coe_pow, smul_eq_mul] using h

lemma weightedBound_of_supportedSeminorm {K : Compacts A} (s : ℝ≥0) (m : ℕ)
    (f : SupportedField (F := F) K) :
    WeightedBound Set.univ s m (supportedWeightedSeminorm K s m f) f := by
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  calc
    (s : ℝ) ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤
        (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f :=
      mul_le_mul_of_nonneg_left (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ)
        (pow_nonneg s.coe_nonneg _)
    _ ≤ _ := supportedWeightedSeminorm_component s m j hj f

lemma supportedSeminorm_le_of_weightedBound {K : Compacts A} {s : ℝ≥0} (hs : 0 < (s : ℝ))
    {m : ℕ} {C : ℝ} (hC : 0 ≤ C) (f : SupportedField (F := F) K)
    (hb : WeightedBound Set.univ s m C f) : supportedWeightedSeminorm K s m f ≤ C := by
  apply Seminorm.finset_sup_apply_le hC
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  change (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤ C
  have hn : ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤ C / (s : ℝ) ^ j := by
    apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (div_nonneg hC (pow_nonneg s.coe_nonneg _)) j f).2
    intro x _
    simpa only [iteratedFDerivWithin_univ] using hb.deriv_le hs hjm (Set.mem_univ x)
  calc
    _ ≤ (s : ℝ) ^ j * (C / (s : ℝ) ^ j) := mul_le_mul_of_nonneg_left hn (pow_nonneg s.coe_nonneg _)
    _ = C := by field_simp [ne_of_gt hs]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
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

variable [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadSectionNormed
local instance planeReadSectionSpace_r332fac_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRead_smooth (i : A.centers) {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContDiff ℝ ∞ (A.tensorPlaneRead i u) :=
  (A.tensorChartRead_smooth i hu).comp planeCoordinateIsometry.symm.contDiff

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteParametrix
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite parametrix improvement with derivative loss. This is a finite
algebraic iteration; no bounded inverse on one Banach space is assumed. -/
noncomputable section

namespace ClosedSurfaceR4.FiniteParametrix

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma boundProfile_nonneg {L : ℕ} {K C : ℕ → ℝ}
    (hK : ∀ m, 0 ≤ K m) (hC : ∀ m, 0 ≤ C m) (j m : ℕ) :
    0 ≤ boundProfile L K C j m := by
  induction j generalizing m with
  | zero => exact hC m
  | succ j ih => exact mul_nonneg (hK m) (ih (m + L))

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformFreeModeConstants
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit free-mode constants, independent of both short scales and
of the perturbation size. These constants are used before selecting scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

lemma freeModeBudget_nonneg (n L : ℕ) (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (q m : ℕ) :
    0 ≤ freeModeBudget n L B D q m := by
  apply add_nonneg _ (amplitudeConstant_nonneg _ _ (hB m))
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (initialConstant_nonneg _ _ (hB m))
  exact FiniteParametrix.boundProfile_nonneg
    (fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _))
    (fun r => (fullErrorConstant_nonneg _ _ (hB r)).trans (le_max_left _ _)) _ _

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CorrectedNormalSeed
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit size and difference budgets for the actual corrected normal seed. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
open JetPolynomial (SupportedField supportedWeightedSeminorm)

variable {F : RField 4} {U : Set Base}

lemma correctedSeedBudget_nonneg (L : ℕ) (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m)
    (q m : ℕ) {N : ℝ} (hN : 0 ≤ N) : 0 ≤ correctedSeedBudget L B D q m N := by
  have h := freeModeBudget_nonneg 4 L B D hB q m
  dsimp only [correctedSeedBudget]
  positivity

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartedTrialAmplitude
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutoff square-root trial amplitudes on the actual transported support.
These use the original tensor field and the inverse of its phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (ψ : SupportedField (F := ℝ) c.chartCompact)
    (Q : SmallModes.Base → Tensor →L[ℝ] ℝ)
    (h : LocalBounds c.e.source c.e.target s r ρ R reference c.realMap ψ Q c.e c.e.symm)

lemma trialAmplitude_apply (hρ : 0 < ρ) {A : SmallModes.Base → Tensor}
    (hA : ContDiffOn ℝ ∞ A c.e.source) (hball : InTrialBall c.e.source reference r A)
    (y : SmallModes.Base) :
    c.trialAmplitude ψ Q h hρ A y = phaseAmplitude ψ (coefficient Q c.e.symm A) y := by
  classical
  simp only [trialAmplitude, dite_eq_left (show ContDiffOn ℝ ∞ A c.e.source ∧
    InTrialBall c.e.source reference r A from ⟨hA,hball⟩)]
  rfl

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorReadBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed atlas bounds for the genuine smooth coordinate representatives.
The constants precede the map and scale, and no derivative order is lost. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma localize_outer_restore (i j : A.centers) (f : JetPolynomial.Base → V) :
    localize (i : M) (A.outer i) (restore (j : M) (A.outer j) f) =
      fun x => localize (i : M) (A.outer i) (A.outer j) x •
        f (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize,restore,indicator_of_mem hi,indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hj (A.outer_support j h))
      simp only [localize,restore,indicator_of_mem hi,indicator_of_notMem hj,hz,smul_zero,zero_smul]
  · simp only [localize,indicator_of_notMem hi,zero_smul]

lemma localize_outer_restore_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : JetPolynomial.Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedEstimates.WeightedBound univ s m C f →
      WeightedEstimates.WeightedBound univ s m (D*C)
        (localize (i : M) (A.outer i) (restore (j : M) (A.outer j) f)) := by
  let K := (chart (i : M)) '' (tsupport (A.outer i) ∩ tsupport (A.outer j))
  have hK : IsCompact K :=
    ((isClosed_tsupport _).inter (isClosed_tsupport _)).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono (fun _ h => A.outer_support i h.1))
  have hKO : K ⊆ (transition (i : M) (j : M)).source := by
    rintro x ⟨p,hp,rfl⟩
    refine ⟨(chart (i : M)).map_source (A.outer_support i hp.1),?_⟩
    change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
    rw [(chart (i : M)).left_inv (A.outer_support i hp.1)]
    exact A.outer_support j hp.2
  obtain ⟨D,hD,hd⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source hK hKO
    (localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i) (A.outer_smooth j))
    (localize_tsupport_inter (i : M) (A.outer_support i) (A.outer j))
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D,hD,?_⟩
  intro f s C hs hs1 hC hf hb
  rw [A.localize_outer_restore]
  exact hd f s C hs hs1 hC hf hb

theorem vectorChartRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.WeightedBound s m C F →
      WeightedEstimates.WeightedBound univ s m (D*C) (A.vectorChartRead i F) := by
  classical
  choose D hD hd using fun j : A.centers => A.localize_outer_restore_bound (V := V) i j m
  refine ⟨∑ j : A.centers, D j,Finset.sum_nonneg (fun j _ => hD j),?_⟩
  intro F s C hs hs1 hC hF hb
  have he : A.vectorChartRead i F = fun x => ∑ j : A.centers,
      localize (i : M) (A.outer i)
        (restore (j : M) (A.outer j) (localize (j : M) (A.weight j) F)) x := by
    unfold vectorChartRead
    conv_lhs => rw [← A.sum_restore_localize F]
    exact localize_sum Finset.univ _ _ _
  rw [he,Finset.sum_mul]
  apply WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
  · intro j _
    exact (localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
      (restore_smooth (j : M) (A.outer_smooth j) (A.outer_support j)
        (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF))).contDiffOn
  · intro j _
    exact hd j _ s C hs hs1 hC
      (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF) (hb j)

theorem vectorPlaneRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.WeightedBound s m C F →
      WeightedEstimates.WeightedBound univ s m (D*C) (A.vectorPlaneRead i F) := by
  obtain ⟨D,hD,hd⟩ := A.vectorChartRead_bound (V := V) i m
  refine ⟨D,hD,?_⟩
  intro F s C hs hs1 hC hF hb
  exact weightedBound_comp_isometry planeCoordinateIsometry.symm
    (A.vectorChartRead_smooth i hF) (hd F s C hs hs1 hC hF hb)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalOscillatoryModes
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global phase/amplitude representatives of the actual supported oscillations. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (planeCoordinateIsometry)
open QuadraticMean (realMode realPartCLM)

lemma realMode_contDiff {n : ℕ} (τ : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) => realMode (p.1/τ) p.2) := by
  change ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) =>
    realPartCLM n (QuadraticMean.phase (p.1/τ) • p.2))
  apply (realPartCLM n).contDiff.comp
  apply ContDiff.smul (f := fun p : ℝ × (Fin n → ℂ) => QuadraticMean.phase (p.1/τ))
    (g := fun p : ℝ × (Fin n → ℂ) => p.2)
  · have ha : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) => ((p.1/τ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_fst.div_const τ)
    exact Complex.contDiff_exp.comp (ha.mul contDiff_const)
  · exact contDiff_snd

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma surfaceMode_smooth {n : ℕ} (τ : ℝ) {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z) :
    ContMDiff planeModel 𝓘(ℝ,Fin n → ℝ) ∞ (surfaceMode τ φ Z) :=
  (realMode_contDiff τ).contMDiff.comp (hφ.prodMk_space hZ)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteAtlasFreeMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact global free-mode identities for an arbitrary finite family in
each fixed atlas chart. This accommodates the variable number of grid cells. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeFiberSpace
local instance finiteAtlasFreeDualSmul_r332fac_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeFiberNormed
local instance finiteAtlasFreeSectionNormed_r332fac_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance finiteAtlasFreeSectionSpace_r332fac_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteAtlasIndexDecidable
omit [CompactSpace M] in
lemma finiteAtlasFreeOscillation_smooth
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x) :
    ContMDiff planeModel 𝓘(ℝ, RealModes.RVec 4) ∞
      (A.finiteAtlasFreeOscillation d hρ δ q u) := by
  have hh := ContMDiff.sum (t := Finset.univ) (fun (a : Σ i, ι i) _ => surfaceMode_smooth τ
    (restore_smooth (a.1 : M) (A.outer_smooth a.1) (A.outer_support a.1)
      (c a.1 a.2).smoothPhase)
    (restore_smooth (a.1 : M) (A.outer_smooth a.1) (A.outer_support a.1)
      ((d a.1 a.2).freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)).contDiff))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [finiteAtlasFreeOscillation,finiteGlobalPhase,finiteGlobalAmplitude,Finset.sum_apply]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasPhaseCatalog
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed finite catalogs for the actual restored global grid phases and
their readings in every atlas chart. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma restored_linear_phase_mem_catalog (V : Finset SmallModes.Base)
    (i : A.centers) {v : SmallModes.Base} (hv : v ∈ V) :
    restore (i : M) (A.outer i) (phaseLinear v ∘ planeCoordinateIsometry) ∈
      A.linearPhaseCatalog V := by
  classical
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨v,hv,rfl⟩⟩

lemma linearPhaseCatalog_smooth (V : Finset SmallModes.Base) :
    ∀ f ∈ A.linearPhaseCatalog V, ContMDiff planeModel 𝓘(ℝ) ∞ f := by
  classical
  intro f hf
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hf
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hi
  exact restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
    ((phaseLinear v).contDiff.comp planeCoordinateIsometry.contDiff)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ShiftedSmoothingBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing bounds with an unweighted finite derivative prefix. In the
correction scheme the map has prefix order two and the metric defect order zero. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates MeasureTheory
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma ShiftedBound.deriv_le {q m : ℕ} {s C : ℝ} {f : Base → V}
    (h : ShiftedBound q m s C f) (hs : 0 < s) {j : ℕ} (hj : j ≤ q + m) (x : Base) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ C / s ^ (j - q) := by
  apply (le_div_iff₀ (pow_pos hs _)).mpr
  simpa only [mul_comm] using h j hj x

/-- An unweighted prefix of any lower order is controlled by a shifted bound. -/
lemma ShiftedBound.prefix {q m : ℕ} {s C : ℝ} {f : Base → V}
    (h : ShiftedBound q m s C f) (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    {j : ℕ} (hj : j ≤ q + m) :
    WeightedBound Set.univ 1 j (C / s ^ (j - q)) f := by
  intro i hi x _
  simp only [one_pow, one_mul, iteratedFDerivWithin_univ]
  apply (h.deriv_le hs (hi.trans hj) x).trans
  exact div_le_div_of_nonneg_left hC (pow_pos hs _)
    (pow_le_pow_of_le_one hs.le hs1 (Nat.sub_le_sub_right hi q))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorReadPrefixBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chart readings retain the unweighted derivative prefix of the true map. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma prefix_directional_bound {f : SmallModes.Base → V} (hf : ContDiff ℝ ∞ f)
    {s C : ℝ} {m : ℕ} (hs : 0 < s) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m+1, WeightedEstimates.WeightedBound univ 1 j (C/s^(j-1)) f)
    (v : SmallModes.Base) (hv : ‖v‖ ≤ 1) :
    WeightedEstimates.WeightedBound univ s m C (SmallModes.coordDeriv v f) := by
  intro j hj x _
  have hh := ((hb (j+1) (by omega)).directional isOpen_univ zero_lt_one hf.contDiffOn v) j le_rfl x (mem_univ x)
  simp only [one_pow,one_mul,div_one,Nat.add_sub_cancel] at hh
  calc
    _ ≤ s^j*(‖v‖*(C/s^j)) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = ‖v‖*C := by field_simp
    _ ≤ C := mul_le_of_le_one_left hC hv

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem vectorPlaneRead_prefix_bounds (i : A.centers) (q m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.ShiftedBound q m s C F → ∀ j ≤ q+m,
      WeightedEstimates.WeightedBound univ 1 j (D*C/s^(j-q)) (A.vectorPlaneRead i F) := by
  classical
  choose D hD hd using fun j => A.vectorPlaneRead_bound (V := V) i j
  let T := ∑ j ∈ Finset.range (q+m+1), D j
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => hD j)
  refine ⟨T,hT,?_⟩
  intro F s C hs hs1 hC hF hb j hj
  have hp : A.WeightedBound 1 j (C/s^(j-q)) F := fun k => (hb k).prefix hs hs1 hC hj
  have hh := hd j F 1 (C/s^(j-q)) zero_lt_one le_rfl (by positivity) hF hp
  apply hh.mono_const
  calc
    D j*(C/s^(j-q)) = D j*C/s^(j-q) := by ring
    _ ≤ T*C/s^(j-q) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => hD k) (Finset.mem_range.mpr (by omega))) hC)
      (pow_nonneg hs.le _)

theorem vectorPlaneRead_directional_prefix_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.ShiftedBound 1 m s C F → ∀ v : SmallModes.Base, ‖v‖ ≤ 1 →
      WeightedEstimates.WeightedBound univ s m (D*C) (SmallModes.coordDeriv v (A.vectorPlaneRead i F)) := by
  obtain ⟨D,hD,hd⟩ := A.vectorPlaneRead_prefix_bounds (V := V) i 1 m
  refine ⟨D,hD,?_⟩
  intro F s C hs hs1 hC hF hb v hv
  exact prefix_directional_bound (A.vectorPlaneRead_smooth i hF) hs (mul_nonneg hD hC)
    (fun j hj => hd F s C hs hs1 hC hF hb j (by omega)) v hv

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CatalogPhaseBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every restored phase in the fixed catalog has a common derivative
budget, independent of the selected grid and the fast scale. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem linearPhaseCatalog_derivative_bounds (V : Finset SmallModes.Base) :
    ∃ P : ℕ → ℝ, (∀ m, 1 ≤ P m) ∧
      ∀ φ ∈ A.linearPhaseCatalog V, ∀ k : A.centers,
      ∀ (s : ℝ), 0 < s → s ≤ 1 → ∀ m v, ‖v‖ ≤ 1 →
        WeightedEstimates.WeightedBound univ s m (P m) (SmallModes.coordDeriv v (A.vectorPlaneRead k φ)) := by
  classical
  choose C hC hc using fun (φ : A.linearPhaseCatalog V) m =>
    A.exists_shifted_bound 1 m (A.linearPhaseCatalog_smooth V φ.val φ.property)
  choose D hD hd using fun (k : A.centers) m =>
    A.vectorPlaneRead_directional_prefix_bound (V := ℝ) k m
  let C₀ := fun m => ∑ φ : A.linearPhaseCatalog V, C φ m
  let D₀ := fun m => ∑ k : A.centers, D k m
  have hC₀ (m : ℕ) : 0 ≤ C₀ m := Finset.sum_nonneg (fun φ _ => hC φ m)
  have hD₀ (m : ℕ) : 0 ≤ D₀ m := Finset.sum_nonneg (fun k _ => hD k m)
  refine ⟨fun m => 1+D₀ m*C₀ m,fun m => le_add_of_nonneg_right
    (mul_nonneg (hD₀ m) (hC₀ m)),?_⟩
  intro φ hφ k s hs hs1 m v hv
  let f : A.linearPhaseCatalog V := ⟨φ,hφ⟩
  have hscale : A.ShiftedBound 1 m s (C f m) φ := by
    intro i j hj x
    have hh := hc f m i j hj x
    simp only [one_pow,one_mul] at hh
    calc
      _ ≤ 1*‖iteratedFDeriv ℝ j (localize (i : M) (A.weight i) φ) x‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hs.le hs1) (norm_nonneg _)
      _ ≤ C f m := by simpa only [one_mul] using hh
  have hc' : C f m ≤ C₀ m :=
    Finset.single_le_sum (fun g _ => hC g m) (Finset.mem_univ f)
  have hd' : D k m ≤ D₀ m :=
    Finset.single_le_sum (fun i _ => hD i m) (Finset.mem_univ k)
  apply (hd k m φ s (C f m) hs hs1 (hC f m)
    (A.linearPhaseCatalog_smooth V φ hφ) hscale v hv).mono_const
  exact (mul_le_mul hd' hc' (hC f m) (hD₀ m)).trans
    (le_add_of_nonneg_left zero_le_one)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedReciprocal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial weighted bounds for the reciprocal operations occurring in
metric inversion and normal reconstruction. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates

lemma norm_iteratedFDerivWithin_inv (j : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y⁻¹) ({0}ᶜ) x‖ =
      (j.factorial : ℝ)*‖x⁻¹‖^(j+1) := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  have h := iteratedDerivWithin_one_div j isOpen_compl_singleton
    (show x ∈ ({0}ᶜ : Set ℝ) from hx)
  simp only [one_div] at h
  rw [h,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Real.norm_natCast,norm_zpow]
  have he : (-1-(j : ℤ)) = -((j+1 : ℕ) : ℤ) := by omega
  rw [he,zpow_neg,zpow_natCast,← inv_pow,← norm_inv]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Both the input size and inverse denominator enter polynomially at each
fixed derivative order. There is no compact-range hypothesis. -/
theorem WeightedBound.inv_real {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C K : ℝ} {m : ℕ} {f : E → ℝ}
    (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    (hf : ContDiffOn ℝ ∞ f U) (hne : ∀ x ∈ U, f x ≠ 0)
    (hInv : ∀ x ∈ U, ‖(f x)⁻¹‖ ≤ K) (hb : WeightedBound U s m C f) :
    WeightedBound U s m ((m.factorial : ℝ)^2*K^(m+1)*C^m) (fun x => (f x)⁻¹) := by
  have hV : UniqueDiffOn ℝ ({0}ᶜ : Set ℝ) := isOpen_compl_singleton.uniqueDiffOn
  have hg : ContDiffOn ℝ ∞ (fun x : ℝ => x⁻¹) ({0}ᶜ) :=
    contDiffOn_id.inv (fun x hx => hx)
  have hD : 0 ≤ (m.factorial : ℝ)*K^(m+1) := by positivity
  have hd : ∀ j ≤ m, ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y⁻¹) ({0}ᶜ) (f x)‖ ≤
        (m.factorial : ℝ)*K^(m+1) := by
    intro j hj x hx
    rw [norm_iteratedFDerivWithin_inv j (hne x hx)]
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le hj
    · exact (pow_le_pow_left₀ (norm_nonneg _) (hInv x hx) _).trans
        (pow_le_pow_right₀ hK (by omega))
    · positivity
    · positivity
  have hh := hb.comp hU hV hs hC hD hf hg (fun x hx => hne x hx) hd
  convert hh using 1 <;> first | rfl | ring

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedRealAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real scalar and vector products used in the quantitative normal formula. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.mul_real_dup2 {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f g : E → ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2^m*C*D) (fun x => f x*g x) := by
  intro j hj x hx
  calc
    _ ≤ s^j*(∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*
        ‖iteratedFDerivWithin ℝ i f U x‖*‖iteratedFDerivWithin ℝ (j-i) g U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_mul_le (n := j) (N := ∞) hf hg hU hx
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ 2^j*C*D := weighted_binomial_bound hs hC hD j _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedInverseSqrt
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial weighted bounds for normalization by a positive square root. -/
noncomputable section
open Set Polynomial
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.WeightedEstimates

lemma norm_iteratedFDerivWithin_inverse_half (j : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y^(-1/2 : ℝ)) (Ioi 0) x‖ =
      ‖(descPochhammer ℝ j).eval (-1/2)‖*x^(-1/2-(j : ℝ)) := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_of_isOpen_eq_iterate isOpen_Ioi hx,Real.iter_deriv_rpow_const]
  simp only [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hx _)]

lemma inverse_half_power_bound {x K : ℝ} (hx : 0 < x) (hK : 1 ≤ K)
    (hi : x⁻¹ ≤ K) {j m : ℕ} (hj : j ≤ m) :
    x^(-1/2-(j : ℝ)) ≤ K^(m+1) := by
  have he : x^(-1/2-(j : ℝ)) = (x⁻¹)^((j : ℝ)+1/2) := by
    rw [← Real.rpow_neg_one x,← Real.rpow_mul hx.le]
    congr 1
    ring
  rw [he]
  have hj0 : 0 ≤ (j : ℝ)+1/2 := by positivity
  calc
    (x⁻¹)^((j : ℝ)+1/2) ≤ K^((j : ℝ)+1/2) :=
      Real.rpow_le_rpow (inv_nonneg.mpr hx.le) hi hj0
    _ ≤ K^((m+1 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hK (by
      have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
      push_cast
      linarith)
    _ = K^(m+1) := Real.rpow_natCast _ _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weighted_inverse_sqrt (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {U : Set E}, UniqueDiffOn ℝ U →
      ∀ {s C K : ℝ} {f : E → ℝ}, 0 < s → 1 ≤ C → 1 ≤ K →
      ContDiffOn ℝ ∞ f U → (∀ x ∈ U, 0 < f x) →
      (∀ x ∈ U, (f x)⁻¹ ≤ K) → WeightedBound U s m C f →
      WeightedBound U s m ((m.factorial : ℝ)*D*K^(m+1)*C^m)
        (fun x => (Real.sqrt (f x))⁻¹) := by
  let D : ℝ := 1+∑ j ∈ Finset.range (m+1), ‖(descPochhammer ℝ j).eval (-1/2)‖
  have hD : 1 ≤ D := by
    have hh : 0 ≤ ∑ j ∈ Finset.range (m+1), ‖(descPochhammer ℝ j).eval (-1/2)‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    dsimp only [D]
    linarith
  have hDj {j : ℕ} (hj : j ≤ m) : ‖(descPochhammer ℝ j).eval (-1/2)‖ ≤ D := by
    have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (m+1)) =>
      norm_nonneg ((descPochhammer ℝ i).eval (-1/2))) (Finset.mem_range.mpr (by omega : j < m+1))
    dsimp only [D]
    linarith
  refine ⟨D,hD,?_⟩
  intro U hU s C K f hs hC hK hf hpos hi hb
  have hg : ContDiffOn ℝ ∞ (fun y : ℝ => y^(-1/2 : ℝ)) (Ioi 0) := by
    intro x hx
    exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt
  have hd : ∀ j ≤ m, ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y^(-1/2 : ℝ)) (Ioi 0) (f x)‖ ≤ D*K^(m+1) := by
    intro j hj x hx
    rw [norm_iteratedFDerivWithin_inverse_half j (hpos x hx)]
    exact mul_le_mul (hDj hj) (inverse_half_power_bound (hpos x hx) hK (hi x hx) hj)
      (Real.rpow_nonneg (hpos x hx).le _) (zero_le_one.trans hD)
  have hbound := hb.comp hU isOpen_Ioi.uniqueDiffOn hs hC (by positivity : 0 ≤ D*K^(m+1))
    hf hg hpos hd
  have hbound' : WeightedBound U s m ((m.factorial : ℝ)*D*K^(m+1)*C^m)
      ((fun y : ℝ => y^(-1/2 : ℝ)) ∘ f) := by
    convert hbound using 1
    all_goals try with_reducible_and_instances rfl
    ring
  apply hbound'.congr
  intro x hx
  simp only [Function.comp_apply,Real.sqrt_eq_rpow]
  rw [show (-1/2 : ℝ) = -(1/2) by ring,Real.rpow_neg (hpos x hx).le]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PositivePolynomialBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit normal-frame budgets have fixed polynomial growth. This
keeps their exponents independent of multiplicative input constants. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma polynomialBound_const {c : ℝ} (hc : 0 ≤ c) : HasPolynomialBound (fun _ => c) := by
  exact ⟨0,max 1 c,le_max_left _ _,fun x _ => ⟨hc,by
    simp only [pow_zero,mul_one]
    exact le_max_right (1 : ℝ) c⟩⟩

lemma polynomialBound_id : HasPolynomialBound (fun x => x) := by
  exact ⟨1,1,le_rfl,fun x hx => ⟨zero_le_one.trans hx,by simp⟩⟩

lemma HasPolynomialBound.add {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x+g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C+D,by linarith,?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨add_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x+g x ≤ C*x^d+D*x^e := add_le_add hf'.2 hg'.2
    _ ≤ C*x^(d+e)+D*x^(d+e) := add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_right d e)) (zero_le_one.trans hC))
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_left e d)) (zero_le_one.trans hD))
    _ = (C+D)*x^(d+e) := by ring

lemma HasPolynomialBound.mul {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x*g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C*D,by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hD)],?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨mul_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x*g x ≤ (C*x^d)*(D*x^e) := mul_le_mul hf'.2 hg'.2 hg'.1
      (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hx) _))
    _ = (C*D)*x^(d+e) := by rw [pow_add]; ring

lemma HasPolynomialBound.pow {f : ℝ → ℝ} (hf : HasPolynomialBound f) (n : ℕ) :
    HasPolynomialBound (fun x => (f x)^n) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  refine ⟨d*n,C^n,one_le_pow₀ hC,?_⟩
  intro x hx
  have hh := hf x hx
  refine ⟨pow_nonneg hh.1 _,?_⟩
  calc
    (f x)^n ≤ (C*x^d)^n := pow_le_pow_left₀ hh.1 hh.2 _
    _ = C^n*x^(d*n) := by rw [mul_pow,pow_mul]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialBudgetAlgebra
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite composition and inverse-scale evaluation of the polynomial
budgets in the correction construction. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma HasPolynomialBound.of_le {f g : ℝ → ℝ} (hg : HasPolynomialBound g)
    (h0 : ∀ x, 1 ≤ x → 0 ≤ f x) (hle : ∀ x, 1 ≤ x → f x ≤ g x) :
    HasPolynomialBound f := by
  obtain ⟨d,C,hC,hg⟩ := hg
  exact ⟨d,C,hC,fun x hx => ⟨h0 x hx,(hle x hx).trans (hg x hx).2⟩⟩

lemma HasPolynomialBound.max {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => max (f x) (g x)) := by
  have hfn : ∀ x, 1 ≤ x → 0 ≤ f x := by
    obtain ⟨_,_,_,h⟩ := hf
    exact fun x hx => (h x hx).1
  have hgn : ∀ x, 1 ≤ x → 0 ≤ g x := by
    obtain ⟨_,_,_,h⟩ := hg
    exact fun x hx => (h x hx).1
  exact (hf.add hg).of_le (fun x hx => (hfn x hx).trans (le_max_left _ _))
    (fun x hx => max_le (le_add_of_nonneg_right (hgn x hx)) (le_add_of_nonneg_left (hfn x hx)))

lemma HasPolynomialBound.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, HasPolynomialBound (f i)) :
    HasPolynomialBound (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polynomialBound_const (show (0:ℝ) ≤ 0 by rfl)
  | @insert i s hi ih =>
    have h := (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using h

lemma HasPolynomialBound.comp {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) (hge : ∀ x, 1 ≤ x → 1 ≤ g x) :
    HasPolynomialBound (fun x => f (g x)) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨e*d,C*D^d,one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hD),?_⟩
  intro x hx
  refine ⟨(hf (g x) (hge x hx)).1,?_⟩
  calc
    f (g x) ≤ C*(g x)^d := (hf (g x) (hge x hx)).2
    _ ≤ C*(D*x^e)^d := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hg x hx).1 (hg x hx).2 _) (zero_le_one.trans hC)
    _ = (C*D^d)*x^(e*d) := by rw [mul_pow,pow_mul]; ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridCutoffSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local cell cutoff has the exact global refined support used in
phase selection. This keeps the solver's geometry on that original support. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma cellChartCompact_subset (i : A.centers) (a : Finset Index) (h : ℝ) (k : Index) :
    (A.cellChartCompact i a h k : Set JetPolynomial.Base) ⊆ A.chartWeightCompact i :=
  Set.image_mono (refinedCutoff_tsupport_outer (i : M) (A.weight i) a h k)

lemma restore_cell_tsupport {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : A.centers) (a : Finset Index) (h : ℝ) (k : Index)
    (f : JetPolynomial.Base → V)
    (hf : tsupport f ⊆ (A.cellChartCompact i a h k : Set JetPolynomial.Base)) :
    tsupport (restore (i : M) (A.outer i) f) ⊆
      tsupport (refinedCutoff (i : M) (A.weight i) a h k) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_cases hs : p ∈ (chart (i : M)).source
  · have hn : f (chart (i : M) p) ≠ 0 := by
      intro hz
      apply hp
      simp only [restore,indicator_of_mem hs,hz,smul_zero]
    obtain ⟨q,hq,he⟩ := hf (subset_tsupport f hn)
    have hqs := A.weight_support i
      (refinedCutoff_tsupport_outer (i : M) (A.weight i) a h k hq)
    have hqp : q = p := (chart (i : M)).injOn hqs hs he
    simpa only [hqp] using hq
  · exfalso
    apply hp
    simp only [restore,indicator_of_notMem hs]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GridFreeSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual free amplitudes have precisely the global grid supports
used in the quadratic cancellation theorem. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGrid PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
local instance gridFreeSupportFiberNormed_r332fac_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance gridFreeSupportFiberSpace_r332fac_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance gridFreeSupportDualAdd_r332fac_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridFreeSupportDualSmul_r332fac_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance gridFreeSupportSectionNormed_r332fac_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridFreeSupportSectionSpace_r332fac_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma finiteGlobalAmplitude_grid_support
    {a : A.centers → Finset Index} {h : ℝ}
    {G : A.centers → JetPolynomial.Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ((a i) × Fin 3) → JetPolynomial.Base → ℝ} {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0 (G i) (hG i) (φ i j)
      (A.cellChartCompact i (a i) h j.1.val) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (i : A.centers) (j : (a i) × Fin 3) :
    tsupport (A.finiteGlobalAmplitude d hρ δ q u i j) ⊆
      A.gridPhaseSupport h ⟨i,j⟩ := by
  exact A.restore_cell_tsupport i (a i) h j.1.val
    ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u))
    ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)).tsupport_subset

omit [CompactSpace M] in
lemma finiteGlobalPhase_eq_gridRestoredPhase
    {a : A.centers → Finset Index}
    (φ : ∀ i, ((a i) × Fin 3) → JetPolynomial.Base → ℝ)
    (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
    (w : AtlasCellPhase (ι := A.centers) → ℝ)
    (hφ : ∀ i j, φ i j = phaseLinear (w (i,j.1.val,j.2) • ξ (i,j.1.val,j.2)) ∘
      planeCoordinateIsometry) (i : A.centers) (j : (a i) × Fin 3) :
    A.finiteGlobalPhase (ι := fun i => (a i) × Fin 3) (φ := φ) i j = A.gridRestoredPhase (s := a) ξ w ⟨i,j⟩ := by
  simp only [finiteGlobalPhase,hφ,gridRestoredPhase,gridPhaseLabel]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialModeBudgets
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite free and forced parametrices have polynomial budgets. These
are the actual constants used by the existing mode estimates. -/
noncomputable section
namespace ClosedSurfaceR4.SmallModes
open RealModes

theorem errorConstant_polynomial (m : ℕ) :
    HasPolynomialBound (errorConstant m) := by
  unfold errorConstant reducedConstant
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.add
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

theorem fullErrorConstant_polynomial (n m : ℕ) :
    HasPolynomialBound (fullErrorConstant n m) := by
  unfold fullErrorConstant reducedConstant targetConstant
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.add
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

theorem amplitudeConstant_polynomial (n m : ℕ) :
    HasPolynomialBound (amplitudeConstant n m) := by
  unfold amplitudeConstant targetConstant
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.add
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

theorem initialConstant_polynomial (n m : ℕ) :
    HasPolynomialBound (initialConstant n m) := by
  unfold initialConstant
  exact ((polynomialBound_const (by positivity)).add
    ((polynomialBound_const (by positivity)).mul polynomialBound_id)).add
      (amplitudeConstant_polynomial n m)

end ClosedSurfaceR4.SmallModes

namespace ClosedSurfaceR4.FiniteParametrix
open RealModes

theorem boundProfile_polynomial (L : ℕ) (K C : ℕ → ℝ → ℝ)
    (hK : ∀ m, HasPolynomialBound (K m)) (hC : ∀ m, HasPolynomialBound (C m))
    (q m : ℕ) : HasPolynomialBound (fun x => boundProfile L (fun r => K r x) (fun r => C r x) q m) := by
  induction q generalizing m with
  | zero => exact hC m
  | succ q ih => exact (hK m).mul (ih (m+L))

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialSupportedModeBudgets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial control of the actual supported free-mode and normalized
mean constants, including their finite derivative-loss recurrences. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.SmallModes
open RealModes

theorem freeModeBudget_polynomial (n L : ℕ) (B D : ℕ → ℝ → ℝ)
    (hB : ∀ m, HasPolynomialBound (B m)) (hD : ∀ m, HasPolynomialBound (D m))
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q m : ℕ) :
    HasPolynomialBound (fun x => freeModeBudget n L (fun r => B r x) (fun r => D r x) q m) := by
  let κ := fun r x => max (errorConstant r (B r x))
    (D r x * initialConstant n (r+L) (B (r+L) x))
  let κ₀ := fun r x => max (fullErrorConstant n r (B r x))
    (D r x * initialConstant n (r+L) (B (r+L) x))
  have hκ (r : ℕ) : HasPolynomialBound (κ r) :=
    ((errorConstant_polynomial r).comp (hB r) (hB1 r)).max
      ((hD r).mul ((initialConstant_polynomial n (r+L)).comp (hB (r+L)) (hB1 (r+L))))
  have hκ₀ (r : ℕ) : HasPolynomialBound (κ₀ r) :=
    ((fullErrorConstant_polynomial n r).comp (hB r) (hB1 r)).max
      ((hD r).mul ((initialConstant_polynomial n (r+L)).comp (hB (r+L)) (hB1 (r+L))))
  have hi := (initialConstant_polynomial n m).comp (hB m) (hB1 m)
  have hsum := HasPolynomialBound.sum (Finset.range q)
    (fun i x => initialConstant n m (B m x)*
      FiniteParametrix.boundProfile (L+1) (fun r => κ r x) (fun r => κ₀ r x) i (m+(L+1)))
    (fun i _ => hi.mul (FiniteParametrix.boundProfile_polynomial (L+1) κ κ₀ hκ hκ₀ i (m+(L+1))))
  exact hsum.add ((amplitudeConstant_polynomial n m).comp (hB m) (hB1 m))

end ClosedSurfaceR4.SmallModes

namespace ClosedSurfaceR4.RealModes
open SmallModes

theorem correctedSeedBudget_polynomial (L : ℕ) (B D : ℕ → ℝ → ℝ) (N : ℝ → ℝ)
    (hB : ∀ m, HasPolynomialBound (B m)) (hD : ∀ m, HasPolynomialBound (D m))
    (hN : HasPolynomialBound N) (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q m : ℕ) :
    HasPolynomialBound (fun x => correctedSeedBudget L (fun r => B r x) (fun r => D r x) q m (N x)) := by
  exact ((polynomialBound_const zero_le_one).add
    (freeModeBudget_polynomial 4 L B D hB hD hB1 q m)).mul
      (((polynomialBound_const (Real.sqrt_nonneg 2)).mul
        (polynomialBound_const (show (0 : ℝ) ≤ 2^(m+(q+1)*(L+1)) by positivity))).mul hN)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricFreeBudgets
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial budgets for the actual unperturbed free metric modes. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open RealModes SmallModes

theorem metricFreeSizeBudget_polynomial (C J N : ℕ → ℝ → ℝ)
    (hC : ∀ m, HasPolynomialBound (C m)) (hJ : ∀ m, HasPolynomialBound (J m))
    (hN : ∀ m, HasPolynomialBound (N m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x) (q m : ℕ) :
    HasPolynomialBound (fun x => metricFreeSizeBudget
      (fun r => C r x) (fun r => J r x) (fun r => N r x) q m) := by
  have hz : ∀ m : ℕ, HasPolynomialBound (fun _ : ℝ => (0 : ℝ)) :=
    fun _ => polynomialBound_const le_rfl
  exact (((polynomialBound_const (Nat.cast_nonneg m.factorial)).mul
    (polynomialBound_const (show (0 : ℝ) ≤ 2^m by positivity))).mul
      (correctedSeedBudget_polynomial 0 C (fun _ _ => 0) (N (m+q+1)) hC hz
        (hN (m+q+1)) hC1 q m)).mul ((hJ m).pow m)

theorem metricFreeResidualBudget_polynomial (C J N : ℕ → ℝ → ℝ)
    (hC : ∀ m, HasPolynomialBound (C m)) (hJ : ∀ m, HasPolynomialBound (J m))
    (hN : ∀ m, HasPolynomialBound (N m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x) (q m : ℕ) :
    HasPolynomialBound (fun x => metricFreeResidualBudget
      (fun r => C r x) (fun r => J r x) (fun r => N r x) q m) := by
  have he (r : ℕ) := (errorConstant_polynomial r).comp (hC r) (hC1 r)
  have hf (r : ℕ) := (fullErrorConstant_polynomial 4 r).comp (hC r) (hC1 r)
  have hb := FiniteParametrix.boundProfile_polynomial 1
    (fun r x => errorConstant r (C r x)) (fun r x => fullErrorConstant 4 r (C r x)) he hf q m
  have ht : HasPolynomialBound (fun x => tensorChartBudget m (J m x) (J (m+1) x)) := by
    unfold tensorChartBudget
    repeat first
      | exact hJ _
      | apply HasPolynomialBound.mul
      | apply HasPolynomialBound.pow
      | (apply polynomialBound_const; positivity)
  exact (ht.mul (polynomialBound_const (show (0 : ℝ) ≤ 2^m by positivity))).mul
    (hb.mul (((polynomialBound_const (Real.sqrt_nonneg 2)).mul
      (polynomialBound_const (show (0 : ℝ) ≤ 2^(m+q+1) by positivity))).mul (hN (m+q+1))))

namespace PolynomialSolveData
variable {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {τ : ℝ} {s : ℝ≥0}

lemma metric_freeSizeFactor_eq (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    (hD : ∀ m, c.D m = 0) (N : ℕ → ℝ) (q m : ℕ) :
    c.freeSizeFactor q m (N (m+q+1)) = metricFreeSizeBudget c.C c.J N q m := by
  have hD' : c.D = fun _ => 0 := funext hD
  simp only [freeSizeFactor,metricFreeSizeBudget,tensorOrder_emptyMetricPolynomial,hD']

end PolynomialSolveData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialRootBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit square-root and square-root-difference bounds from a reciprocal
positivity margin, without a compact-set derivative constant. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RootMean
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sqrtBudget_nonneg (m : ℕ) {D B : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B) :
    0 ≤ sqrtBudget m D B := by unfold sqrtBudget; positivity

lemma inverse_sqrt_le {x B : ℝ} (hx : 0 < x) (hB : 1 ≤ B) (hi : x⁻¹ ≤ B) :
    (Real.sqrt x)⁻¹ ≤ B := by
  have hh := inverse_half_power_bound hx hB hi (j := 0) (m := 0) (Nat.le_refl 0)
  have he : x^(-1/2 : ℝ) = (Real.sqrt x)⁻¹ := by
    rw [Real.sqrt_eq_rpow,show (-1/2 : ℝ) = -(1/2) by ring,Real.rpow_neg hx.le]
  simpa only [Nat.cast_zero,Nat.zero_add,sub_zero,pow_one,he] using hh

theorem polynomial_sqrt_bound (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {U : Set E}, UniqueDiffOn ℝ U →
      ∀ {s B : ℝ} {f : E → ℝ}, 0 < s → 1 ≤ B →
      ContDiffOn ℝ ∞ f U → (∀ x ∈ U, 0 < f x) →
      (∀ x ∈ U, (f x)⁻¹ ≤ B) → WeightedBound U s m B f →
      WeightedBound U s m (sqrtBudget m D B) (fun x => Real.sqrt (f x)) := by
  obtain ⟨D,hD,hbound⟩ := weighted_inverse_sqrt (E := E) m
  refine ⟨D,hD,?_⟩
  intro U hU s B f hs hB hf hp hi hb
  have hr := hf.sqrt (fun x hx => (hp x hx).ne')
  have hi' := hr.inv (fun x hx => (Real.sqrt_pos.mpr (hp x hx)).ne')
  have hh := hb.mul_real_dup2 hU hs.le (zero_le_one.trans hB) (by positivity)
    hf hi' (hbound hU hs hB hB hf hp hi hb)
  apply hh.congr
  intro x hx
  change Real.sqrt (f x) = f x*(Real.sqrt (f x))⁻¹
  rw [← div_eq_mul_inv,eq_div_iff (Real.sqrt_pos.mpr (hp x hx)).ne']
  exact Real.mul_self_sqrt (hp x hx).le

theorem polynomial_root_bounds (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {U : Set E}, UniqueDiffOn ℝ U →
      ∀ {s B A : ℝ} {f g : E → ℝ}, 0 < s → 1 ≤ B → 0 ≤ A →
      ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
      (∀ x ∈ U, 0 < f x) → (∀ x ∈ U, 0 < g x) →
      (∀ x ∈ U, (f x)⁻¹ ≤ B) → (∀ x ∈ U, (g x)⁻¹ ≤ B) →
      WeightedBound U s m B f → WeightedBound U s m B g →
      WeightedBound U s m A (f-g) →
      WeightedBound U s m (sqrtBudget m D B) (fun x => Real.sqrt (f x)) ∧
      WeightedBound U s m (sqrtBudget m D B) (fun x => Real.sqrt (g x)) ∧
      WeightedBound U s m (rootDifferenceBudget m D B*A)
        (fun x => Real.sqrt (f x)-Real.sqrt (g x)) := by
  obtain ⟨D,hD,hr⟩ := polynomial_sqrt_bound (E := E) m
  refine ⟨D,hD,?_⟩
  intro U hU s B A f g hs hB hA hf hg hfp hgp hfi hgi hfb hgb hdiff
  have hrf := hf.sqrt (fun x hx => (hfp x hx).ne')
  have hrg := hg.sqrt (fun x hx => (hgp x hx).ne')
  have bF := hr hU hs hB hf hfp hfi hfb
  have bG := hr hU hs hB hg hgp hgi hgb
  have hS : 0 ≤ sqrtBudget m D B := sqrtBudget_nonneg m (zero_le_one.trans hD) (zero_le_one.trans hB)
  have hsum := bF.add hU hs.le hrf hrg bG
  have hsum' : WeightedBound U s m (1+2*sqrtBudget m D B)
      (fun x => Real.sqrt (f x)+Real.sqrt (g x)) := hsum.mono_const (by linarith)
  have hpos (x : E) (hx : x ∈ U) : 0 < Real.sqrt (f x)+Real.sqrt (g x) :=
    add_pos (Real.sqrt_pos.mpr (hfp x hx)) (Real.sqrt_pos.mpr (hgp x hx))
  have hinv (x : E) (hx : x ∈ U) :
      ‖(Real.sqrt (f x)+Real.sqrt (g x))⁻¹‖ ≤ B := by
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hpos x hx))]
    exact ((inv_le_inv₀ (hpos x hx) (Real.sqrt_pos.mpr (hfp x hx))).mpr
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))).trans (inverse_sqrt_le (hfp x hx) hB (hfi x hx))
  have bInv := hsum'.inv_real hU hs (by linarith) hB (hrf.add hrg)
    (fun x hx => (hpos x hx).ne') hinv
  have hsmoothInv := (hrf.add hrg).inv (fun x hx => (hpos x hx).ne')
  have hh := hdiff.mul_real_dup2 hU hs.le hA (by positivity) (hf.sub hg) hsmoothInv bInv
  refine ⟨bF,bG,?_⟩
  have hh' : WeightedBound U s m (rootDifferenceBudget m D B*A)
      (fun x => (f x-g x)*(Real.sqrt (f x)+Real.sqrt (g x))⁻¹) := by
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    unfold rootDifferenceBudget
    ring
  apply hh'.congr
  intro x hx
  exact sqrt_difference (hfp x hx) (hgp x hx)

end ClosedSurfaceR4.RootMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAmplitudeBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the supported square-root amplitudes of the
metric decomposition, including their difference estimate. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RootMean
open WeightedEstimates RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem polynomial_phaseAmplitude_bounds (m : ℕ) :
    ∃ d : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ {U : Set E}, UniqueDiffOn ℝ U → ∀ {s B A : ℝ} {ψ f g : E → ℝ},
      0 < s → 1 ≤ B → 0 ≤ A →
      ContDiffOn ℝ ∞ ψ U → ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
      (∀ x ∈ U, 0 < f x) → (∀ x ∈ U, 0 < g x) →
      (∀ x ∈ U, (f x)⁻¹ ≤ B) → (∀ x ∈ U, (g x)⁻¹ ≤ B) →
      WeightedBound U s m B ψ → WeightedBound U s m B f → WeightedBound U s m B g →
      WeightedBound U s m A (f-g) →
      WeightedBound U s m (C*B^d) (phaseAmplitude ψ f) ∧
      WeightedBound U s m (C*B^d) (phaseAmplitude ψ g) ∧
      WeightedBound U s m (C*B^d*A) (fun x => phaseAmplitude ψ f x-phaseAmplitude ψ g x) := by
  obtain ⟨D,hD,hr⟩ := polynomial_root_bounds (E := E) m
  have hpoly : HasPolynomialBound (phaseAmplitudeBudget m D) := by
    unfold phaseAmplitudeBudget rootDifferenceBudget sqrtBudget
    repeat first
      | exact polynomialBound_id
      | apply HasPolynomialBound.add
      | apply HasPolynomialBound.mul
      | apply HasPolynomialBound.pow
      | (apply polynomialBound_const; positivity)
  obtain ⟨d,C,hC,hpoly⟩ := hpoly
  refine ⟨d,C,hC,?_⟩
  intro U hU s B A ψ f g hs hB hA hψ hf hg hfp hgp hfi hgi hbψ hbf hbg hdiff
  obtain ⟨bF,bG,bDiff⟩ := hr hU hs hB hA hf hg hfp hgp hfi hgi hbf hbg hdiff
  have hB0 := zero_le_one.trans hB
  have hS := sqrtBudget_nonneg m (zero_le_one.trans hD) hB0
  have hR : 0 ≤ rootDifferenceBudget m D B := by unfold rootDifferenceBudget; positivity
  have hleft : 2^m*B*sqrtBudget m D B ≤ phaseAmplitudeBudget m D B := by
    unfold phaseAmplitudeBudget
    have hn : 0 ≤ 2^m*B*rootDifferenceBudget m D B := by positivity
    linarith
  have hright : 2^m*B*rootDifferenceBudget m D B ≤ phaseAmplitudeBudget m D B := by
    unfold phaseAmplitudeBudget
    have hn : 0 ≤ 2^m*B*sqrtBudget m D B := by positivity
    linarith
  have hfroot := hf.sqrt (fun x hx => (hfp x hx).ne')
  have hgroot := hg.sqrt (fun x hx => (hgp x hx).ne')
  have hfa := hbψ.mul_real_dup2 hU hs.le hB0 hS hψ hfroot bF
  have hga := hbψ.mul_real_dup2 hU hs.le hB0 hS hψ hgroot bG
  refine ⟨hfa.mono_const (hleft.trans (hpoly B hB).2),
    hga.mono_const (hleft.trans (hpoly B hB).2),?_⟩
  have hda := hbψ.mul_real_dup2 hU hs.le hB0 (mul_nonneg hR hA) hψ (hfroot.sub hgroot) bDiff
  have hsize : 2^m*B*(rootDifferenceBudget m D B*A) ≤ C*B^d*A := by
    calc
      _ = (2^m*B*rootDifferenceBudget m D B)*A := by ring
      _ ≤ C*B^d*A := mul_le_mul_of_nonneg_right (hright.trans (hpoly B hB).2) hA
  apply (hda.mono_const hsize).congr
  intro x hx
  dsimp only [phaseAmplitude]
  ring

end ClosedSurfaceR4.RootMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLocalAmplitude
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial square-root amplitudes for the actual local metric data. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes RootMean WeightedEstimates FiniteMean

lemma coefficientBudget_polynomial (m : ℕ) : HasPolynomialBound (coefficientBudget m) := by
  unfold coefficientBudget
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

variable {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
  {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}

lemma inputFactor_le_coefficientBudget (d : Budgets U V s F ψ Q χ e)
    (m : ℕ) {B : ℝ} (hB : 1 ≤ B) (hi : d.inv m ≤ B) (hf : d.forms m ≤ B) :
    inputFactor d m ≤ coefficientBudget m B := by
  have hI := d.inv_pos m
  have hF := d.forms_pos m
  unfold inputFactor coefficientBudget
  gcongr

theorem polynomial_local_amplitude_bounds (m : ℕ) :
    ∃ p : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
      {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base},
      ∀ (_h : LocalBounds U V s r ρ R reference F ψ Q χ e)
        (d : Budgets U V s F ψ Q χ e),
      0 < s → s ≤ 1 → 0 < ρ → ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      d.inv m ≤ B → d.forms m ≤ B → d.psi m ≤ B →
    ∀ (A A' : Base → Tensor) (D : ℝ), 0 ≤ D →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ A' U →
      InTrialBall U reference r A → InTrialBall U reference r A' →
      WeightedBound U s m B A → WeightedBound U s m B A' →
      WeightedBound U s m D (A-A') →
      WeightedBound V s m (C*B^p) (phaseAmplitude ψ (coefficient Q e A)) ∧
      WeightedBound V s m (C*B^p) (phaseAmplitude ψ (coefficient Q e A')) ∧
      WeightedBound V s m (C*B^p*D)
        (fun x => phaseAmplitude ψ (coefficient Q e A) x-phaseAmplitude ψ (coefficient Q e A') x) := by
  obtain ⟨k,C₀,hC₀,hamp⟩ := polynomial_phaseAmplitude_bounds (E := Base) m
  let S := fun B : ℝ => 1+B+coefficientBudget m B*B
  have hSp : HasPolynomialBound S :=
    ((polynomialBound_const zero_le_one).add polynomialBound_id).add
      ((coefficientBudget_polynomial m).mul polynomialBound_id)
  have hpoly : HasPolynomialBound (fun B => C₀*(S B)^k*(1+coefficientBudget m B)) :=
    ((polynomialBound_const (zero_le_one.trans hC₀)).mul (hSp.pow k)).mul
      ((polynomialBound_const zero_le_one).add (coefficientBudget_polynomial m))
  obtain ⟨p,C,hC,hpoly⟩ := hpoly
  refine ⟨p,C,hC,?_⟩
  intro U V s r ρ R reference F ψ Q χ e h d hs hs1 hρ B hB hρB hi hf hψ A A' D hD hA hA' hball hball' hbA hbA' hbD
  have hB0 := zero_le_one.trans hB
  have hJ : 0 ≤ coefficientBudget m B := by unfold coefficientBudget; positivity
  have hS : 1 ≤ S B ∧ B ≤ S B ∧ coefficientBudget m B*B ≤ S B := by
    dsimp [S]
    have hh : 0 ≤ coefficientBudget m B*B := mul_nonneg hJ hB0
    constructor
    · linarith
    constructor <;> linarith
  have hfactor := inputFactor_le_coefficientBudget d m hB hi hf
  have hcoeff (T : Base → Tensor) (hT : ContDiffOn ℝ ∞ T U)
      (hbT : WeightedBound U s m B T) : WeightedBound V s m (S B) (coefficient Q e T) := by
    have hh := weighted_coefficient h.openU.uniqueDiffOn h.domain.isOpen.uniqueDiffOn hs hs1
      (d.inv_pos m) (zero_le_one.trans (d.forms_pos m)) hB0 h.smoothQ h.smoothInv
      h.invInto hT (d.inv_bound m) (d.forms_bound m) hbT
    exact hh.mono_const ((mul_le_mul_of_nonneg_right hfactor hB0).trans hS.2.2)
  have hdiff := weighted_coefficient_difference h.openU.uniqueDiffOn h.domain.isOpen.uniqueDiffOn hs hs1
    (d.inv_pos m) (zero_le_one.trans (d.forms_pos m)) hD h.smoothQ h.smoothInv
    h.invInto hA hA' (d.inv_bound m) (d.forms_bound m) hbD
  have hdiff' : WeightedBound V s m (coefficientBudget m B*D)
      ((coefficient Q e A)-(coefficient Q e A')) :=
    hdiff.mono_const (mul_le_mul_of_nonneg_right hfactor hD)
  have hpos (T : Base → Tensor) (ht : InTrialBall U reference r T) :
      ∀ x ∈ V, 0 < coefficient Q e T x :=
    fun x hx => hρ.trans_le (coefficient_trial_range h.invInto h.margin ht hx).1
  have hinv (T : Base → Tensor) (ht : InTrialBall U reference r T) :
      ∀ x ∈ V, (coefficient Q e T x)⁻¹ ≤ S B := by
    intro x hx
    exact ((inv_le_inv₀ (hpos T ht x hx) hρ).mpr
      (coefficient_trial_range h.invInto h.margin ht hx).1).trans (hρB.trans hS.2.1)
  obtain ⟨ha,ha',hd⟩ := hamp h.domain.isOpen.uniqueDiffOn hs hS.1 (mul_nonneg hJ hD)
    h.smoothPsi (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto hA)
    (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto hA')
    (hpos A hball) (hpos A' hball') (hinv A hball) (hinv A' hball')
    ((d.psi_bound m).mono_const (hψ.trans hS.2.1)) (hcoeff A hA hbA) (hcoeff A' hA' hbA') hdiff'
  have hsize := (hpoly B hB).2
  have hbase : C₀*(S B)^k ≤ C*B^p := by
    calc
      _ ≤ C₀*(S B)^k*(1+coefficientBudget m B) :=
        le_mul_of_one_le_right (by positivity) (by linarith)
      _ ≤ _ := hsize
  have hdiffsize : C₀*(S B)^k*(coefficientBudget m B*D) ≤ C*B^p*D := by
    calc
      _ ≤ (C₀*(S B)^k*(1+coefficientBudget m B))*D := by
        have hz : 0 ≤ C₀*(S B)^k := by positivity
        nlinarith [mul_nonneg hz hD]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsize hD
  exact ⟨ha.mono_const hbase,ha'.mono_const hbase,hd.mono_const hdiffsize⟩

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialTrialAmplitude
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the actual supported square-root trial amplitude. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean

 theorem polynomial_trial_amplitude_bounds (m : ℕ) :
    ∃ p : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
      {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
      {K : Compacts Base} {s : ℝ≥0}
      {c : PolynomialSolveData P ε G hG φ K τ s}
      {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference),
      ∀ hρ : 0 < ρ, 0 < (s : ℝ) → s ≤ 1 → ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      d.budgets.inv m ≤ B → d.budgets.forms m ≤ B → d.budgets.psi m ≤ B →
      ∀ (f g : SmallModes.Base → Tensor) (D : ℝ), 0 ≤ D →
      ContDiffOn ℝ ∞ f c.e.source → ContDiffOn ℝ ∞ g c.e.source →
      InTrialBall c.e.source reference r f → InTrialBall c.e.source reference r g →
      WeightedBound c.e.source s m B f → WeightedBound c.e.source s m B g →
      WeightedBound c.e.source s m D (f-g) →
      supportedWeightedSeminorm c.chartCompact s m (d.amplitude hρ f) ≤ C*B^p ∧
      supportedWeightedSeminorm c.chartCompact s m (d.amplitude hρ g) ≤ C*B^p ∧
      supportedWeightedSeminorm c.chartCompact s m
        (d.amplitude hρ f-d.amplitude hρ g) ≤ C*B^p*D := by
  obtain ⟨p,C,hC,hamp⟩ := polynomial_local_amplitude_bounds m
  refine ⟨p,C,hC,?_⟩
  intro n P ε τ G hG φ K s c r ρ R reference d hρ hs hs1 B hB hρB hi hf hp f g D hD
    hfs hgs hfb hgb hbf hbg hdiff
  obtain ⟨hu,hv,hd⟩ := hamp d.localBounds d.budgets hs hs1 hρ B hB hρB hi hf hp
    f g D hD hfs hgs hfb hgb hbf hbg hdiff
  have hef : (d.amplitude hρ f : SmallModes.Base → ℝ) =
      phaseAmplitude d.cutoff (coefficient d.form c.e.symm f) :=
    funext (c.trialAmplitude_apply d.cutoff d.form d.localBounds hρ hfs hfb)
  have heg : (d.amplitude hρ g : SmallModes.Base → ℝ) =
      phaseAmplitude d.cutoff (coefficient d.form c.e.symm g) :=
    funext (c.trialAmplitude_apply d.cutoff d.form d.localBounds hρ hgs hgb)
  have hC0 : 0 ≤ C*B^p := mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hB) _)
  have hsp := chartSupport_subset c.e (modeSupport K) c.supportChart
  have hb1 : WeightedBound c.e.target s m (C*B^p) (d.amplitude hρ f) := by
    simpa only [hef] using hu
  have hb2 : WeightedBound c.e.target s m (C*B^p) (d.amplitude hρ g) := by
    simpa only [heg] using hv
  have hb3 : WeightedBound c.e.target s m (C*B^p*D) (d.amplitude hρ f-d.amplitude hρ g) := by
    change WeightedBound c.e.target s m _ (fun x => d.amplitude hρ f x-d.amplitude hρ g x)
    simpa only [hef,heg] using hd
  exact ⟨supportedSeminorm_le_of_weightedBound hs hC0 _
      (hb1.extend_support c.e.open_target ((d.amplitude hρ f).tsupport_subset.trans hsp) hC0),
    supportedSeminorm_le_of_weightedBound hs hC0 _
      (hb2.extend_support c.e.open_target ((d.amplitude hρ g).tsupport_subset.trans hsp) hC0),
    supportedSeminorm_le_of_weightedBound hs (mul_nonneg hC0 hD) _
      (hb3.extend_support c.e.open_target
        ((d.amplitude hρ f-d.amplitude hρ g).tsupport_subset.trans hsp) (mul_nonneg hC0 hD))⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialChartedSeed
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual slow-scale complex amplitudes with polynomial geometric and input budgets. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem polynomial_charted_seed_bounds (q m : ℕ) :
    ∃ p : ℕ, ∃ A : ℝ, 1 ≤ A ∧
    ∀ {τ : ℝ} {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
      {K : Compacts Base} {s : ℝ≥0}
      {c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s}
      {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference),
      (∀ j, c.D j = 0) → ∀ hρ : 0 < ρ,
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      d.budgets.inv (m+q+1) ≤ B → d.budgets.forms (m+q+1) ≤ B →
      d.budgets.psi (m+q+1) ≤ B →
      ∀ N : ℕ → ℝ, (∀ j, 0 ≤ N j) → d.budgets.normal (m+q+1) ≤ N (m+q+1) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ f : SmallModes.Base → Tensor,
      ContDiff ℝ ∞ f → InTrialBall univ reference r f →
      WeightedBound univ s (m+q+1) B f →
      WeightedBound univ s m
        (metricFreeSizeBudget c.C c.J N q m*(A*B^p)*(δ*τ))
        (d.freeAmplitude hρ δ q f) := by
  obtain ⟨p,A,hA,hamp⟩ := polynomial_trial_amplitude_bounds (m+q+1)
  refine ⟨p,A,hA,?_⟩
  intro τ G hG φ K s c r ρ R reference d hD hρ hτ hs hτs hs1 B hB hρB hi hf hp N hN hn δ hδ f hfs hfb hbf
  have hz : WeightedBound c.e.source s (m+q+1) 0 (f-f) := by
    apply (weightedBound_zero c.e.source s (m+q+1) (F := Tensor)).congr
    intro x _
    exact sub_self (f x)
  have hball : InTrialBall c.e.source reference r f := fun x _ => hfb x (mem_univ x)
  have ha := (hamp d hρ hs hs1 B hB hρB hi hf hp f f 0 le_rfl hfs.contDiffOn hfs.contDiffOn
    hball hball (hbf.restrict_open c.e.open_source) (hbf.restrict_open c.e.open_source) hz).1
  have hj : PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m = m+q+1 := by
    simp only [PolynomialSolveData.inputOrder,tensorOrder_emptyMetricPolynomial,Nat.zero_add,Nat.mul_one]
    omega
  have ha' : supportedWeightedSeminorm c.chartCompact s
      (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (d.amplitude hρ f) ≤ A*B^p := by
    simpa only [hj] using ha
  have hn' : WeightedBound c.e.target s
      (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) (N (m+q+1)) (freeNormal c.realMap) := by
    rw [hj]
    exact (d.budgets.normal_bound (m+q+1)).mono_const hn
  have hAp : 0 ≤ A*B^p := mul_nonneg (zero_le_one.trans hA) (pow_nonneg (zero_le_one.trans hB) _)
  have hsmall : τ/s + (0 : ℝ)/τ^tensorLoss emptyMetricPolynomial ≤ 1 := by
    simp only [zero_div,add_zero]
    exact (div_le_one₀ hs).mpr hτs
  have hb := c.originalFreeSeed_bound hδ hτ hs hτs hs1 le_rfl hsmall q m
    hAp (hN _) hn' (d.amplitude hρ f) ha'
  have hbudget := correctedSeedBudget_nonneg (tensorOrder emptyMetricPolynomial)
    c.C c.D c.nonnegC q m (hN (m+q+1))
  have htwo : (1 : ℝ) ≤ 2^m := one_le_pow₀ (by norm_num)
  have hJ : 0 ≤ c.J m^m := pow_nonneg (zero_le_one.trans (c.oneLEJ m)) _
  have hcoeff : (m.factorial : ℝ) * c.J m^m *
      correctedSeedBudget (tensorOrder emptyMetricPolynomial) c.C c.D q m (N (m+q+1)) ≤
      c.freeSizeFactor q m (N (m+q+1)) := by
    calc
      _ = (m.factorial : ℝ) * 1 *
          correctedSeedBudget (tensorOrder emptyMetricPolynomial) c.C c.D q m (N (m+q+1)) *
          c.J m^m := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg _)) hbudget) hJ
  rw [c.metric_freeSizeFactor_eq hD N q m] at hcoeff
  apply (weightedBound_of_supportedSeminorm s m (d.freeAmplitude hρ δ q f)).mono_const
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff hAp) (mul_nonneg hδ hτ.le))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAtlasSeed
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual complex amplitude bounds for arbitrary finite phase families. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAtlasSeedFiberSpace
local instance polynomialAtlasSeedDualAdd_r332fac_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAtlasSeedDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAtlasSeedFiberNormed
local instance polynomialAtlasSeedSectionNormed_r332fac_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialAtlasSeedSectionSpace_r332fac_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_finite_atlas_seed (q m : ℕ) :
    ∃ (p : ℕ) (E D : ℝ), 1 ≤ E ∧ 0 ≤ D ∧
    ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)],
    ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
      {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
      {τ : ℝ} {s : ℝ≥0}
      {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0
        (A.jetChartMap i F) (A.jetChartMap_smooth i hF) (φ i j) (K i j) τ s}
      {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
      (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)),
      ∀ C J : ℕ → ℝ,
      (∀ i j, (c i j).C = C ∧ (c i j).J = J ∧ ∀ k, (c i j).D k = 0) →
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      (∀ i j, (d i j).budgets.inv (m+q+1) ≤ B ∧ (d i j).budgets.forms (m+q+1) ≤ B ∧
        (d i j).budgets.psi (m+q+1) ≤ B) →
      ∀ N : ℕ → ℝ, (∀ k, 0 ≤ N k) →
      (∀ i j, (d i j).budgets.normal (m+q+1) ≤ N (m+q+1)) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ u : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ i, WeightedEstimates.WeightedBound univ s (m+q+1) B (A.tensorPlaneRead i u)) →
      ∀ k i j, WeightedEstimates.WeightedBound univ s m
        (D*metricFreeSizeBudget C J N q m*(E*B^p)*(δ*τ))
        (A.vectorPlaneRead k (A.finiteGlobalAmplitude d hρ δ q u i j)) := by
  classical
  obtain ⟨p,E,hE,hseed⟩ := polynomial_charted_seed_bounds q m
  choose D hD hd using fun k i : A.centers =>
    A.localize_outer_restore_bound (V := Fin 4 → ℂ) k i m
  let D₀ := ∑ k : A.centers, ∑ i : A.centers, D k i
  have hD₀ : 0 ≤ D₀ := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => hD k i
  refine ⟨p,E,D₀,hE,hD₀,?_⟩
  intro ι _ F hF φ K τ s c r ρ R reference d C J hc hρ hτ hs hτs hs1 B hB hρB hb N hN hnormal δ hδ u hu hball hbu k i j
  have hh := hseed (d i j) (hc i j).2.2 hρ hτ hs hτs hs1 B hB hρB
    (hb i j).1 (hb i j).2.1 (hb i j).2.2 N hN (hnormal i j) δ hδ
    (A.tensorPlaneRead i u) (A.tensorPlaneRead_smooth i hu) (hball i) (hbu i)
  have hC : (c i j).C = C := (hc i j).1
  have hJ : (c i j).J = J := (hc i j).2.1
  rw [hC,hJ] at hh
  have hsize : 0 ≤ metricFreeSizeBudget C J N q m*(E*B^p)*(δ*τ) := by
    have hbgt := correctedSeedBudget_nonneg 0 (c i j).C (fun _ => 0)
      (c i j).nonnegC q m (hN (m+q+1))
    have hjgt := (c i j).oneLEJ m
    rw [hC] at hbgt
    rw [hJ] at hjgt
    unfold metricFreeSizeBudget
    positivity
  have hout := hd k i ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)) s
    (metricFreeSizeBudget C J N q m*(E*B^p)*(δ*τ)) hs hs1 hsize
    (((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)).contDiff) hh
  have hsm := restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
    (((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)).contDiff)
  have hplane := weightedBound_comp_isometry planeCoordinateIsometry.symm
    (A.vectorChartRead_smooth k hsm) hout
  change WeightedEstimates.WeightedBound univ s m
    (D k i*(metricFreeSizeBudget C J N q m*(E*B^p)*(δ*τ)))
    (A.vectorPlaneRead k (A.finiteGlobalAmplitude d hρ δ q u i j)) at hplane
  apply hplane.mono_const
  have hDi : D k i ≤ D₀ := (Finset.single_le_sum (fun j _ => hD k j)
    (Finset.mem_univ i)).trans (Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun j _ => hD k j) (Finset.mem_univ k))
  calc
    _ ≤ D₀*(metricFreeSizeBudget C J N q m*(E*B^p)*(δ*τ)) :=
      mul_le_mul_of_nonneg_right hDi hsize
    _ = _ := by ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAtlasSeedProfile
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! One polynomial profile for all actual grid amplitudes, before the variable family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialSeedProfileFiberSpace
local instance polynomialSeedProfileDualAdd_r332fac_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialSeedProfileDualSmul
variable (A : SmoothingAtlas M)


attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialSeedProfileFiberNormed
local instance polynomialSeedProfileSectionNormed_r332fac_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialSeedProfileSectionSpace_r332fac_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_atlas_seed_profile (q : ℕ) (C J N B : ℕ → ℝ → ℝ)
    (hC : ∀ m, HasPolynomialBound (C m)) (hJ : ∀ m, HasPolynomialBound (J m))
    (hN : ∀ m, HasPolynomialBound (N m)) (hB : ∀ m, HasPolynomialBound (B m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x) (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) :
    ∃ α : ℕ → ℝ → ℝ, (∀ m, HasPolynomialBound (α m)) ∧
    ∀ x : ℝ, 1 ≤ x → ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
      (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
      {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
      {τ : ℝ} {s : ℝ≥0}
      {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0
        (A.jetChartMap i F) (A.jetChartMap_smooth i hF) (φ i j) (K i j) τ s}
      {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
      (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)),
      (∀ i j, (c i j).C = (fun m => C m x) ∧
        (c i j).J = (fun m => J m x) ∧ ∀ m, (c i j).D m = 0) →
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, ρ⁻¹ ≤ B m x) →
      (∀ i j m, (d i j).budgets.inv m ≤ B m x ∧ (d i j).budgets.forms m ≤ B m x ∧
        (d i j).budgets.psi m ≤ B m x ∧ (d i j).budgets.normal m ≤ N m x) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ u : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (u y)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ i m, WeightedEstimates.WeightedBound univ s m (B m x) (A.tensorPlaneRead i u)) →
      ∀ k i j m, WeightedEstimates.WeightedBound univ s (m+1) (α m x*(δ*τ))
        (A.vectorPlaneRead k (A.finiteGlobalAmplitude d hρ δ q u i j)) := by
  classical
  choose p E D hE hD hseed using fun m => A.polynomial_finite_atlas_seed q (m+1)
  let α := fun m x => D m*metricFreeSizeBudget (fun j => C j x) (fun j => J j x)
    (fun j => N j x) q (m+1) * (E m*(B ((m+1)+q+1) x)^(p m))
  have hα (m : ℕ) : HasPolynomialBound (α m) :=
    ((polynomialBound_const (hD m)).mul
      (metricFreeSizeBudget_polynomial C J N hC hJ hN hC1 q (m+1))).mul
        ((polynomialBound_const (zero_le_one.trans (hE m))).mul
          ((hB ((m+1)+q+1)).pow (p m)))
  refine ⟨α,hα,?_⟩
  intro x hx ι _ F hF φ K τ s c r ρ R reference d hc hρ hτ hs hτs hs1 hρB hb
    δ hδ u hu hball hbu k i j m
  have hN0 (l : ℕ) : 0 ≤ N l x := by
    obtain ⟨_,_,_,hh⟩ := hN l
    exact (hh x hx).1
  exact hseed m F hF d (fun l => C l x) (fun l => J l x) hc hρ hτ hs hτs hs1
    (B ((m+1)+q+1) x) (hB1 _ x hx) (hρB _)
    (fun i j => ⟨(hb i j _).1,(hb i j _).2.1,(hb i j _).2.2.1⟩)
    (fun l => N l x) hN0 (fun i j => (hb i j _).2.2.2)
    δ hδ u hu hball (fun i => hbu i _) k i j

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GridFreeCorrection
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic correction for the actual free grid amplitudes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeCorrectionDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeCorrectionDualSmul
variable (A : SmoothingAtlas M)

open PhaseGeometry PhaseGrid


attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeCorrectionFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeCorrectionFiberSpace
local instance gridFreeCorrectionSectionNormed_r332fac_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridFreeCorrectionSectionSpace_r332fac_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance instDecidableEqGridPhaseIndex_1_r332fac_1 {s : A.centers → Finset Index} : DecidableEq (A.GridPhaseIndex s) := Classical.decEq _
theorem grid_free_quadratic_correction (V : Finset SmallModes.Base)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {ε κ b D₀ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hb : 0 < b)
    (FJ C J N B : ℕ → ℝ → ℝ)
    (hFJ : ∀ m, RealModes.HasPolynomialBound (FJ m))
    (hFJ1 : ∀ m x, 1 ≤ x → 1 ≤ FJ m x)
    (hC : ∀ m, RealModes.HasPolynomialBound (C m))
    (hJ : ∀ m, RealModes.HasPolynomialBound (J m))
    (hN : ∀ m, RealModes.HasPolynomialBound (N m))
    (hB : ∀ m, RealModes.HasPolynomialBound (B m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x)
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q : ℕ) :
    ∃ (e : ℕ → ℕ) (E : ℕ → ℝ), (∀ m, 1 ≤ E m) ∧
      ∀ (h : ℝ) (a : A.centers → Finset Index)
        (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
        (w : AtlasCellPhase (ι := A.centers) → ℝ),
      (∀ l, 1 ≤ w l) →
      (∀ l : A.GridPhaseIndex a, w (A.gridPhaseLabel l) • ξ (A.gridPhaseLabel l) ∈ V) →
      ∀ n : ℕ, Fintype.card (A.GridPhaseIndex a) ≤ n → ∀ x : ℝ, 1 ≤ x →
      ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F),
      (∀ l p, atlasActive (fun i : A.centers => (i : M)) A.weight a h l p →
        atlasGram F (l.1 : M) p ≠ 0 ∧ atlasSecondTensor F (l.1 : M) p ≠ 0 ∧
        ε*‖atlasSecondTensor F (l.1 : M) p‖ ≤
          ‖secondQuadratic (atlasSecondTensor F (l.1 : M) p) (-(ξ l).2,(ξ l).1)‖) →
      AtlasPairMargins (fun i : A.centers => (i : M)) A.weight a h κ ξ w F →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) y)) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead k F) y))⁻¹‖ ≤ D₀) →
      ∀ {φ : ∀ i, ((a i) × Fin 3) → JetPolynomial.Base → ℝ}
        {τ : ℝ} {s : ℝ≥0}
        {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0
          (A.jetChartMap i F) (A.jetChartMap_smooth i hF) (φ i j)
          (A.cellChartCompact i (a i) h j.1.val) τ s}
        {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
        (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)),
      (∀ i j, φ i j = phaseLinear (w (i,j.1.val,j.2) • ξ (i,j.1.val,j.2)) ∘
        planeCoordinateIsometry) →
      (∀ i j, (c i j).C = (fun m => C m x) ∧ (c i j).J = (fun m => J m x) ∧
        ∀ m, (c i j).D m = 0) →
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, ρ⁻¹ ≤ B m x) →
      (∀ i j m, (d i j).budgets.inv m ≤ B m x ∧ (d i j).budgets.forms m ≤ B m x ∧
        (d i j).budgets.psi m ≤ B m x ∧ (d i j).budgets.normal m ≤ N m x) →
      (∀ k m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
        (FJ m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead k F)) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ u : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (u y)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ i m, WeightedEstimates.WeightedBound univ s m (B m x) (A.tensorPlaneRead i u)) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m (δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(e m))) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          ((τ/s)^(q+1)*(δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(e m))))
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) + A.finiteAtlasNonzero d hρ δ q u)) := by
  obtain ⟨α,hα,hamp⟩ := A.polynomial_atlas_seed_profile q C J N B hC hJ hN hB hC1 hB1
  obtain ⟨P,hP,hphase⟩ := A.linearPhaseCatalog_derivative_bounds V
  obtain ⟨e,E,hE,hquad⟩ := A.grid_global_quadratic_correction V houter hε hκ hb
    FJ α (fun m _ => P m) hFJ hFJ1 hα (fun m => RealModes.polynomialBound_const
      (zero_le_one.trans (hP m))) q
  refine ⟨e,E,hE,?_⟩
  intro h a ξ w hw hV n hn x hx F hF hlocal hpairs hImm hnormal hgram
    φ τ s c r ρ R reference d hφ hc hρ hτ hs hτs hs1 hρB hbud hFjets δ hδ u hu hball hbu
  let Z := fun l : A.GridPhaseIndex a => A.finiteGlobalAmplitude d hρ δ q u l.1 l.2
  have hZ (l : A.GridPhaseIndex a) : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z l) :=
    restore_smooth (l.1 : M) (A.outer_smooth l.1) (A.outer_support l.1)
      ((d l.1 l.2).freeAmplitude hρ δ q (A.tensorPlaneRead l.1 u)).contDiff
  have hSZ (l : A.GridPhaseIndex a) : tsupport (Z l) ⊆ A.gridPhaseSupport h l :=
    A.finiteGlobalAmplitude_grid_support d hρ δ q u l.1 l.2
  have hbound := hamp x hx F hF d hc hρ hτ hs hτs hs1 hρB hbud δ hδ u hu hball hbu
  have hder (k : A.centers) (l : A.GridPhaseIndex a) (m : ℕ) (v : SmallModes.Base) (hv : ‖v‖ ≤ 1) :=
    hphase (A.gridRestoredPhase (s := a) ξ w l)
      (A.restored_linear_phase_mem_catalog V l.1 (hV l)) k s hs hs1 m v hv
  obtain ⟨W,hW,hsize,hres⟩ := hquad h a ξ w hw hV n hn x hx F hF
    hlocal hpairs hImm hnormal hgram τ δ s hτ hs hτs hs1 hδ hFjets Z hZ hSZ
    (fun k l m => hbound k l.1 l.2 m) hder
  have hphases : A.gridRestoredPhase (s := a) ξ w =
      (fun l : A.GridPhaseIndex a => A.finiteGlobalPhase (ι := fun i => (a i) × Fin 3) (φ := φ) l.1 l.2) := by
    funext l
    exact (A.finiteGlobalPhase_eq_gridRestoredPhase φ ξ w hφ l.1 l.2).symm
  refine ⟨W,hW,hsize,?_⟩
  intro m
  simpa only [hphases,finiteAtlasNonzero,Z] using hres m

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAtlasFreeProfile
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! One polynomial profile for all actual grid amplitudes, before the variable family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFreeProfileFiberSpace
local instance polynomialFreeProfileDualAdd_r332fac_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFreeProfileDualSmul
variable (A : SmoothingAtlas M)


attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFreeProfileFiberNormed
local instance polynomialFreeProfileSectionNormed_r332fac_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialFreeProfileSectionSpace_r332fac_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_atlas_free_profile (q : ℕ) (C J N B : ℕ → ℝ → ℝ)
    (hC : ∀ m, HasPolynomialBound (C m)) (hJ : ∀ m, HasPolynomialBound (J m))
    (hN : ∀ m, HasPolynomialBound (N m)) (hB : ∀ m, HasPolynomialBound (B m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x) (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) :
    ∃ α β : ℕ → ℝ → ℝ, (∀ m, HasPolynomialBound (α m)) ∧
      (∀ m, HasPolynomialBound (β m)) ∧
    ∀ x : ℝ, 1 ≤ x → ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
      (n : ℕ), (∀ i, Fintype.card (ι i) ≤ n) →
      ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
      {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
      {τ : ℝ} {s : ℝ≥0}
      {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0
        (A.jetChartMap i F) (A.jetChartMap_smooth i hF) (φ i j) (K i j) τ s}
      {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
      (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)),
      (∀ i j, (c i j).C = (fun m => C m x) ∧
        (c i j).J = (fun m => J m x) ∧ ∀ m, (c i j).D m = 0) →
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      (∀ m, ρ⁻¹ ≤ B m x) →
      (∀ i j m, (d i j).budgets.inv m ≤ B m x ∧ (d i j).budgets.forms m ≤ B m x ∧
        (d i j).budgets.psi m ≤ B m x ∧ (d i j).budgets.normal m ≤ N m x) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ u : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (u y)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ i m, WeightedEstimates.WeightedBound univ s m (B m x) (A.tensorPlaneRead i u)) →
      ∀ m, A.WeightedBound τ m (α m x*(n : ℝ)*(δ*τ))
          (A.finiteAtlasFreeOscillation d hρ δ q u) ∧
        A.TensorWeightedBound τ m ((τ/s)^(q+1)*(β m x*(n : ℝ)*(δ*τ)))
          (linearMetricTensor F (spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u)) := by
  classical
  choose p E Dv Dt hE hDv hDt hfree using fun m => A.polynomial_finite_atlas_free q m
  let α := fun m x => Dv m*max 1 (metricFreeSizeBudget (fun j => C j x) (fun j => J j x)
    (fun j => N j x) q m)*(E m*(B (m+q+1) x)^(p m))
  let β := fun m x => Dt m*max 1 (metricFreeResidualBudget (fun j => C j x) (fun j => J j x)
    (fun j => N j x) q m)*(E m*(B (m+q+1) x)^(p m))
  have hα (m : ℕ) : HasPolynomialBound (α m) :=
    ((polynomialBound_const (hDv m)).mul
      ((polynomialBound_const zero_le_one).max
        (metricFreeSizeBudget_polynomial C J N hC hJ hN hC1 q m))).mul
          ((polynomialBound_const (zero_le_one.trans (hE m))).mul ((hB (m+q+1)).pow (p m)))
  have hβ (m : ℕ) : HasPolynomialBound (β m) :=
    ((polynomialBound_const (hDt m)).mul
      ((polynomialBound_const zero_le_one).max
        (metricFreeResidualBudget_polynomial C J N hC hJ hN hC1 q m))).mul
          ((polynomialBound_const (zero_le_one.trans (hE m))).mul ((hB (m+q+1)).pow (p m)))
  refine ⟨α,β,hα,hβ,?_⟩
  intro x hx ι _ n hn F hF φ K τ s c r ρ R reference d hc hρ hτ hs hτs hs1 hK hρB hb
    δ hδ u hu hball hbu m
  have hN0 (l : ℕ) : 0 ≤ N l x := by
    obtain ⟨_,_,_,hh⟩ := hN l
    exact (hh x hx).1
  have hh := hfree m n hn F hF d (fun l => C l x) (fun l => J l x) hc hρ hτ hs hτs hs1
    hK (B (m+q+1) x) (hB1 _ x hx) (hρB _)
    (fun i j => ⟨(hb i j _).1,(hb i j _).2.1,(hb i j _).2.2.1⟩)
    (fun l => N l x) hN0 (fun i j => (hb i j _).2.2.2)
    δ hδ u hu hball (fun i => hbu i _)
  constructor
  · convert hh.1 using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [α]
    ring
  · convert hh.2 using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [β]
    ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_GridIncrementProfile
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic correction for the actual free grid amplitudes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridIncrementProfileFiberSpace
local instance gridIncrementProfileDualAdd_r332fac_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridIncrementProfileDualSmul
variable (A : SmoothingAtlas M)

open PhaseGeometry PhaseGrid


attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridIncrementProfileFiberNormed
local instance gridIncrementProfileSectionNormed_r332fac_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridIncrementProfileSectionSpace_r332fac_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance instDecidableEqGridPhaseIndex_2_r332fac_1 {s : A.centers → Finset Index} : DecidableEq (A.GridPhaseIndex s) := Classical.decEq _
theorem grid_free_forced_increment_oai (V : Finset SmallModes.Base)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {ε κ b D₀ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hb : 0 < b)
    (FJ C J N B : ℕ → ℝ → ℝ)
    (hFJ : ∀ m, RealModes.HasPolynomialBound (FJ m))
    (hFJ1 : ∀ m x, 1 ≤ x → 1 ≤ FJ m x)
    (hC : ∀ m, RealModes.HasPolynomialBound (C m))
    (hJ : ∀ m, RealModes.HasPolynomialBound (J m))
    (hN : ∀ m, RealModes.HasPolynomialBound (N m))
    (hB : ∀ m, RealModes.HasPolynomialBound (B m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x)
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q : ℕ) :
    ∃ α β γ ζ : ℕ → ℝ → ℝ, ∃ D : ℕ → ℝ,
      (∀ m, RealModes.HasPolynomialBound (α m)) ∧
      (∀ m, RealModes.HasPolynomialBound (β m)) ∧
      (∀ m, RealModes.HasPolynomialBound (γ m)) ∧
      (∀ m, RealModes.HasPolynomialBound (ζ m)) ∧ (∀ m, 0 ≤ D m) ∧
      ∀ (h : ℝ) (a : A.centers → Finset Index)
        (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
        (w : AtlasCellPhase (ι := A.centers) → ℝ),
      (∀ l, 1 ≤ w l) →
      (∀ l : A.GridPhaseIndex a, w (A.gridPhaseLabel l) • ξ (A.gridPhaseLabel l) ∈ V) →
      ∀ n : ℕ, Fintype.card (A.GridPhaseIndex a) ≤ n → ∀ x : ℝ, 1 ≤ x →
      ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F),
      (∀ l p, atlasActive (fun i : A.centers => (i : M)) A.weight a h l p →
        atlasGram F (l.1 : M) p ≠ 0 ∧ atlasSecondTensor F (l.1 : M) p ≠ 0 ∧
        ε*‖atlasSecondTensor F (l.1 : M) p‖ ≤
          ‖secondQuadratic (atlasSecondTensor F (l.1 : M) p) (-(ξ l).2,(ξ l).1)‖) →
      AtlasPairMargins (fun i : A.centers => (i : M)) A.weight a h κ ξ w F →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) y)) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead k F) y))⁻¹‖ ≤ D₀) →
      ∀ {φ : ∀ i, ((a i) × Fin 3) → JetPolynomial.Base → ℝ}
        {τ : ℝ} {s : ℝ≥0}
        {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0
          (A.jetChartMap i F) (A.jetChartMap_smooth i hF) (φ i j)
          (A.cellChartCompact i (a i) h j.1.val) τ s}
        {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
        (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)),
      (∀ i j, φ i j = phaseLinear (w (i,j.1.val,j.2) • ξ (i,j.1.val,j.2)) ∘
        planeCoordinateIsometry) →
      (∀ i j, (c i j).C = (fun m => C m x) ∧ (c i j).J = (fun m => J m x) ∧
        ∀ m, (c i j).D m = 0) →
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, ρ⁻¹ ≤ B m x) →
      (∀ i j m, (d i j).budgets.inv m ≤ B m x ∧ (d i j).budgets.forms m ≤ B m x ∧
        (d i j).budgets.psi m ≤ B m x ∧ (d i j).budgets.normal m ≤ N m x) →
      (∀ k m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
        (FJ m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead k F)) →
      ∀ δ : ℝ, 0 < δ → δ ≤ τ → ∀ u : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (u y)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ i m, WeightedEstimates.WeightedBound univ s m (B m x) (A.tensorPlaneRead i u)) →
      ∀ H : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (H y)) →
      ∀ Rm : ℕ → ℝ,
      (∀ m, A.TensorWeightedBound τ m (Rm m)
        (A.finiteAtlasFreeMean d hρ δ q u-δ^2 • H)) →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, A.WeightedBound τ m
          ((α m x*(n : ℝ)+β m x*((n : ℝ)+2*(n : ℝ)^2))*(δ*τ)) U) ∧
        (∀ m, A.TensorWeightedBound τ m
          ((τ/s)^(q+1)*(ζ m x*(n : ℝ)*(δ*τ)+γ m x*((n : ℝ)+2*(n : ℝ)^2)*δ^2)+Rm m+
            D m*(2*(α (m+1) x*(n : ℝ))*(β (m+1) x*((n : ℝ)+2*(n : ℝ)^2))+
              (β (m+1) x*((n : ℝ)+2*(n : ℝ)^2))^2)*(δ^3/τ))
          (inducedTensor (F+U)-inducedTensor F-δ^2 • H)) := by
  classical
  obtain ⟨Af,Rf,hAf,hRf,hfree⟩ := A.polynomial_atlas_free_profile q C J N B hC hJ hN hB hC1 hB1
  obtain ⟨e,E,hE,hquad⟩ := A.grid_free_quadratic_correction V houter hε hκ hb
    FJ C J N B hFJ hFJ1 hC hJ hN hB hC1 hB1 q
  choose D hD hinc using A.finite_atlas_increment_bound
  let L := ‖spaceCoordinates.symm.toContinuousLinearMap‖
  let α := fun m x => L*Af m x
  let γ := fun m x => E m*x^(e m)
  let β := fun m x => L*γ m x
  have hL : 0 ≤ L := norm_nonneg _
  have hα (m : ℕ) : RealModes.HasPolynomialBound (α m) :=
    (RealModes.polynomialBound_const hL).mul (hAf m)
  have hγ (m : ℕ) : RealModes.HasPolynomialBound (γ m) :=
    (RealModes.polynomialBound_const (zero_le_one.trans (hE m))).mul
      (RealModes.polynomialBound_id.pow (e m))
  have hβ (m : ℕ) : RealModes.HasPolynomialBound (β m) :=
    (RealModes.polynomialBound_const hL).mul (hγ m)
  refine ⟨α,β,γ,Rf,D,hα,hβ,hγ,hRf,hD,?_⟩
  intro h a ξ w hw hV n hn x hx F hF hlocal hpairs hImm hnormal hgram
    φ τ s c r ρ R reference d hφ hc hρ hτ hs hτs hs1 hρB hbud hFjets δ hδ hδτ u hu hball hbu
    H hH Rm hRm
  have hτ1 : τ ≤ 1 := hτs.trans hs1
  have hK (i : A.centers) (j : (a i) × Fin 3) :
      (modeSupport (A.cellChartCompact i (a i) h j.1.val) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
    Set.image_mono (A.cellChartCompact_subset i (a i) h j.1.val)
  have hcard (i : A.centers) : Fintype.card ((a i) × Fin 3) ≤ n :=
    (Fintype.card_le_of_injective (fun j : (a i) × Fin 3 => (⟨i,j⟩ : A.GridPhaseIndex a))
      (by intro j k he; exact eq_of_heq (Sigma.mk.inj he).2)).trans hn
  have hfr := hfree x hx n hcard F hF d hc hρ hτ hs hτs hs1 hK hρB hbud
    δ hδ.le u hu hball hbu
  obtain ⟨W,hW,hWb,hWe⟩ := hquad h a ξ w hw hV n hn x hx F hF hlocal hpairs
    hImm hnormal hgram d hφ hc hρ hτ hs hτs hs1 hρB hbud hFjets δ hδ.le u hu hball hbu
  let U₀ := spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u
  let V₀ := spaceCoordinates.symm ∘ W
  have hU₀ : ContMDiff planeModel spaceModel ∞ U₀ :=
    spaceCoordinates.symm.contDiff.contMDiff.comp (A.finiteAtlasFreeOscillation_smooth d hρ δ q u)
  have hV₀ : ContMDiff planeModel spaceModel ∞ V₀ :=
    spaceCoordinates.symm.contDiff.contMDiff.comp hW
  have hUb (m : ℕ) : A.WeightedBound τ m (α m x*(n : ℝ)*(δ*τ)) U₀ := by
    have hh := A.weightedBound_clm spaceCoordinates.symm.toContinuousLinearMap
      (A.finiteAtlasFreeOscillation_smooth d hρ δ q u) hτ.le (hfr m).1
    convert hh using 1
    · dsimp [α,L]
      ring
    · rfl
  have hVb (m : ℕ) : A.WeightedBound τ m
      (β m x*((n : ℝ)+2*(n : ℝ)^2)*δ^2) V₀ := by
    have hh := A.weightedBound_clm spaceCoordinates.symm.toContinuousLinearMap hW hτ.le (hWb m)
    convert hh using 1
    · dsimp [β,γ,L]
      ring
    · rfl
  have hα0 (m : ℕ) : 0 ≤ α m x := by
    obtain ⟨_,_,_,hh⟩ := hα m
    exact (hh x hx).1
  have hβ0 (m : ℕ) : 0 ≤ β m x := by
    obtain ⟨_,_,_,hh⟩ := hβ m
    exact (hh x hx).1
  refine ⟨U₀+V₀,hU₀.add hV₀,?_,?_⟩
  · intro m
    have hδsq : δ^2 ≤ δ*τ := by nlinarith
    have hVb' : A.WeightedBound τ m
        (β m x*((n : ℝ)+2*(n : ℝ)^2)*(δ*τ)) V₀ :=
      fun i => (hVb m i).mono_const (mul_le_mul_of_nonneg_left hδsq (mul_nonneg (hβ0 m) (by positivity)))
    have hh := A.weightedBound_add hU₀ hV₀ hτ.le (hUb m) hVb'
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · intro m
    have hh := hinc m d hρ δ q u hK F V₀ hF hV₀ H hH hτ hτ1 hδ hδτ
      (α (m+1) x*(n : ℝ)) (β (m+1) x*((n : ℝ)+2*(n : ℝ)^2))
      ((τ/s)^(q+1)*(Rf m x*(n : ℝ)*(δ*τ)))
      ((τ/s)^(q+1)*(γ m x*((n : ℝ)+2*(n : ℝ)^2)*δ^2)) (Rm m)
      (mul_nonneg (hα0 _) (Nat.cast_nonneg _)) (mul_nonneg (hβ0 _) (by positivity))
      (hUb (m+1)) (hVb (m+1)) (hfr m).2
      (by convert hWe m using 1; dsimp [γ] <;> ring) (hRm m)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_forced_increment_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_forced_increment_oai.{u_1}
