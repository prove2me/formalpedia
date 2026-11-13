-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_nonlinear_profiles
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:36:45.129471+00:00
-- url     : https://prove2.me/submissions/bf43beb5-d03a-4b35-b7a3-7c07b92ec3d5

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_remainder_bound

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_OscillatoryModel
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes

lemma partial_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Base → E} {p : Base} (hF : DifferentiableAt ℝ F p)
    (hG : DifferentiableAt ℝ G p) (v : Base) :
    coordDeriv v (fun q => F q + G q) p = coordDeriv v F p + coordDeriv v G p := by
  simp only [coordDeriv, fderiv_fun_add hF hG, add_apply]

end ClosedSurfaceR4.SmallModes

end

end OAI
end

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



lemma WeightedBound.mono_order {U : Set E} {s C : ℝ} {m r : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hr : r ≤ m) : WeightedBound U s r C f :=
  fun j hj => h j (hj.trans hr)

lemma WeightedBound.fderivWithin {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hs : 0 < s) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) (fderivWithin ℝ f U) := by
  intro j hj x hx
  rw [norm_iteratedFDerivWithin_fderivWithin hU hx]
  apply (le_div_iff₀ hs).2
  have hh := hb (j + 1) (Nat.add_le_add_right hj 1) x hx
  rw [pow_succ] at hh
  nlinarith


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




lemma smooth_compact_weighted_bound {U : Set E} {V K : Set F}
    (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V) (hK : IsCompact K) (hKV : K ⊆ V)
    {g : F → G} (hg : ContDiffOn ℝ ∞ g V) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (f : E → F) (s C : ℝ), 0 < s → 1 ≤ C →
      ContDiffOn ℝ ∞ f U → MapsTo f U K → WeightedBound U s m C f →
      WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (g ∘ f) := by
  obtain ⟨D, hD, hbD⟩ := compact_coefficient_bound hV hK hKV hg m
  refine ⟨D, hD, ?_⟩
  intro f s C hs hC hf hfk hbf
  exact hbf.comp hU hV hs hC (le_trans zero_le_one hD) hf hg
    (fun x hx => hKV (hfk hx)) (fun j hj x hx => hbD j hj (f x) (hfk hx))




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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ForcedModes
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (realPartCLM)

lemma realMetric_add {n : ℕ} {F U : RField n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hU : DifferentiableAt ℝ U p) (v w : Base) :
    realMetric (fun q => F q + U q) v w p =
      realMetric F v w p + realLinearized F U v w p + realMetric U v w p := by
  unfold realMetric realLinearized
  rw [partial_add hF hU v, partial_add hF hU w]
  simp only [add_dotProduct, dotProduct_add]
  rw [dotProduct_comm (coordDeriv v U p)]
  ring

end ClosedSurfaceR4.RealModes

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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricTensors
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma realLinearizedTensor_apply {n : ℕ} (F U : RField n) (p : Base) (i : Fin 3) :
    realLinearizedTensor F U p i = realLinearized F U (firstDirection i) (secondDirection i) p := by
  fin_cases i <;> rfl

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_DoubleModes
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma realMetricTensor_add {n : ℕ} {F X : RField n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hX : DifferentiableAt ℝ X p) :
    realMetricTensor (fun q => F q + X q) p =
      realMetricTensor F p + realLinearizedTensor F X p + realMetricTensor X p := by
  ext i
  simp only [Pi.add_apply, realMetricTensor_apply, realLinearizedTensor_apply,
    realMetric_add hF hX]


end ClosedSurfaceR4.RealModes

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_WeightedPolynomialBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted estimates for the finite higher-jet monomials in paper 094-01.
The loss exponent adds under products and is unchanged when the output
order increases; only the multiplicative constant depends on that order. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.mul_real {U : Set A} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {f g : A → ℝ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => f x * g x) :=
  hbf.smul_real hU hs hC hD hf hg hbg

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_DirectionalJetBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Higher directional jets of a controlled second jet lose one scale per
additional derivative. These are the factors in the finite jet polynomials. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.WeightedEstimates

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.iteratedDirectional {U : Set A} (hU : IsOpen U) {f : A → E}
    {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hf : ContDiffOn ℝ ∞ f U)
    (vs : List A) (hv : ∀ v ∈ vs, ‖v‖ ≤ 1) (m : ℕ)
    (hb : WeightedBound U s (m + vs.length) C f) :
    WeightedBound U s m (C / s ^ vs.length) (iteratedDirectional vs f) := by
  induction vs generalizing m with
  | nil => simpa [ClosedSurfaceR4.WeightedEstimates.iteratedDirectional] using hb
  | cons v vs ih =>
    have he : m + (v :: vs).length = (m + 1) + vs.length := by simp; omega
    have ht := ih (fun w hw => hv w (List.mem_cons_of_mem v hw)) (m + 1) (he ▸ hb)
    have hd := ht.directional hU hs (contDiffOn_iteratedDirectional hU hf vs) v
    apply hd.mono_const
    have hn : ‖v‖ ≤ 1 := hv v (List.mem_cons_self ..)
    have hc : 0 ≤ C / s ^ vs.length / s := by positivity
    calc
      ‖v‖ * (C / s ^ vs.length / s) ≤ C / s ^ vs.length / s := mul_le_of_le_one_left hc hn
      _ = C / s ^ (v :: vs).length := by simp [pow_succ, div_div]

end ClosedSurfaceR4.WeightedEstimates

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetWordDecomposition
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every ordered coordinate jet is a derivative of a component of the
actual second jet, with precisely the excess derivative count. -/
noncomputable section

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma exists_lowWord (w : List (Fin 2)) (hw : w.length ≤ 2) :
    ∃ i : Fin 7, lowWord i = w := by
  cases w with
  | nil => exact ⟨0, rfl⟩
  | cons a w =>
    cases w with
    | nil =>
      fin_cases a
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    | cons b w =>
      have he : w = [] := List.eq_nil_of_length_eq_zero (by
        simp only [List.length_cons] at hw
        omega)
      subst w
      fin_cases a <;> fin_cases b
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨6, rfl⟩

lemma split_lowWord (w : List (Fin 2)) :
    ∃ v : List (Fin 2), ∃ i : Fin 7, w = v ++ lowWord i ∧ v.length = w.length - 2 := by
  obtain ⟨i, hi⟩ := exists_lowWord (w.drop (w.length - 2)) (by
    rw [List.length_drop]
    omega)
  refine ⟨w.take (w.length - 2), i, ?_, ?_⟩
  · rw [hi, List.take_append_drop]
  · rw [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]

lemma iteratedDirectional_append {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v w : List A) (f : A → E) :
    iteratedDirectional (v ++ w) f = iteratedDirectional v (iteratedDirectional w f) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [List.cons_append, iteratedDirectional, ih]

/-- The scale loss of an ordered jet factor is its derivative order minus two. -/
lemma jet_as_lowJet_derivative (w : List (Fin 2)) (a : Fin 4) :
    ∃ v : List (Fin 2), ∃ i : Fin 7, v.length = w.length - 2 ∧
      ∀ (G : Base → Space), jet G w a =
        iteratedDirectional (v.map coordinateVector) (fun p => lowJet G p (Sum.inr (i, a))) := by
  obtain ⟨v, i, hw, hv⟩ := split_lowWord w
  refine ⟨v, i, hv, ?_⟩
  intro G
  change iteratedDirectional (w.map coordinateVector) (fun p => G p a) = _
  rw [hw, List.map_append, iteratedDirectional_append]
  rfl

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedActualJets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual jets have precisely one scale loss per derivative beyond the
controlled second jet, with no loss for their first two derivatives. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma norm_coordinateVector_le (v : Fin 2) : ‖coordinateVector v‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro i
  by_cases h : i = v
  · subst i
    simp [coordinateVector]
  · simp [coordinateVector, h]

/-- A weighted bound on the second-jet map controls every actual higher jet. -/
theorem weighted_actual_jet {U : Set Base} (hU : IsOpen U) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) {s B : ℝ} (hs : 0 < s) (hB : 0 ≤ B)
    (m : ℕ) (w : List (Fin 2)) (a : Fin 4)
    (hb : WeightedBound U s (m + (w.length - 2)) B (lowJet G)) :
    WeightedBound U s m (B / s ^ (w.length - 2)) (jet G w a) := by
  obtain ⟨v, i, hv, he⟩ := jet_as_lowJet_derivative w a
  rw [he G]
  have hQ := (lowJet_smooth hG).contDiffOn (s := U)
  have hcomp := hb.component hU.uniqueDiffOn hs.le hB hQ (Sum.inr (i, a))
  have hf : ContDiffOn ℝ ∞ (fun p => lowJet G p (Sum.inr (i, a))) U :=
    (contDiff_pi.mp (lowJet_smooth hG) (Sum.inr (i, a))).contDiffOn
  have hvnorm : ∀ x ∈ v.map coordinateVector, ‖x‖ ≤ 1 := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact norm_coordinateVector_le j
  have hcomp' : WeightedBound U s (m + (v.map coordinateVector).length) B
      (fun p => lowJet G p (Sum.inr (i, a))) := by
    simpa only [List.length_map, hv] using hcomp
  have hd := hcomp'.iteratedDirectional hU hs hB hf (v.map coordinateVector) hvnorm m
  simpa only [List.length_map, hv] using hd

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetVariations
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual variations of the ordered coordinate jets. The position entries
do not vary, and a second-jet variation costs at most two short-scale powers. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma lowJet_affine {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (t : ℝ) (p : Base) :
    lowJet (fun q => G q + t • H q) p = lowJet G p + t • variationLowJet H p := by
  funext i
  cases i with
  | inl i => simp [lowJet, variationLowJet]
  | inr i =>
    change jet (fun q => G q + t • H q) (lowWord i.1) i.2 p = _
    rw [jet_add (H := fun q => t • H q) hG (ContDiff.const_smul t hH), jet_smul hH]
    rfl

theorem weighted_variationLowJet {U : Set Base} (hU : IsOpen U)
    {H : Base → Space} (hH : ContDiff ℝ ∞ H) {s C : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C) (m : ℕ)
    (hb : WeightedBound U s (m + 2) C H) :
    WeightedBound U s m (C / s ^ 2) (variationLowJet H) := by
  apply WeightedBound.pi hU.uniqueDiffOn hs (div_nonneg hC (sq_nonneg s))
    (fun i => (contDiff_pi.mp (variationLowJet_smooth hH) i).contDiffOn)
  intro i
  cases i with
  | inl i =>
    change WeightedBound U s m (C / s ^ 2) (fun _ => (0 : ℝ))
    exact (weightedBound_const U s m (0 : ℝ)).mono_const
      (by simpa only [norm_zero] using div_nonneg hC (sq_nonneg s))
  | inr i =>
    obtain ⟨w, a⟩ := i
    have hlen : (lowWord w).length ≤ 2 := by fin_cases w <;> simp [lowWord]
    have hc := hb.component hU.uniqueDiffOn hs.le hC hH.contDiffOn a
    have hbc : WeightedBound U s (m + ((lowWord w).map coordinateVector).length) C
        (fun p => H p a) := by
      simpa only [List.length_map] using hc.mono_order (Nat.add_le_add_left hlen m)
    have hd := hbc.iteratedDirectional hU hs hC
      (contDiff_pi.mp hH a).contDiffOn ((lowWord w).map coordinateVector)
      (fun v hv => by
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
        exact norm_coordinateVector_le j) m
    apply hd.mono_const
    apply div_le_div_of_nonneg_left hC (pow_pos hs 2)
    exact pow_le_pow_of_le_one hs.le hs1 (by simpa only [List.length_map] using hlen)

end ClosedSurfaceR4.JetPolynomial

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

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalIsometryBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isometric coordinate transport on the open domains used by the local
polynomial estimates. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma weightedBound_comp_isometry_on {A B F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : A ≃ₗᵢ[ℝ] B) {U : Set B} (hU : IsOpen U) {f : B → F}
    (hf : ContDiff ℝ ∞ f) {s C : ℝ} {m : ℕ}
    (hb : WeightedBound U s m C f) :
    WeightedBound (e ⁻¹' U) s m C (f ∘ e) := by
  intro j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j (hU.preimage e.continuous) hx]
  change s ^ j * ‖iteratedFDeriv ℝ j
    (f ∘ (e.toContinuousLinearEquiv.toContinuousLinearMap : A → B)) x‖ ≤ C
  rw [e.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hf x (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),
    ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]
  change s ^ j * ‖iteratedFDeriv ℝ j f (e x)‖ ≤ C
  have hh := hb j hj (e x) hx
  rw [iteratedFDerivWithin_of_isOpen j hU hx] at hh
  exact hh

end ClosedSurfaceR4.JetPolynomial

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
local instance planeReadSectionSpace_r0002d1_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRestore_sub (f g : A.centers → SmallModes.Base → Tensor) :
    A.tensorPlaneRestore (f-g) = A.tensorPlaneRestore f - A.tensorPlaneRestore g := by
  funext p
  simp only [tensorPlaneRestore, Pi.sub_apply, map_sub, bundleRestore, smul_sub,
    Finset.sum_sub_distrib]

variable [CompactSpace M]

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedLowCoefficients
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform angular-slice estimates for smooth low-jet coefficients on a
compact admissible set. The angular parameter adds no scale loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma weighted_lowJet_pair {U : Set Base} (hU : IsOpen U) {Q : Base → LowJet}
    (hQ : ContDiffOn ℝ ∞ Q U) {s B : ℝ} (hs : 0 < s) (hB : 1 ≤ B) (m : ℕ)
    (hb : WeightedBound U s m B Q) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    WeightedBound U s m (2 * B) (fun p => (Q p, t)) := by
  have hleft : WeightedBound U s m B (fun p => (Q p, (0 : ℝ))) := by
    simpa only [ContinuousLinearMap.norm_inl, one_mul, Function.comp_def,
      ContinuousLinearMap.inl_apply] using
      hb.linear hU.uniqueDiffOn hs.le hQ (ContinuousLinearMap.inl ℝ LowJet ℝ)
  have hc : ‖((0 : LowJet), t)‖ ≤ 1 := by
    rw [Prod.norm_def, norm_zero, Real.norm_of_nonneg ht.1]
    exact max_le (by norm_num) ht.2
  have hright : WeightedBound U s m 1 (fun _ : Base => ((0 : LowJet), t)) :=
    (weightedBound_const U s m ((0 : LowJet), t)).mono_const hc
  have hsum := hleft.add hU.uniqueDiffOn hs.le (hQ.prodMk contDiffOn_const) contDiffOn_const hright
  have hp : WeightedBound U s m (B + 1) (fun p => (Q p, t)) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using hsum
  exact hp.mono_const (by linarith)

/-- The same constant controls every angular slice over the unit period. -/
theorem compact_low_coefficient {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {c : LowJet × ℝ → ℝ} (hc : ContDiffOn ℝ ∞ c (O ×ˢ Set.univ))
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (Q : Base → LowJet) (s : ℝ), 0 < s →
      ContDiffOn ℝ ∞ Q U → Set.MapsTo Q U K → WeightedBound U s m B Q →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U s m D (fun p => c (Q p, t)) := by
  have hcompact : IsCompact (K ×ˢ Set.Icc (0 : ℝ) 1) := hK.prod isCompact_Icc
  have hsub : K ×ˢ Set.Icc (0 : ℝ) 1 ⊆ O ×ˢ Set.univ :=
    fun _ hz => ⟨hKO hz.1, Set.mem_univ _⟩
  obtain ⟨D, hD, hb⟩ := smooth_compact_weighted_bound hU.uniqueDiffOn
    (hO.prod isOpen_univ).uniqueDiffOn hcompact hsub hc m
  refine ⟨(m.factorial : ℝ) * D * (2 * B) ^ m, by positivity, ?_⟩
  intro Q s hs hQ hQK hQB t ht
  exact hb (fun p => (Q p, t)) s (2 * B) hs (by linarith)
    (hQ.prodMk contDiffOn_const) (fun p hp => ⟨hQK hp, ht⟩)
    (weighted_lowJet_pair hU hQ hs hB m hQB ht)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_WeightedPolynomialVariation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A first-variation estimate for every finite higher-jet polynomial.
Its scale exponent is fixed by the polynomial, independently of output order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma weighted_plain_jet {U : Set Base} (hU : IsOpen U) {H : Base → Space}
    (hH : ContDiff ℝ ∞ H) {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C)
    (m : ℕ) (w : List (Fin 2)) (a : Fin 4)
    (hb : WeightedBound U s (m + w.length) C H) :
    WeightedBound U s m (C / s ^ w.length) (jet H w a) := by
  have hc := hb.component hU.uniqueDiffOn hs.le hC hH.contDiffOn a
  have hcw : WeightedBound U s (m + (w.map coordinateVector).length) C (fun p => H p a) := by
    simpa only [List.length_map] using hc
  change WeightedBound U s m (C / s ^ w.length)
    (iteratedDirectional (w.map coordinateVector) (fun x => H x a))
  simpa only [List.length_map] using hcw.iteratedDirectional hU hs hC
    (contDiff_pi.mp hH a).contDiffOn (w.map coordinateVector)
    (fun v hv => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
      exact norm_coordinateVector_le i) m

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_MixedJetPolynomial
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomials in the base-map jet and three independent variation jets.
Differentiating the base map increases the scale loss by at most two. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

namespace MixedExpression

lemma ofExpression_loss (e : Expression) : (ofExpression e).loss = e.loss := by
  induction e with
  | coeff => rfl
  | atom _ _ _ ih => simp only [ofExpression, loss, ↓reduceIte, Expression.loss, ih]
  | add _ _ ihe ihf => simp only [ofExpression, loss, Expression.loss, ihe, ihf]

lemma loss_sumList_le {ι : Type*} (l : List ι) (f : ι → MixedExpression) (N : ℕ)
    (h : ∀ i ∈ l, (f i).loss ≤ N) : (sumList l f).loss ≤ N := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons i l ih =>
    exact max_le (h i (List.mem_cons_self ..))
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

theorem loss_differentiate (j : Fin 3) (e : MixedExpression) :
    (e.differentiate j).loss ≤ e.loss + 2 := by
  induction e with
  | coeff c =>
    apply loss_sumList_le
    intro i _
    have hl : (lowWord i.1).length ≤ 2 := by
      obtain ⟨i, a⟩ := i
      fin_cases i <;> simp [lowWord]
    simpa only [loss, Fin.succ_ne_zero, ↓reduceIte, Nat.add_zero] using hl
  | atom i w a e ih =>
    by_cases hi : i = 0
    · subst i
      simp only [differentiate, loss, Fin.succ_ne_zero, ↓reduceIte]
      omega
    · simp only [differentiate, hi, ↓reduceIte, loss]
      omega
  | add e f ihe ihf =>
    simp only [differentiate, loss]
    omega

theorem loss_third_variation (e : Expression) :
    ((((ofExpression e).differentiate 0).differentiate 1).differentiate 2).loss ≤ e.loss + 6 := by
  have h₁ := loss_differentiate 0 (ofExpression e)
  have h₂ := loss_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := loss_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [ofExpression_loss] at h₁
  omega

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetRegularity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial order and smoothness of mixed jet expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

lemma order_sumList_le {ι : Type*} (l : List ι) (f : ι → MixedExpression) (N : ℕ)
    (hN : 2 ≤ N) (h : ∀ i ∈ l, (f i).order ≤ N) : (sumList l f).order ≤ N := by
  induction l with
  | nil => exact hN
  | cons i l ih =>
    exact max_le (h i (List.mem_cons_self ..))
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

lemma order_differentiate (j : Fin 3) (e : MixedExpression) :
    (e.differentiate j).order ≤ e.order := by
  induction e with
  | coeff c =>
    apply order_sumList_le _ _ 2 (le_refl 2)
    intro i _
    have hl : (lowWord i.1).length ≤ 2 := by
      obtain ⟨i, a⟩ := i
      fin_cases i <;> simp [lowWord]
    exact max_le hl (le_refl 2)
  | atom i w a e ih =>
    by_cases hi : i = 0
    · simp only [differentiate, hi, ↓reduceIte, order]
      omega
    · simp only [differentiate, hi, ↓reduceIte, order]
      omega
  | add e f ihe ihf =>
    simp only [differentiate, order]
    omega

lemma order_ofExpression (e : Expression) : (ofExpression e).order = e.order := by
  induction e with
  | coeff => rfl
  | atom _ _ _ ih => simp only [ofExpression, order, Expression.order, ih]
  | add _ _ ihe ihf => simp only [ofExpression, order, Expression.order, ihe, ihf]

theorem eval_smooth {O : Set LowJet} {U : Set Base} {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hQ : Set.MapsTo (lowJet (G 0)) U O)
    {e : MixedExpression} (he : e.SmoothCoeffs O) :
    ContDiffOn ℝ ∞ (e.eval G) (U ×ˢ Set.univ) := by
  induction e with
  | coeff c =>
    exact he.comp (((lowJet_smooth (hG 0)).comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun z hz => ⟨hQ hz.1, hz.2⟩)
  | atom i w a e ih =>
    exact (((jet_smooth (hG i) w a).comp contDiff_fst).contDiffOn.mul (ih he))
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

lemma parameter_smooth {O : Set LowJet} {U : Set Base} {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hQ : Set.MapsTo (lowJet (G 0)) U O)
    {e : MixedExpression} (he : e.SmoothCoeffs O) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun p => e.eval G (p, t)) U :=
  (eval_smooth hG hQ he).comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun _ hp => ⟨hp, Set.mem_univ t⟩)

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedMixedJets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform mixed-variation bounds with the sharp excess-jet scale loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression
open WeightedEstimates

/-- Unit weighted bounds on the direction maps cost their full jet orders;
the base map costs only the order beyond its controlled second jet. -/
theorem compact_mixed_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : MixedExpression) (he : e.SmoothCoeffs O) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Fin 4 → Base → Space) (s : ℝ), 0 < s → s ≤ 1 →
      (∀ i, ContDiff ℝ ∞ (G i)) → Set.MapsTo (lowJet (G 0)) U K →
      WeightedBound U s (m + e.order) B (lowJet (G 0)) →
      (∀ i : Fin 3, WeightedBound U s (m + e.order) 1 (G i.succ)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (D / s ^ e.loss) (fun p => e.eval G (p, t)) := by
  induction e with
  | coeff c =>
    obtain ⟨D, hD, hd⟩ := compact_low_coefficient hU hO hK hKO he m B hB
    refine ⟨D, hD, ?_⟩
    intro G s hs _ hG hGK hb _ t ht
    simpa only [loss, pow_zero, div_one, eval] using
      hd (lowJet (G 0)) s hs (lowJet_smooth (hG 0)).contDiffOn hGK
        (hb.mono_order (by omega)) t ht
  | atom i w a e ih =>
    obtain ⟨D, hD, hd⟩ := ih he
    refine ⟨2 ^ m * B * D, by positivity, ?_⟩
    intro G s hs hs1 hG hGK hb hv t ht
    have hQ : Set.MapsTo (lowJet (G 0)) U O := fun _ hp => hKO (hGK hp)
    have htail := hd G s hs hs1 hG hGK
      (hb.mono_order (by simp only [order]; omega))
      (fun j => (hv j).mono_order (by simp only [order]; omega)) t ht
    have hj : WeightedBound U s m
        (B / s ^ (if i = 0 then w.length - 2 else w.length)) (jet (G i) w a) := by
      by_cases hi : i = 0
      · subst i
        simp only [↓reduceIte]
        exact weighted_actual_jet hU (hG 0) hs (zero_le_one.trans hB) m w a
          (hb.mono_order (by simp only [order]; omega))
      · let j : Fin 3 := i.pred hi
        have hij : i = j.succ := (Fin.succ_pred i hi).symm
        rw [hij]
        simp only [Fin.succ_ne_zero, ↓reduceIte]
        exact (weighted_plain_jet hU (hG j.succ) hs zero_le_one m w a
          ((hv j).mono_order (by simp only [order]; omega))).mono_const
            (div_le_div_of_nonneg_right hB (pow_nonneg hs.le _))
    have hp := hj.mul_real hU.uniqueDiffOn hs.le (by positivity) (by positivity)
      (jet_smooth (hG i) w a).contDiffOn (parameter_smooth hG hQ (e := e) he t) htail
    convert hp using 1 <;> first | rfl | simp only [loss, pow_add]; ring
  | add e f ihe ihf =>
    obtain ⟨D, hD, hd⟩ := ihe he.1
    obtain ⟨C, hC, hc⟩ := ihf he.2
    refine ⟨D + C, add_nonneg hD hC, ?_⟩
    intro G s hs hs1 hG hGK hb hv t ht
    have hQ : Set.MapsTo (lowJet (G 0)) U O := fun _ hp => hKO (hGK hp)
    have hd' := hd G s hs hs1 hG hGK (hb.mono_order (by simp only [order]; omega))
      (fun j => (hv j).mono_order (by simp only [order]; omega)) t ht
    have hc' := hc G s hs hs1 hG hGK (hb.mono_order (by simp only [order]; omega))
      (fun j => (hv j).mono_order (by simp only [order]; omega)) t ht
    have hd'' : WeightedBound U s m (D / s ^ max e.loss f.loss) (fun p => e.eval G (p, t)) :=
      hd'.mono_const (div_le_div_of_nonneg_left hD (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (le_max_left _ _)))
    have hc'' : WeightedBound U s m (C / s ^ max e.loss f.loss) (fun p => f.eval G (p, t)) :=
      hc'.mono_const (div_le_div_of_nonneg_left hC (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (le_max_right _ _)))
    simpa only [loss, add_div, eval] using hd''.add hU.uniqueDiffOn hs.le
      (parameter_smooth hG hQ (e := e) he.1 t) (parameter_smooth hG hQ (e := f) he.2 t) hc''

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetHomogeneity
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Homogeneity in each variation slot, including the zero polynomial. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

lemma scaleSlot_base (G : Fin 4 → Base → Space) (j : Fin 3) (c : ℝ) :
    scaleSlot G j c 0 = G 0 := by
  funext p
  simp only [scaleSlot, Ne.symm (Fin.succ_ne_zero j), ↓reduceIte]

lemma scaleSlot_smooth {G : Fin 4 → Base → Space} (hG : ∀ i, ContDiff ℝ ∞ (G i))
    (j : Fin 3) (c : ℝ) : ∀ i, ContDiff ℝ ∞ (scaleSlot G j c i) := by
  intro i
  change ContDiff ℝ ∞ (fun p => if i = j.succ then c • G i p else G i p)
  by_cases hi : i = j.succ
  · simpa only [scaleSlot, hi, ↓reduceIte] using ContDiff.const_smul c (hG j.succ)
  · simpa only [scaleSlot, hi, ↓reduceIte] using hG i

theorem DegreeIn.eval_scaleSlot {j : Fin 3} {e : MixedExpression} {n : ℕ}
    (h : DegreeIn j e n) {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (c : ℝ) (z : Base × ℝ) :
    e.eval (scaleSlot G j c) z = c ^ n * e.eval G z := by
  induction h with
  | coeff d => simp only [eval, scaleSlot_base, pow_zero, one_mul]
  | zero n => simp only [eval, mul_zero]
  | other i w a hi h ih =>
    have he : scaleSlot G j c i = G i := by
      funext p
      simp only [scaleSlot, hi, ↓reduceIte]
    simp only [eval, he, ih]
    ring
  | same w a h ih =>
    have he : scaleSlot G j c j.succ = fun p => c • G j.succ p := by
      funext p
      simp only [scaleSlot, ↓reduceIte]
    simp only [eval, he, jet_smul (hG j.succ), ih, pow_succ]
    ring
  | add he hf ihe ihf => simp only [eval, ihe, ihf, mul_add]

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialVariationBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first three actual polynomial variations have one fixed scale
exponent, the excess-jet loss plus six. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression

namespace Expression

lemma variations_order (e : Expression) (i : Fin 3) : (e.variations i).order ≤ e.order := by
  have h₁ := order_differentiate 0 (ofExpression e)
  have h₂ := order_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := order_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [order_ofExpression] at h₁
  fin_cases i
  · exact h₁
  · exact h₂.trans h₁
  · exact h₃.trans (h₂.trans h₁)

lemma variations_loss (e : Expression) (i : Fin 3) : (e.variations i).loss ≤ e.loss + 6 := by
  have h₁ := loss_differentiate 0 (ofExpression e)
  have h₂ := loss_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := loss_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [ofExpression_loss] at h₁
  fin_cases i
  · change ((ofExpression e).differentiate 0).loss ≤ e.loss + 6
    omega
  · change (((ofExpression e).differentiate 0).differentiate 1).loss ≤ e.loss + 6
    omega
  · exact loss_third_variation e

/-- The constant can depend on the requested output order; the exponent and
finite input loss do not. All three direction maps have unit weighted norm. -/
theorem compact_three_variation_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Fin 4 → Base → Space) (s : ℝ), 0 < s → s ≤ 1 →
      (∀ i, ContDiff ℝ ∞ (G i)) → Set.MapsTo (lowJet (G 0)) U K →
      WeightedBound U s (m + e.order) B (lowJet (G 0)) →
      (∀ i : Fin 3, WeightedBound U s (m + e.order) 1 (G i.succ)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m (D / s ^ (e.loss + 6))
          (fun p => (e.variations i).eval G (p, t)) := by
  classical
  have hex := fun i : Fin 3 => compact_mixed_bound hU hO hK hKO (e.variations i)
    (e.variations_smoothCoeffs hO he i) m B hB
  choose D hD hb using hex
  refine ⟨∑ i, D i, Finset.sum_nonneg (fun i _ => hD i), ?_⟩
  intro G s hs hs1 hG hGK hGb hHb t ht i
  have hi := hb i G s hs hs1 hG hGK
    (hGb.mono_order (Nat.add_le_add_left (e.variations_order i) m))
    (fun j => (hHb j).mono_order (Nat.add_le_add_left (e.variations_order i) m)) t ht
  apply hi.mono_const
  calc
    D i / s ^ (e.variations i).loss ≤ D i / s ^ (e.loss + 6) :=
      div_le_div_of_nonneg_left (hD i) (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (e.variations_loss i))
    _ ≤ (∑ j, D j) / s ^ (e.loss + 6) :=
      div_le_div_of_nonneg_right (Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i))
        (pow_nonneg hs.le _)

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialVariationScaling
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multilinear scaling of the three actual polynomial variations. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

namespace MixedExpression

lemma rescale_smooth {G : Fin 4 → Base → Space} (hG : ∀ i, ContDiff ℝ ∞ (G i))
    (c : Fin 3 → ℝ) : ∀ i, ContDiff ℝ ∞ (rescale G c i) := by
  intro i
  fin_cases i
  · exact hG 0
  · exact ContDiff.const_smul (c 0) (hG 1)
  · exact ContDiff.const_smul (c 1) (hG 2)
  · exact ContDiff.const_smul (c 2) (hG 3)

lemma rescale_eq (G : Fin 4 → Base → Space) (c : Fin 3 → ℝ) :
    rescale G c = scaleSlot (scaleSlot (scaleSlot G 0 (c 0)) 1 (c 1)) 2 (c 2) := by
  funext i p
  fin_cases i <;> simp [rescale, scaleSlot]

lemma eval_rescale {e : MixedExpression} {n : Fin 3 → ℕ}
    (he : ∀ j, DegreeIn j e (n j)) {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (c : Fin 3 → ℝ) (z : Base × ℝ) :
    e.eval (rescale G c) z =
      (c 0 ^ n 0 * c 1 ^ n 1 * c 2 ^ n 2) * e.eval G z := by
  rw [rescale_eq, (he 2).eval_scaleSlot
    (scaleSlot_smooth (scaleSlot_smooth hG 0 (c 0)) 1 (c 1)),
    (he 1).eval_scaleSlot (scaleSlot_smooth hG 0 (c 0)), (he 0).eval_scaleSlot hG]
  ring

end MixedExpression
namespace Expression

lemma variations_rescale (e : Expression) {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (c : Fin 3 → ℝ) (z : Base × ℝ) (i : Fin 3) :
    (e.variations i).eval (rescale G c) z =
      (c 0 * (if 1 ≤ i then c 1 else 1) * (if 2 ≤ i then c 2 else 1)) *
        (e.variations i).eval G z := by
  have h := eval_rescale (fun j => e.variations_degree i j) hG c z
  fin_cases i <;> simpa using h

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RealQuadraticVariation
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real quadratic variation is the sum of its zero and double phases. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

lemma evalComplex_real_jets (e : MixedExpression) (F : Fin 4 → Base → Space) (z : Base × ℝ) :
    e.evalComplex (F 0) (fun i w a p => (jet (F i) w a p : ℂ)) z = (e.eval F z : ℂ) := by
  induction e with
  | coeff c => rfl
  | atom i w a e ih => simp only [evalComplex, eval, ih, Complex.ofReal_mul]
  | add e f ihe ihf => simp only [evalComplex, eval, ihe, ihf, Complex.ofReal_add]

lemma jet_zero (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    jet (0 : Base → Space) w a p = 0 := by
  exact congrFun (iteratedDirectional_zero (w.map coordinateVector)) p

lemma quadraticComplex_real_fields (e : Expression) (G H K : Base → Space) (z : Base × ℝ) :
    quadraticComplex e G (fun w a p => (jet H w a p : ℂ)) (fun w a p => (jet K w a p : ℂ)) z =
      ((e.variations 1).eval ![G, H, K, 0] z : ℂ) := by
  have he : pairJetData G (fun w a p => (jet H w a p : ℂ)) (fun w a p => (jet K w a p : ℂ)) =
      fun i w a p => (jet (![G, H, K, 0] i) w a p : ℂ) := by
    funext i w a p
    fin_cases i <;> simp [pairJetData, jet_zero]
  change (e.variations 1).evalComplex G _ z = _
  rw [he]
  exact evalComplex_real_jets (e.variations 1) ![G, H, K, 0] z

end ClosedSurfaceR4.JetPolynomial

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SecondVariationAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact algebra of the real second variation, including its unused
third direction slot. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

lemma real_second_variation_add_left (e : Expression) (G : Base → Space)
    {H K : Base → Space} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (J : Base → Space) (z : Base × ℝ) :
    (e.variations 1).eval ![G,(fun x => H x + K x),J,0] z =
      (e.variations 1).eval ![G,H,J,0] z + (e.variations 1).eval ![G,K,J,0] z := by
  have hj : (fun w a p => (jet (fun x => H x + K x) w a p : ℂ)) =
      (fun w a p => (jet H w a p : ℂ)) + (fun w a p => (jet K w a p : ℂ)) := by
    funext w a p
    simp only [jet_add hH hK, Complex.ofReal_add, Pi.add_apply]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add, ← quadraticComplex_real_fields, ← quadraticComplex_real_fields,
    ← quadraticComplex_real_fields, hj, quadraticComplex_add_left]

lemma real_second_variation_add_right (e : Expression) (G : Base → Space)
    (J : Base → Space) {H K : Base → Space} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (z : Base × ℝ) :
    (e.variations 1).eval ![G,J,(fun x => H x + K x),0] z =
      (e.variations 1).eval ![G,J,H,0] z + (e.variations 1).eval ![G,J,K,0] z := by
  have hj : (fun w a p => (jet (fun x => H x + K x) w a p : ℂ)) =
      (fun w a p => (jet H w a p : ℂ)) + (fun w a p => (jet K w a p : ℂ)) := by
    funext w a p
    simp only [jet_add hH hK, Complex.ofReal_add, Pi.add_apply]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add, ← quadraticComplex_real_fields, ← quadraticComplex_real_fields,
    ← quadraticComplex_real_fields, hj, quadraticComplex_add_right]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_QuadraticInteraction
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the mixed and pure terms introduced by the second, forced
correction from the quadratic tensor of the first, free correction. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinateFullQuadratic_add {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) {X Y : RealModes.RField 4}
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) :
    coordinateFullQuadratic P ε G (X + Y) =
      coordinateFullQuadratic P ε G X + coordinateQuadraticInteraction P ε G X Y := by
  have hx := hX.comp planeCoordinateIsometry.contDiff
  have hy := hY.comp planeCoordinateIsometry.contDiff
  have ha : X + Y = (fun x => X x + Y x) := rfl
  have hc : (X + Y) ∘ planeCoordinateIsometry =
      (fun x => (X ∘ planeCoordinateIsometry) x + (Y ∘ planeCoordinateIsometry) x) := rfl
  funext p k
  simp only [coordinateFullQuadratic, Pi.add_apply, coordinateQuadraticInteraction]
  rw [ha, RealModes.realMetricTensor_add (hX.differentiable (by simp) p) (hY.differentiable (by simp) p)]
  simp only [Pi.add_apply, coordinateQuadraticPolynomial]
  rw [← ha, hc]
  simp_rw [real_second_variation_add_left _ G hx hy,
    real_second_variation_add_right _ G _ hx hy]
  simp only [mul_add, Finset.sum_add_distrib]
  ring_nf

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasFiniteCancellation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite global metric-linear corrections assembled from local phase solvers. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasSolveFiberNormed_r0002d1_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasSolveFiberSpace_r0002d1_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasSolveDualAdd_r0002d1_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasSolveDualSmul_r0002d1_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance atlasSolveSectionNormed_r0002d1_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasSolveSectionSpace_r0002d1_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma jetChartMap_plane (i : A.centers) (F : M → Space) :
    A.jetChartMap i F ∘ planeCoordinateIsometry.symm = spaceCoordinates ∘ A.vectorPlaneRead i F := rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasJetReadBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted bounds for the exact coordinate maps entering the polynomial metric. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem jetPlaneRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ∀ τ C : ℝ, 0 < τ → τ ≤ 1 → 0 ≤ C → A.WeightedBound τ m C F →
      WeightedEstimates.WeightedBound univ τ m (D*C)
        (A.jetChartMap i F ∘ planeCoordinateIsometry.symm) := by
  obtain ⟨D,hD,hd⟩ := A.vectorPlaneRead_bound (V := Space) i m
  refine ⟨‖spaceCoordinates.toContinuousLinearMap‖*D,mul_nonneg (norm_nonneg _) hD,?_⟩
  intro F hF τ C hτ hτ1 hC hb
  rw [A.jetChartMap_plane]
  have hh := (hd F τ C hτ hτ1 hC hF hb).linear uniqueDiffOn_univ hτ.le
    (A.vectorPlaneRead_smooth i hF).contDiffOn spaceCoordinates.toContinuousLinearMap
  simpa only [mul_assoc,ContinuousLinearEquiv.coe_coe] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LinearMetricChartReconstruction
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mixed metric is reconstructed from the genuine chart readings. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
local instance linearReadFiberNormed_r0002d1_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance linearReadFiberSpace_r0002d1_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance linearReadDualAdd_r0002d1_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance linearReadDualSmul_r0002d1_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.linearReadSectionNormed
local instance linearReadSectionSpace_r0002d1_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma vectorPlaneRead_add {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : A.centers) (F G : M → V) :
    A.vectorPlaneRead i (F+G) = A.vectorPlaneRead i F + A.vectorPlaneRead i G := by
  funext x
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target <;>
    simp [vectorPlaneRead,vectorChartRead,localize,hx,smul_add]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialMetric
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual globally restored polynomial perturbation of the metric,
with its exact first, second and higher-order variation decomposition. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricDualSmul
variable (A : SmoothingAtlas M)
variable {n : A.centers → ℕ}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricFiberNormed
local instance polynomialMetricSectionNormed_r0002d1_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialMetricSectionSpace_r0002d1_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma jetChartMap_add (i : A.centers) (G X : M → Space) :
    A.jetChartMap i (G+X) = A.jetChartMap i G+A.jetChartMap i X := by
  have h := A.vectorPlaneRead_add i G X
  funext x
  have hh := congrFun h (planeCoordinateIsometry x)
  change spaceCoordinates (A.vectorChartRead i (G+X) x) =
    spaceCoordinates (A.vectorChartRead i G x)+spaceCoordinates (A.vectorChartRead i X x)
  simpa only [vectorPlaneRead,Function.comp_apply,planeCoordinateIsometry.symm_apply_apply,
    Pi.add_apply,map_add] using congrArg spaceCoordinates hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialValueBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restored polynomial value has one fixed finite loss. Compact local
jet ranges suffice: a fixed cutoff removes the irrelevant values away from
the outer atlas supports before applying the restoration estimate. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialValueFiberSpace
local instance polynomialValueDualAdd_r0002d1_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialValueDualSmul_r0002d1_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialValueFiberNormed
local instance polynomialValueSectionNormed_r0002d1_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialValueSectionSpace_r0002d1_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_outer_cutoff (i : A.centers)
    {U : Set JetPolynomial.Base} (hU : IsOpen U)
    (houter : (chart (i : M)) '' tsupport (A.outer i) ⊆ U) :
    ∃ (K : Compacts JetPolynomial.Base) (χ : SupportedField (F := ℝ) K),
      tsupport (χ : JetPolynomial.Base → ℝ) ⊆ U ∧
      ∀ p ∈ tsupport (A.outer i), χ (chart (i : M) p) = 1 := by
  let S : Set JetPolynomial.Base := (chart (i : M)) '' tsupport (A.outer i)
  have hS : IsCompact S := (isClosed_tsupport (A.outer i)).isCompact.image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (A.outer_support i))
  obtain ⟨V,hV,hSV,hVU,hVc⟩ := exists_open_between_and_isCompact_closure hS hU houter
  obtain ⟨χ,hχ,_,hχs,hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV hS.isClosed hSV
  let K : Compacts JetPolynomial.Base := ⟨closure V,hVc⟩
  let χ' : SupportedField (F := ℝ) K := ContDiffMapSupportedIn.of_support_subset hχ
    (by rw [hχs]; exact subset_closure)
  refine ⟨K,χ',?_,?_⟩
  · change closure (Function.support χ) ⊆ U
    rw [hχs]
    exact hVU
  · intro p hp
    exact (hχone (chart (i : M) p)).mp ⟨p,hp,rfl⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasTensorLocalBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restored polynomial value has one fixed finite loss. Compact local
jet ranges suffice: a fixed cutoff removes the irrelevant values away from
the outer atlas supports before applying the restoration estimate. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorLocalFiberSpace
local instance tensorLocalDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorLocalFiberSpace
local instance tensorLocalDualSmul_r0002d1_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)


attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorLocalFiberNormed
local instance tensorLocalSectionNormed_r0002d1_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance tensorLocalSectionSpace_r0002d1_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- Compact coordinate bounds on the outer supports suffice for global restoration. -/
theorem tensorPlaneRestore_bound_on_outer
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i)
    (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : A.centers → SmallModes.Base → Tensor),
      (∀ i, ContDiff ℝ ∞ (f i)) → ∀ (s C : ℝ), 0 < s → s ≤ 1 → 0 ≤ C →
      (∀ i, WeightedEstimates.WeightedBound (planeCoordinateIsometry.symm ⁻¹' U i) s m C (f i)) →
      A.TensorWeightedBound s m (D*C) (A.tensorPlaneRestore f) := by
  classical
  choose K χ hχU hχone using fun i => A.polynomial_outer_cutoff i (hU i) (houter i)
  obtain ⟨D,hD,hd⟩ := A.tensorPlaneRestore_bound m
  let N : A.centers → ℝ := fun i => supportedWeightedSeminorm (K i) 1 m (χ i)
  have hN (i) : 0 ≤ N i := apply_nonneg _ _
  let E : A.centers → ℝ := fun i => 2^m * N i
  have hE (i) : 0 ≤ E i := mul_nonneg (by positivity) (hN i)
  let E₀ := ∑ i : A.centers, E i
  have hE₀ : 0 ≤ E₀ := Finset.sum_nonneg (fun i _ => hE i)
  refine ⟨D*E₀,mul_nonneg hD hE₀,?_⟩
  intro f hf s C hs hs1 hC hb
  let ψ : A.centers → SmallModes.Base → ℝ := fun i => (χ i) ∘ planeCoordinateIsometry.symm
  let g : A.centers → SmallModes.Base → Tensor := fun i x => ψ i x • f i x
  have hψ (i) : ContDiff ℝ ∞ (ψ i) := (χ i).contDiff.comp planeCoordinateIsometry.symm.contDiff
  have hg (i) : ContDiff ℝ ∞ (g i) := (hψ i).smul (hf i)
  have hψsp (i) : tsupport (ψ i) ⊆ planeCoordinateIsometry.symm ⁻¹' U i := by
    apply (show tsupport (ψ i) ⊆ planeCoordinateIsometry.symm ⁻¹' tsupport (χ i) from ?_).trans
      (preimage_mono (hχU i))
    apply closure_minimal _ ((isClosed_tsupport (χ i)).preimage planeCoordinateIsometry.symm.continuous)
    intro x hx
    exact subset_tsupport (χ i) hx
  have hψb (i) : WeightedEstimates.WeightedBound univ s m (N i) (ψ i) :=
    weightedBound_comp_isometry planeCoordinateIsometry.symm (χ i).contDiff
      ((weightedBound_of_supportedSeminorm (1 : ℝ≥0) m (χ i)).shrink_scale hs.le hs1)
  have hgb (i) : WeightedEstimates.WeightedBound univ s m (E i*C) (g i) := by
    let V := planeCoordinateIsometry.symm ⁻¹' U i
    have hV : IsOpen V := (hU i).preimage planeCoordinateIsometry.symm.continuous
    have hprod := ((hψb i).restrict_open hV).smul_real hV.uniqueDiffOn hs.le (hN i) hC
      (hψ i).contDiffOn (hf i).contDiffOn (hb i)
    exact hprod.extend_support hV
      ((tsupport_smul_subset_left (ψ i) (f i)).trans (hψsp i)) (mul_nonneg (hE i) hC)
  have hglobal (i) : WeightedEstimates.WeightedBound univ s m (E₀*C) (g i) := by
    apply (hgb i).mono_const
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ i)) hC
  have hout := hd g s (E₀*C) hs hs1 (mul_nonneg hE₀ hC) hg hglobal
  have heq : A.tensorPlaneRestore g = A.tensorPlaneRestore f := by
    funext p
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : p ∈ tsupport (A.outer i)
    · have hχp := hχone i p hp
      change A.outer i p • (A.tensorTriv i).symmL ℝ p
        (fiberFromThree ((χ i) (planeCoordinateIsometry.symm
          (planeCoordinateIsometry (chart (i : M) p))) • f i
            (planeCoordinateIsometry (chart (i : M) p)))) = _
      simp only [planeCoordinateIsometry.symm_apply_apply,hχp,one_smul]
      rfl
    · have hz : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport hp
      simp only [bundleRestore,hz,zero_smul]
  rw [heq] at hout
  simpa only [mul_assoc] using hout

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedMultilinearVariations
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product bounds for non-normalized variation maps. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression WeightedEstimates

namespace MixedExpression

lemma rescale_succ (G : Fin 4 → Base → Space) (c : Fin 3 → ℝ) (i : Fin 3) :
    rescale G c i.succ = fun p => c i • G i.succ p := by
  fin_cases i <;> rfl

lemma rescale_inverse (G : Fin 4 → Base → Space) (C : Fin 3 → ℝ)
    (hC : ∀ i, C i ≠ 0) : rescale (rescale G (fun i => (C i)⁻¹)) C = G := by
  funext i p
  fin_cases i <;> simp [rescale, smul_smul, hC]

end MixedExpression
namespace Expression

/-- Bounds for the first three actual variations, linear in each participating
map bound and with a single accuracy-independent scale exponent. -/
theorem compact_multilinear_variation_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Fin 4 → Base → Space) (s : ℝ) (C : Fin 3 → ℝ),
      0 < s → s ≤ 1 → (∀ i, 0 < C i) →
      (∀ i, ContDiff ℝ ∞ (G i)) → Set.MapsTo (lowJet (G 0)) U K →
      WeightedBound U s (m + e.order) B (lowJet (G 0)) →
      (∀ i : Fin 3, WeightedBound U s (m + e.order) (C i) (G i.succ)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m
          (D * (C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)) /
            s ^ (e.loss + 6)) (fun p => (e.variations i).eval G (p, t)) := by
  obtain ⟨D, hD, hb⟩ := e.compact_three_variation_bound hU hO hK hKO he m B hB
  refine ⟨D, hD, ?_⟩
  intro G s C hs hs1 hC hG hGK hGb hHb t ht i
  let H := rescale G (fun j => (C j)⁻¹)
  have hH := rescale_smooth hG (fun j => (C j)⁻¹)
  have hunit : ∀ j : Fin 3, WeightedBound U s (m + e.order) 1 (H j.succ) := by
    intro j
    have h := (hHb j).const_smul hU.uniqueDiffOn (hG j.succ).contDiffOn (C j)⁻¹
    simpa only [H, rescale_succ, abs_of_pos (inv_pos.mpr (hC j)),
      inv_mul_cancel₀ (ne_of_gt (hC j))] using h
  have hnorm := hb H s hs hs1 hH hGK hGb hunit t ht i
  let W : ℝ := C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)
  have hW : 0 < W := by
    have h₀ := hC 0
    have h₁ := hC 1
    have h₂ := hC 2
    dsimp only [W]
    split_ifs <;> positivity
  have heval : (fun p => (e.variations i).eval G (p, t)) =
      (fun p => W • (e.variations i).eval H (p, t)) := by
    funext p
    have hr := rescale_inverse G C (fun j => ne_of_gt (hC j))
    have hv := e.variations_rescale hH C (p, t) i
    rw [hr] at hv
    exact hv
  rw [heval]
  have hsmooth := MixedExpression.parameter_smooth hH
    (fun p hp => hKO (hGK hp)) (e := e.variations i) (e.variations_smoothCoeffs hO he i) t
  have h := hnorm.const_smul hU.uniqueDiffOn hsmooth W
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [abs_of_pos hW]
  ring

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_RealPolynomialVariationBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds for arbitrary real variations at the short scale. These are the
nonoscillatory estimates used for mixed terms and the Taylor remainder. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates MixedExpression

theorem compact_real_variation_bound {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Fin 4 → Base → Space) (s ε : ℝ) (C : Fin 3 → ℝ),
      0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → (∀ j, 0 < C j) →
      (∀ j, ContDiff ℝ ∞ (G j)) → Set.MapsTo (lowJet (G 0)) U Q →
      WeightedBound U s (m + order P) B (lowJet (G 0)) →
      (∀ j : Fin 3, WeightedBound U s (m + order P) (C j) (G j.succ)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m
          (D * ε * (C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)) / s ^ loss P)
          (realVariation P ε G i t) := by
  have hex (l : Fin n) := (P l).compact_multilinear_variation_bound hU hO hQ hQO (hP l) m B hB
  choose D hD hd using hex
  refine ⟨∑ l, D l, Finset.sum_nonneg (fun l _ => hD l), ?_⟩
  intro G s ε C hs hs1 hε hε1 hC hG hGQ hGb hHb t ht i
  let W := C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)
  have hW : 0 ≤ W := by
    have h0 := (hC 0).le
    have h1 := (hC 1).le
    have h2 := (hC 2).le
    dsimp only [W]
    split_ifs <;> positivity
  have hv (l : Fin n) : WeightedBound U s m (D l * ε * W / s ^ loss P)
      (fun p => ε ^ (l.val + 1) * ((P l).variations i).eval G (p,t)) := by
    have hDl := hD l
    have ho : (P l).order ≤ order P := Finset.le_sup (f := fun k => (P k).order) (Finset.mem_univ l)
    have hh := hd l G s C hs hs1 hC hG hGQ
      (hGb.mono_order (Nat.add_le_add_left ho m))
      (fun j => (hHb j).mono_order (Nat.add_le_add_left ho m)) t ht i
    have hsmall := hh.mono_const (div_le_div_of_nonneg_left (mul_nonneg (hD l) hW) (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1
        (Finset.le_sup (f := fun k => (P k).loss + 6) (Finset.mem_univ l))))
    have hsm := MixedExpression.parameter_smooth hG (fun p hp => hQO (hGQ hp))
      (e := (P l).variations i) ((P l).variations_smoothCoeffs hO (hP l) i) t
    have hscaled := hsmall.const_smul hU.uniqueDiffOn hsm (ε ^ (l.val + 1))
    apply hscaled.mono_const
    rw [abs_of_nonneg (pow_nonneg hε _)]
    have he : ε ^ (l.val + 1) ≤ ε := by
      simpa only [pow_one] using pow_le_pow_of_le_one hε hε1 (show 1 ≤ l.val + 1 by omega)
    calc
      _ ≤ ε * (D l * W / s ^ loss P) := mul_le_mul_of_nonneg_right he (by positivity)
      _ = _ := by ring
  have hh := WeightedBound.finset_sum hU.uniqueDiffOn hs.le Finset.univ
    (fun l => D l * ε * W / s ^ loss P)
    (fun l p => ε ^ (l.val + 1) * ((P l).variations i).eval G (p,t))
    (fun l _ => contDiffOn_const.mul (MixedExpression.parameter_smooth hG (fun p hp => hQO (hGQ hp))
      (e := (P l).variations i) ((P l).variations_smoothCoeffs hO (hP l) i) t))
    (fun l _ => hv l)
  change WeightedBound U s m ((∑ l, D l) * ε * W / s ^ loss P)
    (fun p => ∑ l, ε ^ (l.val + 1) * ((P l).variations i).eval G (p,t))
  simpa only [← Finset.sum_div, ← Finset.sum_mul] using hh

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_RealPolynomialQuadraticBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bilinear bounds for the mixed polynomial contribution of the free and
forced displacements. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates MixedExpression

lemma pairFamily_smooth {G H K : Base → Space} (hG : ContDiff ℝ ∞ G)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) :
    ∀ i, ContDiff ℝ ∞ (![G,H,K,0] i) := by
  intro i
  fin_cases i
  · exact hG
  · exact hH
  · exact hK
  · exact contDiff_const

lemma realVariation_smooth {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} {O : Set LowJet} (hO : IsOpen O) (hP : ∀ l, (P l).SmoothCoeffs O)
    {G : Fin 4 → Base → Space} (hG : ∀ j, ContDiff ℝ ∞ (G j))
    (hQ : Set.MapsTo (lowJet (G 0)) U O) (ε : ℝ) (i : Fin 3) (t : ℝ) :
    ContDiffOn ℝ ∞ (realVariation P ε G i t) U :=
  ContDiffOn.sum fun l _ => contDiffOn_const.mul
    (MixedExpression.parameter_smooth hG hQ ((P l).variations_smoothCoeffs hO (hP l) i) t)

theorem quadraticCross_bound {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G H K : Base → Space) (s ε C D : ℝ),
      0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C → 0 < D →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ H → ContDiff ℝ ∞ K →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B (lowJet G) →
      WeightedBound U s (m + order P) C H → WeightedBound U s (m + order P) D K →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (E * ε * C * D / s ^ loss P) (quadraticCross P ε G H K t) := by
  obtain ⟨E,hE,he⟩ := compact_real_variation_bound hU hO hQ hQO P hP m B hB
  refine ⟨E,hE,?_⟩
  intro G H K s ε C D hs hs1 hε hε1 hC hD hG hH hK hGQ hGb hHb hKb t ht
  have hh (X Y : Base → Space) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
      (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
      (hbX : WeightedBound U s (m + order P) A X)
      (hbY : WeightedBound U s (m + order P) B Y) :
      WeightedBound U s m (E * ε * A * B / s ^ loss P) (realVariation P ε ![G,X,Y,0] 1 t) := by
    have hb : ∀ j : Fin 3, WeightedBound U s (m + order P) (![A,B,1] j) (![G,X,Y,0] j.succ) := by
      intro j
      fin_cases j
      · exact hbX
      · exact hbY
      · exact (weightedBound_zero U s (m + order P)).mono_const zero_le_one
    have hx := he ![G,X,Y,0] s ε ![A,B,1] hs hs1 hε hε1
      (fun j => by fin_cases j; exact hA; exact hB; norm_num)
      (pairFamily_smooth hG hX hY) hGQ hGb hb t ht 1
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, show (1 : Fin 3) ≤ 1 by decide,
      show ¬ (2 : Fin 3) ≤ 1 by decide, ↓reduceIte, mul_one, mul_assoc] using hx
  have hsHK := realVariation_smooth hO hP (pairFamily_smooth hG hH hK)
    (fun _ hp => hQO (hGQ hp)) ε 1 t
  have hsKH := realVariation_smooth hO hP (pairFamily_smooth hG hK hH)
    (fun _ hp => hQO (hGQ hp)) ε 1 t
  have hb := (hh H K C D hC hD hH hK hHb hKb).add hU.uniqueDiffOn hs.le hsHK hsKH
    (hh K H D C hD hC hK hH hKb hHb)
  have hf := hb.const_smul hU.uniqueDiffOn (hsHK.add hsKH) (1 / 2 : ℝ)
  change WeightedBound U s m _ (quadraticCross P ε G H K t) at hf
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorRealVariationBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common tensor bounds for the actual mixed quadratic term and cubic
Taylor remainder. The exponent does not depend on the correction depth. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma tensorQuadraticCross_smooth {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    {G H K : Base → Space} (hG : ContDiff ℝ ∞ G)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (ε t : ℝ) :
    ContDiff ℝ ∞ (tensorQuadraticCross P ε G H K t) := by
  apply contDiff_pi.mpr
  intro k
  apply contDiffOn_univ.mp
  exact contDiffOn_const.mul
    ((realVariation_smooth isOpen_univ (hP k) (pairFamily_smooth hG hH hK)
      (fun _ _ => Set.mem_univ _) ε 1 t).add
    (realVariation_smooth isOpen_univ (hP k) (pairFamily_smooth hG hK hH)
      (fun _ _ => Set.mem_univ _) ε 1 t))

theorem tensorQuadraticCross_bound {n : ℕ} {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G H K : Base → Space) (s ε C D : ℝ),
      0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C → 0 < D →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ H → ContDiff ℝ ∞ K →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + tensorOrder P) B (lowJet G) →
      WeightedBound U s (m + tensorOrder P) C H →
      WeightedBound U s (m + tensorOrder P) D K → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (E * ε * C * D / s ^ tensorLoss P)
          (tensorQuadraticCross P ε G H K t) := by
  have hex (k : Fin 3) := quadraticCross_bound hU isOpen_univ hQ (Set.subset_univ Q)
    (P k) (hP k) m B hB
  choose E hE he using hex
  refine ⟨∑ k, E k, Finset.sum_nonneg (fun k _ => hE k), ?_⟩
  intro G H K s ε C D hs hs1 hε hε1 hC hD hG hH hK hGQ hGb hHb hKb t ht
  have hsum : 0 ≤ ∑ k, E k := Finset.sum_nonneg (fun k _ => hE k)
  apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
  · exact contDiffOn_pi.mp (tensorQuadraticCross_smooth hP hG hH hK ε t).contDiffOn
  · intro k
    have hEk := hE k
    have ho : order (P k) ≤ tensorOrder P :=
      Finset.le_sup (f := fun j => order (P j)) (Finset.mem_univ k)
    have hl : loss (P k) ≤ tensorLoss P :=
      Finset.le_sup (f := fun j => loss (P j)) (Finset.mem_univ k)
    have hb := he k G H K s ε C D hs hs1 hε hε1 hC hD hG hH hK hGQ
      (hGb.mono_order (Nat.add_le_add_left ho m))
      (hHb.mono_order (Nat.add_le_add_left ho m)) (hKb.mono_order (Nat.add_le_add_left ho m)) t ht
    apply hb.mono_const
    calc
      _ ≤ E k * ε * C * D / s ^ tensorLoss P :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hs _)
          (pow_le_pow_of_le_one hs.le hs1 hl)
      _ ≤ _ := by
        gcongr
        exact Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ k)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateNonlinearBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder_emptyMetricPolynomial _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate realizations of the actual bilinear and cubic polynomial
terms in the nonlinear increment identity. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma coordinateQuadraticPolynomial_eq_cross {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (X : RealModes.RField 4) (t : ℝ) :
    coordinateQuadraticPolynomial P ε G X t = fun p => (1 / 2 : ℝ) •
      tensorQuadraticCross P ε G (X ∘ planeCoordinateIsometry) (X ∘ planeCoordinateIsometry) t
        (planeCoordinateIsometry.symm p) := by
  funext p k
  simp only [coordinateQuadraticPolynomial, tensorQuadraticCross, quadraticCross,
    realVariation, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_add, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma coordinateQuadraticInteraction_eq_cross {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (X Y : RealModes.RField 4) :
    coordinateQuadraticInteraction P ε G X Y = fun p =>
      (RealModes.realLinearizedTensor X Y p + RealModes.realMetricTensor Y p) +
      tensorQuadraticCross P ε G (X ∘ planeCoordinateIsometry) (Y ∘ planeCoordinateIsometry) 0
        (planeCoordinateIsometry.symm p) + coordinateQuadraticPolynomial P ε G Y 0 p := by
  funext p k
  simp only [coordinateQuadraticInteraction, tensorQuadraticCross, quadraticCross,
    realVariation, Pi.add_apply]
  congr 1
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem coordinateCross_bound {n : ℕ} {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (X Y : RealModes.RField 4)
      (s ε C D : ℝ), 0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C → 0 < D →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ X → ContDiff ℝ ∞ Y →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + tensorOrder P) B (lowJet G) →
      WeightedBound Set.univ s (m + tensorOrder P) C X →
      WeightedBound Set.univ s (m + tensorOrder P) D Y →
        WeightedBound (planeCoordinateIsometry.symm ⁻¹' U) s m (E * ε * C * D / s ^ tensorLoss P)
          (tensorQuadraticCross P ε G (X ∘ planeCoordinateIsometry)
            (Y ∘ planeCoordinateIsometry) 0 ∘ planeCoordinateIsometry.symm) := by
  obtain ⟨E,hE,he⟩ := tensorQuadraticCross_bound hU hQ P hP m B hB
  refine ⟨E,hE,?_⟩
  intro G X Y s ε C D hs hs1 hε hε1 hC hD hG hX hY hGQ hGb hXb hYb
  have hx := weightedBound_comp_isometry planeCoordinateIsometry hX hXb
  have hy := weightedBound_comp_isometry planeCoordinateIsometry hY hYb
  have hb := he G (X ∘ planeCoordinateIsometry) (Y ∘ planeCoordinateIsometry)
    s ε C D hs hs1 hε hε1 hC hD hG (hX.comp planeCoordinateIsometry.contDiff)
    (hY.comp planeCoordinateIsometry.contDiff) hGQ hGb
    (fun j hj p hp => by
      simpa only [iteratedFDerivWithin_of_isOpen j hU hp, iteratedFDerivWithin_univ]
        using hx j hj p (Set.mem_univ p))
    (fun j hj p hp => by
      simpa only [iteratedFDerivWithin_of_isOpen j hU hp, iteratedFDerivWithin_univ]
        using hy j hj p (Set.mem_univ p)) 0 (by constructor <;> norm_num)
  exact weightedBound_comp_isometry_on planeCoordinateIsometry.symm hU
    (tensorQuadraticCross_smooth hP hG (hX.comp planeCoordinateIsometry.contDiff)
      (hY.comp planeCoordinateIsometry.contDiff) ε 0) hb

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialNonlinearScales
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smallness hypotheses convert the polynomial mixed and cubic terms
to the common delta-cubed/wavelength error scale. -/
noncomputable section
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma polynomial_mixed_scale {E ε A B δ τ : ℝ} {p : ℕ}
    (hE : 0 ≤ E) (_hε : 0 ≤ ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hsmall : ε / τ ^ p ≤ 1) :
    E * ε * (A * δ * τ) * (B * δ ^ 2) / τ ^ p ≤ E * A * B * (δ ^ 3 / τ) := by
  have hτ2 : τ ^ 2 ≤ 1 := pow_le_one₀ hτ.le hτ1
  calc
    _ = (E * A * B * (δ ^ 3 / τ)) * ((ε / τ ^ p) * τ ^ 2) := by field_simp
    _ ≤ (E * A * B * (δ ^ 3 / τ)) * 1 := by gcongr; exact (mul_le_of_le_one_left (sq_nonneg τ) hsmall).trans hτ2
    _ = _ := mul_one _

lemma polynomial_self_scale {E ε B δ τ : ℝ} {p : ℕ}
    (hE : 0 ≤ E) (_hε : 0 ≤ ε) (_hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδτ : δ ≤ τ) (hsmall : ε / τ ^ p ≤ 1) :
    E * ε * (B * δ ^ 2) * (B * δ ^ 2) / τ ^ p ≤ E * B ^ 2 * (δ ^ 3 / τ) := by
  have hδ1 : δ ≤ 1 := hδτ.trans hτ1
  have hdt : δ * τ ≤ 1 := (mul_le_of_le_one_left hτ.le hδ1).trans hτ1
  calc
    _ = (E * B ^ 2 * (δ ^ 3 / τ)) * ((ε / τ ^ p) * (δ * τ)) := by field_simp
    _ ≤ (E * B ^ 2 * (δ ^ 3 / τ)) * 1 := by gcongr; exact (mul_le_of_le_one_left (mul_nonneg hδ hτ.le) hsmall).trans hdt
    _ = _ := mul_one _

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScaledNonlinearBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mixed and cubic nonlinear errors at the scales of the small
increment construction. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma coordinateQuadraticPolynomial_smooth {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ) {G : Base → Space}
    {X : RealModes.RField 4} (hG : ContDiff ℝ ∞ G) (hX : ContDiff ℝ ∞ X) (ε t : ℝ) :
    ContDiff ℝ ∞ (coordinateQuadraticPolynomial P ε G X t) := by
  rw [coordinateQuadraticPolynomial_eq_cross]
  exact ((tensorQuadraticCross_smooth hP hG (hX.comp planeCoordinateIsometry.contDiff)
    (hX.comp planeCoordinateIsometry.contDiff) ε t).comp
    planeCoordinateIsometry.symm.contDiff).const_smul (1 / 2 : ℝ)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialInteractionBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder_emptyMetricPolynomial _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only the polynomial part of the mixed free/forced quadratic error. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma coordinatePolynomialInteraction_smooth {n : ℕ}
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    {G : Base → Space} {X Y : RealModes.RField 4}
    (hG : ContDiff ℝ ∞ G) (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) (ε : ℝ) :
    ContDiff ℝ ∞ (coordinatePolynomialInteraction P ε G X Y) :=
  ((tensorQuadraticCross_smooth hP hG (hX.comp planeCoordinateIsometry.contDiff)
    (hY.comp planeCoordinateIsometry.contDiff) ε 0).comp planeCoordinateIsometry.symm.contDiff).add
    (coordinateQuadraticPolynomial_smooth hP hG hY ε 0)

lemma coordinate_quadratic_add {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {X Y : RealModes.RField 4} (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) :
    coordinateQuadraticPolynomial P ε G (X+Y) 0 =
      coordinateQuadraticPolynomial P ε G X 0+coordinatePolynomialInteraction P ε G X Y := by
  have hh := coordinateFullQuadratic_add P ε G hX hY
  funext x k
  have he := congrArg (fun f => f x k) hh
  have hm := congrFun (RealModes.realMetricTensor_add
    (hX.differentiable (by simp) x) (hY.differentiable (by simp) x)) k
  have hc := congrArg (fun f => f x k) (coordinateQuadraticInteraction_eq_cross P ε G X Y)
  change RealModes.realMetricTensor (X+Y) x k+_ =
    (RealModes.realMetricTensor X x k+_)+coordinateQuadraticInteraction P ε G X Y x k at he
  change coordinateQuadraticPolynomial P ε G (X+Y) 0 x k =
    coordinateQuadraticPolynomial P ε G X 0 x k+
      (tensorQuadraticCross P ε G (X ∘ planeCoordinateIsometry) (Y ∘ planeCoordinateIsometry) 0
        (planeCoordinateIsometry.symm x) k+coordinateQuadraticPolynomial P ε G Y 0 x k)
  simp only [Pi.add_apply] at hm hc
  change RealModes.realMetricTensor (X+Y) x k =
    RealModes.realMetricTensor X x k+RealModes.realLinearizedTensor X Y x k+
      RealModes.realMetricTensor Y x k at hm
  linarith only [he,hm,hc]

theorem scaled_polynomial_interaction_bound {n : ℕ} {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    (m : ℕ) (B₀ : ℝ) (hB₀ : 1 ≤ B₀) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (X Y : RealModes.RField 4)
      (τ ε δ A B : ℝ), 0 < τ → τ ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < δ → δ ≤ τ →
      0 < A → 0 < B → ε/τ^tensorLoss P ≤ 1 →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ X → ContDiff ℝ ∞ Y →
      Set.MapsTo (lowJet G) U Q → WeightedBound U τ (m+tensorOrder P) B₀ (lowJet G) →
      WeightedBound Set.univ τ (m+tensorOrder P+1) (A*δ*τ) X →
      WeightedBound Set.univ τ (m+tensorOrder P+1) (B*δ^2) Y →
      WeightedBound (planeCoordinateIsometry.symm ⁻¹' U) τ m
        (E*(A*B+B^2)*(δ^3/τ)) (coordinatePolynomialInteraction P ε G X Y) := by
  obtain ⟨E,hE,he⟩ := coordinateCross_bound hU hQ P hP m B₀ hB₀
  refine ⟨E,hE,?_⟩
  intro G X Y τ ε δ A B hτ hτ1 hε hε1 hδ hδτ hA hB hsmall hG hX hY hGQ hGb hXb hYb
  let V := planeCoordinateIsometry.symm ⁻¹' U
  have hV : IsOpen V := hU.preimage planeCoordinateIsometry.symm.continuous
  have hX0 := hXb.mono_order (show m + tensorOrder P ≤ m + tensorOrder P + 1 by omega)
  have hY0 := hYb.mono_order (show m + tensorOrder P ≤ m + tensorOrder P + 1 by omega)
  have hc := he G X Y τ ε (A * δ * τ) (B * δ ^ 2) hτ hτ1 hε hε1
    (by positivity) (by positivity) hG hX hY hGQ hGb hX0 hY0
  have hcc := hc.mono_const (polynomial_mixed_scale hE hε hA.le hB.le hδ.le hτ hτ1 hsmall)
  have hy := he G Y Y τ ε (B * δ ^ 2) (B * δ ^ 2) hτ hτ1 hε hε1
    (by positivity) (by positivity) hG hY hY hGQ hGb hY0 hY0
  have hyy := hy.mono_const (polynomial_self_scale hE hε hB.le hδ.le hτ hτ1 hδτ hsmall)
  have hsYY : ContDiffOn ℝ ∞ (tensorQuadraticCross P ε G (Y ∘ planeCoordinateIsometry)
      (Y ∘ planeCoordinateIsometry) 0 ∘ planeCoordinateIsometry.symm) V := ((tensorQuadraticCross_smooth hP hG (hY.comp planeCoordinateIsometry.contDiff)
    (hY.comp planeCoordinateIsometry.contDiff) ε 0).comp planeCoordinateIsometry.symm.contDiff).contDiffOn
  have hyhalf := hyy.const_smul hV.uniqueDiffOn hsYY (1 / 2 : ℝ)
  have hys : WeightedBound V τ m (E * B ^ 2 * (δ ^ 3 / τ))
      (coordinateQuadraticPolynomial P ε G Y 0) := by
    rw [coordinateQuadraticPolynomial_eq_cross]
    apply hyhalf.mono_const
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_of_le_one_left (by positivity) (by norm_num)
  have hscross : ContDiffOn ℝ ∞ (tensorQuadraticCross P ε G (X ∘ planeCoordinateIsometry)
      (Y ∘ planeCoordinateIsometry) 0 ∘ planeCoordinateIsometry.symm) V :=
    ((tensorQuadraticCross_smooth hP hG (hX.comp planeCoordinateIsometry.contDiff)
      (hY.comp planeCoordinateIsometry.contDiff) ε 0).comp planeCoordinateIsometry.symm.contDiff).contDiffOn
  have hadd := hcc.add hV.uniqueDiffOn hτ.le hscross
    (coordinateQuadraticPolynomial_smooth hP hG hY ε 0).contDiffOn hys
  convert hadd using 1 <;> first | rfl | ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialInteractionBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restored polynomial value has one fixed finite loss. Compact local
jet ranges suffice: a fixed cutoff removes the irrelevant values away from
the outer atlas supports before applying the restoration estimate. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasInteractionFiberNormed_r0002d1_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasInteractionFiberSpace_r0002d1_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasInteractionDualAdd_r0002d1_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasInteractionDualSmul_r0002d1_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)




local instance atlasInteractionSectionNormed_r0002d1_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasInteractionSectionSpace_r0002d1_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma atlasPolynomialQuadratic_difference {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression) (ε : ℝ)
    (F X Y : M → Space) (hX : ContMDiff planeModel spaceModel ∞ X)
    (hY : ContMDiff planeModel spaceModel ∞ Y) :
    A.atlasPolynomialQuadratic P ε F (X+Y)-A.atlasPolynomialQuadratic P ε F X =
      A.tensorPlaneRestore (fun i => coordinatePolynomialInteraction (P i) ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)
        (A.jetChartMap i Y ∘ planeCoordinateIsometry.symm)) := by
  unfold atlasPolynomialQuadratic
  rw [← A.tensorPlaneRestore_sub]
  congr 1
  funext i
  have he : A.jetChartMap i (X+Y) ∘ planeCoordinateIsometry.symm =
      (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)+
        (A.jetChartMap i Y ∘ planeCoordinateIsometry.symm) := by
    rw [A.jetChartMap_add]
    rfl
  simp only [Pi.sub_apply,he,coordinate_quadratic_add (P i) ε (A.jetChartMap i F)
    ((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff)
    ((A.jetChartMap_smooth i hY).comp planeCoordinateIsometry.symm.contDiff),add_sub_cancel_left]

/-- The mixed polynomial error is cubic in the correction amplitude after
using the fixed loss condition. -/
theorem atlas_polynomial_interaction_bound {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ U i)
    (Q : A.centers → Set LowJet) (hQ : ∀ i, IsCompact (Q i))
    (m : ℕ) (B C D : A.centers → ℝ) (hB : ∀ i, 1 ≤ B i)
    (hC : ∀ i, 0 < C i) (hD : ∀ i, 0 < D i) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (F X Y : M → Space),
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ X →
      ContMDiff planeModel spaceModel ∞ Y →
      ∀ τ ε δ : ℝ, 0 < τ → τ ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < δ → δ ≤ τ →
      (∀ i, ε/τ^tensorLoss (P i) ≤ 1) →
      (∀ i, MapsTo (lowJet (A.jetChartMap i F)) (U i) (Q i)) →
      (∀ i, WeightedEstimates.WeightedBound (U i) τ (m+tensorOrder (P i)) (B i)
        (lowJet (A.jetChartMap i F))) →
      (∀ i, WeightedEstimates.WeightedBound univ τ (m+tensorOrder (P i)+1)
        (C i*δ*τ) (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)) →
      (∀ i, WeightedEstimates.WeightedBound univ τ (m+tensorOrder (P i)+1)
        (D i*δ^2) (A.jetChartMap i Y ∘ planeCoordinateIsometry.symm)) →
      A.TensorWeightedBound τ m (E*(δ^3/τ))
        (A.atlasPolynomialQuadratic P ε F (X+Y)-A.atlasPolynomialQuadratic P ε F X) := by
  classical
  choose E hE he using fun i : A.centers => scaled_polynomial_interaction_bound (hU i) (hQ i)
    (P i) (hP i) m (B i) (hB i)
  obtain ⟨D₀,hD₀,hd⟩ := A.tensorPlaneRestore_bound_on_outer U hU houter m
  let S := ∑ i : A.centers, E i*(C i*D i+(D i)^2)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => mul_nonneg (hE i)
    (add_nonneg (mul_nonneg (hC i).le (hD i).le) (sq_nonneg _)))
  refine ⟨D₀*S,mul_nonneg hD₀ hS,?_⟩
  intro F X Y hF hX hY τ ε δ hτ hτ1 hε hε1 hδ hδτ hsmall hGQ hGb hXb hYb
  have hlocal (i : A.centers) := he i (A.jetChartMap i F)
    (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)
    (A.jetChartMap i Y ∘ planeCoordinateIsometry.symm) τ ε δ (C i) (D i)
    hτ hτ1 hε hε1 hδ hδτ (hC i) (hD i) (hsmall i) (A.jetChartMap_smooth i hF)
    ((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff)
    ((A.jetChartMap_smooth i hY).comp planeCoordinateIsometry.symm.contDiff)
    (hGQ i) (hGb i) (hXb i) (hYb i)
  have hb (i : A.centers) : WeightedEstimates.WeightedBound
      (planeCoordinateIsometry.symm ⁻¹' U i) τ m (S*(δ^3/τ))
      (coordinatePolynomialInteraction (P i) ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)
        (A.jetChartMap i Y ∘ planeCoordinateIsometry.symm)) :=
    (hlocal i).mono_const (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => mul_nonneg (hE j)
        (add_nonneg (mul_nonneg (hC j).le (hD j).le) (sq_nonneg _))) (Finset.mem_univ i))
      (div_nonneg (pow_nonneg hδ.le _) hτ.le))
  have hh := hd _ (fun i => coordinatePolynomialInteraction_smooth (hP i)
    (A.jetChartMap_smooth i hF)
    ((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff)
    ((A.jetChartMap_smooth i hY).comp planeCoordinateIsometry.symm.contDiff) ε)
    τ (S*(δ^3/τ)) hτ hτ1 (mul_nonneg hS (div_nonneg (pow_nonneg hδ.le _) hτ.le)) hb
  rw [A.atlasPolynomialQuadratic_difference P ε F X Y hX hY]
  simpa only [mul_assoc] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetSegment
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact low-jet margins and uniform bounds along the actual Taylor
segment, obtained from the second derivatives of the displacement. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma lowJet_segment_bound {U : Set Base} (hU : IsOpen U)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {s B C : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hGb : WeightedBound U s m B (lowJet G))
    (hHb : WeightedBound U s (m + 2) C H) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    WeightedBound U s m (B + C / s ^ 2) (lowJet (fun p => G p + t • H p)) := by
  have hv := weighted_variationLowJet hU hH hs hs1 hC m hHb
  have hscl := hv.const_smul hU.uniqueDiffOn (variationLowJet_smooth hH).contDiffOn t
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hb := hscl.mono_const (mul_le_of_le_one_left (div_nonneg hC (sq_nonneg s)) ht1)
  have ha := hGb.add hU.uniqueDiffOn hs.le (lowJet_smooth hG).contDiffOn
    ((variationLowJet_smooth hH).const_smul t).contDiffOn hb
  exact ha.congr (fun p _ => lowJet_affine hG hH t p)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetSegmentEnlargement
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed compact enlargement contains the jets of every small correction segment. -/
noncomputable section
open Set
open scoped ContDiff Pointwise
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma lowJet_segment_mem_add_closedBall {U : Set Base} (hU : IsOpen U)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {K : Set LowJet} (hmap : MapsTo (lowJet G) U K)
    {τ δ C : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 ≤ δ) (hδτ : δ ≤ τ) (hC : 0 ≤ C)
    (hHb : WeightedBound U τ 2 (C*δ*τ) H) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    MapsTo (lowJet (fun x => G x+t • H x)) U (K+Metric.closedBall 0 C) := by
  have hc : (C*δ*τ)/τ^2 ≤ C := by
    apply (div_le_iff₀ (sq_pos_of_pos hτ)).2
    nlinarith only [mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hδτ hτ.le) hC]
  have hv := weighted_variationLowJet hU hH hτ hτ1
    (mul_nonneg (mul_nonneg hC hδ) hτ.le) 0 hHb
  intro x hx
  rw [lowJet_affine hG hH t x]
  apply Set.add_mem_add (hmap hx)
  rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs]
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  exact (mul_le_of_le_one_left (norm_nonneg _) ht1).trans ((hv.norm_le hx).trans hc)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactLocalBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform slow-scale bounds on a relatively compact coordinate domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_local_weighted_bound {V Ω K : Set E}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hVK : V ⊆ K) (hKΩ : K ⊆ Ω) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f Ω) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 → WeightedBound V s m C f := by
  obtain ⟨C,hC,hb⟩ := compact_coefficient_bound hΩ.uniqueDiffOn hK hKΩ hf m
  refine ⟨C,hC,?_⟩
  intro s hs hs1 j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hV hx]
  have hh := hb j hj x (hVK hx)
  rw [iteratedFDerivWithin_of_isOpen j hΩ (hKΩ (hVK hx))] at hh
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs hs1)).trans hh

end ClosedSurfaceR4.WeightedEstimates

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

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetPrefixBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual positional two-jet on a fixed bounded domain. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem directional_of_prefix {U : Set E} (hU : IsOpen U)
    {f : E → V} (hf : ContDiff ℝ ∞ f) {s C : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m+1, WeightedBound U 1 j (C/s^(j-1)) f)
    (v : E) (hv : ‖v‖ ≤ 1) :
    WeightedBound U s m C (fun x => fderiv ℝ f x v) := by
  intro j hj x hx
  have hh := ((hb (j+1) (by omega)).directional hU zero_lt_one hf.contDiffOn v)
    j le_rfl x hx
  simp only [one_pow,one_mul,div_one,Nat.add_sub_cancel] at hh
  calc
    _ ≤ s^j*(‖v‖*(C/s^j)) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = ‖v‖*C := by field_simp
    _ ≤ C := mul_le_of_le_one_left hC hv

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem jet_lowWord_bound {U : Set Base} (hU : IsOpen U)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) {s C : ℝ} {m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) G)
    (w : Fin 7) (a : Fin 4) :
    WeightedBound U s m C (fun p => jet G (lowWord w) a p) := by
  let f : Base → ℝ := fun p => G p a
  have hf : ContDiff ℝ ∞ f := contDiff_pi.mp hG a
  have hp (j : ℕ) (hj : j ≤ m+2) : WeightedBound U 1 j (C/s^(j-2)) f :=
    (hb j hj).component hU.uniqueDiffOn zero_le_one
      (div_nonneg hC (pow_nonneg hs.le _)) hG.contDiffOn a
  have hzero : WeightedBound U s m C f := by
    intro j hj x hx
    have hh := hp j (by omega) j le_rfl x hx
    simp only [one_pow,one_mul] at hh
    calc
      _ ≤ s^j*(C/s^(j-2)) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
      _ ≤ s^j*(C/s^j) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hC (pow_pos hs _)
          (pow_le_pow_of_le_one hs.le hs1 (Nat.sub_le _ _))) (pow_nonneg hs.le _)
      _ = C := by field_simp
  have hunit (v : Fin 2) : ‖coordinateVector v‖ = 1 := by
    simp only [coordinateVector,Pi.norm_single,norm_one]
  have hfirst (v : Fin 2) (j : ℕ) (hj : j ≤ m+1) :
      WeightedBound U 1 j (C/s^(j-1)) (fun x => fderiv ℝ f x (coordinateVector v)) := by
    have hh := (hp (j+1) (by omega)).directional hU zero_lt_one hf.contDiffOn (coordinateVector v)
    have he : j+1-2 = j-1 := by omega
    simpa only [hunit,one_mul,div_one,he] using hh
  have hone (v : Fin 2) :
      WeightedBound U s m C (fun x => fderiv ℝ f x (coordinateVector v)) := by
    apply directional_of_prefix hU hf hs hC _ (coordinateVector v) (hunit v).le
    intro j hj
    apply (hp j (by omega)).mono_const
    exact div_le_div_of_nonneg_left hC (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 (by omega))
  have htwo (v v' : Fin 2) : WeightedBound U s m C
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector v')) x (coordinateVector v)) :=
    directional_of_prefix hU
      ((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)
      hs hC (hfirst v') (coordinateVector v) (hunit v).le
  fin_cases w
  · exact hzero
  · exact hone 0
  · exact hone 1
  · exact htwo 0 0
  · exact htwo 0 1
  · exact htwo 1 0
  · exact htwo 1 1

theorem bounded_lowJet_prefix {U : Set Base} (hU : IsOpen U)
    (K : Compacts Base) (hUK : U ⊆ K) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (G : Base → Space), ContDiff ℝ ∞ G → ∀ s C : ℝ,
      0 < s → s ≤ 1 → 0 ≤ C →
      (∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) G) →
      WeightedBound U s m (D+C) (lowJet G) := by
  obtain ⟨D,hD,hd⟩ := compact_local_weighted_bound hU isOpen_univ K.isCompact hUK
    (subset_univ _) (contDiff_id : ContDiff ℝ ∞ (id : Base → Base)).contDiffOn m
  refine ⟨D,hD,?_⟩
  intro G hG s C hs hs1 hC hb
  apply WeightedBound.pi hU.uniqueDiffOn hs (by linarith)
  · intro i
    exact (contDiff_pi.mp (lowJet_smooth hG) i).contDiffOn
  · intro i
    cases i with
    | inl i =>
      exact ((hd s hs.le hs1).component hU.uniqueDiffOn hs.le
        (zero_le_one.trans hD) contDiff_id.contDiffOn i).mono_const (by linarith)
    | inr i =>
      exact (jet_lowWord_bound hU hG hs hs1 hC hb i.1 i.2).mono_const (by linarith)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetCompactRange
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One compact positional-jet range for all maps in a bounded C2 family. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem bounded_lowJet_range {U : Set Base} (hU : IsOpen U)
    (K : Compacts Base) (hUK : U ⊆ K) {C : ℝ} (hC : 0 ≤ C) :
    ∃ Q : Set LowJet, IsCompact Q ∧ ∀ (G : Base → Space), ContDiff ℝ ∞ G →
      WeightedBound U 1 2 C G → MapsTo (lowJet G) U Q := by
  obtain ⟨D,_,hd⟩ := bounded_lowJet_prefix hU K hUK 0
  refine ⟨Metric.closedBall 0 (D+C),isCompact_closedBall _ _,?_⟩
  intro G hG hb p hp
  have hj := hd G hG 1 C zero_lt_one le_rfl hC (fun j hj => by
    simpa only [one_pow,div_one] using hb.mono_order (by omega : j ≤ 2))
  simpa only [Metric.mem_closedBall,dist_zero_right] using hj.norm_le hp

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AtlasJetProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact jet ranges and coefficient bounds derived from the actual atlas input norms. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlas_jet_profiles
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (KU : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hUK : ∀ i, U i ⊆ KU i)
    (R : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) :
    ∃ (Q : A.centers → Set LowJet) (B : A.centers → ℕ → ℝ),
      (∀ i, IsCompact (Q i)) ∧ (∀ i m, 1 ≤ B i m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
      ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
      (∀ m, A.ShiftedBound 2 m s (R m) G) →
      (∀ i, MapsTo (lowJet (A.jetChartMap i G)) (U i) (Q i)) ∧
      ∀ i m, WeightedEstimates.WeightedBound (U i) s m (B i m) (lowJet (A.jetChartMap i G)) := by
  classical
  choose E hE he using fun i m => A.vectorPlaneRead_prefix_bounds (V := Space) i 2 m
  let C := fun i m => ‖spaceCoordinates.toContinuousLinearMap‖ * E i m * R m
  have hC (i m) : 0 ≤ C i m := mul_nonneg
    (mul_nonneg (norm_nonneg _) (hE i m)) (hR m)
  have hpref (G : M → Space) (hG : ContMDiff planeModel spaceModel ∞ G)
      (s : ℝ≥0) (hs : 0 < (s:ℝ)) (hs1 : s ≤ 1)
      (hb : ∀ m, A.ShiftedBound 2 m s (R m) G) (i m j) (hj : j ≤ m+2) :
      WeightedEstimates.WeightedBound (U i) 1 j (C i m/(s:ℝ)^(j-2)) (A.jetChartMap i G) := by
    have hh := (he i m G s (R m) hs hs1 (hR m) hG (hb m) j (by omega)).linear
      uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i hG).contDiffOn
      spaceCoordinates.toContinuousLinearMap
    have hc := weightedBound_comp_isometry planeCoordinateIsometry
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)) hh
    have heq : (spaceCoordinates ∘ A.vectorPlaneRead i G) ∘ planeCoordinateIsometry =
        A.jetChartMap i G := by
      funext x
      have hx := congrFun (A.jetChartMap_plane i G) (planeCoordinateIsometry x)
      simpa only [Function.comp_apply,LinearIsometryEquiv.symm_apply_apply] using hx.symm
    change WeightedEstimates.WeightedBound univ 1 j _
      ((spaceCoordinates ∘ A.vectorPlaneRead i G) ∘ planeCoordinateIsometry) at hc
    rw [heq] at hc
    have hb' : WeightedEstimates.WeightedBound univ 1 j (C i m/(s:ℝ)^(j-2)) (A.jetChartMap i G) := by
      simpa only [C,mul_div_assoc,mul_assoc] using hc
    exact hb'.restrict_open (hU i)
  choose Q hQ hmaps using fun i => bounded_lowJet_range (hU i) (KU i) (hUK i) (hC i 0)
  choose D hD hd using fun i m => bounded_lowJet_prefix (hU i) (KU i) (hUK i) m
  refine ⟨Q,fun i m => D i m+C i m,hQ,fun i m => (hD i m).trans
    (le_add_of_nonneg_right (hC i m)),?_⟩
  intro G hG s hs hs1 hb
  constructor
  · intro i
    apply hmaps i _ (A.jetChartMap_smooth i hG)
    simpa only [Nat.sub_self,pow_zero,div_one] using hpref G hG s hs hs1 hb i 0 2 (by omega)
  · intro i m
    exact hd i m (A.jetChartMap i G) (A.jetChartMap_smooth i hG) s (C i m)
      hs hs1 (hC i m) (hpref G hG s hs hs1 hb i m)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialNonlinearProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder_emptyMetricPolynomial _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform nonlinear error bounds from the global norms used by the iteration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology NNReal BigOperators Pointwise
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlas_polynomial_nonlinear_profiles_oai {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (Ω : A.centers → Set JetPolynomial.Base) (hΩ : ∀ i, IsOpen (Ω i))
    (KΩ : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hΩK : ∀ i, Ω i ⊆ KΩ i)
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ Ω i)
    (R U V : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) (hU : ∀ m, 0 ≤ U m) (hV : ∀ m, 0 ≤ V m) :
    ∃ E₁ E₂ : ℕ → ℝ, (∀ m, 0 ≤ E₁ m) ∧ (∀ m, 0 ≤ E₂ m) ∧
      ∀ (G X Y : M → Space), ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel spaceModel ∞ X → ContMDiff planeModel spaceModel ∞ Y →
      ∀ (s : ℝ≥0) (τ ε δ : ℝ), 0 < τ → 0 < (s:ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → 0 < δ → δ ≤ τ →
      (∀ i, ε/τ^tensorLoss (P i) ≤ 1) →
      (∀ m, A.ShiftedBound 2 m s (R m) G) →
      (∀ m, A.WeightedBound τ m (U m*(δ*τ)) X) →
      (∀ m, A.WeightedBound τ m (V m*δ^2) Y) →
      (∀ m, A.TensorWeightedBound τ m (E₁ m*(δ^3/τ))
        (A.atlasPolynomialQuadratic P ε G (X+Y)-A.atlasPolynomialQuadratic P ε G X)) ∧
      (∀ m, A.TensorWeightedBound τ m (E₂ m*(δ^3/τ))
        (A.atlasPolynomialRemainder P ε G (X+Y))) := by
  classical
  obtain ⟨K,B,hK,hB,hjet⟩ := A.atlas_jet_profiles Ω hΩ KΩ hΩK R hR
  choose D hD hd using fun i m => A.jetPlaneRead_bound i m
  let Cx := fun i m => 1+D i m*U m
  let Cy := fun i m => 1+D i m*V m
  let C := fun i m => Cx i m+Cy i m
  have hCx (i m) : 0 < Cx i m := by
    dsimp [Cx]
    linarith [mul_nonneg (hD i m) (hU m)]
  have hCy (i m) : 0 < Cy i m := by
    dsimp [Cy]
    linarith [mul_nonneg (hD i m) (hV m)]
  have hC (i m) : 0 < C i m := add_pos (hCx i m) (hCy i m)
  let K' := fun i => K i+Metric.closedBall (0 : LowJet) (C i 2)
  have hK' (i) : IsCompact (K' i) := (hK i).add (isCompact_closedBall _ _)
  choose E₁ hE₁ he₁ using fun m => A.atlas_polynomial_interaction_bound P hP Ω hΩ houter K hK m
    (fun i => B i (m+tensorOrder (P i)))
    (fun i => Cx i (m+tensorOrder (P i)+1)) (fun i => Cy i (m+tensorOrder (P i)+1))
    (fun i => hB i _) (fun i => hCx i _) (fun i => hCy i _)
  choose E₂ hE₂ he₂ using fun m => A.atlas_polynomial_remainder_bound P hP Ω hΩ houter K' hK' m
    (fun i => B i (m+tensorOrder (P i))+C i (m+tensorOrder (P i)+2))
    (fun i => C i (m+tensorOrder (P i)))
    (fun i => (hB i _).trans (le_add_of_nonneg_right (hC i _).le)) (fun i => hC i _)
  refine ⟨E₁,E₂,hE₁,hE₂,?_⟩
  intro G X Y hG hX hY s τ ε δ hτ hs hτs hs1 hε hε1 hδ hδτ hsmall hGb hXb hYb
  have hτ1 : τ ≤ 1 := hτs.trans hs1
  have hδ2 : δ^2 ≤ δ*τ := by nlinarith
  obtain ⟨hmap,hbound⟩ := hjet G hG s hs hs1 hGb
  have hx (i m) : WeightedEstimates.WeightedBound univ τ m (Cx i m*δ*τ)
      (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) := by
    have hh := hd i m X hX τ (U m*(δ*τ)) hτ hτ1 (mul_nonneg (hU m) (mul_nonneg hδ.le hτ.le)) (hXb m)
    apply hh.mono_const
    dsimp [Cx]
    nlinarith [mul_nonneg hδ.le hτ.le]
  have hy (i m) : WeightedEstimates.WeightedBound univ τ m (Cy i m*δ^2)
      (A.jetChartMap i Y ∘ planeCoordinateIsometry.symm) := by
    have hh := hd i m Y hY τ (V m*δ^2) hτ hτ1 (mul_nonneg (hV m) (sq_nonneg δ)) (hYb m)
    apply hh.mono_const
    dsimp [Cy]
    nlinarith [sq_nonneg δ]
  have hc (i m) : WeightedEstimates.WeightedBound univ τ m (C i m*δ*τ)
      (A.jetChartMap i (X+Y) ∘ planeCoordinateIsometry.symm) := by
    have hh := (hx i m).add uniqueDiffOn_univ hτ.le
      (((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff).contDiffOn)
      (((A.jetChartMap_smooth i hY).comp planeCoordinateIsometry.symm.contDiff).contDiffOn) (hy i m)
    have he : A.jetChartMap i (X+Y) ∘ planeCoordinateIsometry.symm =
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)+(A.jetChartMap i Y ∘ planeCoordinateIsometry.symm) := by
      rw [A.jetChartMap_add]
      rfl
    rw [he]
    apply hh.mono_const
    have hh' := mul_le_mul_of_nonneg_left hδ2 (hCy i m).le
    dsimp only [C]
    nlinarith only [hh']
  have hc' (i m) : WeightedEstimates.WeightedBound (Ω i) τ m (C i m*δ*τ)
      (A.jetChartMap i (X+Y)) := by
    have hh := weightedBound_comp_isometry planeCoordinateIsometry
      ((A.jetChartMap_smooth i (hX.add hY)).comp planeCoordinateIsometry.symm.contDiff) (hc i m)
    have he : (A.jetChartMap i (X+Y) ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry =
        A.jetChartMap i (X+Y) := by
      funext x
      simp only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
    rw [he] at hh
    exact hh.restrict_open (hΩ i)
  have hseg (i t) (ht : t ∈ Icc (0:ℝ) 1) : MapsTo
      (lowJet (fun x => A.jetChartMap i G x+t • A.jetChartMap i (X+Y) x)) (Ω i) (K' i) :=
    lowJet_segment_mem_add_closedBall (hΩ i) (A.jetChartMap_smooth i hG)
      (A.jetChartMap_smooth i (hX.add hY)) (hmap i) hτ hτ1 hδ.le hδτ (hC i 2).le (hc' i 2) ht
  have hsegb (i m t) (ht : t ∈ Icc (0:ℝ) 1) : WeightedEstimates.WeightedBound (Ω i) τ m
      (B i m+C i (m+2))
      (lowJet (fun x => A.jetChartMap i G x+t • A.jetChartMap i (X+Y) x)) := by
    have hh := lowJet_segment_bound (hΩ i) (A.jetChartMap_smooth i hG)
      (A.jetChartMap_smooth i (hX.add hY)) hτ hτ1 (mul_nonneg (mul_nonneg (hC i (m+2)).le hδ.le) hτ.le)
      ((hbound i m).shrink_scale hτ.le hτs) (hc' i (m+2)) ht
    apply hh.mono_const
    apply add_le_add le_rfl
    apply (div_le_iff₀ (sq_pos_of_pos hτ)).2
    nlinarith only [mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hδτ hτ.le) (hC i (m+2)).le]
  constructor
  · intro m
    exact he₁ m G X Y hG hX hY τ ε δ hτ hτ1 hε hε1 hδ hδτ hsmall hmap
      (fun i => (hbound i _).shrink_scale hτ.le hτs) (fun i => hx i _) (fun i => hy i _)
  · intro m
    exact he₂ m G (X+Y) hG (hX.add hY) τ ε δ hτ hτ1 hε hε1 hδ hsmall hseg
      (fun i t ht => hsegb i _ t ht) (fun i => hc i _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_nonlinear_profiles_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_nonlinear_profiles_oai.{u_1}
