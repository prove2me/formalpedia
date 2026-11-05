-- Prove2me | solution 1 for OAI.SmoothLocal.HighEquation.comparison_initial_energy_zero
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:46:56.249174+00:00
-- url     : https://prove2.me/submissions/f3b8a4d5-63be-4a25-989d-229be992ad25

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators
open Filter

namespace SmoothLocal.Geometry

section Height
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {F : Coord → V} {p : Coord} {U : Set Coord}

theorem partial_contDiffOn (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (i : Fin 2) :
    ContDiffOn ℝ ∞ (coordPartial i F) U := by
  exact (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

end Height
end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace HessianCalculus

variable {f h : Coord → ℝ} {p : Coord}

theorem coordPartial_sub_at
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q - h q) p = coordPartial i f p - coordPartial i h p := by
  simp [coordPartial, fderiv_fun_sub hf hh]

end HessianCalculus

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open scoped Matrix.Norms.Elementwise
open Filter

namespace SmoothLocal.Geometry

theorem coordPartial_eq_of_eventuallyEq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f h : Coord → V} {p : Coord} (heq : f =ᶠ[𝓝 p] h) (i : Fin 2) :
    coordPartial i f p = coordPartial i h p := by
  unfold coordPartial
  rw [heq.fderiv_eq]

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
namespace LowQuotient

variable {U : Set Coord} {a b : Coord → ℝ} {p : Coord}

theorem iterated_contDiffOn (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U)
    (ds : List (Fin 2)) : ContDiffOn ℝ ∞ (iteratedCoordPartial ds a) U := by
  induction ds with
  | nil => exact ha
  | cons i ds ih => exact partial_contDiffOn ih hU i

theorem iterated_differentiableAt (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U)
    (hp : p ∈ U) (ds : List (Fin 2)) :
    DifferentiableAt ℝ (iteratedCoordPartial ds a) p :=
  ((iterated_contDiffOn ha hU ds).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)

end LowQuotient
end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

theorem boxPoint_hasDerivAt_t (t s : ℝ) :
    HasDerivAt (fun x => boxPoint x s) (Pi.single 0 (1 : ℝ) : Coord) t := by
  simpa [boxPoint] using
    ((hasDerivAt_id t).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add_const
      (s • (Pi.single 1 (1 : ℝ) : Coord))

variable {tl tr sb st : ℝ} {f g : Coord → ℝ}

variable {U : Set Coord}

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

namespace CoordinateBound

theorem iterated_sub {f h : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (ds : List (Fin 2)) {p : Coord} (hp : p ∈ U) :
    iteratedCoordPartial ds (fun x => f x - h x) p =
      iteratedCoordPartial ds f p - iteratedCoordPartial ds h p := by
  induction ds generalizing p with
  | nil => rfl
  | cons i ds ih =>
    have he : iteratedCoordPartial ds (fun x => f x - h x) =ᶠ[𝓝 p]
        (fun x => iteratedCoordPartial ds f x - iteratedCoordPartial ds h x) := by
      filter_upwards [hU.mem_nhds hp] with x hx
      exact ih hx
    change coordPartial i (iteratedCoordPartial ds (fun x => f x - h x)) p = _
    rw [coordPartial_eq_of_eventuallyEq he i]
    exact HessianCalculus.coordPartial_sub_at
      (LowQuotient.iterated_differentiableAt hf hU hp ds)
      (LowQuotient.iterated_differentiableAt hh hU hp ds) i

end CoordinateBound
end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem horizontal_partial_eq_of_slice_eq {f f0 : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hf0 : ContDiffOn ℝ ∞ f0 U) (hU : IsOpen U)
    {left right a : ℝ}
    (hline : ∀ x ∈ Ioo left right, boxPoint x a ∈ U)
    (heq : ∀ x ∈ Ioo left right, f0 (boxPoint x a) = f (boxPoint x a))
    {x : ℝ} (hx : x ∈ Ioo left right) :
    coordPartial 0 f0 (boxPoint x a) = coordPartial 0 f (boxPoint x a) := by
  have hd : HasDerivAt (fun t => f (boxPoint t a)) (coordPartial 0 f (boxPoint x a)) x :=
    ((hf.contDiffAt (hU.mem_nhds (hline x hx))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      x (boxPoint_hasDerivAt_t x a)
  have hd0 : HasDerivAt (fun t => f0 (boxPoint t a)) (coordPartial 0 f0 (boxPoint x a)) x :=
    ((hf0.contDiffAt (hU.mem_nhds (hline x hx))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      x (boxPoint_hasDerivAt_t x a)
  have hev : (fun t => f0 (boxPoint t a)) =ᶠ[𝓝 x] (fun t => f (boxPoint t a)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact heq t ht
  rw [← hd0.deriv, ← hd.deriv]
  exact hev.deriv_eq

theorem qSolutionJet_eq_of_cauchy_data {z z0 : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hz0 : ContDiffOn ℝ ∞ z0 U) (hU : IsOpen U)
    {left right a : ℝ}
    (hline : ∀ x ∈ Ioo left right, boxPoint x a ∈ U)
    (hvalue : ∀ x ∈ Ioo left right, z0 (boxPoint x a) = z (boxPoint x a))
    (hvelocity : ∀ x ∈ Ioo left right,
      coordPartial 1 z0 (boxPoint x a) = coordPartial 1 z (boxPoint x a))
    {x : ℝ} (hx : x ∈ Ioo left right) :
    qSolutionJet z0 (boxPoint x a) = qSolutionJet z (boxPoint x a) := by
  have hxfirst : ∀ x ∈ Ioo left right,
      coordPartial 0 z0 (boxPoint x a) = coordPartial 0 z (boxPoint x a) :=
    fun x hx => horizontal_partial_eq_of_slice_eq hz hz0 hU hline hvalue hx
  have hxx := horizontal_partial_eq_of_slice_eq (partial_contDiffOn hz hU 0)
    (partial_contDiffOn hz0 hU 0) hU hline hxfirst hx
  have hxy := horizontal_partial_eq_of_slice_eq (partial_contDiffOn hz hU 1)
    (partial_contDiffOn hz0 hU 1) hU hline hvelocity hx
  ext i
  fin_cases i
  · rfl
  · rfl
  · exact hxfirst x hx
  · exact hvelocity x hx
  · exact hxy
  · exact hxx

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Taylor
open SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem comparison_initial_partials_zero
    {U : Set Coord} {P z : Coord → ℝ} (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U)
    {left right a : ℝ} (hcut : ∀ x ∈ Ioo left right, boxPoint x a ∈ U)
    (hvalue : ∀ x ∈ Ioo left right, P (boxPoint x a) = z (boxPoint x a))
    (hvelocity : ∀ x ∈ Ioo left right, coordPartial 1 P (boxPoint x a) = coordPartial 1 z (boxPoint x a))
    {x : ℝ} (hx : x ∈ Ioo left right) :
    coordPartial 0 (comparisonDifference P z) (boxPoint x a) = 0 ∧
    coordPartial 1 (comparisonDifference P z) (boxPoint x a) = 0 := by
  have hj := qSolutionJet_eq_of_cauchy_data hz hP hU hcut hvalue hvelocity hx
  have hxEq : coordPartial 0 P (boxPoint x a) = coordPartial 0 z (boxPoint x a) :=
    congrArg (fun w : DarbouxState => w 2) hj
  have h0 := CoordinateBound.iterated_sub hz hP hU [0] (hcut x hx)
  have h1 := CoordinateBound.iterated_sub hz hP hU [1] (hcut x hx)
  change coordPartial 0 (comparisonDifference P z) (boxPoint x a) =
    coordPartial 0 z (boxPoint x a)-coordPartial 0 P (boxPoint x a) at h0
  change coordPartial 1 (comparisonDifference P z) (boxPoint x a) =
    coordPartial 1 z (boxPoint x a)-coordPartial 1 P (boxPoint x a) at h1
  exact ⟨by rw [h0,hxEq,sub_self],by rw [h1,hvelocity x hx,sub_self]⟩

theorem comparison_initial_energy_zero
    {U : Set Coord} {P z S : Coord → ℝ} (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U)
    {left right xl xr a : ℝ} (hlr : xl ≤ xr)
    (hcut : ∀ x ∈ Ioo left right, boxPoint x a ∈ U)
    (hvalue : ∀ x ∈ Ioo left right, P (boxPoint x a) = z (boxPoint x a))
    (hvelocity : ∀ x ∈ Ioo left right, coordPartial 1 P (boxPoint x a) = coordPartial 1 z (boxPoint x a))
    (hxl : left < xl) (hxr : xr < right) :
    (∫ x in xl..xr, energyDensity S (comparisonDifference P z) (coordinatePoint x a)) = 0 := by
  have hpoint (x : ℝ) (hx : x ∈ uIcc xl xr) :
      energyDensity S (comparisonDifference P z) (coordinatePoint x a) = 0 := by
    have hx' : x ∈ Icc xl xr := by simpa only [uIcc_of_le hlr] using hx
    have hi : x ∈ Ioo left right := ⟨hxl.trans_le hx'.1,hx'.2.trans_lt hxr⟩
    obtain ⟨h0,h1⟩ := comparison_initial_partials_zero hU hz hP hcut hvalue hvelocity hi
    have he : coordinatePoint x a = boxPoint x a := by ext i; fin_cases i <;> simp [coordinatePoint,boxPoint]
    rw [he]
    simp only [energyDensity,h0,h1,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,add_zero,zero_div]
  calc
    _ = ∫ x in xl..xr, (0 : ℝ) := intervalIntegral.integral_congr hpoint
    _ = 0 := intervalIntegral.integral_zero

end SmoothLocal.HighEquation

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.HighEquation.comparison_initial_energy_zero := @OAI.SmoothLocal.HighEquation.comparison_initial_energy_zero
