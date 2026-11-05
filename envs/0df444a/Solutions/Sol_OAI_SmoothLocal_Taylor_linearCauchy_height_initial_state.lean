-- Prove2me | solution 1 for OAI.SmoothLocal.Taylor.linearCauchy_height_initial_state
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:46:08.797195+00:00
-- url     : https://prove2.me/submissions/1e2575e3-af28-4d3e-85be-17baf2814d3d

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
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem verticalPoint_hasDerivAt (x y : ℝ) :
    HasDerivAt (fun t : ℝ => (![x, t] : Coord)) (Pi.single 1 (1 : ℝ)) y := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa using hasDerivAt_const y x
  · convert hasDerivAt_id y using 1 <;> rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem spatialStrip_isOpen {I : Set ℝ} (hI : IsOpen I) : IsOpen (spatialStrip I) :=
  hI.preimage (continuous_apply 0)

theorem point_eta (p : Coord) : (![p 0, p 1] : Coord) = p := by
  ext i
  fin_cases i <;> rfl

end SmoothLocal.Taylor

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem initialPoint_contDiff (a : ℝ) :
    ContDiff ℝ ∞ (fun x => (![x, a] : Coord)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_id
  · exact contDiff_const

end SmoothLocal.Taylor

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem linearCauchy_contDiffOn {u0 u1 : ℝ → ℝ} {I : Set ℝ}
    (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I) (a : ℝ) :
    ContDiffOn ℝ ∞ (linearCauchy a u0 u1) (spatialStrip I) :=
  (h0.comp (contDiffOn_apply ℝ ℝ 0 (spatialStrip I)) (fun _ hp => hp)).add
    ((h1.comp (contDiffOn_apply ℝ ℝ 0 (spatialStrip I)) (fun _ hp => hp)).mul
      ((contDiffOn_apply ℝ ℝ 1 (spatialStrip I)).sub contDiffOn_const))

theorem linearCauchy_value (a x : ℝ) (u0 u1 : ℝ → ℝ) :
    linearCauchy a u0 u1 ![x, a] = u0 x := by simp [linearCauchy]

theorem linearCauchy_velocity {u0 u1 : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I)
    (a : ℝ) {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 1 (linearCauchy a u0 u1) p = u1 (p 0) := by
  have hlin := linearCauchy_contDiffOn h0 h1 a
  have hd : HasFDerivAt (linearCauchy a u0 u1)
      (fderiv ℝ (linearCauchy a u0 u1) p) (![p 0, p 1] : Coord) := by
    simpa only [point_eta] using
      ((hlin.contDiffAt ((spatialStrip_isOpen hI).mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hc := hd.comp_hasDerivAt (p 1) (verticalPoint_hasDerivAt (p 0) (p 1))
  have he : (fun t => linearCauchy a u0 u1 ![p 0, t]) =
      (fun t => u0 (p 0) + u1 (p 0) * (t - a)) := rfl
  change HasDerivAt (fun t => linearCauchy a u0 u1 ![p 0, t])
    (coordPartial 1 (linearCauchy a u0 u1) p) (p 1) at hc
  rw [he] at hc
  have hf := ((hasDerivAt_id (p 1)).sub_const a).const_mul (u1 (p 0))
  have hf' := hf.const_add (u0 (p 0))
  simpa only [mul_one] using hc.unique hf'

end SmoothLocal.Taylor

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
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Weighted

theorem heightCauchyValue_contDiffOn {z : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (hz : ContDiffOn ℝ ∞ z U) (a : ℝ)
    (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U) :
    ContDiffOn ℝ ∞ (heightCauchyValue z a) I :=
  hz.comp (initialPoint_contDiff a).contDiffOn hcut

theorem heightCauchyVelocity_contDiffOn {z : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) (a : ℝ)
    (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U) :
    ContDiffOn ℝ ∞ (heightCauchyVelocity z a) I :=
  (partial_contDiffOn hz hU 1).comp (initialPoint_contDiff a).contDiffOn hcut

theorem linearCauchy_height_initial_state {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) (left right a : ℝ)
    (hcut : ∀ x ∈ Ioo left right, (![x, a] : Coord) ∈ U)
    {x : ℝ} (hx : x ∈ Ioo left right) :
    qSolutionJet (linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a)) ![x, a] =
      qSolutionJet z ![x, a] := by
  have h0 := heightCauchyValue_contDiffOn hz a hcut
  have h1 := heightCauchyVelocity_contDiffOn hz hU a hcut
  have hlin := linearCauchy_contDiffOn h0 h1 a
  let V : Set Coord := U ∩ spatialStrip (Ioo left right)
  have hV : IsOpen V := hU.inter (spatialStrip_isOpen isOpen_Ioo)
  have hzV : ContDiffOn ℝ ∞ z V := hz.mono inter_subset_left
  have hlinV : ContDiffOn ℝ ∞
      (linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a)) V :=
    hlin.mono inter_subset_right
  have hpoint (y : ℝ) : boxPoint y a = (![y, a] : Coord) := by
    ext i
    fin_cases i <;> simp [boxPoint]
  have hline : ∀ x ∈ Ioo left right, boxPoint x a ∈ V := by
    intro y hy
    rw [hpoint]
    exact ⟨hcut y hy, hy⟩
  have hval : ∀ y ∈ Ioo left right,
      linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a) (boxPoint y a) =
      z (boxPoint y a) := by
    intro y _
    rw [hpoint]
    exact linearCauchy_value a y _ _
  have hvel : ∀ y ∈ Ioo left right,
      coordPartial 1 (linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a))
        (boxPoint y a) = coordPartial 1 z (boxPoint y a) := by
    intro y hy
    rw [hpoint]
    exact linearCauchy_velocity isOpen_Ioo h0 h1 a (p := ![y, a]) hy
  have hh := qSolutionJet_eq_of_cauchy_data hzV hlinV hV hline hval hvel hx
  rw [hpoint] at hh
  exact hh

end SmoothLocal.Taylor

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Taylor.linearCauchy_height_initial_state := @OAI.SmoothLocal.Taylor.linearCauchy_height_initial_state
