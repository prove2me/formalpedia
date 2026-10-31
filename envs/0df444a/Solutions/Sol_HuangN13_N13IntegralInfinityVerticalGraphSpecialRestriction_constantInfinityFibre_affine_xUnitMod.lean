-- Prove2me | solution 1 for HuangN13.N13IntegralInfinityVerticalGraphSpecialRestriction.constantInfinityFibre_affine_xUnitMod
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:56:06.543749+00:00
-- url     : https://prove2.me/submissions/2504f777-543c-413d-9c6e-7cd0c6812860

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialComparisonCore
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_yClass_relation
import Theorems.Thm_MazurProof_N13GoodModelTwo_affineEquation_iff_fixed

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
theorem xClass_mem_graphIdeal
    (xClass : R[X] →+* A) (yClass : A) (u v : R[X]) :
    xClass u ∈ graphIdeal xClass yClass u v :=
  Ideal.subset_span (by simp)
end
end MazurProof.GeneralizedGraphIdealCore
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
theorem ySubClass_mem_graphIdeal
    (xClass : R[X] →+* A) (yClass : A) (u v : R[X]) :
    ySubClass xClass yClass v ∈ graphIdeal xClass yClass u v :=
  Ideal.subset_span (by simp)
end
end MazurProof.GeneralizedGraphIdealCore
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
/-- Replacing the graph ordinate by a congruent polynomial modulo the
horizontal equation does not change the graph ideal. -/
theorem graphIdeal_eq_of_dvd_sub
    (xClass : R[X] →+* A) (yClass : A)
    (u v V : R[X]) (h : u ∣ V - v) :
    graphIdeal xClass yClass u V =
      graphIdeal xClass yClass u v := by
  obtain ⟨t, ht⟩ := h
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_graphIdeal xClass yClass u v
    · have hmultiple :
          xClass (V - v) ∈ graphIdeal xClass yClass u v := by
        rw [ht, map_mul, mul_comm]
        exact Ideal.mul_mem_left _
          (xClass t) (xClass_mem_graphIdeal xClass yClass u v)
      have heq :
          ySubClass xClass yClass V =
            ySubClass xClass yClass v - xClass (V - v) := by
        simp [ySubClass, map_sub]
      rw [heq]
      exact Ideal.sub_mem _
        (ySubClass_mem_graphIdeal xClass yClass u v) hmultiple
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_graphIdeal xClass yClass u V
    · have hmultiple :
          xClass (V - v) ∈ graphIdeal xClass yClass u V := by
        rw [ht, map_mul, mul_comm]
        exact Ideal.mul_mem_left _
          (xClass t) (xClass_mem_graphIdeal xClass yClass u V)
      have heq :
          ySubClass xClass yClass v =
            ySubClass xClass yClass V + xClass (V - v) := by
        simp [ySubClass, map_sub]
      rw [heq]
      exact Ideal.add_mem _
        (ySubClass_mem_graphIdeal xClass yClass u V) hmultiple
end
end MazurProof.GeneralizedGraphIdealCore
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
/-- The product of the two raw graph functions is the negative substituted
curve equation. -/
theorem ySubClass_mul_conjugateV_raw
    (xClass : R[X] →+* A) (yClass : A) (h rhs v : R[X])
    (hy : yClass ^ 2 + xClass h * yClass = xClass rhs) :
    ySubClass xClass yClass v *
        ySubClass xClass yClass (conjugateV h v) =
      -xClass (v ^ 2 + h * v - rhs) := by
  calc
    ySubClass xClass yClass v *
          ySubClass xClass yClass (conjugateV h v) =
        yClass ^ 2 + xClass h * yClass -
          (xClass v ^ 2 + xClass h * xClass v) := by
      simp only [ySubClass, conjugateV, map_neg, map_sub]
      ring
    _ = xClass rhs - xClass (v ^ 2 + h * v) := by
      rw [hy, map_add, map_mul, map_pow]
    _ = -xClass (v ^ 2 + h * v - rhs) := by
      rw [map_sub]
      ring
end
end MazurProof.GeneralizedGraphIdealCore
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
theorem ySubClass_mul_conjugate
    (xClass : R[X] →+* A) (yClass : A) (h rhs : R[X])
    (D : SemiGraph h rhs)
    (hy : yClass ^ 2 + xClass h * yClass = xClass rhs) :
    ySubClass xClass yClass D.v *
        ySubClass xClass yClass (conjugateV h D.v) =
      -(xClass D.u * xClass D.w) := by
  calc
    ySubClass xClass yClass D.v *
          ySubClass xClass yClass (conjugateV h D.v) =
        -xClass (D.v ^ 2 + h * D.v - rhs) :=
      ySubClass_mul_conjugateV_raw xClass yClass h rhs D.v hy
    _ = -xClass (D.u * D.w) := by rw [D.curve_eq]
    _ = -(xClass D.u * xClass D.w) := by rw [map_mul]
end
end MazurProof.GeneralizedGraphIdealCore
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.GeneralizedGraphIdealCore
noncomputable section
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
/-- A generalized graph and its hyperelliptic conjugate multiply to `(u)`.
The only regularity input is the explicit Bézout identity for
`u`, `2v+h`, and `w`. -/
theorem graphIdeal_mul_conj
    (xClass : R[X] →+* A) (yClass : A) (h rhs : R[X])
    (D : SemiGraph h rhs)
    (hy : yClass ^ 2 + xClass h * yClass = xClass rhs)
    (hbez :
      ∃ a b c : R[X],
        a * D.u + b * (2 * D.v + h) + c * D.w = 1) :
    graphIdeal xClass yClass D.u D.v *
        graphIdeal xClass yClass D.u (conjugateV h D.v) =
      Ideal.span ({xClass D.u} : Set A) := by
  let I := graphIdeal xClass yClass D.u D.v
  let J :=
    graphIdeal xClass yClass D.u (conjugateV h D.v)
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro p hp q hq
    rw [Ideal.mem_span_singleton]
    obtain ⟨p₀, pY, hpEq⟩ := Ideal.mem_span_pair.mp hp
    obtain ⟨q₀, qY, hqEq⟩ := Ideal.mem_span_pair.mp hq
    refine
      ⟨p₀ * q₀ * xClass D.u +
          p₀ * qY *
            ySubClass xClass yClass (conjugateV h D.v) +
          pY * q₀ * ySubClass xClass yClass D.v -
          pY * qY * xClass D.w,
        ?_⟩
    rw [← hpEq, ← hqEq]
    linear_combination
      pY * qY *
        ySubClass_mul_conjugate xClass yClass h rhs D hy
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨a, b, c, habc⟩ := hbez
    have huI : xClass D.u ∈ I :=
      xClass_mem_graphIdeal xClass yClass D.u D.v
    have huJ : xClass D.u ∈ J :=
      xClass_mem_graphIdeal xClass yClass D.u
        (conjugateV h D.v)
    have hvI : ySubClass xClass yClass D.v ∈ I :=
      ySubClass_mem_graphIdeal xClass yClass D.u D.v
    have hvJ :
        ySubClass xClass yClass (conjugateV h D.v) ∈ J :=
      ySubClass_mem_graphIdeal xClass yClass D.u
        (conjugateV h D.v)
    have hu2 : xClass D.u * xClass D.u ∈ I * J :=
      Ideal.mul_mem_mul huI huJ
    have huv : xClass D.u * xClass (2 * D.v + h) ∈ I * J := by
      have hp :
          xClass D.u *
              ySubClass xClass yClass (conjugateV h D.v) ∈ I * J :=
        Ideal.mul_mem_mul huI hvJ
      have hm :
          ySubClass xClass yClass D.v * xClass D.u ∈ I * J :=
        Ideal.mul_mem_mul hvI huJ
      have hd := Ideal.sub_mem (I * J) hp hm
      convert hd using 1
      simp only [two_mul, ySubClass, conjugateV, map_neg, map_sub,
        map_add]
      ring
    have huw : xClass D.u * xClass D.w ∈ I * J := by
      have hg :
          ySubClass xClass yClass D.v *
              ySubClass xClass yClass (conjugateV h D.v) ∈ I * J :=
        Ideal.mul_mem_mul hvI hvJ
      have hneg := (I * J).neg_mem hg
      rw [ySubClass_mul_conjugate xClass yClass h rhs D hy] at hneg
      simpa using hneg
    have ha :
        xClass a * (xClass D.u * xClass D.u) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass a) hu2
    have hb :
        xClass b * (xClass D.u * xClass (2 * D.v + h)) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass b) huv
    have hc :
        xClass c * (xClass D.u * xClass D.w) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass c) huw
    have hsum :=
      Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass a * (xClass D.u * xClass D.u) +
            xClass b * (xClass D.u * xClass (2 * D.v + h)) +
            xClass c * (xClass D.u * xClass D.w) =
          xClass D.u := by
      calc
        _ = xClass D.u *
            xClass
              (a * D.u + b * (2 * D.v + h) + c * D.w) := by
          simp only [two_mul, map_add, map_mul]
          ring
        _ = xClass D.u * 1 := by rw [habc, map_one]
        _ = xClass D.u := mul_one _
    rw [heq] at hsum
    exact hsum
end
end MazurProof.GeneralizedGraphIdealCore
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialDivisorCharts
noncomputable section
@[simp] theorem ofDivisor_mk (P Q : CurvePoint) :
    ofDivisor s(P, Q) =
      tensor (point P) (point Q) :=
  rfl
end
end MazurProof.N13SpecialDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialGraphDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT
theorem point_affineIdeal
    (P : N13SpecialDivisorCharts.AffinePoint) :
    (N13SpecialDivisorCharts.point (Sum.inl P)).affineIdeal =
      N13SpecialDivisorCharts.affinePointIdeal P := by
  rw [N13SpecialDivisorCharts.point]
  split <;> rfl
end
end MazurProof.N13SpecialGraphDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The affine chart ideal of one sheet is its literal point graph ideal. -/
theorem verticalPoint_affineIdeal (a y : K) :
    (N13SpecialDivisorCharts.point
        (verticalPoint a y)).affineIdeal =
      mumfordIdeal (X - C a) (C y) := by
  change
    (N13SpecialDivisorCharts.point
        (Sum.inl
          (⟨(a, y), _⟩ :
            N13SpecialDivisorCharts.AffinePoint))).affineIdeal =
      _
  rw [N13SpecialGraphDivisorCharts.point_affineIdeal]
  rfl
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The affine vertical derivative is one at every special affine point. -/
theorem hPoly_eval (a : K) :
    hPoly.eval a = 1 := by
  simp only [hPoly, eval_add, eval_pow, eval_X, eval_one]
  fin_cases a <;> decide
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- Both finite base coordinates are roots of the affine right-hand side. -/
theorem rhsPoly_eval (a : K) :
    rhsPoly.eval a = 0 := by
  simp only [rhsPoly, eval_add, eval_pow, eval_X]
  fin_cases a <;> decide
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The two affine sheet ideals multiply to the principal fibre ideal. -/
theorem verticalPointIdeal_mul :
    ∀ a : K,
      mumfordIdeal (X - C a) 0 *
          mumfordIdeal (X - C a) 1 =
        Ideal.span ({xClass (X - C a)} :
          Set CoordinateRing) := by
  intro a
  let p : K[X] := X - C a
  have hrhs : p ∣ -rhsPoly := by
    have hdiv :
        p ∣ -rhsPoly - C ((-rhsPoly).eval a) :=
      X_sub_C_dvd_sub_C_eval
    simpa [p, rhsPoly_eval a] using hdiv
  let w : K[X] := Classical.choose hrhs
  have hw : -rhsPoly = p * w :=
    Classical.choose_spec hrhs
  let D :
      GeneralizedGraphIdealCore.SemiGraph hPoly rhsPoly :=
    { u := p
      v := 0
      w := w
      curve_eq := by
        simpa using hw }
  have hhdiv : p ∣ hPoly - C 1 := by
    simpa [p, hPoly_eval a] using
      (X_sub_C_dvd_sub_C_eval (p := hPoly) (a := a))
  obtain ⟨s, hs⟩ := hhdiv
  have hbez :
      ∃ A B C : K[X],
        A * D.u + B * (2 * D.v + hPoly) + C * D.w = 1 := by
    refine ⟨-s, 1, 0, ?_⟩
    dsimp [D]
    have htwo : (2 : K[X]) = 0 :=
      CharP.cast_eq_zero (K[X]) 2
    rw [htwo, zero_mul, zero_add, one_mul, zero_mul, add_zero]
    rw [C_1] at hs
    linear_combination hs
  have hconj :
      mumfordIdeal p (conjugateV 0) =
        mumfordIdeal p 1 := by
    have heval :
        (conjugateV 0).eval a = 1 := by
      simp [conjugateV, hPoly_eval a]
    have hdiv :
        p ∣ conjugateV 0 - C 1 := by
      simpa [p, heval] using
        (X_sub_C_dvd_sub_C_eval
          (p := conjugateV 0) (a := a))
    simpa [mumfordIdeal,
      GeneralizedGraphIdealCore.graphIdeal,
      ySubClass,
      GeneralizedGraphIdealCore.ySubClass] using
      (GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
        xClassHom yClass p 1 (conjugateV 0) hdiv)
  rw [← hconj]
  change
    GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p 0 *
        GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p
            (GeneralizedGraphIdealCore.conjugateV hPoly 0) =
      Ideal.span ({xClassHom p} : Set CoordinateRing)
  exact
    (GeneralizedGraphIdealCore.graphIdeal_mul_conj
      xClassHom yClass hPoly rhsPoly D
      yClass_relation hbez)
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The affine ideal of a finite canonical divisor is `(X-a)`. -/
theorem canonicalDivisor_affineIdeal (a : K) :
    (N13SpecialDivisorCharts.ofDivisor
        (N13AbelFiberTwoModel.canonicalDivisor
          (Sum.inl a))).affineIdeal =
      Ideal.span ({xClass (X - C a)} :
        Set CoordinateRing) := by
  rw [N13AbelFiberTwoModel.canonicalDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13SpecialDivisorCharts.point
        (verticalPoint a 0)).affineIdeal *
      (N13SpecialDivisorCharts.point
        (verticalPoint a 1)).affineIdeal =
      _
  rw [verticalPoint_affineIdeal, verticalPoint_affineIdeal]
  simpa using verticalPointIdeal_mul a
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
/-- One of the two special curve points above the base point at infinity. -/
def infinityVerticalPoint (v : K) :
    N13SpecialDivisorCharts.CurvePoint :=
  N13AbelFiberTwoModel.curvePointEquiv.symm
    (Sum.inr (), v)
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT
/-- A point above the base point at infinity is absent from the ordinary
affine chart. -/
theorem infinityVerticalPoint_affineIdeal (v : K) :
    (N13SpecialDivisorCharts.point
        (infinityVerticalPoint v)).affineIdeal = ⊤ := by
  rw [N13SpecialDivisorCharts.point.eq_def]
  rfl
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The canonical divisor above the base point at infinity is absent from
the ordinary affine chart. -/
theorem canonicalInfinityDivisor_affineIdeal :
    (N13SpecialDivisorCharts.ofDivisor
        (N13AbelFiberTwoModel.canonicalDivisor
          (Sum.inr ()))).affineIdeal = ⊤ := by
  rw [N13AbelFiberTwoModel.canonicalDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13SpecialDivisorCharts.point
        (infinityVerticalPoint 0)).affineIdeal *
      (N13SpecialDivisorCharts.point
        (infinityVerticalPoint 1)).affineIdeal =
      ⊤
  rw [infinityVerticalPoint_affineIdeal,
    infinityVerticalPoint_affineIdeal]
  simp
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The affine ideal of the constant-`t` canonical fibre is unit at `t=0`
and `(x-1)` at `t=1`. -/
theorem constantInfinityFibreDivisor_affineIdeal (a : K) :
    (N13SpecialDivisorCharts.ofDivisor
        (constantInfinityFibreDivisor a)).affineIdeal =
      if a = 0 then ⊤ else
        Ideal.span
          ({xClass (X - C 1)} : Set CoordinateRing) := by
  rcases
      N13GoodModelTwo.fixedTwo_eq_zero_or_one
        a (ZMod.pow_card a) with rfl | rfl
  · simp [constantInfinityFibreDivisor,
      canonicalInfinityDivisor_affineIdeal]
  · simp [constantInfinityFibreDivisor,
      canonicalDivisor_affineIdeal]
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- The canonical constant special fibre has `x` invertible modulo its
affine chart ideal.  At `t=0` the affine ideal is the unit ideal; at `t=1`
the relation is `x=1`. -/
theorem constantInfinityFibre_affine_xUnitMod
    (a : K) :
    N13SpecialAffineSaturation.XUnitMod
      (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialVerticalDivisorCharts.constantInfinityFibreDivisor
          a)).affineIdeal := by
  rw [
    N13SpecialVerticalDivisorCharts.constantInfinityFibreDivisor_affineIdeal]
  rcases
      N13GoodModelTwo.fixedTwo_eq_zero_or_one
        a (ZMod.pow_card a) with rfl | rfl
  · refine ⟨0, ?_⟩
    simp
  · simp only [if_false, one_ne_zero]
    refine ⟨1, ?_⟩
    have hgen :
        N13GoodCoordinateRingTwo.xClass (X - C (1 : K)) ∈
          Ideal.span
            ({N13GoodCoordinateRingTwo.xClass (X - C (1 : K))} :
              Set N13GoodCoordinateRingTwo.CoordinateRing) :=
      Ideal.subset_span (by simp)
    have hneg :=
      (Ideal.span
        ({N13GoodCoordinateRingTwo.xClass (X - C (1 : K))} :
          Set N13GoodCoordinateRingTwo.CoordinateRing)).neg_mem hgen
    convert hneg using 1
    simp [N13SpecialCurveOverlap.xClass]
end
end MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
end
end


set_option autoImplicit false
open Polynomial
theorem solution
    (a : MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.K) :
    MazurProof.N13SpecialAffineSaturation.XUnitMod
      (MazurProof.N13SpecialDivisorCharts.ofDivisor
        (MazurProof.N13SpecialVerticalDivisorCharts.constantInfinityFibreDivisor
          a)).affineIdeal := by
  exact MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.constantInfinityFibre_affine_xUnitMod a
