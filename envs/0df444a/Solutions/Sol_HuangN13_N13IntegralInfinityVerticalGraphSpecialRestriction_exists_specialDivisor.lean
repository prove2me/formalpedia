-- Prove2me | solution 1 for HuangN13.N13IntegralInfinityVerticalGraphSpecialRestriction.exists_specialDivisor
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:21:19.115863+00:00
-- url     : https://prove2.me/submissions/379d2d53-1e8a-4aa0-a44f-1bd0c9167045

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_InfinityGraphLineCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore
import Theorems.Thm_HuangN13_N13IntegralInfinityVerticalGraphSpecialRestriction_constantInfinityFibre_affine_xUnitMod
import Theorems.Thm_HuangN13_N13SpecialAffineSaturation_chartPair_eq_of_infinityIdeal_eq
import Theorems.Thm_HuangN13_N13SpecialInfinityGraphDivisorCharts_ofDivisor_graphDivisor_infinityIdeal
import Theorems.Thm_MazurProof_N13SpecialInfinityGraphDivisor_curveEquationAtRoot

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
namespace MazurProof.N13SpecialVerticalDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The ordinate on the special infinity chart satisfies its generalized
quadratic equation. -/
theorem infinity_yClass_relation :
    N13SpecialInfinityChart.vClass ^ 2 +
        (algebraMap K[X]
          N13SpecialDivisorCharts.SpecialInfinity)
            N13SpecialInfinityChart.hPoly *
          N13SpecialInfinityChart.vClass =
      (algebraMap K[X]
        N13SpecialDivisorCharts.SpecialInfinity)
          N13SpecialInfinityChart.rhsPoly := by
  change
    N13SpecialInfinityChart.vClass ^ 2 +
        (AdjoinRoot.of N13SpecialInfinityChart.curvePoly)
            N13SpecialInfinityChart.hPoly *
          N13SpecialInfinityChart.vClass =
      (AdjoinRoot.of N13SpecialInfinityChart.curvePoly)
        N13SpecialInfinityChart.rhsPoly
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [N13SpecialInfinityChart.curvePoly]
  ring
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
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- At any `F₂`-rational base coordinate `t = a`, the two infinity-chart
sheet ideals multiply to the principal fibre ideal `(t-a)`. -/
theorem infinityPointIdeal_mul (a : K) :
    N13SpecialDivisorCharts.infinityPointIdeal a 0 *
        N13SpecialDivisorCharts.infinityPointIdeal a 1 =
      Ideal.span
        ({N13SpecialInfinityChart.tClass -
            algebraMap K[X] N13SpecialDivisorCharts.SpecialInfinity
              (C a)} :
          Set N13SpecialDivisorCharts.SpecialInfinity) := by
  let xClassHom :
      K[X] →+* N13SpecialDivisorCharts.SpecialInfinity :=
    AdjoinRoot.of N13SpecialInfinityChart.curvePoly
  let yClass : N13SpecialDivisorCharts.SpecialInfinity :=
    N13SpecialInfinityChart.vClass
  let p : K[X] := X - C a
  have hrhs : p ∣ -N13SpecialInfinityChart.rhsPoly := by
    have heval :
        (-N13SpecialInfinityChart.rhsPoly).eval a = 0 := by
      simp only [N13SpecialInfinityChart.rhsPoly, eval_neg,
        eval_add, eval_X, eval_pow]
      fin_cases a <;> decide
    have hdiv :
        p ∣ -N13SpecialInfinityChart.rhsPoly -
          C ((-N13SpecialInfinityChart.rhsPoly).eval a) :=
      X_sub_C_dvd_sub_C_eval
    simpa [p, heval] using hdiv
  let w : K[X] := Classical.choose hrhs
  have hw :
      -N13SpecialInfinityChart.rhsPoly = p * w :=
    Classical.choose_spec hrhs
  let D : GeneralizedGraphIdealCore.SemiGraph
      N13SpecialInfinityChart.hPoly
      N13SpecialInfinityChart.rhsPoly :=
    { u := p
      v := 0
      w := w
      curve_eq := by simpa using hw }
  have hhEval :
      N13SpecialInfinityChart.hPoly.eval a = 1 := by
    simp only [N13SpecialInfinityChart.hPoly, eval_add,
      eval_one, eval_pow, eval_X]
    fin_cases a <;> decide
  have hhdiv :
      p ∣ N13SpecialInfinityChart.hPoly - C 1 := by
    simpa [p, hhEval] using
      (X_sub_C_dvd_sub_C_eval
        (p := N13SpecialInfinityChart.hPoly) (a := a))
  obtain ⟨s, hs⟩ := hhdiv
  have hbez :
      ∃ A B C : K[X],
        A * D.u +
            B * (2 * D.v + N13SpecialInfinityChart.hPoly) +
            C * D.w = 1 := by
    refine ⟨-s, 1, 0, ?_⟩
    dsimp [D]
    have htwo : (2 : K[X]) = 0 :=
      CharP.cast_eq_zero (K[X]) 2
    rw [htwo, zero_mul, zero_add, one_mul, zero_mul, add_zero]
    rw [C_1] at hs
    linear_combination hs
  have hconj :
      GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p
            (GeneralizedGraphIdealCore.conjugateV
              N13SpecialInfinityChart.hPoly 0) =
        GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p 1 := by
    have heval :
        (GeneralizedGraphIdealCore.conjugateV
          N13SpecialInfinityChart.hPoly 0).eval a = 1 := by
      simp [GeneralizedGraphIdealCore.conjugateV, hhEval]
    have hdiv :
        p ∣
          GeneralizedGraphIdealCore.conjugateV
              N13SpecialInfinityChart.hPoly 0 -
            C 1 := by
      simpa [p, heval] using
        (X_sub_C_dvd_sub_C_eval
          (p := GeneralizedGraphIdealCore.conjugateV
            N13SpecialInfinityChart.hPoly 0)
          (a := a))
    exact
      GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
        xClassHom yClass p 1
        (GeneralizedGraphIdealCore.conjugateV
          N13SpecialInfinityChart.hPoly 0) hdiv
  have hproduct :=
    GeneralizedGraphIdealCore.graphIdeal_mul_conj
      xClassHom yClass
        N13SpecialInfinityChart.hPoly
        N13SpecialInfinityChart.rhsPoly
        D infinity_yClass_relation hbez
  rw [hconj] at hproduct
  change
    GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p 0 *
        GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass p 1 =
      Ideal.span ({xClassHom p} :
        Set N13SpecialDivisorCharts.SpecialInfinity) at hproduct
  have hX :
      xClassHom X = N13SpecialInfinityChart.tClass := rfl
  simpa [N13SpecialDivisorCharts.infinityPointIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass,
    xClassHom, yClass, p, hX] using hproduct
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
/-- At `t = 1`, the two infinity-chart sheet ideals multiply to `(t-1)`. -/
theorem infinityPointIdeal_one_mul :
    N13SpecialDivisorCharts.infinityPointIdeal 1 0 *
        N13SpecialDivisorCharts.infinityPointIdeal 1 1 =
      Ideal.span
        ({N13SpecialInfinityChart.tClass -
            algebraMap K[X]
              N13SpecialDivisorCharts.SpecialInfinity (C 1)} :
          Set N13SpecialDivisorCharts.SpecialInfinity) :=
  infinityPointIdeal_mul 1
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
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- A point above the base point at infinity has its literal ideal at
`t = 0`. -/
theorem infinityVerticalPoint_infinityIdeal (v : K) :
    (N13SpecialDivisorCharts.point
        (infinityVerticalPoint v)).infinityIdeal =
      N13SpecialDivisorCharts.infinityPointIdeal 0 v := by
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
/-- The infinity ideal of the canonical divisor above infinity is the
principal fibre ideal `(t)`. -/
theorem canonicalInfinityDivisor_infinityIdeal :
    (N13SpecialDivisorCharts.ofDivisor
        (N13AbelFiberTwoModel.canonicalDivisor
          (Sum.inr ()))).infinityIdeal =
      Ideal.span
        ({N13SpecialInfinityChart.tClass} :
          Set N13SpecialDivisorCharts.SpecialInfinity) := by
  rw [N13AbelFiberTwoModel.canonicalDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13SpecialDivisorCharts.point
        (infinityVerticalPoint 0)).infinityIdeal *
      (N13SpecialDivisorCharts.point
        (infinityVerticalPoint 1)).infinityIdeal =
      _
  rw [infinityVerticalPoint_infinityIdeal,
    infinityVerticalPoint_infinityIdeal,
    infinityPointIdeal_mul]
  congr 2
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
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- A finite point above `x = 0` is absent from the infinity chart. -/
theorem verticalPoint_zero_infinityIdeal (y : K) :
    (N13SpecialDivisorCharts.point
      (verticalPoint 0 y)).infinityIdeal = ⊤ := by
  rw [N13SpecialDivisorCharts.point.eq_def]
  dsimp [verticalPoint, N13AbelFiberTwoModel.curvePointEquiv]
  simp [N13SpecialDivisorCharts.affineZeroPoint]
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
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT
/-- A finite point above `x = 1` has its literal ideal at `t = 1`. -/
theorem verticalPoint_one_infinityIdeal (y : K) :
    (N13SpecialDivisorCharts.point
        (verticalPoint 1 y)).infinityIdeal =
      N13SpecialDivisorCharts.infinityPointIdeal 1 y := by
  rw [N13SpecialDivisorCharts.point.eq_def]
  dsimp [verticalPoint, N13AbelFiberTwoModel.curvePointEquiv]
  simp [N13SpecialDivisorCharts.affineOnePoint]
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
/-- The infinity ideal of a finite canonical fibre is unit above `x = 0`
and the principal ideal `(t-1)` above `x = 1`. -/
theorem canonicalDivisor_infinityIdeal (a : K) :
    (N13SpecialDivisorCharts.ofDivisor
        (N13AbelFiberTwoModel.canonicalDivisor
          (Sum.inl a))).infinityIdeal =
      if a = 0 then ⊤ else
        Ideal.span
          ({N13SpecialInfinityChart.tClass -
              algebraMap K[X]
                N13SpecialDivisorCharts.SpecialInfinity (C 1)} :
            Set N13SpecialDivisorCharts.SpecialInfinity) := by
  rw [N13AbelFiberTwoModel.canonicalDivisor,
    N13SpecialDivisorCharts.ofDivisor_mk]
  change
    (N13SpecialDivisorCharts.point
        (verticalPoint a 0)).infinityIdeal *
      (N13SpecialDivisorCharts.point
        (verticalPoint a 1)).infinityIdeal =
      _
  rcases
      N13GoodModelTwo.fixedTwo_eq_zero_or_one
        a (ZMod.pow_card a) with rfl | rfl
  · rw [verticalPoint_zero_infinityIdeal,
      verticalPoint_zero_infinityIdeal]
    simp
  · rw [verticalPoint_one_infinityIdeal,
      verticalPoint_one_infinityIdeal]
    simp only [if_false, one_ne_zero]
    change
      N13SpecialDivisorCharts.infinityPointIdeal 1 0 *
          N13SpecialDivisorCharts.infinityPointIdeal 1 1 =
        _
    exact infinityPointIdeal_one_mul
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
/-- The infinity ideal of the constant-`t` canonical fibre is the principal
fibre ideal `(t-a)`. -/
theorem constantInfinityFibreDivisor_infinityIdeal (a : K) :
    (N13SpecialDivisorCharts.ofDivisor
        (constantInfinityFibreDivisor a)).infinityIdeal =
      Ideal.span
        ({N13SpecialInfinityChart.tClass -
            algebraMap K[X]
              N13SpecialDivisorCharts.SpecialInfinity (C a)} :
          Set N13SpecialDivisorCharts.SpecialInfinity) := by
  rcases
      N13GoodModelTwo.fixedTwo_eq_zero_or_one
        a (ZMod.pow_card a) with rfl | rfl
  · rw [constantInfinityFibreDivisor,
      if_pos rfl, canonicalInfinityDivisor_infinityIdeal]
    congr 2
    simp
  · rw [constantInfinityFibreDivisor,
      if_neg one_ne_zero,
      canonicalDivisor_infinityIdeal]
    simp
end
end MazurProof.N13SpecialVerticalDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialConstantInfinityVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialConstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT
/-- Substitution of either constant `F₂` coordinate into the special
infinity equation leaves the sheet polynomial `v²+v`. -/
theorem verticalCurve_C (a : K) :
    verticalCurve (C a) = X ^ 2 + X := by
  rcases
      N13GoodModelTwo.fixedTwo_eq_zero_or_one
        a (ZMod.pow_card a) with rfl | rfl
  · unfold verticalCurve
    simp [N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly]
  · unfold verticalCurve
    simp [N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly]
    have htwo : (2 : K[X]) = 0 :=
      CharP.cast_eq_zero (K[X]) 2
    linear_combination X * htwo - htwo
end
end MazurProof.N13SpecialConstantInfinityVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialConstantInfinityVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialConstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT
/-- A monic quadratic factor of `v²+v` is the full polynomial `v²+v`. -/
theorem monicQuadratic_eq_X_sq_add_X
    (m w : K[X])
    (hm : m.Monic)
    (hdeg : m.natDegree = 2)
    (hcurve : X ^ 2 + X = m * w) :
    m = X ^ 2 + X := by
  have htargetMonic : (X ^ 2 + X : K[X]).Monic := by
    apply monic_X_pow_add
    rw [degree_X]
    norm_num
  have htargetDegree : (X ^ 2 + X : K[X]).natDegree = 2 := by
    compute_degree
    norm_num
  have hmDegree : m.IsMonicOfDegree 2 :=
    ⟨hdeg, hm⟩
  have hprodDegree : (m * w).IsMonicOfDegree (2 + 0) := by
    rw [← hcurve]
    exact ⟨by simpa using htargetDegree, htargetMonic⟩
  have hwDegree : w.IsMonicOfDegree 0 :=
    hmDegree.of_mul_left hprodDegree
  have hw : w = 1 :=
    eq_one_of_monic_natDegree_zero
      hwDegree.monic hwDegree.natDegree_eq
  rw [hw, mul_one] at hcurve
  exact hcurve.symm
end
end MazurProof.N13SpecialConstantInfinityVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialConstantInfinityVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialConstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT
/-- A constant vertical quadratic graph cuts out exactly the principal
base-fibre ideal `(t-a)`. -/
theorem verticalIdeal_eq_span
    (m w : K[X])
    (a : K)
    (hm : m.Monic)
    (hdeg : m.natDegree = 2)
    (hcurve : verticalCurve (C a) = m * w) :
    verticalIdeal m a =
      Ideal.span
        ({N13SpecialInfinityChart.tClass -
            algebraMap K[X] Ring (C a)} : Set Ring) := by
  have hmShape : m = X ^ 2 + X := by
    apply monicQuadratic_eq_X_sq_add_X m w hm hdeg
    rw [← hcurve, verticalCurve_C]
  let xClassHom : K[X] →+* Ring :=
    AdjoinRoot.of N13SpecialInfinityChart.curvePoly
  let p : K[X] := X - C a
  let J : Ideal Ring :=
    Ideal.span ({xClassHom p} : Set Ring)
  have hpJ : xClassHom p ∈ J :=
    Ideal.subset_span (by simp)
  have hhEval :
      N13SpecialInfinityChart.hPoly.eval a = 1 := by
    simp only [N13SpecialInfinityChart.hPoly, eval_add,
      eval_one, eval_pow, eval_X]
    fin_cases a <;> decide
  have hrhsEval :
      N13SpecialInfinityChart.rhsPoly.eval a = 0 := by
    simp only [N13SpecialInfinityChart.rhsPoly,
      eval_add, eval_X, eval_pow]
    fin_cases a <;> decide
  have hhdiv :
      p ∣ N13SpecialInfinityChart.hPoly - C 1 := by
    simpa [p, hhEval] using
      (X_sub_C_dvd_sub_C_eval
        (p := N13SpecialInfinityChart.hPoly) (a := a))
  have hrhsdiv :
      p ∣ N13SpecialInfinityChart.rhsPoly := by
    simpa [p, hrhsEval] using
      (X_sub_C_dvd_sub_C_eval
        (p := N13SpecialInfinityChart.rhsPoly) (a := a))
  have hhJ :
      xClassHom (N13SpecialInfinityChart.hPoly - C 1) ∈ J := by
    obtain ⟨q, hq⟩ := hhdiv
    rw [hq, map_mul]
    exact Ideal.mul_mem_right (xClassHom q) J hpJ
  have hrhsJ :
      xClassHom N13SpecialInfinityChart.rhsPoly ∈ J := by
    obtain ⟨q, hq⟩ := hrhsdiv
    rw [hq, map_mul]
    exact Ideal.mul_mem_right (xClassHom q) J hpJ
  have hvvJ :
      N13SpecialInfinityChart.vClass ^ 2 +
          N13SpecialInfinityChart.vClass ∈ J := by
    have hdelta :=
      Ideal.mul_mem_right N13SpecialInfinityChart.vClass J hhJ
    have hmem := Ideal.sub_mem J hrhsJ hdelta
    have hrel :=
      N13SpecialVerticalDivisorCharts.infinity_yClass_relation
    change
      N13SpecialInfinityChart.vClass ^ 2 +
          xClassHom N13SpecialInfinityChart.hPoly *
            N13SpecialInfinityChart.vClass =
        xClassHom N13SpecialInfinityChart.rhsPoly at hrel
    convert hmem using 1
    change
      N13SpecialInfinityChart.vClass ^ 2 +
          N13SpecialInfinityChart.vClass =
        xClassHom N13SpecialInfinityChart.rhsPoly -
          xClassHom
              (N13SpecialInfinityChart.hPoly - C 1) *
            N13SpecialInfinityChart.vClass
    simp only [map_sub]
    have hOne : xClassHom (C (1 : K)) = 1 := rfl
    rw [hOne]
    linear_combination hrel
  have hpClass :
      xClassHom p =
        N13SpecialInfinityChart.tClass -
          algebraMap K[X] Ring (C a) := by
    simp [xClassHom, p, N13SpecialInfinityChart.tClass]
  rw [verticalIdeal]
  rw [← hpClass]
  change
    Ideal.span
        ({aeval N13SpecialInfinityChart.vClass m,
          xClassHom p} : Set Ring) =
      J
  rw [hmShape]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · simpa using hvvJ
    · exact hpJ
  · apply Ideal.span_mono
    simp
end
end MazurProof.N13SpecialConstantInfinityVerticalGraph
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialAffineSaturation
noncomputable section
/-- The unit ideal trivially makes the affine coordinate invertible in the
quotient. -/
theorem top_xUnitMod :
    XUnitMod (⊤ : Ideal AffineCurve) := by
  exact ⟨0, by simp⟩
end
end MazurProof.N13SpecialAffineSaturation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialAffineSaturation
noncomputable section
/-- If the affine coordinate is invertible modulo each of two ideals, it is
also invertible modulo their product.  The inverse witness is obtained by
multiplying the two Bézout relations. -/
theorem mul_xUnitMod
    {I J : Ideal AffineCurve}
    (hI : XUnitMod I)
    (hJ : XUnitMod J) :
    XUnitMod (I * J) := by
  obtain ⟨q, hq⟩ := hI
  obtain ⟨r, hr⟩ := hJ
  refine
    ⟨q + r - q * r * N13SpecialCurveOverlap.xClass, ?_⟩
  have hprod := Ideal.mul_mem_mul hq hr
  convert hprod using 1
  ring
end
end MazurProof.N13SpecialAffineSaturation
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialAffineSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Reduction preserves the property that `x` is a unit modulo an affine
ideal: reduce an explicit inverse relation coefficientwise. -/
theorem map_reduceCoordinate_xUnitMod
    {I : Ideal N13OrdinaryCurveOverlap.AffineCurve}
    (hx : N13IntegralInfinityGraphSaturation.XUnitMod I) :
    XUnitMod
      (Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate I) := by
  obtain ⟨q, hq⟩ := hx
  refine
    ⟨N13GeneralizedMumfordReduction.reduceCoordinate q, ?_⟩
  have hmap :=
    Ideal.mem_map_of_mem
      N13GeneralizedMumfordReduction.reduceCoordinate hq
  simpa [XUnitMod,
    N13IntegralInfinityGraphSaturation.XUnitMod,
    N13OrdinaryCurveOverlap.xClass,
    N13SpecialCurveOverlap.xClass] using hmap
end
end MazurProof.N13SpecialAffineSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinityGraphDivisorCharts
noncomputable section
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityGraphDivisor.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityGraphDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The affine chart contribution of one infinity-graph root is absent at
`t = 0` and is the point graph at `x = 1` for the nonzero root. -/
theorem rootPoint_affineIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (hdeg : D.u.natDegree = 2)
    (a : K)
    (ha : a ∈ N13SpecialInfinityGraphDivisor.rootPair D hdeg) :
    (N13SpecialDivisorCharts.point
        (N13SpecialInfinityGraphDivisor.rootPoint
          D hdeg a ha)).affineIdeal =
      if a = 0 then ⊤ else
        N13GoodCoordinateRingTwo.mumfordIdeal
          (X - C 1) (C (D.v.eval a)) := by
  rw [N13SpecialInfinityGraphDivisor.rootPoint]
  split
  · subst a
    rw [N13SpecialDivisorCharts.point.eq_def]
    rfl
  · have ha1 : a = 1 :=
      (N13GoodModelTwo.fixedTwo_eq_zero_or_one
        a (ZMod.pow_card a)).resolve_left ‹a ≠ 0›
    rw [N13SpecialDivisorCharts.point.eq_def]
    dsimp
    rfl
end
end MazurProof.N13SpecialInfinityGraphDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinityGraphDivisorCharts
noncomputable section
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The canonical affine ideal of any selected pair of infinity-graph
roots is the product of their explicit affine contributions. -/
theorem ofDivisor_graphRoots_affineIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (hdeg : D.u.natDegree = 2)
    (z : Sym2 K)
    (hz :
      ∀ a ∈ z,
        a ∈ N13SpecialInfinityGraphDivisor.rootPair D hdeg) :
    (N13SpecialDivisorCharts.ofDivisor
        (Sym2.pmap
          (N13SpecialInfinityGraphDivisor.rootPoint D hdeg)
          z hz)).affineIdeal =
      rootAffineIdeal D z := by
  induction z using Sym2.ind with
  | _ a b =>
      rw [Sym2.pmap_pair,
        N13SpecialDivisorCharts.ofDivisor_mk]
      change
        (N13SpecialDivisorCharts.point
            (N13SpecialInfinityGraphDivisor.rootPoint D hdeg a
              (hz a (Sym2.mem_mk_left a b)))).affineIdeal *
          (N13SpecialDivisorCharts.point
            (N13SpecialInfinityGraphDivisor.rootPoint D hdeg b
              (hz b (Sym2.mem_mk_right a b)))).affineIdeal =
        rootAffineIdeal D s(a, b)
      rw [rootPoint_affineIdeal, rootPoint_affineIdeal,
        rootAffineIdeal_mk]
end
end MazurProof.N13SpecialInfinityGraphDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialInfinityGraphDivisorCharts
noncomputable section
/-- The canonical affine ideal of an infinity-graph divisor is the product
of the contributions of its two infinity roots. -/
theorem ofDivisor_graphDivisor_affineIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialInfinityGraphDivisor.graphDivisor D hdeg)).affineIdeal =
      rootAffineIdeal D
        (N13SpecialInfinityGraphDivisor.rootPair D hdeg) := by
  unfold N13SpecialInfinityGraphDivisor.graphDivisor
  exact
    ofDivisor_graphRoots_affineIdeal D hdeg
      (N13SpecialInfinityGraphDivisor.rootPair D hdeg)
      (fun _ ha => ha)
end
end MazurProof.N13SpecialInfinityGraphDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialNonconstantInfinityVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialNonconstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT
/-- Evaluating a base polynomial at the special class `t` is the canonical
map from the base polynomial ring into the infinity coordinate ring. -/
theorem xClassHom_eq_aeval_tClass (p : K[X]) :
    N13SpecialInfinityGraphDivisorCharts.xClassHom p =
      aeval N13SpecialInfinityChart.tClass p := by
  let ψ : K[X] →ₐ[K] Ring :=
    IsScalarTower.toAlgHom K K[X] Ring
  have h :
      aeval N13SpecialInfinityChart.tClass = ψ := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    rfl
  exact (DFunLike.congr_fun h p).symm
end
end MazurProof.N13SpecialNonconstantInfinityVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialNonconstantInfinityVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialNonconstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT
/-- The two linear equations `t=a+v` and `v=t+a` define the same element
of the special coordinate ring. -/
theorem verticalLinear_eq_horizontalLinear (a : K) :
    N13SpecialInfinityChart.tClass -
        aeval N13SpecialInfinityChart.vClass (C a + X) =
      N13SpecialInfinityChart.vClass -
        N13SpecialInfinityGraphDivisorCharts.xClassHom (X + C a) := by
  simp only [map_add, Polynomial.aeval_C, aeval_X]
  rw [xClassHom_eq_aeval_tClass, xClassHom_eq_aeval_tClass]
  simp only [Polynomial.aeval_X, Polynomial.aeval_C]
  have htwoK : (2 : K) = 0 :=
    CharP.cast_eq_zero K 2
  have htwo : (2 : Ring) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (algebraMap K Ring) htwoK
  linear_combination
    (N13SpecialInfinityChart.tClass -
      N13SpecialInfinityChart.vClass) * htwo
end
end MazurProof.N13SpecialNonconstantInfinityVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialNonconstantInfinityVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialNonconstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT
/-- After imposing the common linear equation, evaluating `m` at `v`
or at `t+a` gives the same class. -/
theorem verticalPolynomial_sub_horizontalPolynomial_mem
    (m : K[X])
    (a : K) :
    aeval N13SpecialInfinityChart.vClass m -
        N13SpecialInfinityGraphDivisorCharts.xClassHom
          (translate a m) ∈
      Ideal.span
        ({N13SpecialInfinityChart.vClass -
            N13SpecialInfinityGraphDivisorCharts.xClassHom
              (X + C a)} : Set Ring) := by
  let s : Ring :=
    N13SpecialInfinityGraphDivisorCharts.xClassHom (X + C a)
  obtain ⟨q, hq⟩ :=
    sub_dvd_eval_sub N13SpecialInfinityChart.vClass s
      (m.map (algebraMap K Ring))
  have hdiff :
      aeval N13SpecialInfinityChart.vClass m -
          aeval s m =
        (N13SpecialInfinityChart.vClass - s) * q := by
    simpa [Polynomial.aeval_def] using hq
  have hs :
      N13SpecialInfinityGraphDivisorCharts.xClassHom
          (translate a m) =
        aeval s m := by
    rw [xClassHom_eq_aeval_tClass, translate, aeval_comp]
    apply congrArg (fun z : Ring => aeval z m)
    simpa only [s] using
      (xClassHom_eq_aeval_tClass (X + C a)).symm
  change
    aeval N13SpecialInfinityChart.vClass m -
        N13SpecialInfinityGraphDivisorCharts.xClassHom
          (translate a m) ∈
      Ideal.span
        ({N13SpecialInfinityChart.vClass - s} : Set Ring)
  rw [hs, hdiff]
  exact
    Ideal.mul_mem_right q _
      (Ideal.subset_span (by simp))
end
end MazurProof.N13SpecialNonconstantInfinityVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialNonconstantInfinityVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialNonconstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT
/-- The nonconstant vertical ideal is literally the horizontal graph ideal
obtained by the involutive translation `v=t+a`. -/
theorem verticalIdeal_eq_graphIdeal
    (m : K[X])
    (a : K) :
    verticalIdeal m a =
      N13SpecialInfinityGraphDivisorCharts.graphIdeal
        (translate a m) (X + C a) := by
  let g : Ring :=
    N13SpecialInfinityChart.vClass -
      N13SpecialInfinityGraphDivisorCharts.xClassHom (X + C a)
  let mV : Ring :=
    aeval N13SpecialInfinityChart.vClass m
  let mT : Ring :=
    N13SpecialInfinityGraphDivisorCharts.xClassHom (translate a m)
  have hlinear := verticalLinear_eq_horizontalLinear a
  have hdiff :
      mV - mT ∈ Ideal.span ({g} : Set Ring) := by
    exact verticalPolynomial_sub_horizontalPolynomial_mem m a
  rw [verticalIdeal,
    N13SpecialInfinityGraphDivisorCharts.graphIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass]
  change Ideal.span ({mV, _} : Set Ring) =
    Ideal.span ({mT, g} : Set Ring)
  rw [hlinear]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have hmT :
          mT ∈ Ideal.span ({mT, g} : Set Ring) :=
        Ideal.subset_span (by simp)
      have hdiff' :
          mV - mT ∈ Ideal.span ({mT, g} : Set Ring) :=
        (Ideal.span_mono (by
          intro z hz
          simp only [Set.mem_singleton_iff] at hz
          subst z
          simp [g])) hdiff
      have hadd :=
        Ideal.add_mem (Ideal.span ({mT, g} : Set Ring)) hdiff' hmT
      simpa [g] using hadd
    · exact Ideal.subset_span (by simp [g])
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have hmV :
          mV ∈ Ideal.span ({mV, g} : Set Ring) :=
        Ideal.subset_span (by simp)
      have hdiff' :
          mV - mT ∈ Ideal.span ({mV, g} : Set Ring) :=
        (Ideal.span_mono (by
          intro z hz
          simp only [Set.mem_singleton_iff] at hz
          subst z
          simp [g])) hdiff
      have hsub :=
        Ideal.sub_mem (Ideal.span ({mV, g} : Set Ring)) hmV hdiff'
      simpa [g] using hsub
    · exact Ideal.subset_span (by simp [g])
end
end MazurProof.N13SpecialNonconstantInfinityVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- Reduction commutes with evaluation of a polynomial at the infinity
ordinate `v`. -/
theorem reduce_aeval_vClass (p : R₂[X]) :
    N13IntegralInfinityReduction.reduceCoordinate
        (aeval N13IntegralInfinityGraphJacobian.yClass p) =
      aeval N13SpecialInfinityChart.vClass
        (N13IntegralInfinityReduction.reducePoly p) := by
  have h :=
    Polynomial.map_aeval_eq_aeval_map
      (R := R₂)
      (S := N13IntegralInfinityReduction.IntegralRing)
      (T := K)
      (U := N13IntegralInfinityReduction.SpecialRing)
      (φ := N13IntegralInfinityReduction.reduceBase)
      (ψ := N13IntegralInfinityReduction.reduceCoordinate)
      (by
        ext r
        change
          N13IntegralInfinityReduction.specialBaseClass
              (C (N13IntegralInfinityReduction.reduceBase r)) =
            N13IntegralInfinityReduction.reduceCoordinate
              (N13IntegralInfinityReduction.integralBaseClass (C r))
        rw [N13IntegralInfinityReduction.reduce_integralBaseClass]
        simp [N13IntegralInfinityReduction.reducePoly])
      p N13IntegralInfinityGraphJacobian.yClass
  have hv :
      N13IntegralInfinityReduction.reduceCoordinate
          N13IntegralInfinityGraphJacobian.yClass =
        N13SpecialInfinityChart.vClass :=
    N13IntegralInfinityReduction.reduce_vClass
  rw [hv] at h
  simpa only [N13IntegralInfinityReduction.reducePoly_apply] using h
end
end MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialConstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- When the slope `c` vanishes after reduction, the reduced integral
factorization is the constant special vertical factorization at `t=ā`. -/
theorem reduced_curve_eq_of_reduce_c_eq_zero
    (E : VerticalGraph)
    (hc :
      N13IntegralInfinityReduction.reduceBase E.c = 0) :
    N13SpecialConstantInfinityVerticalGraph.verticalCurve
          (C (N13IntegralInfinityReduction.reduceBase E.a)) =
      N13IntegralInfinityReduction.reducePoly E.m *
        N13IntegralInfinityReduction.reducePoly E.w := by
  have h :=
    congrArg N13IntegralInfinityReduction.reducePoly E.curve_eq
  rw [reduce_verticalCurve] at h
  simpa [N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.s,
    N13IntegralInfinityReduction.reducePoly, hc] using h
end
end MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialConstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- In the constant-slope branch, reducing the integral infinity graph ideal
gives the literal special vertical ideal `(m̄(v),t-ā)`. -/
theorem map_infinityIdeal_of_reduce_c_eq_zero
    (E : VerticalGraph)
    (hc :
      N13IntegralInfinityReduction.reduceBase E.c = 0) :
    Ideal.map N13IntegralInfinityReduction.reduceCoordinate E.ideal =
      N13SpecialConstantInfinityVerticalGraph.verticalIdeal
        (N13IntegralInfinityReduction.reducePoly E.m)
        (N13IntegralInfinityReduction.reduceBase E.a) := by
  rw [N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.ideal,
    N13SpecialConstantInfinityVerticalGraph.verticalIdeal,
    Ideal.map_span, Set.image_pair]
  simp only [map_sub, N13IntegralInfinityReduction.reduce_tClass,
    reduce_aeval_vClass]
  congr 2
  simp [N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.s,
    N13IntegralInfinityReduction.reducePoly, hc]
  exact
    (IsScalarTower.algebraMap_apply
      K K[X] N13IntegralInfinityReduction.SpecialRing
      (N13IntegralInfinityReduction.reduceBase E.a)).symm
end
end MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialNonconstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- In the unit-slope branch, reducing the integral infinity graph ideal
gives the literal nonconstant special vertical ideal
`(m̄(v),t-(ā+v))`. -/
theorem map_infinityIdeal_of_reduce_c_eq_one
    (E : VerticalGraph)
    (hc :
      N13IntegralInfinityReduction.reduceBase E.c = 1) :
    Ideal.map N13IntegralInfinityReduction.reduceCoordinate E.ideal =
      N13SpecialNonconstantInfinityVerticalGraph.verticalIdeal
        (N13IntegralInfinityReduction.reducePoly E.m)
        (N13IntegralInfinityReduction.reduceBase E.a) := by
  rw [N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.ideal,
    N13SpecialNonconstantInfinityVerticalGraph.verticalIdeal,
    Ideal.map_span, Set.image_pair]
  simp only [map_sub, N13IntegralInfinityReduction.reduce_tClass,
    reduce_aeval_vClass]
  congr 2
  simp [N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.s,
    N13IntegralInfinityReduction.reducePoly, hc]
end
end MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- One affine contribution of an infinity root makes `x` invertible:
the root `t=0` contributes the unit ideal, while every nonzero root
contributes the relation `x=1`. -/
theorem rootAffineFactor_xUnitMod
    (a z : K) :
    N13SpecialAffineSaturation.XUnitMod
      (if a = 0 then
        (⊤ : Ideal N13SpecialDivisorCharts.SpecialAffine)
      else
        N13GoodCoordinateRingTwo.mumfordIdeal
          (X - C 1) (C z)) := by
  by_cases ha : a = 0
  · simp only [ha, if_true]
    exact N13SpecialAffineSaturation.top_xUnitMod
  · simp only [ha, if_false]
    refine ⟨1, ?_⟩
    have hgen :=
      N13GoodCoordinateRingTwo.xClass_mem_mumfordIdeal
        (X - C (1 : K)) (C z)
    have hneg :=
      (N13GoodCoordinateRingTwo.mumfordIdeal
        (X - C (1 : K)) (C z)).neg_mem hgen
    convert hneg using 1
    simp [N13SpecialCurveOverlap.xClass]
end
end MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The affine ideal of the completed divisor of any monic quadratic
special infinity graph makes `x` invertible modulo the ideal. -/
theorem graphDivisor_affine_xUnitMod
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    N13SpecialAffineSaturation.XUnitMod
      (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialInfinityGraphDivisor.graphDivisor D hdeg)).affineIdeal := by
  rw [
    N13SpecialInfinityGraphDivisorCharts.ofDivisor_graphDivisor_affineIdeal]
  let z := N13SpecialInfinityGraphDivisor.rootPair D hdeg
  change
    N13SpecialAffineSaturation.XUnitMod
      (N13SpecialInfinityGraphDivisorCharts.rootAffineIdeal D z)
  induction z using Sym2.ind with
  | _ a b =>
      rw [N13SpecialInfinityGraphDivisorCharts.rootAffineIdeal_mk]
      exact
        N13SpecialAffineSaturation.mul_xUnitMod
          (rootAffineFactor_xUnitMod a (D.v.eval a))
          (rootAffineFactor_xUnitMod b (D.v.eval b))
end
end MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialConstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialVerticalDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- If the vertical slope reduces to zero, the complete reduced two-chart
line is the canonical fibre over the constant special coordinate `t=ā`. -/
theorem restrict_twoChartLine_of_reduce_c_eq_zero
    (u : R₂[X])
    (E : VerticalGraph)
    (hu : u.Monic)
    (huDegree : u.natDegree = 2)
    (hmDegree : E.m.natDegree = 2)
    (huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal)
    (hc :
      N13IntegralInfinityReduction.reduceBase E.c = 0) :
    N13TwoChartSpecialRestriction.restrict
        (N13IntegralInfinityVerticalGraphTwoChart.twoChartLine
          u E hu huDegree hmDegree huMem) =
      N13SpecialDivisorCharts.ofDivisor
        (N13SpecialVerticalDivisorCharts.constantInfinityFibreDivisor
          (N13IntegralInfinityReduction.reduceBase E.a)) := by
  apply
    HuangN13.N13SpecialAffineSaturation.chartPair_eq_of_infinityIdeal_eq
  · apply
      N13SpecialAffineSaturation.map_reduceCoordinate_xUnitMod
    exact
      N13IntegralInfinityVerticalGraphTwoChart.affineIdeal_xUnitMod
        u E hu huDegree
  · exact
      HuangN13.N13IntegralInfinityVerticalGraphSpecialRestriction.constantInfinityFibre_affine_xUnitMod
        (N13IntegralInfinityReduction.reduceBase E.a)
  · change
      Ideal.map N13IntegralInfinityReduction.reduceCoordinate E.ideal =
        (N13SpecialDivisorCharts.ofDivisor
          (N13SpecialVerticalDivisorCharts.constantInfinityFibreDivisor
            (N13IntegralInfinityReduction.reduceBase E.a))).infinityIdeal
    rw [map_infinityIdeal_of_reduce_c_eq_zero E hc,
      N13SpecialConstantInfinityVerticalGraph.verticalIdeal_eq_span
        (N13IntegralInfinityReduction.reducePoly E.m)
        (N13IntegralInfinityReduction.reducePoly E.w)
        (N13IntegralInfinityReduction.reduceBase E.a)
        (reduced_m_monic E)
        (reduced_m_natDegree E hmDegree)
        (reduced_curve_eq_of_reduce_c_eq_zero E hc),
      N13SpecialVerticalDivisorCharts.constantInfinityFibreDivisor_infinityIdeal]
end
end MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialConstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityGraphDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialNonconstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- If the vertical slope reduces to one, the complete reduced two-chart
line is the canonical completed divisor of the translated horizontal graph
`m̄(t+ā)=0, v=t+ā`. -/
theorem restrict_twoChartLine_of_reduce_c_eq_one
    (u : R₂[X])
    (E : VerticalGraph)
    (hu : u.Monic)
    (huDegree : u.natDegree = 2)
    (hmDegree : E.m.natDegree = 2)
    (huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal)
    (hc :
      N13IntegralInfinityReduction.reduceBase E.c = 1) :
    let mbar := N13IntegralInfinityReduction.reducePoly E.m
    let wbar := N13IntegralInfinityReduction.reducePoly E.w
    let abar := N13IntegralInfinityReduction.reduceBase E.a
    let hcurve :
        N13SpecialConstantInfinityVerticalGraph.verticalCurve
            (C abar + X) =
          mbar * wbar :=
      reduced_curve_eq_of_reduce_c_eq_one E hc
    let D :=
      N13SpecialNonconstantInfinityVerticalGraph.horizontalGraph
        mbar wbar abar (reduced_m_monic E) hcurve
    let hDdeg : D.u.natDegree = 2 :=
      N13SpecialNonconstantInfinityVerticalGraph.horizontalGraph_u_natDegree
        mbar wbar abar (reduced_m_monic E)
          (reduced_m_natDegree E hmDegree) hcurve
    N13TwoChartSpecialRestriction.restrict
        (N13IntegralInfinityVerticalGraphTwoChart.twoChartLine
          u E hu huDegree hmDegree huMem) =
      N13SpecialDivisorCharts.ofDivisor
        (N13SpecialInfinityGraphDivisor.graphDivisor D hDdeg) := by
  dsimp only
  apply
    HuangN13.N13SpecialAffineSaturation.chartPair_eq_of_infinityIdeal_eq
  · apply
      N13SpecialAffineSaturation.map_reduceCoordinate_xUnitMod
    exact
      N13IntegralInfinityVerticalGraphTwoChart.affineIdeal_xUnitMod
        u E hu huDegree
  · exact graphDivisor_affine_xUnitMod _ _
  · change
      Ideal.map N13IntegralInfinityReduction.reduceCoordinate E.ideal =
        (N13SpecialDivisorCharts.ofDivisor
          (N13SpecialInfinityGraphDivisor.graphDivisor _ _)).infinityIdeal
    rw [map_infinityIdeal_of_reduce_c_eq_one E hc,
      N13SpecialNonconstantInfinityVerticalGraph.verticalIdeal_eq_graphIdeal,
      HuangN13.N13SpecialInfinityGraphDivisorCharts.ofDivisor_graphDivisor_infinityIdeal]
    rfl
end
end MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialConstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- Every integral vertical graph line reduces to the chart pair of a
literal effective degree-two divisor.  Over `F₂` the reduced slope is
either zero, giving a constant fibre, or one, giving the translated
horizontal graph divisor. -/
theorem exists_specialDivisor
    (u : R₂[X])
    (E : VerticalGraph)
    (hu : u.Monic)
    (huDegree : u.natDegree = 2)
    (hmDegree : E.m.natDegree = 2)
    (huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal) :
    ∃ Δ : N13SpecialDivisorCharts.EffectiveDivisorTwo,
      N13TwoChartSpecialRestriction.restrict
          (N13IntegralInfinityVerticalGraphTwoChart.twoChartLine
            u E hu huDegree hmDegree huMem) =
        N13SpecialDivisorCharts.ofDivisor Δ := by
  rcases
      N13GoodModelTwo.fixedTwo_eq_zero_or_one
        (N13IntegralInfinityReduction.reduceBase E.c)
        (ZMod.pow_card
          (N13IntegralInfinityReduction.reduceBase E.c)) with hc | hc
  · refine
      ⟨N13SpecialVerticalDivisorCharts.constantInfinityFibreDivisor
          (N13IntegralInfinityReduction.reduceBase E.a), ?_⟩
    exact
      restrict_twoChartLine_of_reduce_c_eq_zero
        u E hu huDegree hmDegree huMem hc
  · let mbar := N13IntegralInfinityReduction.reducePoly E.m
    let wbar := N13IntegralInfinityReduction.reducePoly E.w
    let abar := N13IntegralInfinityReduction.reduceBase E.a
    let hcurve :
        N13SpecialConstantInfinityVerticalGraph.verticalCurve
            (C abar + X) =
          mbar * wbar :=
      reduced_curve_eq_of_reduce_c_eq_one E hc
    let D :=
      N13SpecialNonconstantInfinityVerticalGraph.horizontalGraph
        mbar wbar abar (reduced_m_monic E) hcurve
    let hDdeg : D.u.natDegree = 2 :=
      N13SpecialNonconstantInfinityVerticalGraph.horizontalGraph_u_natDegree
        mbar wbar abar (reduced_m_monic E)
          (reduced_m_natDegree E hmDegree) hcurve
    refine
      ⟨N13SpecialInfinityGraphDivisor.graphDivisor D hDdeg, ?_⟩
    simpa [mbar, wbar, abar, hcurve, D, hDdeg] using
      (restrict_twoChartLine_of_reduce_c_eq_one
        u E hu huDegree hmDegree huMem hc)
end
end MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
end
end


set_option autoImplicit false
open Polynomial
open scoped Sym2
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem solution
    (u : MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.R₂[X])
    (E : MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.VerticalGraph)
    (hu : u.Monic)
    (huDegree : u.natDegree = 2)
    (hmDegree : E.m.natDegree = 2)
    (huMem :
      MazurProof.N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal) :
    ∃ Δ : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo,
      MazurProof.N13TwoChartSpecialRestriction.restrict
          (MazurProof.N13IntegralInfinityVerticalGraphTwoChart.twoChartLine
            u E hu huDegree hmDegree huMem) =
        MazurProof.N13SpecialDivisorCharts.ofDivisor Δ := by
  exact MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.exists_specialDivisor u E hu huDegree hmDegree huMem
