-- Prove2me | solution 1 for HuangN13.N13IntegralInfinityGraphSpecialRestriction.restrict_twoChartLine
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:01:19.576986+00:00
-- url     : https://prove2.me/submissions/a5619065-c57f-4c4b-b83e-41287e74e7a8

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_InfinityGraphLineCore
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_yClass_relation
import Theorems.Thm_MazurProof_N13SpecialInfinityGraphDivisor_curveEquationAtRoot
import Theorems.Thm_MazurProof_N13SpecialInfinityGraphDivisor_degreeTwo_splits
import Theorems.Thm_MazurProof_N13SpecialInfinityGraphDivisorCharts_yClass_relation

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
@[simp] theorem xClass_add (p q : K[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q
end
end MazurProof.N13GoodCoordinateRingTwo
end
end

section
section
set_option autoImplicit false
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
/-- The two graph generators multiply to the negative Cantor quotient. -/
theorem ySubClass_mul_conjugate (D : SemiMumford) :
    ySubClass D.v * ySubClass (conjugateV D.v) =
      -(xClass D.u * xClass D.w) := by
  calc
    ySubClass D.v * ySubClass (conjugateV D.v) =
        yClass ^ 2 + xClass hPoly * yClass -
          (xClass D.v ^ 2 + xClass hPoly * xClass D.v) := by
      simp only [ySubClass, conjugateV, xClass_neg, xClass_sub]
      ring
    _ = xClass rhsPoly -
          xClass (D.v ^ 2 + hPoly * D.v) := by
      rw [yClass_relation, xClass_add, xClass_mul, xClass_pow]
    _ = -xClass (D.v ^ 2 + hPoly * D.v - rhsPoly) := by
      rw [xClass_sub]
      ring
    _ = -xClass (D.u * D.w) := by rw [D.curve_eq]
    _ = -(xClass D.u * xClass D.w) := by rw [xClass_mul]
end
end MazurProof.N13GoodCoordinateRingTwo
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
/-- Two graph ideals with coprime horizontal equations multiply to the
graph ideal of the product.  The common ordinate is only required modulo
the two factors, so this is the ideal-theoretic Chinese remainder theorem
for a split divisor. -/
theorem graphIdeal_mul_of_coprime
    (xClass : R[X] →+* A) (yClass : A)
    (u₁ u₂ v₁ v₂ V : R[X])
    (h₁ : u₁ ∣ V - v₁)
    (h₂ : u₂ ∣ V - v₂)
    (hcoprime :
      ∃ a b : R[X], a * u₁ + b * u₂ = 1) :
    graphIdeal xClass yClass u₁ v₁ *
        graphIdeal xClass yClass u₂ v₂ =
      graphIdeal xClass yClass (u₁ * u₂) V := by
  rw [← graphIdeal_eq_of_dvd_sub xClass yClass u₁ v₁ V h₁,
    ← graphIdeal_eq_of_dvd_sub xClass yClass u₂ v₂ V h₂]
  let I₁ := graphIdeal xClass yClass u₁ V
  let I₂ := graphIdeal xClass yClass u₂ V
  let I := graphIdeal xClass yClass (u₁ * u₂) V
  let g := ySubClass xClass yClass V
  apply le_antisymm
  · rw [graphIdeal, graphIdeal, graphIdeal,
      Ideal.span_pair_mul_span_pair]
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.subset_span (by simp [map_mul])
    · exact Ideal.mul_mem_left I (xClass u₁)
        (ySubClass_mem_graphIdeal xClass yClass (u₁ * u₂) V)
    · exact Ideal.mul_mem_right (xClass u₂) _
        (Ideal.subset_span
          (Set.mem_insert_iff.mpr
            (Or.inr (Set.mem_singleton _))))
    · exact Ideal.mul_mem_left I g
        (ySubClass_mem_graphIdeal xClass yClass (u₁ * u₂) V)
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [map_mul]
      exact Ideal.mul_mem_mul
        (xClass_mem_graphIdeal xClass yClass u₁ V)
        (xClass_mem_graphIdeal xClass yClass u₂ V)
    · obtain ⟨a, b, hab⟩ := hcoprime
      have h₁g :
          xClass u₁ * g ∈ I₁ * I₂ :=
        Ideal.mul_mem_mul
          (xClass_mem_graphIdeal xClass yClass u₁ V)
          (ySubClass_mem_graphIdeal xClass yClass u₂ V)
      have hg₂ :
          g * xClass u₂ ∈ I₁ * I₂ :=
        Ideal.mul_mem_mul
          (ySubClass_mem_graphIdeal xClass yClass u₁ V)
          (xClass_mem_graphIdeal xClass yClass u₂ V)
      have ha :
          xClass a * (xClass u₁ * g) ∈ I₁ * I₂ :=
        Ideal.mul_mem_left _ (xClass a) h₁g
      have hb :
          xClass b * (g * xClass u₂) ∈ I₁ * I₂ :=
        Ideal.mul_mem_left _ (xClass b) hg₂
      have hsum := Ideal.add_mem (I₁ * I₂) ha hb
      have heq :
          xClass a * (xClass u₁ * g) +
              xClass b * (g * xClass u₂) = g := by
        calc
          _ = xClass (a * u₁ + b * u₂) * g := by
            simp only [map_add, map_mul]
            ring
          _ = g := by rw [hab, map_one, one_mul]
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
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem reduce_integralBaseClass (p : IntegralBase) :
    reduceCoordinate (integralBaseClass p) =
      specialBaseClass (reducePoly p) := by
  exact AdjoinRoot.map_of
    reducePoly
    N13IntegralInfinityChart.infinityCurvePoly
    N13SpecialInfinityChart.curvePoly
    special_curve_dvd p
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
/-- Compatible chart pairs are equal once their two chart ideals agree.

The overlap field is a proposition, so proof irrelevance removes it after
the affine and infinity ideals have been identified. -/
@[ext] theorem ChartPair.ext
    {L M : ChartPair}
    (haffine : L.affineIdeal = M.affineIdeal)
    (hinfinity : L.infinityIdeal = M.infinityIdeal) :
    L = M := by
  cases L
  cases M
  simp_all
end
end MazurProof.N13TwoChartSpecialRestriction
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
attribute [local instance] MazurProof.N13SpecialGraphDivisorCharts.instFactPrimeOfNatNat_fLT
/-- On the special N13 fibre, a repeated-root graph ideal is the square
of its point ideal.  The key local unit is `h(a) = 1` for every `a ∈ F₂`. -/
theorem pointIdeal_sq_eq_mumfordIdeal_of_square
    (D : N13GoodCoordinateRingTwo.SemiMumford)
    (a : K)
    (hfactor : D.u = (X - C a) ^ 2) :
    N13GoodCoordinateRingTwo.mumfordIdeal
          (X - C a) (C (D.v.eval a)) ^ 2 =
      N13GoodCoordinateRingTwo.mumfordIdeal D.u D.v := by
  let p : K[X] := X - C a
  let z : K := D.v.eval a
  let I : Ideal CoordinateRing := mumfordIdeal p D.v
  let J : Ideal CoordinateRing := mumfordIdeal (p ^ 2) D.v
  let g : CoordinateRing := ySubClass D.v
  let plus : CoordinateRing := ySubClass (conjugateV D.v)
  have hdiv : p ∣ D.v - C z := by
    simpa [p, z] using
      (X_sub_C_dvd_sub_C_eval (p := D.v) (a := a))
  have hgraph :
      mumfordIdeal p D.v = mumfordIdeal p (C z) := by
    simpa [mumfordIdeal, GeneralizedGraphIdealCore.graphIdeal,
      ySubClass, GeneralizedGraphIdealCore.ySubClass] using
      (GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
        xClassHom yClass p (C z) D.v hdiv)
  have hpI : xClass p ∈ I :=
    xClass_mem_mumfordIdeal p D.v
  have hgI : g ∈ I := by
    exact ySubClass_mem_mumfordIdeal p D.v
  have hp2I : xClass (p ^ 2) ∈ I ^ 2 := by
    rw [xClass_pow]
    simpa only [pow_two] using Ideal.mul_mem_mul hpI hpI
  have hggI : g * g ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hgI hgI
  have hproduct :
      g * plus = -(xClass (p ^ 2) * xClass D.w) := by
    change
      ySubClass D.v * ySubClass (conjugateV D.v) =
        -(xClass (p ^ 2) * xClass D.w)
    rw [N13GoodCoordinateRingTwo.ySubClass_mul_conjugate D,
      hfactor]
  have hplusgI : plus * g ∈ I ^ 2 := by
    rw [mul_comm, hproduct]
    exact
      (I ^ 2).neg_mem
        (Ideal.mul_mem_right (xClass D.w) _ hp2I)
  have hvv : xClass D.v + xClass D.v = 0 := by
    rw [← xClass_add]
    have htwoPoly : (2 : K[X]) = 0 :=
      CharP.cast_eq_zero (K[X]) 2
    have hvvPoly : D.v + D.v = 0 := by
      calc
        D.v + D.v = 2 * D.v := by ring
        _ = 0 := by rw [htwoPoly, zero_mul]
    rw [hvvPoly, xClass_zero]
  have hplus_sub_g : plus - g = xClass hPoly := by
    simp only [plus, g, conjugateV, ySubClass, xClass_neg,
      xClass_sub]
    linear_combination hvv
  have hhEval : hPoly.eval a = 1 := by
    simp only [hPoly, eval_add, eval_pow, eval_X, eval_one]
    fin_cases a <;> decide
  have hhdiv : p ∣ hPoly - C 1 := by
    simpa [p, hhEval] using
      (X_sub_C_dvd_sub_C_eval (p := hPoly) (a := a))
  have hpgI : xClass p * g ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hpI hgI
  have hdeltaG : xClass (hPoly - C 1) * g ∈ I ^ 2 := by
    obtain ⟨s, hs⟩ := hhdiv
    rw [hs, xClass_mul]
    convert Ideal.mul_mem_left (I ^ 2) (xClass s) hpgI using 1
    ring
  have hhgI : xClass hPoly * g ∈ I ^ 2 := by
    rw [← hplus_sub_g]
    convert Ideal.sub_mem (I ^ 2) hplusgI hggI using 1
    ring
  have hgSq : g ∈ I ^ 2 := by
    have hmem := Ideal.sub_mem (I ^ 2) hhgI hdeltaG
    have heq :
        xClass hPoly * g -
            xClass (hPoly - C 1) * g = g := by
      rw [xClass_sub]
      have hcOne : xClass (C (1 : K)) = 1 := rfl
      rw [hcOne]
      ring
    rw [heq] at hmem
    exact hmem
  have hIJ : I ^ 2 = J := by
    apply le_antisymm
    · change mumfordIdeal p D.v ^ 2 ≤ J
      rw [pow_two, mumfordIdeal, Ideal.span_pair_mul_span_pair]
      apply Ideal.span_le.mpr
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      have hp2J : xClass (p ^ 2) ∈ J :=
        xClass_mem_mumfordIdeal (p ^ 2) D.v
      have hgJ : g ∈ J := by
        exact ySubClass_mem_mumfordIdeal (p ^ 2) D.v
      rcases ht with rfl | rfl | rfl | rfl
      · rw [← xClass_mul, ← pow_two]
        exact hp2J
      · exact Ideal.mul_mem_left J (xClass p) hgJ
      · exact Ideal.mul_mem_right (xClass p) J hgJ
      · exact Ideal.mul_mem_left J g hgJ
    · change mumfordIdeal (p ^ 2) D.v ≤ I ^ 2
      rw [mumfordIdeal]
      apply Ideal.span_le.mpr
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · exact hp2I
      · exact hgSq
  calc
    mumfordIdeal p (C z) ^ 2 = I ^ 2 := by
      change mumfordIdeal p (C z) ^ 2 = mumfordIdeal p D.v ^ 2
      rw [hgraph]
    _ = J := hIJ
    _ = mumfordIdeal D.u D.v := by rw [hfactor]
end
end MazurProof.N13SpecialGraphDivisorCharts
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
attribute [local instance] MazurProof.N13SpecialGraphDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The symmetric-pair construction agrees with the product over its
two-element multiset. -/
theorem rootPolynomial_eq_prod (z : Sym2 K) :
    rootPolynomial z =
      (z.toMultiset.map (fun a => X - C a)).prod := by
  induction z using Sym2.ind with
  | _ a b =>
      simp [rootPolynomial, Sym2.toMultiset]
end
end MazurProof.N13SpecialGraphDivisorCharts
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
open scoped Sym2
namespace MazurProof.N13SpecialInfinityGraphDivisorCharts
noncomputable section
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityGraphDivisorCharts.instFactPrimeOfNatNat_fLT
/-- A special infinity point ideal is the graph ideal of its linear
`t`-factor and constant vertical value. -/
theorem infinityPointIdeal_eq_graphIdeal
    (a z : K) :
    N13SpecialDivisorCharts.infinityPointIdeal a z =
      graphIdeal (X - C a) (C z) := by
  simp [N13SpecialDivisorCharts.infinityPointIdeal,
    graphIdeal, GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass,
    xClassHom, yClass,
    N13SpecialInfinityChart.tClass]
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
/-- At a repeated `F₂`-root, the squared linear graph ideal is the
quadratic graph ideal. -/
theorem pointIdeal_sq_eq_graphIdeal_of_square
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (a : K)
    (hfactor : D.u = (X - C a) ^ 2) :
    graphIdeal (X - C a) (C (D.v.eval a)) ^ 2 =
      graphIdeal D.u D.v := by
  let p : K[X] := X - C a
  let z : K := D.v.eval a
  let I : Ideal Ring := graphIdeal p D.v
  let J : Ideal Ring := graphIdeal (p ^ 2) D.v
  let g : Ring := ySubClass D.v
  let plus : Ring :=
    ySubClass
      (GeneralizedGraphIdealCore.conjugateV
        N13SpecialInfinityChart.hPoly D.v)
  have hdiv : p ∣ D.v - C z := by
    simpa [p, z] using
      (X_sub_C_dvd_sub_C_eval (p := D.v) (a := a))
  have hgraph :
      graphIdeal p D.v = graphIdeal p (C z) := by
    exact
      GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
        xClassHom yClass p (C z) D.v hdiv
  have hpI : xClassHom p ∈ I :=
    GeneralizedGraphIdealCore.xClass_mem_graphIdeal
      xClassHom yClass p D.v
  have hgI : g ∈ I :=
    GeneralizedGraphIdealCore.ySubClass_mem_graphIdeal
      xClassHom yClass p D.v
  have hp2I : xClassHom (p ^ 2) ∈ I ^ 2 := by
    rw [map_pow]
    simpa only [pow_two] using Ideal.mul_mem_mul hpI hpI
  have hggI : g * g ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hgI hgI
  have hproduct :
      g * plus = -(xClassHom (p ^ 2) * xClassHom D.w) := by
    change
      GeneralizedGraphIdealCore.ySubClass
            xClassHom yClass D.v *
          GeneralizedGraphIdealCore.ySubClass
            xClassHom yClass
              (GeneralizedGraphIdealCore.conjugateV
                N13SpecialInfinityChart.hPoly D.v) =
        -(xClassHom (p ^ 2) * xClassHom D.w)
    rw [GeneralizedGraphIdealCore.ySubClass_mul_conjugate
      xClassHom yClass
      N13SpecialInfinityChart.hPoly
      N13SpecialInfinityChart.rhsPoly
      D.toSemiGraph yClass_relation, hfactor]
  have hplusgI : plus * g ∈ I ^ 2 := by
    rw [mul_comm, hproduct]
    exact
      (I ^ 2).neg_mem
        (Ideal.mul_mem_right (xClassHom D.w) _ hp2I)
  have hvv : xClassHom D.v + xClassHom D.v = 0 := by
    rw [← map_add]
    have htwoPoly : (2 : K[X]) = 0 :=
      CharP.cast_eq_zero (K[X]) 2
    have hvvPoly : D.v + D.v = 0 := by
      calc
        D.v + D.v = 2 * D.v := by ring
        _ = 0 := by rw [htwoPoly, zero_mul]
    rw [hvvPoly, map_zero]
  have hplus_sub_g :
      plus - g =
        xClassHom N13SpecialInfinityChart.hPoly := by
    simp only [plus, g, ySubClass,
      GeneralizedGraphIdealCore.ySubClass,
      GeneralizedGraphIdealCore.conjugateV,
      map_neg, map_sub]
    linear_combination hvv
  have hhEval :
      N13SpecialInfinityChart.hPoly.eval a = 1 := by
    simp only [N13SpecialInfinityChart.hPoly,
      eval_add, eval_pow, eval_X, eval_one]
    fin_cases a <;> decide
  have hhdiv :
      p ∣ N13SpecialInfinityChart.hPoly - C 1 := by
    simpa [p, hhEval] using
      (X_sub_C_dvd_sub_C_eval
        (p := N13SpecialInfinityChart.hPoly) (a := a))
  have hpgI : xClassHom p * g ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hpI hgI
  have hdeltaG :
      xClassHom (N13SpecialInfinityChart.hPoly - C 1) * g ∈
        I ^ 2 := by
    obtain ⟨s, hs⟩ := hhdiv
    rw [hs, map_mul]
    convert Ideal.mul_mem_left (I ^ 2) (xClassHom s) hpgI using 1
    ring
  have hhgI :
      xClassHom N13SpecialInfinityChart.hPoly * g ∈ I ^ 2 := by
    rw [← hplus_sub_g]
    convert Ideal.sub_mem (I ^ 2) hplusgI hggI using 1
    ring
  have hgSq : g ∈ I ^ 2 := by
    have hmem := Ideal.sub_mem (I ^ 2) hhgI hdeltaG
    have heq :
        xClassHom N13SpecialInfinityChart.hPoly * g -
            xClassHom
                (N13SpecialInfinityChart.hPoly - C 1) * g =
          g := by
      rw [map_sub]
      have hcOne : xClassHom (C (1 : K)) = 1 := rfl
      rw [hcOne]
      ring
    rw [heq] at hmem
    exact hmem
  have hIJ : I ^ 2 = J := by
    apply le_antisymm
    · change graphIdeal p D.v ^ 2 ≤ J
      rw [pow_two, graphIdeal,
        GeneralizedGraphIdealCore.graphIdeal,
        Ideal.span_pair_mul_span_pair]
      apply Ideal.span_le.mpr
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      have hp2J : xClassHom (p ^ 2) ∈ J :=
        GeneralizedGraphIdealCore.xClass_mem_graphIdeal
          xClassHom yClass (p ^ 2) D.v
      have hgJ : g ∈ J :=
        GeneralizedGraphIdealCore.ySubClass_mem_graphIdeal
          xClassHom yClass (p ^ 2) D.v
      rcases ht with rfl | rfl | rfl | rfl
      · rw [← map_mul, ← pow_two]
        exact hp2J
      · exact Ideal.mul_mem_left J (xClassHom p) hgJ
      · exact Ideal.mul_mem_right (xClassHom p) J hgJ
      · exact Ideal.mul_mem_left J g hgJ
    · change graphIdeal (p ^ 2) D.v ≤ I ^ 2
      rw [graphIdeal, GeneralizedGraphIdealCore.graphIdeal]
      apply Ideal.span_le.mpr
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · exact hp2I
      · exact hgSq
  calc
    graphIdeal p (C z) ^ 2 = I ^ 2 := by
      change graphIdeal p (C z) ^ 2 =
        graphIdeal p D.v ^ 2
      rw [hgraph]
    _ = J := hIJ
    _ = graphIdeal D.u D.v := by rw [hfactor]
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
/-- A root of an infinity-chart graph gives a completed special point. -/
def graphRootPoint
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (a : K) (ha : D.u.IsRoot a) :
    N13SpecialDivisorCharts.CurvePoint :=
  if ha0 : a = 0 then
    Sum.inr
      ⟨D.v.eval a, by
        subst a
        exact
          N13SpecialInfinityGraphDivisor.curveEquationAtRoot D ha⟩
  else
    Sum.inl
      ⟨(1, D.v.eval a), by
        have ha1 : a = 1 :=
          (N13GoodModelTwo.fixedTwo_eq_zero_or_one
            a (ZMod.pow_card a)).resolve_left ha0
        subst a
        simpa using
          (N13GoodModelTwo.affine_iff_infinity_on_overlap
            (show (1 : K) * 1 = 1 by simp)).mpr
            (N13SpecialInfinityGraphDivisor.curveEquationAtRoot D ha)⟩
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
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityGraphDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The completed point attached to a graph root has the corresponding
linear infinity graph ideal. -/
theorem graphRootPoint_infinityIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (a : K) (ha : D.u.IsRoot a) :
    (N13SpecialDivisorCharts.point
        (graphRootPoint D a ha)).infinityIdeal =
      graphIdeal (X - C a) (C (D.v.eval a)) := by
  have hpoint :
      (N13SpecialDivisorCharts.point
          (graphRootPoint D a ha)).infinityIdeal =
        N13SpecialDivisorCharts.infinityPointIdeal
          a (D.v.eval a) := by
    rw [graphRootPoint]
    split
    · subst a
      rw [N13SpecialDivisorCharts.point.eq_def]
      rfl
    · have ha1 : a = 1 :=
        (N13GoodModelTwo.fixedTwo_eq_zero_or_one
          a (ZMod.pow_card a)).resolve_left ‹a ≠ 0›
      change
        N13SpecialDivisorCharts.infinityPointIdeal
            1 (D.v.eval a) =
          N13SpecialDivisorCharts.infinityPointIdeal
            a (D.v.eval a)
      rw [ha1]
  rw [hpoint, infinityPointIdeal_eq_graphIdeal]
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
/-- The product of the two point ideals of a split graph is its quadratic
infinity graph ideal. -/
theorem ofDivisor_graphRoots_infinityIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (z : Sym2 K)
    (hz : ∀ a ∈ z, D.u.IsRoot a)
    (hfactor :
      D.u = N13SpecialGraphDivisorCharts.rootPolynomial z) :
    (N13SpecialDivisorCharts.ofDivisor
        (Sym2.pmap (graphRootPoint D) z hz)).infinityIdeal =
      graphIdeal D.u D.v := by
  induction z using Sym2.ind with
  | _ a b =>
      rw [Sym2.pmap_pair,
        N13SpecialDivisorCharts.ofDivisor_mk]
      change
        (N13SpecialDivisorCharts.point
            (graphRootPoint D a
              (hz a (Sym2.mem_mk_left a b)))).infinityIdeal *
          (N13SpecialDivisorCharts.point
            (graphRootPoint D b
              (hz b (Sym2.mem_mk_right a b)))).infinityIdeal =
        graphIdeal D.u D.v
      rw [graphRootPoint_infinityIdeal,
        graphRootPoint_infinityIdeal]
      by_cases hab : a = b
      · subst b
        simpa only [pow_two] using
          (pointIdeal_sq_eq_graphIdeal_of_square D a
            (by
              simpa only [
                N13SpecialGraphDivisorCharts.rootPolynomial_mk,
                pow_two] using hfactor))
      · have hleft :
            X - C a ∣ D.v - C (D.v.eval a) :=
          X_sub_C_dvd_sub_C_eval
        have hright :
            X - C b ∣ D.v - C (D.v.eval b) :=
          X_sub_C_dvd_sub_C_eval
        have hd : b - a ≠ 0 :=
          sub_ne_zero.mpr (Ne.symm hab)
        have hcop :
            ∃ A B : K[X],
              A * (X - C a) + B * (X - C b) = 1 := by
          refine
            ⟨C ((b - a)⁻¹), -C ((b - a)⁻¹), ?_⟩
          calc
            C ((b - a)⁻¹) * (X - C a) +
                  -C ((b - a)⁻¹) * (X - C b) =
                C ((b - a)⁻¹) * C (b - a) := by
              rw [map_sub]
              ring
            _ = 1 := by
              rw [← map_mul, inv_mul_cancel₀ hd, map_one]
        rw [hfactor]
        exact
          GeneralizedGraphIdealCore.graphIdeal_mul_of_coprime
            xClassHom yClass
            (X - C a) (X - C b)
            (C (D.v.eval a)) (C (D.v.eval b)) D.v
            hleft hright hcop
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
attribute [local instance] MazurProof.N13SpecialGraphDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityGraphDivisor.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityGraphDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The polynomial reconstructed from the chosen infinity roots is the
original monic quadratic. -/
theorem rootPolynomial_rootPair
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    N13SpecialGraphDivisorCharts.rootPolynomial
        (N13SpecialInfinityGraphDivisor.rootPair D hdeg) =
      D.u := by
  calc
    N13SpecialGraphDivisorCharts.rootPolynomial
          (N13SpecialInfinityGraphDivisor.rootPair D hdeg) =
        ((N13SpecialInfinityGraphDivisor.rootPair D hdeg).toMultiset.map
          (fun a => X - C a)).prod :=
      N13SpecialGraphDivisorCharts.rootPolynomial_eq_prod _
    _ = (D.u.roots.map (fun a => X - C a)).prod := by
      rw [N13SpecialInfinityGraphDivisor.rootPair_toMultiset]
    _ = D.u :=
      (Polynomial.Splits.eq_prod_roots_of_monic
        (N13SpecialInfinityGraphDivisor.degreeTwo_splits D hdeg)
        D.u_monic).symm
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
attribute [local instance] MazurProof.N13SpecialGraphDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The canonical infinity ideal of the divisor cut out by a monic
quadratic infinity graph is exactly that graph ideal. -/
theorem ofDivisor_graphDivisor_infinityIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialInfinityGraphDivisor.graphDivisor D hdeg)).infinityIdeal =
      graphIdeal D.u D.v := by
  unfold N13SpecialInfinityGraphDivisor.graphDivisor
  let hz :
      ∀ a ∈ N13SpecialInfinityGraphDivisor.rootPair D hdeg,
        D.u.IsRoot a :=
    fun a ha =>
      (N13SpecialInfinityGraphDivisor.mem_rootPair_iff_isRoot
        D hdeg a).mp ha
  have hpmap :
      Sym2.pmap
          (N13SpecialInfinityGraphDivisor.rootPoint D hdeg)
          (N13SpecialInfinityGraphDivisor.rootPair D hdeg)
          (fun _ ha => ha) =
        Sym2.pmap
          (graphRootPoint D)
          (N13SpecialInfinityGraphDivisor.rootPair D hdeg)
          hz := by
    apply Sym2.ext
    intro P
    rw [Sym2.mem_pmap_iff, Sym2.mem_pmap_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
  rw [hpmap]
  exact
    ofDivisor_graphRoots_infinityIdeal D
      (N13SpecialInfinityGraphDivisor.rootPair D hdeg)
      hz (rootPolynomial_rootPair D hdeg).symm
end
end MazurProof.N13SpecialInfinityGraphDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityGraphSpecialRestriction
noncomputable section
/-- The residue field on both special charts. -/
abbrev K := N13SpecialInfinityChart.K
end
end MazurProof.N13IntegralInfinityGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
theorem eval_one_reflect
    (p : K[X]) (n : ℕ) (hp : p.natDegree ≤ n) :
    (p.reflect n).eval 1 = p.eval 1 := by
  letI : Invertible (1 : K) := invertibleOne
  simpa using
    (Polynomial.eval₂_reflect_mul_pow
      (RingHom.id K) (1 : K) n p hp)
end
end MazurProof.N13IntegralInfinityGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13SpecialGraphDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- Weighted reflection sends two finite infinity roots to their reciprocal
affine factors. -/
theorem reflect_rootPolynomial_mk (a b : K) :
    (N13SpecialGraphDivisorCharts.rootPolynomial s(a, b)).reflect 2 =
      (1 - C a * X) * (1 - C b * X) := by
  rw [N13SpecialGraphDivisorCharts.rootPolynomial_mk,
    reflect_mul (F := 1) (G := 1)
      (X - C a) (X - C b) (by compute_degree) (by compute_degree),
    reflect_sub, reflect_sub]
  simp
end
end MazurProof.N13IntegralInfinityGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- In characteristic two the reciprocal linear factor `1-X` equals
`X-1`. -/
@[simp] theorem one_sub_X_eq_X_sub_one :
    (1 : K[X]) - X = X - 1 := by
  rw [ZModModule.sub_eq_add, ZModModule.sub_eq_add, add_comm]
end
end MazurProof.N13IntegralInfinityGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13SpecialGraphDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityGraphDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
theorem reflected_affineIdeal_eq_rootAffineIdeal_of_rootPolynomial
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (z : Sym2 K)
    (hv : D.v.natDegree ≤ 3)
    (hfactor :
      D.u =
        N13SpecialGraphDivisorCharts.rootPolynomial z)
    (haff :
      D.v.reflect 3 ^ 2 +
          N13GoodCoordinateRingTwo.hPoly * D.v.reflect 3 -
          N13GoodCoordinateRingTwo.rhsPoly =
        D.u.reflect 2 * D.w.reflect 4) :
    N13GoodCoordinateRingTwo.mumfordIdeal
        (D.u.reflect 2) (D.v.reflect 3) =
      N13SpecialInfinityGraphDivisorCharts.rootAffineIdeal D
        z := by
  induction z using Sym2.ind with
  | _ a b =>
      rcases
          N13GoodModelTwo.fixedTwo_eq_zero_or_one
            a (ZMod.pow_card a) with rfl | rfl <;>
        rcases
          N13GoodModelTwo.fixedTwo_eq_zero_or_one
            b (ZMod.pow_card b) with rfl | rfl
      · have hu : D.u.reflect 2 = 1 := by
          rw [hfactor]
          rw [reflect_rootPolynomial_mk]
          simp
        rw [hu, N13SpecialInfinityGraphDivisorCharts.rootAffineIdeal_mk]
        simp
        apply (Ideal.eq_top_iff_one _).mpr
        exact
          N13GoodCoordinateRingTwo.xClass_mem_mumfordIdeal
            1 (D.v.reflect 3)
      · have hu :
            D.u.reflect 2 = X - C (1 : K) := by
          rw [hfactor]
          rw [reflect_rootPolynomial_mk]
          simp [one_sub_X_eq_X_sub_one]
        have hv1 :
            (D.v.reflect 3).eval 1 = D.v.eval 1 :=
          eval_one_reflect D.v 3 hv
        have hdiv :
            X - C (1 : K) ∣
              D.v.reflect 3 - C (D.v.eval 1) := by
          simpa [hv1] using
            (X_sub_C_dvd_sub_C_eval
              (p := D.v.reflect 3) (a := (1 : K)))
        rw [hu,
          N13SpecialInfinityGraphDivisorCharts.rootAffineIdeal_mk]
        simp
        simpa [N13GoodCoordinateRingTwo.mumfordIdeal,
          GeneralizedGraphIdealCore.graphIdeal,
          N13GoodCoordinateRingTwo.ySubClass,
          GeneralizedGraphIdealCore.ySubClass] using
          (GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
            N13GoodCoordinateRingTwo.xClassHom
            N13GoodCoordinateRingTwo.yClass
            (X - C (1 : K))
            (C (D.v.eval 1)) (D.v.reflect 3) hdiv)
      · have hu :
            D.u.reflect 2 = X - C (1 : K) := by
          rw [hfactor]
          rw [reflect_rootPolynomial_mk]
          simp [one_sub_X_eq_X_sub_one]
        have hv1 :
            (D.v.reflect 3).eval 1 = D.v.eval 1 :=
          eval_one_reflect D.v 3 hv
        have hdiv :
            X - C (1 : K) ∣
              D.v.reflect 3 - C (D.v.eval 1) := by
          simpa [hv1] using
            (X_sub_C_dvd_sub_C_eval
              (p := D.v.reflect 3) (a := (1 : K)))
        rw [hu,
          N13SpecialInfinityGraphDivisorCharts.rootAffineIdeal_mk]
        simp
        simpa [N13GoodCoordinateRingTwo.mumfordIdeal,
          GeneralizedGraphIdealCore.graphIdeal,
          N13GoodCoordinateRingTwo.ySubClass,
          GeneralizedGraphIdealCore.ySubClass] using
          (GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
            N13GoodCoordinateRingTwo.xClassHom
            N13GoodCoordinateRingTwo.yClass
            (X - C (1 : K))
            (C (D.v.eval 1)) (D.v.reflect 3) hdiv)
      · have hu :
            D.u.reflect 2 = (X - C (1 : K)) ^ 2 := by
          rw [hfactor]
          rw [reflect_rootPolynomial_mk]
          simp [one_sub_X_eq_X_sub_one, pow_two]
        have huMonic : (D.u.reflect 2).Monic := by
          rw [hu]
          exact (monic_X_sub_C (1 : K)).pow 2
        have hbezout :
            ∃ a b c : K[X],
              a * D.u.reflect 2 +
                  b * (2 * D.v.reflect 3 +
                    N13GoodCoordinateRingTwo.hPoly) +
                  c * D.w.reflect 4 =
                1 := by
          refine ⟨-X, 1, 0, ?_⟩
          rw [hu]
          have htwo : (2 : K[X]) = 0 :=
            CharP.cast_eq_zero (K[X]) 2
          rw [htwo, zero_mul, zero_add]
          simp [N13GoodCoordinateRingTwo.hPoly]
          linear_combination X ^ 2 * htwo
        let A : N13GoodCoordinateRingTwo.SemiMumford :=
          ⟨D.u.reflect 2, D.v.reflect 3, D.w.reflect 4,
            huMonic, haff, hbezout⟩
        have hv1 :
            (D.v.reflect 3).eval 1 = D.v.eval 1 :=
          eval_one_reflect D.v 3 hv
        rw [N13SpecialInfinityGraphDivisorCharts.rootAffineIdeal_mk]
        rw [← hv1]
        simpa [A, pow_two] using
          N13SpecialGraphDivisorCharts.pointIdeal_sq_eq_mumfordIdeal_of_square
            A 1 hu |>.symm
end
end MazurProof.N13IntegralInfinityGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13SpecialGraphDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- Reflected special infinity graph data has the affine ideal obtained
from its canonical completed root divisor. -/
theorem reflected_affineIdeal_eq_rootAffineIdeal
    (D : N13SpecialInfinityGraphDivisor.SemiMumford)
    (hdeg : D.u.natDegree = 2)
    (hv : D.v.natDegree ≤ 3)
    (haff :
      D.v.reflect 3 ^ 2 +
          N13GoodCoordinateRingTwo.hPoly * D.v.reflect 3 -
          N13GoodCoordinateRingTwo.rhsPoly =
        D.u.reflect 2 * D.w.reflect 4) :
    N13GoodCoordinateRingTwo.mumfordIdeal
        (D.u.reflect 2) (D.v.reflect 3) =
      N13SpecialInfinityGraphDivisorCharts.rootAffineIdeal D
        (N13SpecialInfinityGraphDivisor.rootPair D hdeg) := by
  exact
    reflected_affineIdeal_eq_rootAffineIdeal_of_rootPolynomial
      D
      (N13SpecialInfinityGraphDivisor.rootPair D hdeg)
      hv
      (N13SpecialInfinityGraphDivisorCharts.rootPolynomial_rootPair
        D hdeg).symm
      haff
end
end MazurProof.N13IntegralInfinityGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
/-- Coefficient reduction commutes with the weight-two horizontal
reflection. -/
theorem reduce_affineU
    (E : N13IntegralInfinityGraphTwoChart.GraphData) :
    N13GeneralizedMumfordReduction.reducePoly
        (N13IntegralInfinityGraphTwoChart.affineU E) =
      (N13IntegralInfinityReduction.reducePoly E.u).reflect 2 := by
  rw [N13IntegralInfinityGraphTwoChart.affineU,
    N13GeneralizedMumfordReduction.reducePoly_apply,
    ← Polynomial.reflect_map]
  rfl
end
end MazurProof.N13IntegralInfinityGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
/-- Coefficient reduction commutes with the weight-three vertical
reflection. -/
theorem reduce_affineV
    (E : N13IntegralInfinityGraphTwoChart.GraphData) :
    N13GeneralizedMumfordReduction.reducePoly
        (N13IntegralInfinityGraphTwoChart.affineV E) =
      (N13IntegralInfinityReduction.reducePoly E.v).reflect 3 := by
  rw [N13IntegralInfinityGraphTwoChart.affineV,
    N13GeneralizedMumfordReduction.reducePoly_apply,
    ← Polynomial.reflect_map]
  rfl
end
end MazurProof.N13IntegralInfinityGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
/-- Coefficient reduction commutes with the weight-four quotient
reflection. -/
theorem reduce_affineW
    (E : N13IntegralInfinityGraphTwoChart.GraphData) :
    N13GeneralizedMumfordReduction.reducePoly
        (N13IntegralInfinityGraphTwoChart.affineW E) =
      (N13IntegralInfinityReduction.reducePoly E.w).reflect 4 := by
  rw [N13IntegralInfinityGraphTwoChart.affineW,
    N13GeneralizedMumfordReduction.reducePoly_apply,
    ← Polynomial.reflect_map]
  rfl
end
end MazurProof.N13IntegralInfinityGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
/-- Reducing the integral infinity graph ideal gives the special infinity
graph ideal with coefficientwise reduced equations. -/
theorem map_infinityIdeal
    (E : N13IntegralInfinityGraphTwoChart.GraphData) :
    Ideal.map N13IntegralInfinityReduction.reduceCoordinate
        (N13IntegralInfinityGraphTwoChart.infinityIdeal E) =
      N13SpecialInfinityGraphDivisorCharts.graphIdeal
        (N13IntegralInfinityReduction.reducePoly E.u)
        (N13IntegralInfinityReduction.reducePoly E.v) := by
  have hx (p : N13IntegralInfinityReduction.IntegralBase) :
      N13IntegralInfinityReduction.reduceCoordinate
          ((AdjoinRoot.of
            N13IntegralInfinityChart.infinityCurvePoly) p) =
        (AdjoinRoot.of N13SpecialInfinityChart.curvePoly)
          (N13IntegralInfinityReduction.reducePoly p) := by
    change
      N13IntegralInfinityReduction.reduceCoordinate
          (N13IntegralInfinityReduction.integralBaseClass p) =
        N13IntegralInfinityReduction.specialBaseClass
          (N13IntegralInfinityReduction.reducePoly p)
    exact N13IntegralInfinityReduction.reduce_integralBaseClass p
  simp [N13IntegralInfinityGraphTwoChart.infinityIdeal,
    N13SpecialInfinityGraphDivisorCharts.graphIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass,
    Ideal.map_span, Set.image_pair,
    N13IntegralInfinityGraphJacobian.xClassHom,
    N13IntegralInfinityPointSpread.xClassHom,
    N13IntegralInfinityGraphJacobian.yClass,
    N13IntegralInfinityPointSpread.yClass,
    N13SpecialInfinityGraphDivisorCharts.xClassHom,
    N13SpecialInfinityGraphDivisorCharts.yClass,
    N13IntegralInfinityReduction.reducePoly, hx]
end
end MazurProof.N13IntegralInfinityGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Reducing the weighted affine closure gives the reflected special graph
ideal. -/
theorem map_affineIdeal
    (E : N13IntegralInfinityGraphTwoChart.GraphData) :
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralInfinityGraphTwoChart.affineIdeal E) =
      N13GoodCoordinateRingTwo.mumfordIdeal
        ((N13IntegralInfinityReduction.reducePoly E.u).reflect 2)
        ((N13IntegralInfinityReduction.reducePoly E.v).reflect 3) := by
  change
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (N13IntegralInfinityGraphTwoChart.affineU E)
          (N13IntegralInfinityGraphTwoChart.affineV E)) =
      _
  rw [N13GeneralizedMumfordReduction.map_mumfordIdeal,
    reduce_affineU, reduce_affineV]
end
end MazurProof.N13IntegralInfinityGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- The reflected special coefficients satisfy the affine semigraph
identity obtained by reducing the integral weighted-reflection identity. -/
theorem reduce_affine_curve_eq
    (E : N13IntegralInfinityGraphTwoChart.GraphData)
    (hdu : E.u.natDegree ≤ 2)
    (hdv : E.v.natDegree ≤ 3)
    (hdw : E.w.natDegree ≤ 4) :
    (N13IntegralInfinityReduction.reducePoly E.v).reflect 3 ^ 2 +
          N13GoodCoordinateRingTwo.hPoly *
            (N13IntegralInfinityReduction.reducePoly E.v).reflect 3 -
          N13GoodCoordinateRingTwo.rhsPoly =
      (N13IntegralInfinityReduction.reducePoly E.u).reflect 2 *
        (N13IntegralInfinityReduction.reducePoly E.w).reflect 4 := by
  have h :=
    congrArg N13GeneralizedMumfordReduction.reducePoly
      (N13IntegralInfinityGraphTwoChart.affine_curve_eq
        E hdu hdv hdw)
  simpa only [map_add, map_sub, map_mul, map_pow,
    N13GeneralizedMumfordReduction.reduce_hPoly,
    N13GeneralizedMumfordReduction.reduce_rhsPoly,
    reduce_affineU, reduce_affineV, reduce_affineW] using h
end
end MazurProof.N13IntegralInfinityGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The affine restriction of a monic integral infinity quadratic is the
canonical affine ideal of its completed special root divisor. -/
theorem restrict_twoChartLine_affineIdeal
    (E : N13IntegralInfinityGraphTwoChart.GraphData)
    (hu : E.u.Monic)
    (hdeg : E.u.natDegree = 2)
    (hdv : E.v.natDegree ≤ 3)
    (hdw : E.w.natDegree ≤ 4) :
    (N13TwoChartSpecialRestriction.restrict
        (N13IntegralInfinityGraphTwoChart.twoChartLine
          E (by omega) hdv hdw hu.ne_zero)).affineIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialInfinityGraphDivisor.graphDivisor
          (N13SpecialInfinityGraphDivisor.reduceGraphData E hu)
          (N13SpecialInfinityGraphDivisor.reduceGraphData_u_natDegree
            E hu hdeg))).affineIdeal := by
  let D :=
    N13SpecialInfinityGraphDivisor.reduceGraphData E hu
  let hDdeg :=
    N13SpecialInfinityGraphDivisor.reduceGraphData_u_natDegree
      E hu hdeg
  change
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralInfinityGraphTwoChart.affineIdeal E) =
      (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialInfinityGraphDivisor.graphDivisor D hDdeg)).affineIdeal
  rw [map_affineIdeal,
    N13SpecialInfinityGraphDivisorCharts.ofDivisor_graphDivisor_affineIdeal]
  change
    N13GoodCoordinateRingTwo.mumfordIdeal
        (D.u.reflect 2) (D.v.reflect 3) =
      N13SpecialInfinityGraphDivisorCharts.rootAffineIdeal D
        (N13SpecialInfinityGraphDivisor.rootPair D hDdeg)
  apply reflected_affineIdeal_eq_rootAffineIdeal D hDdeg
  · exact Polynomial.natDegree_map_le.trans hdv
  · exact reduce_affine_curve_eq E (by omega) hdv hdw
end
end MazurProof.N13IntegralInfinityGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
/-- The infinity restriction of a monic integral infinity quadratic is the
canonical infinity ideal of the same completed special root divisor. -/
theorem restrict_twoChartLine_infinityIdeal
    (E : N13IntegralInfinityGraphTwoChart.GraphData)
    (hu : E.u.Monic)
    (hdeg : E.u.natDegree = 2)
    (hdv : E.v.natDegree ≤ 3)
    (hdw : E.w.natDegree ≤ 4) :
    (N13TwoChartSpecialRestriction.restrict
        (N13IntegralInfinityGraphTwoChart.twoChartLine
          E (by omega) hdv hdw hu.ne_zero)).infinityIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialInfinityGraphDivisor.graphDivisor
          (N13SpecialInfinityGraphDivisor.reduceGraphData E hu)
          (N13SpecialInfinityGraphDivisor.reduceGraphData_u_natDegree
            E hu hdeg))).infinityIdeal := by
  let D :=
    N13SpecialInfinityGraphDivisor.reduceGraphData E hu
  let hDdeg :=
    N13SpecialInfinityGraphDivisor.reduceGraphData_u_natDegree
      E hu hdeg
  change
    Ideal.map N13IntegralInfinityReduction.reduceCoordinate
        (N13IntegralInfinityGraphTwoChart.infinityIdeal E) =
      (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialInfinityGraphDivisor.graphDivisor D hDdeg)).infinityIdeal
  rw [map_infinityIdeal,
    N13SpecialInfinityGraphDivisorCharts.ofDivisor_graphDivisor_infinityIdeal]
  rfl
end
end MazurProof.N13IntegralInfinityGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- A bounded monic integral infinity quadratic restricts to the complete
canonical chart pair of its special root divisor. -/
theorem restrict_twoChartLine
    (E : N13IntegralInfinityGraphTwoChart.GraphData)
    (hu : E.u.Monic)
    (hdeg : E.u.natDegree = 2)
    (hdv : E.v.natDegree ≤ 3)
    (hdw : E.w.natDegree ≤ 4) :
    N13TwoChartSpecialRestriction.restrict
        (N13IntegralInfinityGraphTwoChart.twoChartLine
          E (by omega) hdv hdw hu.ne_zero) =
      N13SpecialDivisorCharts.ofDivisor
        (N13SpecialInfinityGraphDivisor.graphDivisor
          (N13SpecialInfinityGraphDivisor.reduceGraphData E hu)
          (N13SpecialInfinityGraphDivisor.reduceGraphData_u_natDegree
            E hu hdeg)) := by
  apply N13TwoChartSpecialRestriction.ChartPair.ext
  · exact restrict_twoChartLine_affineIdeal E hu hdeg hdv hdw
  · exact restrict_twoChartLine_infinityIdeal E hu hdeg hdv hdw
end
end MazurProof.N13IntegralInfinityGraphSpecialRestriction
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem solution
    (E : MazurProof.N13IntegralInfinityGraphTwoChart.GraphData)
    (hu : E.u.Monic)
    (hdeg : E.u.natDegree = 2)
    (hdv : E.v.natDegree ≤ 3)
    (hdw : E.w.natDegree ≤ 4) :
    MazurProof.N13TwoChartSpecialRestriction.restrict
        (MazurProof.N13IntegralInfinityGraphTwoChart.twoChartLine
          E (by omega) hdv hdw hu.ne_zero) =
      MazurProof.N13SpecialDivisorCharts.ofDivisor
        (MazurProof.N13SpecialInfinityGraphDivisor.graphDivisor
          (MazurProof.N13SpecialInfinityGraphDivisor.reduceGraphData E hu)
          (MazurProof.N13SpecialInfinityGraphDivisor.reduceGraphData_u_natDegree
            E hu hdeg)) := by
  exact MazurProof.N13IntegralInfinityGraphSpecialRestriction.restrict_twoChartLine E hu hdeg hdv hdw
