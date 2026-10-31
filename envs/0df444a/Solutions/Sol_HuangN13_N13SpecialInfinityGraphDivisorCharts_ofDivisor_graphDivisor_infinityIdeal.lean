-- Prove2me | solution 1 for HuangN13.N13SpecialInfinityGraphDivisorCharts.ofDivisor_graphDivisor_infinityIdeal
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:56:04.687999+00:00
-- url     : https://prove2.me/submissions/d2e9283b-a07b-4235-9277-f575db7cf9c5

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_InfinityGraphLineCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Theorems.Thm_MazurProof_N13SpecialInfinityGraphDivisor_curveEquationAtRoot
import Theorems.Thm_MazurProof_N13SpecialInfinityGraphDivisor_degreeTwo_splits
import Theorems.Thm_MazurProof_N13SpecialInfinityGraphDivisorCharts_yClass_relation

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


set_option autoImplicit false
open Polynomial
theorem solution
    (D : MazurProof.N13SpecialInfinityGraphDivisor.SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    (MazurProof.N13SpecialDivisorCharts.ofDivisor
        (MazurProof.N13SpecialInfinityGraphDivisor.graphDivisor D hdeg)).infinityIdeal =
      MazurProof.N13SpecialInfinityGraphDivisorCharts.graphIdeal D.u D.v := by
  exact MazurProof.N13SpecialInfinityGraphDivisorCharts.ofDivisor_graphDivisor_infinityIdeal D hdeg
