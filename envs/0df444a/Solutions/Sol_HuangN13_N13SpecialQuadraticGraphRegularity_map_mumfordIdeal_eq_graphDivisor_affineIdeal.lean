-- Prove2me | solution 1 for HuangN13.N13SpecialQuadraticGraphRegularity.map_mumfordIdeal_eq_graphDivisor_affineIdeal
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:22:10.230675+00:00
-- url     : https://prove2.me/submissions/f9f29f4f-411a-4f3b-9720-dffb091f3212

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_yClass_relation
import Theorems.Thm_MazurProof_N13SpecialGraphDivisor_degreeTwo_splits

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
/-- A root of the horizontal equation gives its literal graph point. -/
def graphRootPoint
    (D : SemiMumford)
    (a : K) (ha : D.u.IsRoot a) :
    N13SpecialDivisorCharts.CurvePoint :=
  Sum.inl
    ⟨(a, D.v.eval a),
      N13SpecialGraphDivisor.curveEquationAtRoot D ha⟩
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
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialGraphDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The canonical affine ideal of a graph root is its two-generator point
ideal `(X-a, Y-v(a))`. -/
theorem graphRootPoint_affineIdeal
    (D : SemiMumford)
    (a : K) (ha : D.u.IsRoot a) :
    (N13SpecialDivisorCharts.point
        (graphRootPoint D a ha)).affineIdeal =
      mumfordIdeal (X - C a) (C (D.v.eval a)) := by
  change
    (N13SpecialDivisorCharts.point
        (Sum.inl
          (⟨(a, D.v.eval a),
            N13SpecialGraphDivisor.curveEquationAtRoot D ha⟩ :
            N13SpecialDivisorCharts.AffinePoint))).affineIdeal =
      _
  rw [point_affineIdeal]
  rfl
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
/-- The affine chart ideal of a split root divisor is its generalized
Mumford graph ideal.  Distinct roots use the graph Chinese remainder
identity; a repeated root uses the characteristic-two tangent identity. -/
theorem ofDivisor_graphRoots_affineIdeal
    (D : SemiMumford)
    (z : Sym2 K)
    (hz : ∀ a ∈ z, D.u.IsRoot a)
    (hfactor : D.u = rootPolynomial z) :
    (N13SpecialDivisorCharts.ofDivisor
        (Sym2.pmap (graphRootPoint D) z hz)).affineIdeal =
      mumfordIdeal D.u D.v := by
  induction z using Sym2.ind with
  | _ a b =>
      rw [Sym2.pmap_pair,
        N13SpecialDivisorCharts.ofDivisor_mk]
      change
        (N13SpecialDivisorCharts.point
            (graphRootPoint D a
              (hz a (Sym2.mem_mk_left a b)))).affineIdeal *
          (N13SpecialDivisorCharts.point
            (graphRootPoint D b
              (hz b (Sym2.mem_mk_right a b)))).affineIdeal =
        mumfordIdeal D.u D.v
      rw [graphRootPoint_affineIdeal,
        graphRootPoint_affineIdeal]
      by_cases hab : a = b
      · subst b
        simpa only [pow_two] using
          (pointIdeal_sq_eq_mumfordIdeal_of_square D a
            (by
              simpa only [rootPolynomial_mk, pow_two] using hfactor))
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
        simpa [mumfordIdeal,
          GeneralizedGraphIdealCore.graphIdeal,
          ySubClass,
          GeneralizedGraphIdealCore.ySubClass] using
          (GeneralizedGraphIdealCore.graphIdeal_mul_of_coprime
            xClassHom yClass
            (X - C a) (X - C b)
            (C (D.v.eval a)) (C (D.v.eval b)) D.v
            hleft hright hcop)
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
namespace MazurProof.N13SpecialGraphDivisorCharts
noncomputable section
open N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialGraphDivisor.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialGraphDivisorCharts.instFactPrimeOfNatNat_fLT
/-- The polynomial reconstructed from the chosen root pair is the original
monic quadratic. -/
theorem rootPolynomial_rootPair
    (D : SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    rootPolynomial
        (N13SpecialGraphDivisor.rootPair D hdeg) =
      D.u := by
  calc
    rootPolynomial
          (N13SpecialGraphDivisor.rootPair D hdeg) =
        ((N13SpecialGraphDivisor.rootPair D hdeg).toMultiset.map
          (fun a => X - C a)).prod :=
      rootPolynomial_eq_prod _
    _ = (D.u.roots.map (fun a => X - C a)).prod := by
      rw [N13SpecialGraphDivisor.rootPair_toMultiset]
    _ = D.u :=
      (Polynomial.Splits.eq_prod_roots_of_monic
        (N13SpecialGraphDivisor.degreeTwo_splits D hdeg)
        D.u_monic).symm
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
/-- The canonical affine chart ideal of the divisor cut out by a special
quadratic graph is exactly that graph's Mumford ideal. -/
theorem ofDivisor_graphDivisor_affineIdeal
    (D : SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialGraphDivisor.graphDivisor D hdeg)).affineIdeal =
      mumfordIdeal D.u D.v := by
  unfold N13SpecialGraphDivisor.graphDivisor
  let hz :
      ∀ a ∈ N13SpecialGraphDivisor.rootPair D hdeg,
        D.u.IsRoot a :=
    fun a ha =>
      (N13SpecialGraphDivisor.mem_rootPair_iff_isRoot
        D hdeg a).mp ha
  have hpmap :
      Sym2.pmap
          (N13SpecialGraphDivisor.rootPoint D hdeg)
          (N13SpecialGraphDivisor.rootPair D hdeg)
          (fun _ ha => ha) =
        Sym2.pmap
          (graphRootPoint D)
          (N13SpecialGraphDivisor.rootPair D hdeg)
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
    ofDivisor_graphRoots_affineIdeal D
      (N13SpecialGraphDivisor.rootPair D hdeg)
      hz
      (rootPolynomial_rootPair D hdeg).symm
end
end MazurProof.N13SpecialGraphDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialQuadraticGraphRegularity
noncomputable section
/-- Reducing an integral monic quadratic graph ideal gives the affine ideal
of the canonical divisor of its special root graph. -/
theorem map_mumfordIdeal_eq_graphDivisor_affineIdeal
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (hdeg : D.u.natDegree = 2) :
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := N13GeneralizedMumfordReduction.R₂) D.u D.v) =
      (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialGraphDivisor.graphDivisor
          (reduceSemiMumford D hdeg)
          (reduceSemiMumford_u_natDegree D hdeg))).affineIdeal := by
  rw [N13GeneralizedMumfordReduction.map_mumfordIdeal,
    N13SpecialGraphDivisorCharts.ofDivisor_graphDivisor_affineIdeal]
  rfl
end
end MazurProof.N13SpecialQuadraticGraphRegularity
end
end


set_option autoImplicit false
open Polynomial
theorem solution
    (D :
      MazurProof.N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (hdeg : D.u.natDegree = 2) :
    Ideal.map MazurProof.N13GeneralizedMumfordReduction.reduceCoordinate
        (MazurProof.N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := MazurProof.N13GeneralizedMumfordReduction.R₂) D.u D.v) =
      (MazurProof.N13SpecialDivisorCharts.ofDivisor
        (MazurProof.N13SpecialGraphDivisor.graphDivisor
          (MazurProof.N13SpecialQuadraticGraphRegularity.reduceSemiMumford D hdeg)
          (MazurProof.N13SpecialQuadraticGraphRegularity.reduceSemiMumford_u_natDegree D hdeg))).affineIdeal := by
  exact MazurProof.N13SpecialQuadraticGraphRegularity.map_mumfordIdeal_eq_graphDivisor_affineIdeal D hdeg
