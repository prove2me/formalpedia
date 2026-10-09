-- Prove2me | solution 1 for MazurProof.N13MumfordFullKummerIdentityFiber.exists_pade_graph_scalar_of_c_ne_zero_degree_one
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T08:10:37.145485+00:00
-- url     : https://prove2.me/submissions/fb474e96-7049-4b66-a08f-d871b2643a18

import Mathlib
import Definitions.Def_MazurN13_L4

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo
attribute [local simp] MazurProof.N13GaussianFieldEquiv.gaussianI_sq
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GaussianNamedUnitTransport.orderToGaussian_apply
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13IntegralAffinePointSpread.sexticSemi_v
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.QuadraticNormRigidity =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.QuadraticNormRigidity =====
section
/-!
# Square-norm rigidity in a quadratic algebra

In a two-dimensional commutative algebra over a field, an invertible element
whose square and norm are the same scalar is itself scalar.  This is the
structural quadratic-algebra step in the inverse Kummer construction; it is
just Cayley--Hamilton, with no splitting or root enumeration.
-/
namespace MazurProof.QuadraticNormRigidity
noncomputable section
variable {K E : Type*} [Field K] [CharZero K] [CommRing E] [Nontrivial E] [Algebra K E] [Module.Finite K E] [Module.Free K E]
/-- If a unit in a rank-two algebra has both square and norm equal to the
same nonzero scalar, then it comes from the ground field. -/
theorem eq_algebraMap_of_sq_eq_norm
    (b : Module.Basis (Fin 2) K E) (t : E) (s : K)
    (hs : s ≠ 0)
    (hsq : t ^ 2 = algebraMap K E s)
    (hnorm : Algebra.norm K t = s) :
    ∃ r : K, t = algebraMap K E r := by
  let φ : Module.End K E := Algebra.lmul K E t
  let A : Matrix (Fin 2) (Fin 2) K :=
    LinearMap.toMatrix b b φ
  have hchar :
      φ.charpoly =
        Polynomial.X ^ 2 -
          Polynomial.C (Algebra.trace K E t) * Polynomial.X +
          Polynomial.C (Algebra.norm K t) := by
    calc
      φ.charpoly = A.charpoly := by
        exact (LinearMap.charpoly_toMatrix φ b).symm
      _ =
          Polynomial.X ^ 2 -
            Polynomial.C A.trace * Polynomial.X +
            Polynomial.C A.det :=
        Matrix.charpoly_fin_two A
      _ =
          Polynomial.X ^ 2 -
            Polynomial.C (Algebra.trace K E t) * Polynomial.X +
            Polynomial.C (Algebra.norm K t) := by
        dsimp only [A, φ]
        rw [← Algebra.leftMulMatrix_apply]
        rw [← Algebra.trace_eq_matrix_trace b,
          ← Algebra.norm_eq_matrix_det b]
  have hcayley :=
    Algebra.aeval_self_charpoly_lmul (R := K) t
  rw [hchar] at hcayley
  simp only [map_add, map_sub, map_mul, map_pow,
    Polynomial.aeval_X, Polynomial.aeval_C] at hcayley
  rw [hsq, hnorm] at hcayley
  have htrace_ne :
      Algebra.trace K E t ≠ 0 := by
    intro htrace
    rw [htrace] at hcayley
    simp only [map_zero, zero_mul, sub_zero] at hcayley
    have hsum : s + s = 0 := by
      apply FaithfulSMul.algebraMap_injective K E
      simpa only [map_add, map_zero] using hcayley
    have htwo_s : (2 : K) * s = 0 := by
      linear_combination hsum
    exact hs
      ((mul_eq_zero.mp htwo_s).resolve_left (by norm_num))
  have hlinear :
      algebraMap K E (Algebra.trace K E t) * t =
        algebraMap K E (2 * s) := by
    calc
      algebraMap K E (Algebra.trace K E t) * t =
          algebraMap K E s + algebraMap K E s := by
        linear_combination -hcayley
      _ = algebraMap K E (s + s) := by
        rw [map_add]
      _ = algebraMap K E (2 * s) := by
        congr 1
        ring
  refine
    ⟨(2 * s) / Algebra.trace K E t, ?_⟩
  calc
    t =
        algebraMap K E (Algebra.trace K E t)⁻¹ *
          (algebraMap K E (Algebra.trace K E t) * t) := by
      rw [← mul_assoc, ← map_mul]
      simp [htrace_ne]
    _ =
        algebraMap K E (Algebra.trace K E t)⁻¹ *
          algebraMap K E (2 * s) := by
      rw [hlinear]
    _ =
        algebraMap K E
          ((Algebra.trace K E t)⁻¹ * (2 * s)) := by
      exact
        (map_mul (algebraMap K E)
          (Algebra.trace K E t)⁻¹ (2 * s)).symm
    _ =
        algebraMap K E
          ((2 * s) / Algebra.trace K E t) := by
      congr 1
      rw [div_eq_mul_inv]
      ring
/-- The scalar supplied by quadratic rigidity is itself a square root of
the common square and norm. -/
theorem exists_scalar_square_root
    (b : Module.Basis (Fin 2) K E) (t : E) (s : K)
    (hs : s ≠ 0)
    (hsq : t ^ 2 = algebraMap K E s)
    (hnorm : Algebra.norm K t = s) :
    ∃ r : K,
      t = algebraMap K E r ∧ r ^ 2 = s := by
  obtain ⟨r, hr⟩ :=
    eq_algebraMap_of_sq_eq_norm b t s hs hsq hnorm
  refine ⟨r, hr, ?_⟩
  apply FaithfulSMul.algebraMap_injective K E
  rw [map_pow, ← hr, hsq]
end
end MazurProof.QuadraticNormRigidity
end

end

-- ===== FLT.Assumptions.MazurProof.QuadraticAdjoinRootNorm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.QuadraticAdjoinRootNorm =====
section
/-!
# Norms in monic quadratic polynomial quotients

For a monic quadratic `u`, multiplication by the class of `x + yX` has
matrix

```
!![x, -u.coeff 0 * y; y, x - u.coeff 1 * y].
```

Its determinant is the fixed-degree resultant of `u` and `x + yX`.
Reducing a cubic representative modulo `u` then identifies its algebra norm
with the resultant padded to formal degrees `(2, 3)`.  This gives a
root-free bridge between quadratic quotient algebras and the fixed-degree
resultants used by Padé identities.
-/
namespace MazurProof.QuadraticAdjoinRootNorm
noncomputable section
open Polynomial
variable {K : Type*} [Field K]
/-- A polynomial coprime to the modulus represents a unit in the
polynomial quotient. -/
theorem isUnit_mk_of_isCoprime
    (u p : K[X]) (hcop : IsCoprime u p) :
    IsUnit (AdjoinRoot.mk u p) := by
  obtain ⟨a, b, hab⟩ := hcop
  apply IsUnit.of_mul_eq_one (AdjoinRoot.mk u b)
  calc
    AdjoinRoot.mk u p * AdjoinRoot.mk u b =
        AdjoinRoot.mk u (p * b) := by
      rw [map_mul]
    _ = AdjoinRoot.mk u (a * u + b * p) := by
      rw [map_add, map_mul, map_mul,
        AdjoinRoot.mk_self]
      simp [mul_comm]
    _ = AdjoinRoot.mk u 1 := by
      rw [hab]
    _ = 1 := map_one (AdjoinRoot.mk u)
/-- A nonzero resultant is enough to produce the quotient unit. -/
theorem isUnit_mk_of_resultant_ne_zero
    (u p : K[X]) (hu : u ≠ 0)
    (hres : Polynomial.resultant u p ≠ 0) :
    IsUnit (AdjoinRoot.mk u p) := by
  apply isUnit_mk_of_isCoprime
  by_contra hcop
  apply hres
  exact Polynomial.resultant_eq_zero_iff.mpr
    ⟨Or.inl hu, hcop⟩
end
end MazurProof.QuadraticAdjoinRootNorm
end

end

-- ===== FLT.Assumptions.MazurProof.LinearAdjoinRootScalar =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.LinearAdjoinRootScalar =====
section
/-!
# Elements of a linear polynomial quotient are scalar

A quotient by a monic polynomial of degree one has rank one over the
ground field.  Reducing an arbitrary representative modulo that polynomial
therefore gives a constant.  This is the degree-one degeneration of the
quadratic quotient step used in the N13 inverse Kummer construction.
-/
namespace MazurProof.LinearAdjoinRootScalar
noncomputable section
open Polynomial
variable {K : Type*} [Field K]
/-- Every element of a quotient by a monic linear polynomial comes from the
ground field. -/
theorem exists_eq_algebraMap
    (u : K[X]) (hu : u.Monic) (hu1 : u.natDegree = 1)
    (t : AdjoinRoot u) :
    ∃ r : K, t = algebraMap K (AdjoinRoot u) r := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective t
  let rpoly : K[X] := p %ₘ u
  have huNeOne : u ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hu1
    omega
  have hrpoly : rpoly.natDegree ≤ 0 := by
    have hlt := natDegree_modByMonic_lt p hu huNeOne
    dsimp only [rpoly]
    rw [hu1] at hlt
    omega
  refine ⟨rpoly.coeff 0, ?_⟩
  have hrpolyEq : rpoly = C (rpoly.coeff 0) :=
    eq_C_of_natDegree_le_zero hrpoly
  calc
    AdjoinRoot.mk u p =
        AdjoinRoot.mk u
          (AdjoinRoot.modByMonicHom hu (AdjoinRoot.mk u p)) := by
            exact (AdjoinRoot.mk_leftInverse hu
              (AdjoinRoot.mk u p)).symm
    _ = AdjoinRoot.mk u rpoly := by
      rw [AdjoinRoot.modByMonicHom_mk]
    _ = AdjoinRoot.mk u (C (rpoly.coeff 0)) := by
      exact congrArg (AdjoinRoot.mk u) hrpolyEq
    _ = algebraMap K (AdjoinRoot u) (rpoly.coeff 0) := by
      rfl
/-- If an element of a monic linear quotient has scalar square `s`, then its
unique scalar representative is a square root of `s`. -/
theorem exists_scalar_square_root
    (u : K[X]) (hu : u.Monic) (hu1 : u.natDegree = 1)
    (t : AdjoinRoot u) (s : K)
    (hsq : t ^ 2 = algebraMap K (AdjoinRoot u) s) :
    ∃ r : K,
      t = algebraMap K (AdjoinRoot u) r ∧ r ^ 2 = s := by
  obtain ⟨r, hr⟩ := exists_eq_algebraMap u hu hu1 t
  refine ⟨r, hr, ?_⟩
  have hscalar :
      algebraMap K (AdjoinRoot u) (r ^ 2) =
        algebraMap K (AdjoinRoot u) s := by
    rw [map_pow, ← hr, hsq]
  have hdegree : u.degree ≠ 0 := by
    rw [degree_eq_natDegree hu.ne_zero, hu1]
    norm_num
  exact
    (AdjoinRoot.of.injective_of_degree_ne_zero hdegree) hscalar
end
end MazurProof.LinearAdjoinRootScalar
end

end

-- ===== FLT.Assumptions.MazurProof.N13MumfordFullKummerIdentityFiber =====
section
-- ===== FLT.Assumptions.MazurProof.N13MumfordFullKummerIdentityFiber =====
section
/-!
# The remaining identity fibre of the N13 full Kummer map

The target algebra already shows that the N13 full Kummer map has one
kernel fibre.  This file unfolds that fibre instead of treating it as an
opaque equality:

* triviality in the full target is equivalent to an explicit full-gauge
  witness `(β,q)`;
* divisibility by two in the oriented Picard quotient is equivalent to an
  explicit square root of the raw oriented fractional ideal.

The remaining geometric seam is closed here by a dimension-theoretic Padé
numerator, homogeneous resultants, quadratic-algebra rigidity, and Cantor
ideal identities.  No representative enumeration or finite certificate is
used.
-/
namespace MazurProof.N13MumfordFullKummerIdentityFiber
noncomputable section
open Polynomial
open SexticMumford
open scoped nonZeroDivisors
/-! ## Unfolding the full-gauge fibre -/
/-! ## The canonical polynomial square-root witness -/
/-! ## The structural Padé numerator -/
/-! ## The Cantor square behind a Padé half -/
universe u
variable {K : Type u} [Field K]
/-! ## From the sextic norm to the quadratic norm -/
/-- The Padé equation in the quotient by `u`, divided by the unit
represented by `v`, always gives `(l/v)² = c/q`.  This uses only the curve
congruence `f ≡ v² (mod u)` and is independent of the degree or
factorization type of `u`. -/
theorem adjoinRoot_pade_quotient_sq
    (D : LowRep) (a l : ℚ[X]) (q : ℚˣ) (c : ℚ)
    (V : (AdjoinRoot D.toSemi.u)ˣ)
    (hV :
      (V : AdjoinRoot D.toSemi.u) =
        AdjoinRoot.mk D.toSemi.u D.toSemi.v)
    (hrelation :
      Polynomial.C (q : ℚ) * l ^ 2 -
          a ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ) :
    (AdjoinRoot.mk D.toSemi.u l *
          ((V⁻¹ : (AdjoinRoot D.toSemi.u)ˣ) :
            AdjoinRoot D.toSemi.u)) ^ 2 =
      algebraMap ℚ (AdjoinRoot D.toSemi.u)
        (c / (q : ℚ)) := by
  let u : ℚ[X] := D.toSemi.u
  let v : ℚ[X] := D.toSemi.v
  let E : Type := AdjoinRoot u
  have hq : (q : ℚ) ≠ 0 :=
    Units.ne_zero q
  have hcurveMk :
      AdjoinRoot.mk u (N13Mumford.f ℚ) =
        AdjoinRoot.mk u (v ^ 2) := by
    apply (AdjoinRoot.mk_eq_mk).2
    exact D.toSemi.curve_dvd
  have hmapped :=
    congrArg (AdjoinRoot.mk u) hrelation
  have hbase :
      algebraMap ℚ E (q : ℚ) *
            (AdjoinRoot.mk u l) ^ 2 =
        algebraMap ℚ E c * (V : E) ^ 2 := by
    dsimp only [u] at hmapped
    simp only [map_sub, map_mul, map_pow,
      AdjoinRoot.mk_C, AdjoinRoot.mk_self,
      mul_zero, sub_zero] at hmapped
    rw [hcurveMk, map_pow, ← hV] at hmapped
    simpa only [E, u,
      AdjoinRoot.algebraMap_eq] using hmapped
  have hqCancel :
      algebraMap ℚ E ((q : ℚ)⁻¹) *
          algebraMap ℚ E (q : ℚ) = 1 := by
    rw [← map_mul]
    simp [hq]
  have hVCancel :
      (V : E) *
          ((V⁻¹ : (AdjoinRoot u)ˣ) : E) = 1 := by
    rw [← Units.val_mul]
    simp
  change
    (AdjoinRoot.mk u l *
          ((V⁻¹ : (AdjoinRoot u)ˣ) : E)) ^ 2 =
      algebraMap ℚ E (c / (q : ℚ))
  calc
    (AdjoinRoot.mk u l *
          ((V⁻¹ : (AdjoinRoot u)ˣ) : E)) ^ 2 =
        1 *
          (AdjoinRoot.mk u l *
            ((V⁻¹ : (AdjoinRoot u)ˣ) : E)) ^ 2 := by
              rw [one_mul]
    _ =
        (algebraMap ℚ E ((q : ℚ)⁻¹) *
            algebraMap ℚ E (q : ℚ)) *
          (AdjoinRoot.mk u l *
            ((V⁻¹ : (AdjoinRoot u)ˣ) : E)) ^ 2 := by
              rw [hqCancel]
    _ =
        algebraMap ℚ E ((q : ℚ)⁻¹) *
          (algebraMap ℚ E (q : ℚ) *
            (AdjoinRoot.mk u l) ^ 2) *
          (((V⁻¹ : (AdjoinRoot u)ˣ) : E) ^ 2) := by
              ring
    _ =
        algebraMap ℚ E ((q : ℚ)⁻¹) *
          (algebraMap ℚ E c * (V : E) ^ 2) *
          (((V⁻¹ : (AdjoinRoot u)ˣ) : E) ^ 2) := by
              rw [hbase]
    _ =
        (algebraMap ℚ E ((q : ℚ)⁻¹) *
            algebraMap ℚ E c) *
          ((V : E) *
            ((V⁻¹ : (AdjoinRoot u)ˣ) : E)) ^ 2 := by
              ring
    _ =
        algebraMap ℚ E ((q : ℚ)⁻¹) *
          algebraMap ℚ E c := by
            rw [hVCancel]
            ring
    _ =
        algebraMap ℚ E
          (((q : ℚ)⁻¹) * c) := by
            rw [map_mul]
    _ =
        algebraMap ℚ E (c / (q : ℚ)) := by
          congr 1
          rw [div_eq_mul_inv]
          ring
/-- When `u` has degree one, the same graph scalar follows from the fact
that a monic linear quotient is the ground field itself.  No norm
calculation is needed in this degeneration. -/
theorem exists_pade_graph_scalar_of_c_ne_zero_degree_one
    (D : LowRep) (q : ℚˣ) (a l : ℚ[X]) (c : ℚ)
    (hrelation :
      Polynomial.C (q : ℚ) * l ^ 2 -
          a ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ)
    (hu1 : D.toSemi.u.natDegree = 1)
    (hc : c ≠ 0) :
    ∃ b : ℚ,
      b ≠ 0 ∧
      b ^ 2 = c / (q : ℚ) ∧
      D.toSemi.u ∣
        l - Polynomial.C b * D.toSemi.v := by
  let u : ℚ[X] := D.toSemi.u
  let v : ℚ[X] := D.toSemi.v
  have hu : u.Monic := D.toSemi.u_monic
  have hu1' : u.natDegree = 1 := hu1
  have hres :
      Polynomial.resultant u v ≠ 0 := by
    exact N13MumfordKummerNorm.normRoot_ne_zero D
  have hvUnit :
      IsUnit (AdjoinRoot.mk u v) :=
    QuadraticAdjoinRootNorm.isUnit_mk_of_resultant_ne_zero
      u v hu.ne_zero hres
  let V : (AdjoinRoot u)ˣ := hvUnit.unit
  have hV :
      (V : AdjoinRoot u) = AdjoinRoot.mk u v :=
    hvUnit.unit_spec
  let t : AdjoinRoot u :=
    AdjoinRoot.mk u l *
      ((V⁻¹ : (AdjoinRoot u)ˣ) : AdjoinRoot u)
  have hsq :
      t ^ 2 =
        algebraMap ℚ (AdjoinRoot u)
          (c / (q : ℚ)) := by
    exact
      adjoinRoot_pade_quotient_sq
        D a l q c V hV hrelation
  obtain ⟨b, ht, hbSq⟩ :=
    LinearAdjoinRootScalar.exists_scalar_square_root
      u hu hu1' t (c / (q : ℚ)) hsq
  have hs : c / (q : ℚ) ≠ 0 :=
    div_ne_zero hc (Units.ne_zero q)
  have hb : b ≠ 0 := by
    intro hb
    apply hs
    rw [← hbSq, hb]
    norm_num
  have hlEq :
      AdjoinRoot.mk u l =
        AdjoinRoot.mk u
          (Polynomial.C b * v) := by
    calc
      AdjoinRoot.mk u l =
          t * (V : AdjoinRoot u) := by
            dsimp only [t]
            calc
              AdjoinRoot.mk u l =
                  AdjoinRoot.mk u l * 1 := by
                    rw [mul_one]
              _ =
                  AdjoinRoot.mk u l *
                    (((V⁻¹ : (AdjoinRoot u)ˣ) :
                        AdjoinRoot u) *
                      (V : AdjoinRoot u)) := by
                        rw [← Units.val_mul]
                        simp
              _ =
                  (AdjoinRoot.mk u l *
                    ((V⁻¹ : (AdjoinRoot u)ˣ) :
                      AdjoinRoot u)) *
                      (V : AdjoinRoot u) := by
                        ring
      _ =
          algebraMap ℚ (AdjoinRoot u) b *
            (V : AdjoinRoot u) := by
              rw [ht]
      _ =
          AdjoinRoot.mk u
            (Polynomial.C b * v) := by
              rw [map_mul, AdjoinRoot.mk_C, hV,
                AdjoinRoot.algebraMap_eq]
  refine ⟨b, hb, hbSq, ?_⟩
  exact (AdjoinRoot.mk_eq_mk).mp hlEq
/-! ## Closing the finite ideal square -/
namespace FinitePadeGraphRootData
end FinitePadeGraphRootData
namespace FiniteIdealGraphRootData
end FiniteIdealGraphRootData
/-! The branch `c = 0` is not a degenerate coefficient search.  The UFD
identity `q l² = a²u` says directly that the monic polynomial `u` is a
square; the corresponding repeated graph ideal is then the finite square
root. -/
/-! ## Squares in the oriented fractional-ideal quotient -/
/-! ## Absorbing the remaining infinity coordinate -/
/-! ## The structural full-gauge bridge -/
/-! ## Compatibility with the earlier abstract bridge interface -/
end
end MazurProof.N13MumfordFullKummerIdentityFiber
end

end

theorem solution : type_of% @MazurProof.N13MumfordFullKummerIdentityFiber.exists_pade_graph_scalar_of_c_ne_zero_degree_one := @MazurProof.N13MumfordFullKummerIdentityFiber.exists_pade_graph_scalar_of_c_ne_zero_degree_one
