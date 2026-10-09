-- Prove2me | solution 1 for MazurProof.N13MumfordFullKummerIdentityFiber.exists_pade_graph_scalar_of_c_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T08:08:26.670976+00:00
-- url     : https://prove2.me/submissions/bb56f875-02cb-4fe7-9262-c52139a4fc78

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13Mumford_f_monic

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
theorem quad_monic (a b : K) :
    (quad a b).Monic :=
  (isMonicOfDegree_add_add_two b a).monic
theorem quad_natDegree (a b : K) :
    (quad a b).natDegree = 2 :=
  (isMonicOfDegree_add_add_two b a).natDegree_eq
theorem norm_mk_linear (a b x y : K) :
    Algebra.norm K
        (AdjoinRoot.mk (quad a b) (linearPoly x y)) =
      x ^ 2 - b * x * y + a * y ^ 2 := by
  let hu : (quad a b).Monic := quad_monic a b
  let e : Fin (quad a b).natDegree ≃ Fin 2 :=
    finCongr (quad_natDegree a b)
  let basis :
      Module.Basis (Fin 2) K (AdjoinRoot (quad a b)) :=
    (AdjoinRoot.powerBasisAux' hu).reindex e
  have hb0 : basis (0 : Fin 2) = 1 := by
    dsimp only [basis]
    rw [Module.Basis.reindex_apply]
    change
      (AdjoinRoot.powerBasis' hu).basis (e.symm 0) = 1
    rw [PowerBasis.basis_eq_pow,
      AdjoinRoot.powerBasis'_gen]
    norm_num [e]
  have hb1 :
      basis (1 : Fin 2) = AdjoinRoot.root (quad a b) := by
    dsimp only [basis]
    rw [Module.Basis.reindex_apply]
    change
      (AdjoinRoot.powerBasis' hu).basis (e.symm 1) =
        AdjoinRoot.root (quad a b)
    rw [PowerBasis.basis_eq_pow,
      AdjoinRoot.powerBasis'_gen]
    norm_num [e]
  have hrepr (z : AdjoinRoot (quad a b)) (i : Fin 2) :
      basis.repr z i =
        (AdjoinRoot.modByMonicHom hu z).coeff i.val := by
    dsimp only [basis]
    rw [Module.Basis.repr_reindex_apply,
      AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
    congr 1
  have hrem0 :
      linearPoly x y %ₘ quad a b = linearPoly x y := by
    apply (modByMonic_eq_self_iff hu).mpr
    have hdegree :
        (quad a b).degree = (2 : WithBot ℕ) := by
      rw [degree_eq_natDegree (quad_monic a b).ne_zero,
        quad_natDegree]
      norm_num
    rw [hdegree]
    change
      (linearPoly x y).degree <
        ((2 : ℕ) : WithBot ℕ)
    rw [degree_lt_iff_coeff_zero]
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    simp only [linearPoly, coeff_add,
      coeff_C_of_ne_zero hn0, coeff_C_mul_X,
      if_neg hn1, add_zero]
  have hrem1 :
      (linearPoly x y * X) %ₘ quad a b =
        C (-a * y) + C (x - b * y) * X := by
    let r : K[X] :=
      C (-a * y) + C (x - b * y) * X
    have hcongr :
        (linearPoly x y * X) %ₘ quad a b =
          r %ₘ quad a b := by
      apply modByMonic_eq_of_dvd_sub hu
      refine ⟨C y, ?_⟩
      dsimp only [r]
      simp only [quad, linearPoly,
        map_sub, map_mul, map_neg]
      ring
    rw [hcongr]
    apply (modByMonic_eq_self_iff hu).mpr
    have hdegree :
        (quad a b).degree = (2 : WithBot ℕ) := by
      rw [degree_eq_natDegree (quad_monic a b).ne_zero,
        quad_natDegree]
      norm_num
    rw [hdegree]
    change r.degree < ((2 : ℕ) : WithBot ℕ)
    rw [degree_lt_iff_coeff_zero]
    intro n hn
    dsimp only [r]
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    simp only [coeff_add,
      coeff_C_of_ne_zero hn0, coeff_C_mul_X,
      if_neg hn1, add_zero]
  have hmulRoot :
      AdjoinRoot.mk (quad a b) (linearPoly x y) *
          AdjoinRoot.root (quad a b) =
        AdjoinRoot.mk (quad a b) (linearPoly x y * X) := by
    rw [AdjoinRoot.root, map_mul]
  have hmatrix :
      Algebra.leftMulMatrix basis
          (AdjoinRoot.mk (quad a b) (linearPoly x y)) =
        !![x, -a * y; y, x - b * y] := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      rw [Algebra.leftMulMatrix_eq_repr_mul, hrepr]
    · rw [show basis _ = 1 by simpa using hb0,
        mul_one, AdjoinRoot.modByMonicHom_mk, hrem0]
      simp [linearPoly]
    · rw [show basis _ = AdjoinRoot.root (quad a b) by
          simpa using hb1,
        hmulRoot, AdjoinRoot.modByMonicHom_mk, hrem1]
      simp
    · rw [show basis _ = 1 by simpa using hb0,
        mul_one, AdjoinRoot.modByMonicHom_mk, hrem0]
      simp [linearPoly]
    · rw [show basis _ = AdjoinRoot.root (quad a b) by
          simpa using hb1,
        hmulRoot, AdjoinRoot.modByMonicHom_mk, hrem1]
      simp
  rw [Algebra.norm_eq_matrix_det basis, hmatrix]
  rw [Matrix.det_fin_two]
  simp
  ring
theorem resultant_quad_linear (a b x y : K) :
    Polynomial.resultant
        (quad a b) (linearPoly x y) 2 1 =
      x ^ 2 - b * x * y + a * y ^ 2 := by
  rw [Polynomial.resultant]
  rw [Matrix.det_fin_three]
  simp [Polynomial.sylvester, quad, linearPoly,
    Fin.addCases]
  norm_num [coeff_X]
  ring
/-- In a monic quadratic quotient, the algebra norm of a linear
representative is its fixed-degree resultant. -/
theorem norm_mk_eq_resultant_fixed_one
    (u p : K[X]) (hu : u.Monic)
    (hu2 : u.natDegree = 2)
    (hp : p.natDegree ≤ 1) :
    Algebra.norm K (AdjoinRoot.mk u p) =
      Polynomial.resultant u p 2 1 := by
  have huDegree : IsMonicOfDegree u 2 :=
    ⟨hu2, hu⟩
  obtain ⟨b, a, rfl⟩ :=
    isMonicOfDegree_two_iff.mp huDegree
  have hpShape :
      p = linearPoly (p.coeff 0) (p.coeff 1) := by
    calc
      p = C (p.coeff 1) * X + C (p.coeff 0) :=
        eq_X_add_C_of_natDegree_le_one hp
      _ = linearPoly (p.coeff 0) (p.coeff 1) := by
        simp only [linearPoly]
        ring
  rw [hpShape]
  calc
    Algebra.norm K
          (AdjoinRoot.mk
            (X ^ 2 + C b * X + C a)
            (linearPoly (p.coeff 0) (p.coeff 1))) =
        (p.coeff 0) ^ 2 -
          b * (p.coeff 0) * (p.coeff 1) +
          a * (p.coeff 1) ^ 2 := by
      convert
        norm_mk_linear a b (p.coeff 0) (p.coeff 1)
          using 1 <;> rfl
    _ =
        Polynomial.resultant
          (X ^ 2 + C b * X + C a)
          (linearPoly (p.coeff 0) (p.coeff 1)) 2 1 := by
      symm
      convert
        resultant_quad_linear a b (p.coeff 0) (p.coeff 1)
          using 1 <;> rfl
/-- A cubic representative may be reduced modulo the monic quadratic
without changing either the quotient element or the resultant padded to
formal second degree three. -/
theorem norm_mk_eq_resultant_fixed_three
    (u p : K[X]) (hu : u.Monic)
    (hu2 : u.natDegree = 2)
    (hp : p.natDegree ≤ 3) :
    Algebra.norm K (AdjoinRoot.mk u p) =
      Polynomial.resultant u p 2 3 := by
  let r : K[X] := p %ₘ u
  let d : K[X] := p /ₘ u
  have huNeOne : u ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hu2
    omega
  have hr : r.natDegree ≤ 1 := by
    have hlt := natDegree_modByMonic_lt p hu huNeOne
    dsimp only [r]
    rw [hu2] at hlt
    omega
  have hd : d.natDegree + 2 ≤ 3 := by
    dsimp only [d]
    rw [natDegree_divByMonic p hu, hu2]
    omega
  have huLe : u.natDegree ≤ 2 := hu2.le
  have hdecomp : r + u * d = p :=
    modByMonic_add_div p u
  have hmk :
      AdjoinRoot.mk u r = AdjoinRoot.mk u p := by
    simpa only [r, AdjoinRoot.modByMonicHom_mk] using
      AdjoinRoot.mk_leftInverse hu (AdjoinRoot.mk u p)
  have hcoeff : u.coeff 2 = 1 := by
    simpa only [hu2] using hu.coeff_natDegree
  have hresReduce :
      Polynomial.resultant u p 2 3 =
        Polynomial.resultant u r 2 1 := by
    calc
      Polynomial.resultant u p 2 3 =
          Polynomial.resultant u (r + u * d) 2 3 := by
        rw [hdecomp]
      _ = Polynomial.resultant u r 2 3 :=
        resultant_add_mul_right u r d 2 3 hd huLe
      _ = Polynomial.resultant u r 2 1 := by
        have hpad :=
          resultant_add_right_deg u r 2 1 2 hr
        simpa only [Nat.reduceAdd, hcoeff, one_pow,
          one_mul] using hpad
  calc
    Algebra.norm K (AdjoinRoot.mk u p) =
        Algebra.norm K (AdjoinRoot.mk u r) := by
      rw [hmk]
    _ = Polynomial.resultant u r 2 1 :=
      norm_mk_eq_resultant_fixed_one u r hu hu2 hr
    _ = Polynomial.resultant u p 2 3 :=
      hresReduce.symm
/-- For a reduced representative, the default resultant has the same
formal degrees as the quadratic quotient norm, including the constant
representative case. -/
theorem norm_mk_eq_resultant
    (u p : K[X]) (hu : u.Monic)
    (hu2 : u.natDegree = 2)
    (hp : p.natDegree ≤ 1) :
    Algebra.norm K (AdjoinRoot.mk u p) =
      Polynomial.resultant u p := by
  change
    Algebra.norm K (AdjoinRoot.mk u p) =
      Polynomial.resultant u p u.natDegree p.natDegree
  rw [hu2]
  have hcoeff : u.coeff 2 = 1 := by
    simpa only [hu2] using hu.coeff_natDegree
  have hpad :=
    resultant_add_right_deg
      u p 2 p.natDegree (1 - p.natDegree) le_rfl
  have hadd :
      p.natDegree + (1 - p.natDegree) = 1 := by
    omega
  rw [hadd, hcoeff, one_pow, one_mul] at hpad
  rw [← hpad]
  exact norm_mk_eq_resultant_fixed_one u p hu hu2 hp
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
/-- The norm of the quotient of a cubic numerator by a reduced denominator
is the corresponding ratio of resultants.  The denominator is packaged as
an actual unit, so this remains valid when the quadratic quotient is not a
domain. -/
theorem exists_mk_unit_norm_mul_inv
    (u l v : K[X]) (hu : u.Monic)
    (hu2 : u.natDegree = 2)
    (hl : l.natDegree ≤ 3)
    (hv : v.natDegree ≤ 1)
    (hres : Polynomial.resultant u v ≠ 0) :
    ∃ V : (AdjoinRoot u)ˣ,
      (V : AdjoinRoot u) = AdjoinRoot.mk u v ∧
      Algebra.norm K
          (AdjoinRoot.mk u l *
            ((V⁻¹ : (AdjoinRoot u)ˣ) : AdjoinRoot u)) =
        Polynomial.resultant u l 2 3 /
          Polynomial.resultant u v := by
  have hvUnit :
      IsUnit (AdjoinRoot.mk u v) :=
    isUnit_mk_of_resultant_ne_zero
      u v hu.ne_zero hres
  let V : (AdjoinRoot u)ˣ := hvUnit.unit
  have hV :
      (V : AdjoinRoot u) = AdjoinRoot.mk u v :=
    hvUnit.unit_spec
  refine ⟨V, hV, ?_⟩
  have hnormL :
      Algebra.norm K (AdjoinRoot.mk u l) =
        Polynomial.resultant u l 2 3 :=
    norm_mk_eq_resultant_fixed_three
      u l hu hu2 hl
  have hnormV :
      Algebra.norm K (V : AdjoinRoot u) =
        Polynomial.resultant u v := by
    rw [hV]
    exact norm_mk_eq_resultant u v hu hu2 hv
  have hnormInv :
      Algebra.norm K
          ((V⁻¹ : (AdjoinRoot u)ˣ) : AdjoinRoot u) =
        (Polynomial.resultant u v)⁻¹ := by
    calc
      Algebra.norm K
            ((V⁻¹ : (AdjoinRoot u)ˣ) : AdjoinRoot u) =
          (((Units.map (Algebra.norm K) V)⁻¹ : Kˣ) : K) := by
            exact
              (Units.coe_map_inv
                (Algebra.norm K) V).symm
      _ = (Algebra.norm K (V : AdjoinRoot u))⁻¹ := by
        rw [Units.val_inv_eq_inv_val, Units.coe_map]
      _ = (Polynomial.resultant u v)⁻¹ := by
        rw [hnormV]
  rw [map_mul, hnormL, hnormInv, div_eq_mul_inv]
end
end MazurProof.QuadraticAdjoinRootNorm
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
@[simp] theorem mk_branchSquarePolynomial (β : Lˣ) :
    AdjoinRoot.mk N13SexticSquareclass.f
        (branchSquarePolynomial β) =
      (β : L) := by
  exact
    AdjoinRoot.mk_leftInverse
      sextic_f_monic (β : L)
/-! ## The structural Padé numerator -/
/-- Killing the two high coefficients leaves a remainder of degree at most
three, since reduction modulo the monic sextic already kills every
coefficient from degree six upward. -/
theorem padeRemainder_natDegree_le_three
    (B : ℚ[X]) (a : Polynomial.degreeLT ℚ 3)
    (haKer : padeHighCoeffMap B a = 0) :
    (padeRemainderMap B a).natDegree ≤ 3 := by
  have hcoeff :=
    congrArg (fun z : ℚ × ℚ => z) haKer
  have h4 :
      (padeRemainderMap B a).coeff 4 = 0 := by
    exact congrArg Prod.fst hcoeff
  have h5 :
      (padeRemainderMap B a).coeff 5 = 0 := by
    exact congrArg Prod.snd hcoeff
  have hfne :
      N13SexticSquareclass.f ≠ 1 := by
    intro hf
    have hdegree :=
      congrArg Polynomial.natDegree hf
    change
      (N13Mumford.f ℚ).natDegree =
        (1 : ℚ[X]).natDegree at hdegree
    rw [N13Mumford.f_natDegree, natDegree_one] at hdegree
    omega
  have hrem :
      (padeRemainderMap B a).natDegree < 6 := by
    simpa only [padeRemainderMap_apply,
      N13SexticSquareclass.f,
      N13Mumford.f_natDegree] using
        (Polynomial.natDegree_modByMonic_lt
          ((a : ℚ[X]) * B) sextic_f_monic hfne)
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases hn4 : n = 4
  · simpa only [hn4] using h4
  by_cases hn5 : n = 5
  · simpa only [hn5] using h5
  have hn6 : 6 ≤ n := by omega
  exact coeff_eq_zero_of_natDegree_lt
    (hrem.trans_le hn6)
/-! ## The Cantor square behind a Padé half -/
universe u
variable {K : Type u} [Field K]
/-- Multiplicativity of the homogeneous resultant with independent upper
bounds on the two right-hand factors.  Mathlib's primitive theorem uses
their actual degrees; padding contributes the same leading-coefficient
power on both sides. -/
theorem resultant_mul_right_padded
    (f g h : K[X]) (m n k : ℕ)
    (hf : f.natDegree ≤ m)
    (hg : g.natDegree ≤ n)
    (hh : h.natDegree ≤ k) :
    f.resultant (g * h) m (n + k) =
      f.resultant g m n * f.resultant h m k := by
  have hsum :
      n + k =
        (g.natDegree + h.natDegree) +
          ((n - g.natDegree) +
            (k - h.natDegree)) := by
    omega
  have hmuldeg :
      (g * h).natDegree ≤
        g.natDegree + h.natDegree :=
    Polynomial.natDegree_mul_le
  have hpadg :
      f.resultant g m n =
        f.coeff m ^ (n - g.natDegree) *
          f.resultant g m g.natDegree := by
    conv_lhs =>
      rw [show n =
        g.natDegree + (n - g.natDegree) by omega]
    exact Polynomial.resultant_add_right_deg
      f g m g.natDegree
        (n - g.natDegree) le_rfl
  have hpadh :
      f.resultant h m k =
        f.coeff m ^ (k - h.natDegree) *
          f.resultant h m h.natDegree := by
    conv_lhs =>
      rw [show k =
        h.natDegree + (k - h.natDegree) by omega]
    exact Polynomial.resultant_add_right_deg
      f h m h.natDegree
        (k - h.natDegree) le_rfl
  calc
    f.resultant (g * h) m (n + k) =
        f.resultant (g * h) m
          ((g.natDegree + h.natDegree) +
            ((n - g.natDegree) +
              (k - h.natDegree))) := by
                rw [hsum]
    _ =
        f.coeff m ^
            ((n - g.natDegree) +
              (k - h.natDegree)) *
          f.resultant (g * h) m
            (g.natDegree + h.natDegree) := by
              exact Polynomial.resultant_add_right_deg
                f (g * h) m
                  (g.natDegree + h.natDegree)
                  ((n - g.natDegree) +
                    (k - h.natDegree)) hmuldeg
    _ =
        f.coeff m ^
            ((n - g.natDegree) +
              (k - h.natDegree)) *
          (f.resultant g m *
            f.resultant h m) := by
              rw [Polynomial.resultant_mul_right
                f g h m hf]
    _ =
        (f.coeff m ^ (n - g.natDegree) *
            f.resultant g m g.natDegree) *
          (f.coeff m ^ (k - h.natDegree) *
            f.resultant h m h.natDegree) := by
              rw [pow_add]
              ring
    _ =
        f.resultant g m n *
          f.resultant h m k := by
            rw [hpadg, hpadh]
/-- The two fixed-degree homogeneous resultant identities attached to the
Padé equation.  Formal degrees `(2,3,6)` make the statement uniform when
the actual numerator or remainder degree drops; no case split on leading
coefficients is needed. -/
theorem pade_resultant_identities
    (D : LowRep) (a l : ℚ[X]) (q c : ℚ)
    (ha : a.natDegree ≤ 2)
    (hl : l.natDegree ≤ 3)
    (hrelation :
      Polynomial.C q * l ^ 2 -
          a ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ) :
    q ^ 2 * (a.resultant l 2 3) ^ 2 =
        c ^ 2 *
          (N13Mumford.f ℚ).resultant a 6 2 ∧
      -((a.resultant l 2 3) ^ 2) *
          D.toSemi.u.resultant l 2 3 =
        c ^ 3 *
          (N13Mumford.f ℚ).resultant l 6 3 := by
  have hu : D.toSemi.u.natDegree ≤ 2 :=
    D.degree_le_two
  have ha2 : (a ^ 2).natDegree ≤ 4 := by
    rw [Polynomial.natDegree_pow]
    omega
  have hfirstCorrection :
      (-(a * D.toSemi.u)).natDegree + 2 ≤ 6 := by
    rw [Polynomial.natDegree_neg]
    exact Nat.add_le_add_right
      (Polynomial.natDegree_mul_le.trans (by omega)) 2
  have hsecondCorrection :
      (Polynomial.C q * l).natDegree + 3 ≤ 6 := by
    have hq :
        (Polynomial.C q).natDegree = 0 :=
      Polynomial.natDegree_C q
    exact Nat.add_le_add_right
      (Polynomial.natDegree_mul_le.trans (by omega)) 3
  have hresA :=
    congrArg
      (fun p : ℚ[X] => a.resultant p 2 6)
      hrelation
  have hleftA :
      a.resultant
          (Polynomial.C q * l ^ 2 -
            a ^ 2 * D.toSemi.u) 2 6 =
        q ^ 2 * (a.resultant l 2 3) ^ 2 := by
    have hll :
        a.resultant (l * l) 2 6 =
          a.resultant l 2 3 *
            a.resultant l 2 3 := by
      simpa only [Nat.reduceAdd] using
        (resultant_mul_right_padded
          a l l 2 3 3 ha hl hl)
    calc
      a.resultant
            (Polynomial.C q * l ^ 2 -
              a ^ 2 * D.toSemi.u) 2 6 =
          a.resultant
            (Polynomial.C q * l ^ 2 +
              a * (-(a * D.toSemi.u))) 2 6 := by
                congr 2
                ring
      _ =
          a.resultant
            (Polynomial.C q * l ^ 2) 2 6 := by
              exact Polynomial.resultant_add_mul_right
                a (Polynomial.C q * l ^ 2)
                  (-(a * D.toSemi.u)) 2 6
                  hfirstCorrection ha
      _ =
          q ^ 2 * a.resultant (l ^ 2) 2 6 := by
              exact Polynomial.resultant_C_mul_right
                a (l ^ 2) 2 6 q
      _ =
          q ^ 2 *
            (a.resultant l 2 3 *
              a.resultant l 2 3) := by
                rw [show l ^ 2 = l * l by ring, hll]
      _ =
          q ^ 2 * (a.resultant l 2 3) ^ 2 := by
            ring
  have hrightA :
      a.resultant
          (Polynomial.C c * N13Mumford.f ℚ) 2 6 =
        c ^ 2 *
          (N13Mumford.f ℚ).resultant a 6 2 := by
    rw [Polynomial.resultant_C_mul_right,
      Polynomial.resultant_comm]
    norm_num
  have hresL :=
    congrArg
      (fun p : ℚ[X] => l.resultant p 3 6)
      hrelation
  have hleftL :
      l.resultant
          (Polynomial.C q * l ^ 2 -
            a ^ 2 * D.toSemi.u) 3 6 =
        -((a.resultant l 2 3) ^ 2) *
          D.toSemi.u.resultant l 2 3 := by
    have haa :
        l.resultant (a * a) 3 4 =
          l.resultant a 3 2 *
            l.resultant a 3 2 := by
      simpa only [Nat.reduceAdd] using
        (resultant_mul_right_padded
          l a a 3 2 2 hl ha ha)
    have hla :
        l.resultant a 3 2 =
          a.resultant l 2 3 := by
      rw [Polynomial.resultant_comm]
      norm_num
    have hlu :
        l.resultant D.toSemi.u 3 2 =
          D.toSemi.u.resultant l 2 3 := by
      rw [Polynomial.resultant_comm]
      norm_num
    calc
      l.resultant
            (Polynomial.C q * l ^ 2 -
              a ^ 2 * D.toSemi.u) 3 6 =
          l.resultant
            (-(a ^ 2 * D.toSemi.u) +
              l * (Polynomial.C q * l)) 3 6 := by
                congr 2
                ring
      _ =
          l.resultant
            (-(a ^ 2 * D.toSemi.u)) 3 6 := by
              exact Polynomial.resultant_add_mul_right
                l (-(a ^ 2 * D.toSemi.u))
                  (Polynomial.C q * l) 3 6
                  hsecondCorrection hl
      _ =
          (-1 : ℚ) ^ 3 *
            l.resultant
              (a ^ 2 * D.toSemi.u) 3 6 := by
                rw [show -(a ^ 2 * D.toSemi.u) =
                  Polynomial.C (-1 : ℚ) *
                    (a ^ 2 * D.toSemi.u) by simp]
                exact Polynomial.resultant_C_mul_right
                  l (a ^ 2 * D.toSemi.u) 3 6 (-1)
      _ =
          (-1 : ℚ) ^ 3 *
            (l.resultant (a ^ 2) 3 4 *
              l.resultant D.toSemi.u 3 2) := by
                rw [resultant_mul_right_padded
                  l (a ^ 2) D.toSemi.u
                    3 4 2 hl ha2 hu]
      _ =
          (-1 : ℚ) ^ 3 *
            ((l.resultant a 3 2 *
                l.resultant a 3 2) *
              l.resultant D.toSemi.u 3 2) := by
                rw [show a ^ 2 = a * a by ring, haa]
      _ =
          -((a.resultant l 2 3) ^ 2) *
            D.toSemi.u.resultant l 2 3 := by
              rw [hla, hlu]
              ring
  have hrightL :
      l.resultant
          (Polynomial.C c * N13Mumford.f ℚ) 3 6 =
        c ^ 3 *
          (N13Mumford.f ℚ).resultant l 6 3 := by
    rw [Polynomial.resultant_C_mul_right,
      Polynomial.resultant_comm]
    norm_num
  constructor
  · calc
      q ^ 2 * (a.resultant l 2 3) ^ 2 =
          a.resultant
            (Polynomial.C q * l ^ 2 -
              a ^ 2 * D.toSemi.u) 2 6 :=
        hleftA.symm
      _ =
          a.resultant
            (Polynomial.C c * N13Mumford.f ℚ) 2 6 :=
        hresA
      _ = _ := hrightA
  · calc
      -((a.resultant l 2 3) ^ 2) *
            D.toSemi.u.resultant l 2 3 =
          l.resultant
            (Polynomial.C q * l ^ 2 -
              a ^ 2 * D.toSemi.u) 3 6 :=
        hleftL.symm
      _ =
          l.resultant
            (Polynomial.C c * N13Mumford.f ℚ) 3 6 :=
        hresL
      _ = _ := hrightL
/-! ## From the sextic norm to the quadratic norm -/
/-- The sextic norm--resultant formula with a fixed formal right degree.
The sextic is monic, so padding a lower-degree polynomial contributes only
a power of its leading coefficient `1`. -/
theorem sextic_norm_mk_eq_resultant_padded
    (p : ℚ[X]) (n : ℕ) (hp : p.natDegree ≤ n) :
    Algebra.norm ℚ
        (AdjoinRoot.mk N13SexticSquareclass.f p) =
      (N13Mumford.f ℚ).resultant p 6 n := by
  letI : Field L :=
    N13SexticIrreducible.sexticAlgebraField
  have hnorm :
      Algebra.norm ℚ
          (AdjoinRoot.mk N13SexticSquareclass.f p) =
        (N13Mumford.f ℚ).resultant p := by
    rw [← AdjoinRoot.aeval_eq]
    exact
      PowerBasisDiscriminant.norm_aeval_adjoinRoot_eq_resultant
        (N13Mumford.f_monic (K := ℚ))
        N13SexticIrreducible.n13Mumford_f_irreducible
        p
  have hfcoeff :
      (N13Mumford.f ℚ).coeff 6 = 1 := by
    simpa only [N13Mumford.f_natDegree] using
      (N13Mumford.f_monic (K := ℚ)).coeff_natDegree
  have hpad :=
    Polynomial.resultant_add_right_deg
      (N13Mumford.f ℚ) p 6 p.natDegree
        (n - p.natDegree) le_rfl
  have hadd :
      p.natDegree + (n - p.natDegree) = n :=
    Nat.add_sub_of_le hp
  rw [hadd, hfcoeff, one_pow, one_mul] at hpad
  calc
    Algebra.norm ℚ
          (AdjoinRoot.mk N13SexticSquareclass.f p) =
        (N13Mumford.f ℚ).resultant p :=
      hnorm
    _ =
        (N13Mumford.f ℚ).resultant
          p 6 p.natDegree := by
            change
              (N13Mumford.f ℚ).resultant
                  p (N13Mumford.f ℚ).natDegree
                    p.natDegree =
                (N13Mumford.f ℚ).resultant
                  p 6 p.natDegree
            rw [N13Mumford.f_natDegree]
    _ = (N13Mumford.f ℚ).resultant p 6 n :=
      hpad.symm
/-- A nonzero polynomial of degree below six is coprime to the irreducible
N13 sextic.  Hence every monic-padded version of its resultant is nonzero. -/
theorem sextic_resultant_padded_ne_zero
    (p : ℚ[X]) (n : ℕ)
    (hp : p.natDegree ≤ n)
    (hp0 : p ≠ 0)
    (hp6 : p.natDegree < 6) :
    (N13Mumford.f ℚ).resultant p 6 n ≠ 0 := by
  have hcop :
      IsCoprime (N13Mumford.f ℚ) p := by
    rcases
        dvd_or_isCoprime
          (N13Mumford.f ℚ) p
          N13SexticIrreducible.n13Mumford_f_irreducible with
      hdiv | hcop
    · have hdegree :=
        Polynomial.natDegree_le_of_dvd hdiv hp0
      rw [N13Mumford.f_natDegree] at hdegree
      omega
    · exact hcop
  have hdefault :
      (N13Mumford.f ℚ).resultant p ≠ 0 :=
    Polynomial.resultant_ne_zero
      (N13Mumford.f ℚ) p hcop
  have hfcoeff :
      (N13Mumford.f ℚ).coeff 6 = 1 := by
    simpa only [N13Mumford.f_natDegree] using
      (N13Mumford.f_monic (K := ℚ)).coeff_natDegree
  have hpad :=
    Polynomial.resultant_add_right_deg
      (N13Mumford.f ℚ) p 6 p.natDegree
        (n - p.natDegree) le_rfl
  have hadd :
      p.natDegree + (n - p.natDegree) = n :=
    Nat.add_sub_of_le hp
  rw [hadd, hfcoeff, one_pow, one_mul] at hpad
  intro hzero
  apply hdefault
  change
    (N13Mumford.f ℚ).resultant p
      (N13Mumford.f ℚ).natDegree p.natDegree = 0
  rw [N13Mumford.f_natDegree]
  rw [← hpad, hzero]
/-- Reduction modulo the sextic does not alter the Padé product:
the chosen cubic remainder still represents `a(θ)β`. -/
theorem mk_padeRemainderMap
    (β : Lˣ) (a : Polynomial.degreeLT ℚ 3) :
    AdjoinRoot.mk N13SexticSquareclass.f
        (padeRemainderMap
          (branchSquarePolynomial β) a) =
      AdjoinRoot.mk N13SexticSquareclass.f
          (a : ℚ[X]) * (β : L) := by
  have hleft :
      AdjoinRoot.mk N13SexticSquareclass.f
          (((a : ℚ[X]) * branchSquarePolynomial β) %ₘ
            N13SexticSquareclass.f) =
        AdjoinRoot.mk N13SexticSquareclass.f
          ((a : ℚ[X]) * branchSquarePolynomial β) := by
    simpa only [AdjoinRoot.modByMonicHom_mk] using
      (AdjoinRoot.mk_leftInverse sextic_f_monic
        (AdjoinRoot.mk N13SexticSquareclass.f
          ((a : ℚ[X]) * branchSquarePolynomial β)))
  calc
    AdjoinRoot.mk N13SexticSquareclass.f
          (padeRemainderMap
            (branchSquarePolynomial β) a) =
        AdjoinRoot.mk N13SexticSquareclass.f
          (((a : ℚ[X]) * branchSquarePolynomial β) %ₘ
            N13SexticSquareclass.f) := by
              rfl
    _ =
        AdjoinRoot.mk N13SexticSquareclass.f
          ((a : ℚ[X]) * branchSquarePolynomial β) :=
      hleft
    _ =
        AdjoinRoot.mk N13SexticSquareclass.f
            (a : ℚ[X]) * (β : L) := by
          rw [map_mul, mk_branchSquarePolynomial]
/-- Multiplicativity of the sextic norm converts the Padé remainder into
the product of the numerator resultant and the norm of the branch square
root. -/
theorem pade_sextic_resultant_factorization
    (β : Lˣ) (a : Polynomial.degreeLT ℚ 3)
    (ha0 : a ≠ 0)
    (haKer :
      padeHighCoeffMap
          (branchSquarePolynomial β) a = 0) :
    (N13Mumford.f ℚ).resultant
          (padeRemainderMap
            (branchSquarePolynomial β) a) 6 3 =
      (N13Mumford.f ℚ).resultant
          (a : ℚ[X]) 6 2 *
        (N13FullNormPair.normUnits β : ℚ) := by
  let l : ℚ[X] :=
    padeRemainderMap (branchSquarePolynomial β) a
  have ha :
      (a : ℚ[X]).natDegree ≤ 2 :=
    padeNumerator_natDegree_le_two a ha0
  have hl :
      l.natDegree ≤ 3 :=
    padeRemainder_natDegree_le_three
      (branchSquarePolynomial β) a haKer
  have hnormA :=
    sextic_norm_mk_eq_resultant_padded
      (a : ℚ[X]) 2 ha
  have hnormL :=
    sextic_norm_mk_eq_resultant_padded l 3 hl
  calc
    (N13Mumford.f ℚ).resultant l 6 3 =
        Algebra.norm ℚ
          (AdjoinRoot.mk
            N13SexticSquareclass.f l) :=
      hnormL.symm
    _ =
        Algebra.norm ℚ
          (AdjoinRoot.mk N13SexticSquareclass.f
              (a : ℚ[X]) * (β : L)) := by
            rw [mk_padeRemainderMap β a]
    _ =
        Algebra.norm ℚ
            (AdjoinRoot.mk N13SexticSquareclass.f
              (a : ℚ[X])) *
          Algebra.norm ℚ (β : L) := by
            rw [map_mul]
    _ =
        (N13Mumford.f ℚ).resultant
              (a : ℚ[X]) 6 2 *
          (N13FullNormPair.normUnits β : ℚ) := by
            change
              Algebra.norm ℚ
                    (AdjoinRoot.mk N13SexticSquareclass.f
                      (a : ℚ[X])) *
                  Algebra.norm ℚ (β : L) =
                (N13Mumford.f ℚ).resultant
                    (a : ℚ[X]) 6 2 *
                  Algebra.norm ℚ (β : L)
            rw [hnormA]
/-- On the nondegenerate Padé branch, the two homogeneous resultant
identities and the oriented norm equation force the quadratic norm ratio
`Res(u,l) / Res(u,v)` to equal `c/q`.  All cancellations occur only after
the sextic norm proves the Padé cross-resultant nonzero. -/
theorem pade_quadratic_resultant_relation
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (a : Polynomial.degreeLT ℚ 3)
    (ha0 : a ≠ 0)
    (haKer :
      padeHighCoeffMap
          (branchSquarePolynomial β) a = 0)
    (c : ℚ)
    (hrelation :
      Polynomial.C (q : ℚ) *
            (padeRemainderMap
              (branchSquarePolynomial β) a) ^ 2 -
          (a : ℚ[X]) ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ)
    (hsnd :
      (-1 : ℚˣ) *
            N13MumfordKummerNorm.normRootUnit D =
        N13FullNormPair.normUnits β * q ^ 3)
    (hc : c ≠ 0) :
    (q : ℚ) *
          D.toSemi.u.resultant
            (padeRemainderMap
              (branchSquarePolynomial β) a) 2 3 =
      c * N13MumfordKummerNorm.normRoot D := by
  let l : ℚ[X] :=
    padeRemainderMap (branchSquarePolynomial β) a
  have ha :
      (a : ℚ[X]).natDegree ≤ 2 :=
    padeNumerator_natDegree_le_two a ha0
  have hl :
      l.natDegree ≤ 3 :=
    padeRemainder_natDegree_le_three
      (branchSquarePolynomial β) a haKer
  obtain ⟨hfirst, hsecond⟩ :=
    pade_resultant_identities
      D (a : ℚ[X]) l (q : ℚ) c
        ha hl hrelation
  have hfactor :=
    pade_sextic_resultant_factorization
      β a ha0 haKer
  have haPoly : (a : ℚ[X]) ≠ 0 := by
    exact fun h => ha0 (Subtype.ext h)
  have hresA :
      (N13Mumford.f ℚ).resultant
          (a : ℚ[X]) 6 2 ≠ 0 :=
    sextic_resultant_padded_ne_zero
      (a : ℚ[X]) 2 ha haPoly (by omega)
  have hcross :
      (a : ℚ[X]).resultant l 2 3 ≠ 0 := by
    intro hzero
    have hbad :
        c ^ 2 *
            (N13Mumford.f ℚ).resultant
              (a : ℚ[X]) 6 2 = 0 := by
      rw [← hfirst, hzero]
      ring
    exact
      (mul_ne_zero (pow_ne_zero 2 hc) hresA) hbad
  rw [hfactor] at hsecond
  have hcancel :
      ((a : ℚ[X]).resultant l 2 3) ^ 2 *
          (-D.toSemi.u.resultant l 2 3 -
            c * (q : ℚ) ^ 2 *
              (N13FullNormPair.normUnits β : ℚ)) = 0 := by
    linear_combination
      hsecond -
        c * (N13FullNormPair.normUnits β : ℚ) *
          hfirst
  have hscalar :
      -D.toSemi.u.resultant l 2 3 -
          c * (q : ℚ) ^ 2 *
            (N13FullNormPair.normUnits β : ℚ) = 0 :=
    (mul_eq_zero.mp hcancel).resolve_left
      (pow_ne_zero 2 hcross)
  have hS :
      D.toSemi.u.resultant l 2 3 =
        -c * (q : ℚ) ^ 2 *
          (N13FullNormPair.normUnits β : ℚ) := by
    linear_combination -hscalar
  have hsndVal :=
    congrArg (fun z : ℚˣ => (z : ℚ)) hsnd
  change
    (-1 : ℚ) * N13MumfordKummerNorm.normRoot D =
      (N13FullNormPair.normUnits β : ℚ) *
        (q : ℚ) ^ 3 at hsndVal
  have hroot :
      N13MumfordKummerNorm.normRoot D =
        -(N13FullNormPair.normUnits β : ℚ) *
          (q : ℚ) ^ 3 := by
    linear_combination -hsndVal
  change
    (q : ℚ) * D.toSemi.u.resultant l 2 3 =
      c * N13MumfordKummerNorm.normRoot D
  rw [hS, hroot]
  ring
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
/-- If the scalar `c` is nonzero and `u` has its generic quadratic degree,
the Padé quotient `l/v` is rigid.  Its square and its algebra norm both
equal `c/q`, so Cayley--Hamilton forces it to be a rational scalar `b`.
Equivalently, `l ≡ b v (mod u)`. -/
theorem exists_pade_graph_scalar_of_c_ne_zero
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (a : Polynomial.degreeLT ℚ 3)
    (ha0 : a ≠ 0)
    (haKer :
      padeHighCoeffMap
          (branchSquarePolynomial β) a = 0)
    (c : ℚ)
    (hrelation :
      Polynomial.C (q : ℚ) *
            (padeRemainderMap
              (branchSquarePolynomial β) a) ^ 2 -
          (a : ℚ[X]) ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ)
    (hsnd :
      (-1 : ℚˣ) *
            N13MumfordKummerNorm.normRootUnit D =
        N13FullNormPair.normUnits β * q ^ 3)
    (hu2 : D.toSemi.u.natDegree = 2)
    (hc : c ≠ 0) :
    ∃ b : ℚ,
      b ≠ 0 ∧
      b ^ 2 = c / (q : ℚ) ∧
      D.toSemi.u ∣
        padeRemainderMap
              (branchSquarePolynomial β) a -
          Polynomial.C b * D.toSemi.v := by
  let u : ℚ[X] := D.toSemi.u
  let v : ℚ[X] := D.toSemi.v
  let l : ℚ[X] :=
    padeRemainderMap (branchSquarePolynomial β) a
  have hu : u.Monic := D.toSemi.u_monic
  have hu2' : u.natDegree = 2 := hu2
  have hl :
      l.natDegree ≤ 3 :=
    padeRemainder_natDegree_le_three
      (branchSquarePolynomial β) a haKer
  have huOne : u ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hu2'
    omega
  have hvlt : v.natDegree < u.natDegree := by
    have hmod :=
      Polynomial.natDegree_modByMonic_lt v hu huOne
    rw [Polynomial.modByMonic_eq_mod v hu,
      D.toSemi.v_reduced] at hmod
    exact hmod
  have hv : v.natDegree ≤ 1 := by
    omega
  have hres :
      Polynomial.resultant u v ≠ 0 := by
    exact N13MumfordKummerNorm.normRoot_ne_zero D
  let E : Type := AdjoinRoot u
  letI : Nontrivial E := by
    apply AdjoinRoot.nontrivial
    rw [Polynomial.degree_eq_natDegree hu.ne_zero,
      hu2']
    norm_num
  let basis :
      Module.Basis (Fin 2) ℚ E :=
    (AdjoinRoot.powerBasisAux' hu).reindex
      (finCongr hu2')
  letI : Module.Free ℚ E :=
    Module.Free.of_basis basis
  letI : Module.Finite ℚ E :=
    Module.Finite.of_basis basis
  obtain ⟨V, hV, hnorm⟩ :=
    QuadraticAdjoinRootNorm.exists_mk_unit_norm_mul_inv
      u l v hu hu2' hl hv hres
  let t : E :=
    AdjoinRoot.mk u l *
      ((V⁻¹ : (AdjoinRoot u)ˣ) : AdjoinRoot u)
  have hq : (q : ℚ) ≠ 0 :=
    Units.ne_zero q
  have hresultant :=
    pade_quadratic_resultant_relation
      D β q a ha0 haKer c hrelation hsnd hc
  have hratio :
      Polynomial.resultant u l 2 3 /
            Polynomial.resultant u v =
        c / (q : ℚ) := by
    apply (div_eq_div_iff hres hq).2
    simpa only [u, v, l,
      N13MumfordKummerNorm.normRoot,
      mul_comm] using hresultant
  have hnorm' :
      Algebra.norm ℚ t = c / (q : ℚ) := by
    exact hnorm.trans hratio
  have hsq :
      t ^ 2 =
        algebraMap ℚ E (c / (q : ℚ)) := by
    exact
      adjoinRoot_pade_quotient_sq
        D (a : ℚ[X]) l q c V hV hrelation
  have hs : c / (q : ℚ) ≠ 0 :=
    div_ne_zero hc hq
  obtain ⟨b, ht, hbSq⟩ :=
    QuadraticNormRigidity.exists_scalar_square_root
      basis t (c / (q : ℚ)) hs hsq hnorm'
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
          t * (V : E) := by
            dsimp only [t]
            calc
              AdjoinRoot.mk u l =
                  AdjoinRoot.mk u l * 1 := by
                    rw [mul_one]
              _ =
                  AdjoinRoot.mk u l *
                    (((V⁻¹ : (AdjoinRoot u)ˣ) : E) *
                      (V : E)) := by
                        rw [← Units.val_mul]
                        simp
              _ =
                  (AdjoinRoot.mk u l *
                    ((V⁻¹ : (AdjoinRoot u)ˣ) : E)) *
                      (V : E) := by
                        ring
      _ =
          algebraMap ℚ E b * (V : E) := by
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

theorem solution : type_of% @MazurProof.N13MumfordFullKummerIdentityFiber.exists_pade_graph_scalar_of_c_ne_zero := @MazurProof.N13MumfordFullKummerIdentityFiber.exists_pade_graph_scalar_of_c_ne_zero
