-- Prove2me | solution 1 for MazurProof.PowerBasisDiscriminant.norm_aeval_eq_resultant
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:42:01.412891+00:00
-- url     : https://prove2.me/submissions/bbf05504-9acf-4d0c-9886-02f86daa78b1

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.PowerBasisDiscriminant =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.PowerBasisDiscriminant =====
section
/-!
# Structural discriminant identities for power bases

This file supplies two small bridges missing from Mathlib's public API:

* the norm of `q(θ)` is the resultant of the minimal polynomial of `θ`
  with `q`;
* the trace discriminant of a power basis is the polynomial discriminant
  of its minimal polynomial.

The norm proof reindexes the canonical product over embeddings by the
canonical multiset of roots.  It does not choose or enumerate roots and it
does not expand a multiplication matrix.
-/
open Polynomial
open scoped Polynomial BigOperators
namespace MazurProof.PowerBasisDiscriminant
noncomputable section
/-- The norm of a polynomial in a power-basis generator is the resultant
with the generator's minimal polynomial. -/
theorem norm_aeval_eq_resultant
    {K L : Type*}
    [Field K] [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (B : PowerBasis K L)
    (q : K[X]) :
    Algebra.norm K (Polynomial.aeval B.gen q) =
      (minpoly K B.gen).resultant q := by
  let E := AlgebraicClosure L
  letI := Classical.decEq E

  have hres :
      algebraMap K E ((minpoly K B.gen).resultant q) =
        (((minpoly K B.gen).aroots E).map
          (fun y => Polynomial.aeval y q)).prod := by
    rw [← Polynomial.resultant_map_map
      (f := minpoly K B.gen)
      (g := q)
      (m := (minpoly K B.gen).natDegree)
      (n := q.natDegree)
      (algebraMap K E)]
    have hr :=
      Polynomial.resultant_eq_prod_eval
        ((minpoly K B.gen).map (algebraMap K E))
        (q.map (algebraMap K E))
        q.natDegree
        Polynomial.natDegree_map_le
        (IsAlgClosed.splits _)
    rw [((minpoly.monic B.isIntegral_gen).map
      (algebraMap K E)).leadingCoeff, one_pow, one_mul] at hr
    simpa only [Polynomial.aroots_def,
      Polynomial.eval_map_algebraMap,
      (minpoly.monic B.isIntegral_gen).natDegree_map] using hr

  apply (algebraMap K E).injective
  rw [Algebra.norm_eq_prod_embeddings K E]
  rw [hres]
  calc
    (∏ σ : L →ₐ[K] E, σ (Polynomial.aeval B.gen q)) =
        ∏ y : {y // y ∈ (minpoly K B.gen).aroots E},
          Polynomial.aeval y.1 q := by
      apply Fintype.prod_equiv B.liftEquiv'
      intro σ
      simp only [PowerBasis.liftEquiv'_apply_coe]
      exact (Polynomial.aeval_algHom_apply σ B.gen q).symm
    _ = (((minpoly K B.gen).aroots E).map
          (fun y => Polynomial.aeval y q)).prod := by
      rw [Finset.prod_mem_multiset,
      Finset.prod_eq_multiset_prod,
      Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr]
      · exact nodup_roots
          (Separable.map
            (Algebra.IsSeparable.isSeparable K B.gen))
      · intro y
        rfl
end
end MazurProof.PowerBasisDiscriminant
end

end

theorem solution : type_of% @MazurProof.PowerBasisDiscriminant.norm_aeval_eq_resultant := @MazurProof.PowerBasisDiscriminant.norm_aeval_eq_resultant
