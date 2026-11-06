-- Prove2me | solution 1 for Ideal.Factors.integralTrace_residue_eq_sum_ramificationIdx_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:19:55.578206+00:00
-- url     : https://prove2.me/submissions/bde825b8-80f9-444b-9659-d7cf8c809f3c

import Mathlib.RingTheory.Trace.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_DedekindQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralTraceResidue
import Theorems.Thm_Ideal_Factors_integralTrace_mod_eq_sum_ramificationIdx_mul
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_Ideal_Factors_quotientTrace_to_factorResidueTrace
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk

set_option autoImplicit false
open Ideal
open scoped nonZeroDivisors
open UniqueFactorizationMonoid
attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
open Ideal.Factors
universe u v
variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable {S : Type v} [CommRing S] [IsDedekindDomain S] [Algebra R S]
variable [Module.IsTorsionFree R S] [Module.Finite R S]
namespace Ideal.Factors
theorem _root_.solution
    (p : Ideal R) [p.IsMaximal]
    (hp : map (algebraMap R S) p ≠ ⊥) (x : S) :
    algebraMap R p.ResidueField (Algebra.intTrace R S x) =
      ∑ P : (factors (map (algebraMap R S) p)).toFinset,
        (ramificationIdx' p (P : Ideal S) : p.ResidueField) *
          factorResidueTrace p P x := by
  have h := congrArg (quotientResidueEquiv p)
    (integralTrace_mod_eq_sum_ramificationIdx_mul p hp x)
  simpa only [quotientResidueEquiv_mk, map_sum, map_mul, map_natCast,
    quotientTrace_to_factorResidueTrace] using h
end Ideal.Factors
