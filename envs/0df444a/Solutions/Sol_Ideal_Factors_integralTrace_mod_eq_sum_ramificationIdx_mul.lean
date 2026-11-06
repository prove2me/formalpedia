-- Prove2me | solution 1 for Ideal.Factors.integralTrace_mod_eq_sum_ramificationIdx_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:18:51.970602+00:00
-- url     : https://prove2.me/submissions/2bfee67b-bc54-45f9-b3a8-6cb11998bef1

import Mathlib.RingTheory.Trace.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_DedekindQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralTraceResidue
import Theorems.Thm_Ideal_Factors_trace_quotient_map_eq_sum_ramificationIdx_mul


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
    Ideal.Quotient.mk p (Algebra.intTrace R S x) =
      ∑ P : (factors (map (algebraMap R S) p)).toFinset,
        (ramificationIdx' p (P : Ideal S) : R ⧸ p) *
          Algebra.trace (R ⧸ p) (S ⧸ (P : Ideal S))
            (Ideal.Quotient.mk (P : Ideal S) x) := by
  calc
    Ideal.Quotient.mk p (Algebra.intTrace R S x) =
        Algebra.trace (R ⧸ p) (S ⧸ map (algebraMap R S) p)
          (Ideal.Quotient.mk _ x) :=
      by rw [Algebra.trace_quotient_eq_of_isDedekindDomain]
    _ = _ := trace_quotient_map_eq_sum_ramificationIdx_mul p hp x
end Ideal.Factors
