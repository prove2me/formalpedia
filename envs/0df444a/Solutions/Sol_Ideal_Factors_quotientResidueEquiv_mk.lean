-- Prove2me | solution 1 for Ideal.Factors.quotientResidueEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:19:50.597292+00:00
-- url     : https://prove2.me/submissions/e032ba8e-9919-41fe-b461-b64d4adb8c99

import Mathlib.RingTheory.Trace.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_DedekindQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralTraceResidue

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
    {A : Type*} [CommRing A] (I : Ideal A) [I.IsMaximal] (x : A) :
    quotientResidueEquiv I (Ideal.Quotient.mk I x) =
      algebraMap A I.ResidueField x := by
  rw [quotientResidueEquiv, RingEquiv.ofBijective_apply,
    Ideal.algebraMap_quotient_residueField_mk]
end Ideal.Factors
