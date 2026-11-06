-- Prove2me | solution 1 for Ideal.Factors.quotientTrace_to_factorResidueTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:42:37.664209+00:00
-- url     : https://prove2.me/submissions/96dfc03d-8370-4f2e-b1aa-dc6d2cb146ef

import Mathlib.RingTheory.Trace.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_DedekindQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralTraceResidue
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
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
omit [IsDedekindDomain R] [Module.IsTorsionFree R S] [Module.Finite R S]
namespace Ideal.Factors
theorem _root_.solution
    (p : Ideal R) [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) :
    quotientResidueEquiv p
        (Algebra.trace (R ⧸ p) (S ⧸ (P : Ideal S))
          (Ideal.Quotient.mk (P : Ideal S) x)) =
      factorResidueTrace p P x := by
  letI : (P : Ideal S).IsMaximal :=
    (Factors.isPrime p P).isMaximal (Factors.ne_bot p P)
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime (P : Ideal S)) :=
    Localization.AtPrime.algebraOfLiesOver p (P : Ideal S)
  let ep : (R ⧸ p) ≃+* p.ResidueField := quotientResidueEquiv p
  let eP : (S ⧸ (P : Ideal S)) ≃+* (P : Ideal S).ResidueField :=
    quotientResidueEquiv (P : Ideal S)
  have he : RingHom.comp
      (algebraMap p.ResidueField (P : Ideal S).ResidueField) ep =
        RingHom.comp eP (algebraMap (R ⧸ p) (S ⧸ (P : Ideal S))) := by
    ext r
    simp only [RingHom.comp_apply,
      Ideal.Quotient.algebraMap_quotient_of_ramificationIdx_neZero]
    have hep : ep (Ideal.Quotient.mk p r) =
        algebraMap R p.ResidueField r := by
      simpa only [ep] using quotientResidueEquiv_mk p r
    have heP : eP (Ideal.Quotient.mk (P : Ideal S) (algebraMap R S r)) =
        algebraMap S (P : Ideal S).ResidueField (algebraMap R S r) := by
      simpa only [eP] using quotientResidueEquiv_mk (P : Ideal S) (algebraMap R S r)
    change algebraMap p.ResidueField (P : Ideal S).ResidueField
        (ep (Ideal.Quotient.mk p r)) =
      eP (Ideal.Quotient.mk (P : Ideal S) (algebraMap R S r))
    rw [hep, heP, ← IsScalarTower.algebraMap_apply R p.ResidueField,
      ← IsScalarTower.algebraMap_apply R S]
  have htrace := Algebra.trace_eq_of_equiv_equiv ep eP he
    (Ideal.Quotient.mk (P : Ideal S) x)
  calc
    quotientResidueEquiv p
        (Algebra.trace (R ⧸ p) (S ⧸ (P : Ideal S))
          (Ideal.Quotient.mk (P : Ideal S) x)) =
        Algebra.trace p.ResidueField (P : Ideal S).ResidueField
          (eP (Ideal.Quotient.mk (P : Ideal S) x)) := by
      change ep (Algebra.trace (R ⧸ p) (S ⧸ (P : Ideal S))
        (Ideal.Quotient.mk (P : Ideal S) x)) = _
      rw [htrace, ep.apply_symm_apply]
    _ = factorResidueTrace p P x := by
      rw [factorResidueTrace]
      exact congrArg (Algebra.trace p.ResidueField (P : Ideal S).ResidueField)
        (quotientResidueEquiv_mk (P : Ideal S) x)
end Ideal.Factors
