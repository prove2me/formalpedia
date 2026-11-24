-- Prove2me | solution 1 for GlobalTheory.NormVal.inertiaDeg_eq_finrank_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:14:40.727242+00:00
-- url     : https://prove2.me/submissions/064759f1-3c01-4e88-81ca-b75d873a1a40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
import Theorems.Thm_GlobalTheory_NormVal_liesOver_maximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsDiscreteValuationRing IsLocalRing Module TensorProduct
open GlobalTheory.NormVal
variable (R : Type*) {S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S]
namespace GlobalTheory.NormVal
theorem _root_.solution (n : Ideal S) [n.IsMaximal] (B : Type*) [CommRing B]
    [IsLocalRing B] [Algebra S B] [IsLocalization.AtPrime B n] [Algebra R B]
    [IsScalarTower R S B] [IsLocalHom (algebraMap R B)] :
    n.inertiaDeg R = Module.finrank (ResidueField R) (ResidueField B) := by
  have := liesOver_maximalIdeal R n
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal R) n]
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
    (IsLocalization.AtPrime.equivQuotMaximalIdeal n B) ?_
  ext a
  change residue B (algebraMap R B a) =
    IsLocalization.AtPrime.equivQuotMaximalIdeal n B (Ideal.Quotient.mk n (algebraMap R S a))
  rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk, ← IsScalarTower.algebraMap_apply]
  rfl
end GlobalTheory.NormVal
