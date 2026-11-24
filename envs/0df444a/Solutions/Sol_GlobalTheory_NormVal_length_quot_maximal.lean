-- Prove2me | solution 1 for GlobalTheory.NormVal.length_quot_maximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:14:42.18651+00:00
-- url     : https://prove2.me/submissions/4f11220e-c7c6-44b0-8084-ed21a460e9e1

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
theorem _root_.solution (n : Ideal S) [n.IsMaximal] :
    Module.length R (S ⧸ n) = n.inertiaDeg R := by
  have := liesOver_maximalIdeal R n
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal R) n]
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ n) := Module.Finite.of_restrictScalars_finite R _ _
  rw [← Module.length_eq_finrank]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
end GlobalTheory.NormVal
