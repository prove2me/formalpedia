-- Prove2me | solution 1 for GlobalTheory.NormVal.finite_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:02:16.276428+00:00
-- url     : https://prove2.me/submissions/1723cdfa-bded-413f-a544-e8afd77a9fc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
import Theorems.Thm_GlobalTheory_NormVal_inertiaDeg_eq_finrank_residueField

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
    Module.Finite (ResidueField R) (ResidueField B) :=
  Module.finite_of_finrank_pos <| by
    rw [← inertiaDeg_eq_finrank_residueField R n B]
    exact Ideal.inertiaDeg_pos n R
end GlobalTheory.NormVal
