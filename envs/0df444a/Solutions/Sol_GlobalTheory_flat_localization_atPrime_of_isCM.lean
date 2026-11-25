-- Prove2me | solution 1 for GlobalTheory.flat_localization_atPrime_of_isCM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:05:23.871283+00:00
-- url     : https://prove2.me/submissions/dc9f0e0a-e772-4439-9e3b-13604ffce964

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Theorems.Thm_GlobalTheory_flat_of_isCM_of_quasiFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open RingTheory.Sequence IsLocalRing TensorProduct
open GlobalTheory
open ReciprocityTheory.CA
variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
namespace GlobalTheory
theorem _root_.solution (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    [q.LiesOver p] [IsRegularLocalRing (Localization.AtPrime p)] [Algebra.QuasiFiniteAt A q]
    (hB : IsCM (Localization.AtPrime q)) (hd : p.height ≤ q.height) :
    Module.Flat A (Localization.AtPrime q) := by
  letI := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.QuasiFinite (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_restrictScalars A _ _
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := by
    refine flat_of_isCM_of_quasiFinite hB ?_
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p,
      IsLocalization.AtPrime.ringKrullDim_eq_height q]
    exact WithBot.coe_le_coe.mpr hd
  exact .trans A (Localization.AtPrime p) _
end GlobalTheory
