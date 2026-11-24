-- Prove2me | solution 1 for GlobalTheory.ConormalDer.formallySmooth_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:57:21.218813+00:00
-- url     : https://prove2.me/submissions/72993de0-84d5-4d01-9afd-08868d4883b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationExtendingCotangentForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.ConormalDer
namespace GlobalTheory.ConormalDer
theorem _root_.solution (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] :
    Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  haveI := hs.isAlgebraic_field
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : Algebra.IsSeparable (IntermediateField.adjoin F (Set.range ((↑) : s → K))) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1
end GlobalTheory.ConormalDer
