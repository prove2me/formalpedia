-- Prove2me | solution 1 for GlobalTheory.NormEq.eq_zero_of_forall_mem_maxSpec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:14:22.143777+00:00
-- url     : https://prove2.me/submissions/9e94bb11-53f9-423f-90a1-c32167849dbb

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulInvolEqOfFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedAdjoinRootOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormApproximationFirstLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
open GlobalTheory GlobalTheory.NormEq
namespace GlobalTheory.NormEq
theorem _root_.solution {A : Type} [CommRing A] [IsArtinianRing A] [IsReduced A] {y : A}
    (h : ∀ I : MaximalSpectrum A, y ∈ I.asIdeal) : y = 0 := by
  apply (IsArtinianRing.equivPi A).injective
  rw [map_zero]
  funext I
  rw [IsArtinianRing.equivPi_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (h I)
end GlobalTheory.NormEq
