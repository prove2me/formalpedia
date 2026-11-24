-- Prove2me | solution 1 for GlobalTheory.T.exists_uniformizer_compatible_unramifiedExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:21:14.928084+00:00
-- url     : https://prove2.me/submissions/c8fd80af-5b46-4409-9865-9ac3ffc699fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniformizerCompatibleUnramifiedExt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniformizerCompatibleUnramifiedExtStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_unif


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ π : K.O, ∃ π' : K'.O, algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) ∧ IsLocalRing.maximalIdeal K.O = Ideal.span {π} ∧ IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_unif | exact GlobalTheory.UnitLemma.Unr.exists_unif | (intros; apply GlobalTheory.UnitLemma.Unr.exists_unif <;> assumption)
end _root_.GlobalTheory.T
