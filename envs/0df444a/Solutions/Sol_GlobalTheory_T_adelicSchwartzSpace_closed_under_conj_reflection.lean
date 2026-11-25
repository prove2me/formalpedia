-- Prove2me | solution 1 for GlobalTheory.T.adelicSchwartzSpace_closed_under_conj_reflection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:15:37.155316+00:00
-- url     : https://prove2.me/submissions/19cc7e30-e5ba-40c5-99e4-02ee59a6782e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdelicSchwartzSpaceClosedUnderConjReflection
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdelicSchwartzSpaceClosedUnderConjReflectionStatement
import Theorems.Thm_GlobalTheory_Adopt_adelicSchwartzSpace_closed_under_conj_reflection


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by
  first | exact @GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection | exact GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection | (intros; apply GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection <;> assumption)
end _root_.GlobalTheory.T
