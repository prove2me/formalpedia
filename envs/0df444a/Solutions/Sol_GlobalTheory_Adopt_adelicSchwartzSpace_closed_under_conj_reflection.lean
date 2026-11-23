-- Prove2me | solution 1 for GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:52.322407+00:00
-- url     : https://prove2.me/submissions/6e1d7e11-6710-4061-870d-08d13bda43e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdelicSchwartzSpaceClosedUnderConjReflection
import Theorems.Thm_AdelicReflection_GlobalTheory_CompanionTheory_AdelicReflect_schA_conj_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
namespace _root_.GlobalTheory.Adopt
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ κ _ φ hφ
  exact AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect.schA_conj_neg F κ φ hφ
end _root_.GlobalTheory.Adopt
