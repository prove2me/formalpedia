-- Prove2me | solution 1 for GlobalTheory.MinorGerm.Lead.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:07:04.085391+00:00
-- url     : https://prove2.me/submissions/d969be2c-cd38-4068-add7-ee721017feed

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_Low_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type}
variable {p : σ → Prop} [DecidablePred p]
namespace GlobalTheory.MinorGerm
namespace Lead
theorem _root_.solution {α β : σ →₀ ℕ} {P Q : MvPolynomial σ C} (hP : Lead p α P) (hQ : Lead p β Q) :
    Lead p (α + β) (P * Q) := by
  classical
  obtain ⟨hkP, hhP, hsP⟩ := hP
  obtain ⟨hkQ, hhQ, hsQ⟩ := hQ
  refine ⟨?_, ?_, ?_⟩
  · rw [map_mul, hkP, hkQ, MvPolynomial.monomial_mul, mul_one]
  · rw [map_add]
    exact hhP.mul hhQ
  · intro x hx
    rcases Finset.mem_union.1 (Finsupp.support_add hx) with h | h
    · exact hsP x h
    · exact hsQ x h
end Lead
end GlobalTheory.MinorGerm
