-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.Converse.div_mem_normGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:33:04.568336+00:00
-- url     : https://prove2.me/submissions/9c326162-8cbd-46ce-a935-90336c18f7e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EvenCardOfNotLone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEverywhereNormDivOfEtaProdEqOne
import Theorems.Thm_GlobalTheory_QuadSymbol_eta_eq_one_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm GlobalTheory.QuadSymbol.NormIndex
noncomputable section
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.HilbertRecip
open GlobalTheory.QuadSymbol.Converse
variable {K : Type} [Field K]
variable {L : Type} [Field L] [Algebra K L]
namespace GlobalTheory.QuadSymbol.Converse
theorem _root_.solution {A : Type} [CommRing A] [Algebra K A]
    (h : ∀ a b : Aˣ, eta K L A (a * b) = eta K L A a * eta K L A b) {a b : Aˣ}
    (hab : eta K L A b = eta K L A a) : a / b ∈ normGroup K L A := by
  have := h (a / b) b
  rw [div_mul_cancel, hab, right_eq_mul] at this
  exact eta_eq_one_iff.1 this
end GlobalTheory.QuadSymbol.Converse
