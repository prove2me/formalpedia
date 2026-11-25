-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.eta_eq_of_div_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:13:55.532819+00:00
-- url     : https://prove2.me/submissions/b9304e5a-94b9-4da4-ae7d-55511bb08d11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AlmostNormFinDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndexTwoOfFiniteReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEverywhereNormDivOfEtaProdEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsBasisOfIsQuadraticExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EvenCardOfNotLone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsAlmostNormEtaProdEqNegOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EtaProdEqOfEverywhereNormDiv
import Theorems.Thm_GlobalTheory_QuadSymbol_eta_eq_neg_one_iff
import Theorems.Thm_GlobalTheory_QuadSymbol_eta_eq_one_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.QuadSymbol
namespace GlobalTheory.QuadSymbol
theorem _root_.solution {K L : Type} [Field K] [Field L] [Algebra K L] {A : Type} [CommRing A]
    [Algebra K A] {a b : Aˣ} (h : a / b ∈ normGroup K L A) : eta K L A a = eta K L A b := by
  have hiff : a ∈ normGroup K L A ↔ b ∈ normGroup K L A := by
    have := (normGroup K L A).mul_mem_cancel_left (x := a / b) (y := b) h
    rwa [div_mul_cancel] at this
  by_cases hb : b ∈ normGroup K L A
  · rw [eta_eq_one_iff.2 hb, eta_eq_one_iff.2 (hiff.2 hb)]
  · rw [eta_eq_neg_one_iff.2 hb, eta_eq_neg_one_iff.2 (fun ha => hb (hiff.1 ha))]
end GlobalTheory.QuadSymbol
