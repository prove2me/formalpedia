-- Prove2me | solution 1 for GlobalTheory.T.coeff_coefficientSpaceAction_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:14:11.032623+00:00
-- url     : https://prove2.me/submissions/cc52e589-e571-469b-9e55-bd0ecee830f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CoeffCoefficientSpaceActionMemRange
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ReprMemOfCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CoeffCoefficientSpaceActionMemRangeStatement
import Theorems.Thm_GlobalTheory_RowRho_coeff_rhoVr_mem_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.DIV MvPolynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] {n : ℕ} {E : Type} [Field E] (emb : ι → E →+* ℂ) {L : Type} [Field L] (κ : L →+* ℂ), (∀ (τ : ι) (x : E), emb τ x ∈ Set.range κ) → ∀ (lam : ι → Formalism.BasicNotions.DomWeight n) (g : GL (Fin n) E) (v : VV ℂ lam), (∀ m, MvPolynomial.coeff m v.1 ∈ Set.range κ) → ∀ m, MvPolynomial.coeff m ((rhoVr emb lam g) v).1 ∈ Set.range κ := by
  first | exact @GlobalTheory.RowRho.coeff_rhoVr_mem_range | exact GlobalTheory.RowRho.coeff_rhoVr_mem_range | (intros; apply GlobalTheory.RowRho.coeff_rhoVr_mem_range <;> assumption)
end _root_.GlobalTheory.T
