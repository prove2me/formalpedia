-- Prove2me | solution 1 for Leopoldt.leopoldt_CM_of_biquadratic_maximalRealSubfield
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:29:13.831264+00:00
-- url     : https://prove2.me/submissions/66ec6401-ef69-474b-b41c-c22641e25a15

import Theorems.Thm_Leopoldt_leopoldtConjecture_iff_maximalRealSubfield
import Theorems.Thm_Leopoldt_leopoldt_totallyReal_biquadratic

open NumberField

theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCMField K]
    [IsGalois ℚ (maximalRealSubfield K)]
    (hK : Module.finrank ℚ (maximalRealSubfield K) = 4)
    (hG : ∀ σ : maximalRealSubfield K ≃ₐ[ℚ] maximalRealSubfield K, σ * σ = 1) :
    Leopoldt.LeopoldtConjecture p K := by
  apply (Leopoldt.leopoldtConjecture_iff_maximalRealSubfield p K).2
  exact Leopoldt.leopoldt_totallyReal_biquadratic p (maximalRealSubfield K) hK hG
