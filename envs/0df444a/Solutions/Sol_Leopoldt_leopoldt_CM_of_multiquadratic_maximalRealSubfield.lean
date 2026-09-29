-- Prove2me | solution 1 for Leopoldt.leopoldt_CM_of_multiquadratic_maximalRealSubfield
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:33:39.092196+00:00
-- url     : https://prove2.me/submissions/9496cdb4-7dd1-49b5-a1ef-74cf0c33bf1a

import Theorems.Thm_Leopoldt_leopoldtConjecture_iff_maximalRealSubfield
import Theorems.Thm_Leopoldt_leopoldt_totallyReal_multiquadratic

open NumberField

theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCMField K]
    [IsGalois ℚ (maximalRealSubfield K)]
    (hG : ∀ σ : maximalRealSubfield K ≃ₐ[ℚ] maximalRealSubfield K, σ * σ = 1) :
    Leopoldt.LeopoldtConjecture p K := by
  apply (Leopoldt.leopoldtConjecture_iff_maximalRealSubfield p K).2
  exact Leopoldt.leopoldt_totallyReal_multiquadratic p (maximalRealSubfield K) hG
