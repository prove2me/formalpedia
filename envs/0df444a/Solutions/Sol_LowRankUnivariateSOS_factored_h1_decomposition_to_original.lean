-- Prove2me | solution 1 for LowRankUnivariateSOS.factored_h1_decomposition_to_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:43.350325+00:00
-- url     : https://prove2.me/submissions/a6fa094e-c22c-4314-aeb1-28deb83a458e

import Mathlib.Tactic.Linarith
import Definitions.Def_LowRankUnivariateSOS_Socp
import Definitions.Def_LowRankUnivariateSOS_H1Case
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Theorems.Thm_LowRankUnivariateSOS_inKerA_of_shared_reduced
import Theorems.Thm_LowRankUnivariateSOS_inImagePlusSigmaKerCone_of_h1_data


set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution
    (a g p q s : Poly) (u0 : UPair)
    (hg : g ≠ 0)
    (hcop : IsCoprime u0.fst u0.snd)
    (hs : IsSOS s)
    (hp : p = g * q + s * sigma2 u0) :
    ∃ imgPart : Poly, ∃ ws : Finset UPair,
      InImageA (scalePair g u0) imgPart ∧
        (∀ w ∈ ws, InKerA (scalePair a u0) w) ∧
        p = imgPart + ws.sum sigma2 := by
  rcases inImagePlusSigmaKerCone_of_h1_data g p q s u0 hcop hs hp with ⟨v, ws, hker, hp'⟩
  refine ⟨A (scalePair g u0) v, ws, ?_, ?_, ?_⟩
  · exact ⟨v, rfl⟩
  · intro w hw
    exact inKerA_of_shared_reduced hg (hker w hw)
  · exact hp'
end LowRankUnivariateSOS
