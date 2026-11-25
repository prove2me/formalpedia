-- Prove2me | solution 1 for GlobalTheory.K4.TopW.topW_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:27.500023+00:00
-- url     : https://prove2.me/submissions/2fd248ec-5416-450b-917a-dc4007d831ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_CobOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsFirstChernClassOfLineBundle
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsTopWTopWOfExists
import Theorems.Thm_GlobalTheory_K4_TopW_isTopW_topW_of_exists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K4
open GlobalTheory.KEdge GlobalTheory.NeedB
variable {F K Ω : Type*} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
open GlobalTheory.K4.TopW
variable {N : ℕ} {ζ : Ω} {x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)} {η : (Ω ≃ₐ[F] Ω) → ZMod N}
namespace GlobalTheory.K4.TopW
theorem _root_.solution (σ : Ω ≃ₐ[F] Ω) : topW (K := K) ζ x y η σ ≠ 0 := by
  by_cases h : ∃ w : K, IsTopW ζ x y η σ w
  · exact (isTopW_topW_of_exists h).1
  · unfold topW
    rw [dif_neg h]
    exact one_ne_zero
end GlobalTheory.K4.TopW
