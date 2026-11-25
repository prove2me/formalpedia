-- Prove2me | solution 1 for GlobalTheory.PDivGroup.smul_constGen_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:29:36.593165+00:00
-- url     : https://prove2.me/submissions/3a04ae0c-dac8-402b-9daa-35fc143889d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Theorems.Thm_GlobalTheory_PDiv_cast_digit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory
open PDiv
open GlobalTheory.PDivGroup
attribute [instance] commRing hopf cocomm finite projective
variable {p : ℕ} {O : Type} [CommRing O]
variable (p O) [Fact p.Prime]
namespace GlobalTheory.PDivGroup
theorem _root_.solution (a : ℤ_[p]) (n : ℕ) (φ : (const p O).A n) :
    (a • constGen p O).pt n φ = constFun p O n φ (PadicInt.toZModPow n a) := by
  have h : constHom _ (constGen p O) = 𝟙 _ := by
    rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id]
  have h1 := constFun_constHom (constGen p O) n (digit n a) φ
  rw [h, cast_digit] at h1
  exact h1.symm
end GlobalTheory.PDivGroup
