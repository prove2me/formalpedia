-- Prove2me | solution 1 for GlobalTheory.PDivGroup.Test.padicAction_const_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:00:53.082227+00:00
-- url     : https://prove2.me/submissions/2510f3f6-f031-49a0-a0cf-e2bf4a6b2467

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDivGroup_toSpanSingleton_constGen_injective
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT



set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.PDivGroup.Test
open PDiv
variable {p : ℕ} {O : Type} [CommRing O]
namespace GlobalTheory.PDivGroup.Test
theorem _root_.solution [Fact p.Prime] [Nontrivial O] :
    Function.Injective (padicAction (const p O)) := fun a b h => by
  apply toSpanSingleton_constGen_injective p O
  have key : ∀ c : ℤ_[p], tateMap _ _ O (padicAction (const p O) c) (constGen p O) =
      c • constGen p O := fun c => by
    change tateMap _ _ O (algebraMap ℤ_[p] (End (const p O)) c) _ = _
    rw [Algebra.algebraMap_eq_smul_one]
    change tateMap _ _ O (c • 𝟙 (const p O)) _ = _
    rw [map_smul, LinearMap.smul_apply, tateMap_id]
  simp only [LinearMap.toSpanSingleton_apply]
  rw [← key, ← key, h]
end GlobalTheory.PDivGroup.Test
