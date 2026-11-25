-- Prove2me | solution 1 for GlobalTheory.PDivGroup.lieMap_charHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:43:47.461499+00:00
-- url     : https://prove2.me/submissions/d579c4d5-7dbf-487a-ac72-8ab81c3a0ee2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
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
open GlobalTheory
open PDiv
open GlobalTheory.PDivGroup
attribute [instance] commRing hopf cocomm finite projective
variable {p : ℕ} {O : Type} [CommRing O]
variable (p O) [Fact p.Prime]
variable {p O}
namespace GlobalTheory.PDivGroup
theorem _root_.solution [IsAdicComplete (Ideal.span {(p : O)}) O] {G : PDivGroup p O}
    (χ : G.dual.Tate) (x : G.Lie) :
    lieMap G (mu p O) (charHom G χ) x = x (dlog G χ) • muLieGen p O :=
  LinearMap.ext fun w => by
    obtain ⟨c, rfl⟩ := (toSpanSingleton_dlogT_bijective p O).2 w
    rw [LinearMap.toSpanSingleton_apply, map_smul, map_smul, LinearMap.smul_apply, muLieGen_dlogT,
      lieMap_apply, ← dlog_eq_omegaMap, smul_eq_mul (x _), mul_one]
end GlobalTheory.PDivGroup
