-- Prove2me | solution 1 for GlobalTheory.PDivGroup.rigExtMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:11:32.112094+00:00
-- url     : https://prove2.me/submissions/6ac849c6-3947-4cb8-8254-322b564d3d35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_mk
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_id
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
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


attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_mk
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_id

set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O : Type} [CommRing O] (G H K : PDivGroup p O)
variable {G H K}
variable [Fact p.Prime]
namespace GlobalTheory.PDivGroup
theorem _root_.solution (f : G ⟶ H) (g : H ⟶ K) :
    rigExtMap (f ≫ g) = rigExtMap f ∘ₗ rigExtMap g :=
  LinearMap.ext fun x => by
    obtain ⟨⟨c, w⟩, rfl⟩ := Submodule.mkQ_surjective _ x
    exact congrArg G.rigMk (Prod.ext (Subtype.ext (funext fun _ => pullTwo_comp _ _ _))
      (LinearMap.congr_fun (omegaMap_comp f g) w))
end GlobalTheory.PDivGroup
