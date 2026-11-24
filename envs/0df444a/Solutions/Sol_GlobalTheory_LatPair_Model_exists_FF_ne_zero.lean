-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.exists_FF_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:27:13.079553+00:00
-- url     : https://prove2.me/submissions/000f284d-9629-43b5-b929-5c3cd3ab9af5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Theorems.Thm_GlobalTheory_LatPair_Model_FF_ne_zero
import Theorems.Thm_GlobalTheory_LatPair_Mram_ne_bot
import Theorems.Thm_GlobalTheory_LatPair_resChar_ne_one
import Theorems.Thm_GlobalTheory_SplitWeil_Model_exists_hasConductor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.LatPair.Model
theorem _root_.solution [Fintype n] [Nonempty n] {c : 𝓀[k]ˣ} (hc : c ≠ 1) :
    ∃ (q : Unif k) (ψ : AddChar k Circle) (hψ : SplitWeil.HasConductor ψ 1) (φ : Form k n ℂ),
      φ ∈ Mram k n ℂ ∧ FF q (resChar ψ hψ q) φ ≠ 0 := by
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  obtain ⟨ψ, hψ⟩ := SplitWeil.Model.exists_hasConductor (k := k)
  obtain ⟨φ, h, h0⟩ := (Submodule.ne_bot_iff _).1 (Mram_ne_bot (n := n) hc)
  exact ⟨q, ψ, hψ, φ, h, fun e => h0 (FF_ne_zero q (resChar_ne_one hψ q) h e)⟩
end GlobalTheory.LatPair.Model
