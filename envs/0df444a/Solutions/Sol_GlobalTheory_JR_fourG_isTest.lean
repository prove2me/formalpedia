-- Prove2me | solution 1 for GlobalTheory.JR.fourG_isTest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:12:10.321362+00:00
-- url     : https://prove2.me/submissions/f6f777b5-e185-4668-bef5-507138f22edc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantPartialFourierGLBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HasCompactSupportPartialFourierGLBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportPartialFourierGLB
import Theorems.Thm_GlobalTheory_JR_exists_nhds_zero_add_invariant_of_isTest
import Theorems.Thm_GlobalTheory_JR_fourG_hasCompactSupport
import Theorems.Thm_GlobalTheory_JR_fourG_isLocallyConstant_of_invariant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    ∀ f' : Gl r F → ℂ, IsTest f' → IsTest (fourG M ψ f') := by
  intro F E _ _ _ _ _ r M ψ hψ f' hf
  have hU : ∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y := by
    exact exists_nhds_zero_add_invariant_of_isTest (X := Gl r F) (f := f') (by exact hf)
  exact ⟨fourG_isLocallyConstant_of_invariant F E r M ψ hψ f' hf hU,
    fourG_hasCompactSupport F E r M ψ hψ f' hf hU⟩
end GlobalTheory.JR
