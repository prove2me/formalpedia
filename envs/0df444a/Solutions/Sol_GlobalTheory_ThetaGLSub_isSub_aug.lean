-- Prove2me | solution 1 for GlobalTheory.ThetaGLSub.isSub_aug
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:34:09.174965+00:00
-- url     : https://prove2.me/submissions/f1d18d71-20d9-45e7-bec9-d10a9dc9777a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSubAug
import Theorems.Thm_GlobalTheory_ThetaGLSub_om_add
import Theorems.Thm_GlobalTheory_ThetaGLSub_om_smul
import Theorems.Thm_GlobalTheory_ThetaGLSub_om_sub
import Theorems.Thm_GlobalTheory_ThetaGLSub_om_comm
import Theorems.Thm_GlobalTheory_ThetaGLSub_aug_le_SB
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mem_SB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.SplitWeil
open GlobalTheory GlobalTheory.ThetaGLSub
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
variable {m : ℕ}
namespace GlobalTheory.ThetaGLSub
theorem _root_.solution (χ : GL (Fin n) k →* ℂˣ) : IsSub χ (aug m χ) := by
  refine ⟨le_rfl, aug_le_SB χ, fun g Φ hΦ => ?_⟩
  induction hΦ using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨h, Ψ, hΨ, rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨h, om 1 g 1 Ψ, Model.om_mem_SB 1 g 1 hΨ, ?_⟩
    rw [om_sub, om_smul, om_comm]
  | zero =>
    rw [show om (1 : kˣ →* ℂˣ) g (1 : GL (Fin n) k) 0 = 0 from funext fun x => by simp [om]]
    exact (aug m χ).zero_mem
  | add x y _ _ hx hy => rw [om_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [om_smul]; exact Submodule.smul_mem _ c hx
end GlobalTheory.ThetaGLSub
