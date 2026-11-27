-- Prove2me | solution 1 for GlobalTheory.ThetaGLSub.IsSub.sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:34:06.872416+00:00
-- url     : https://prove2.me/submissions/bfe17597-55be-4674-8fb3-3013149364d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSubAug
import Theorems.Thm_GlobalTheory_ThetaGLSub_om_add

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
namespace IsSub
theorem _root_.solution {χ : GL (Fin n) k →* ℂˣ} {N N' : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} (h : IsSub χ N)
    (h' : IsSub χ N') : IsSub χ (N ⊔ N') := by
  refine ⟨le_sup_of_le_left h.1, sup_le h.2.1 h'.2.1, fun g Φ hΦ => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hΦ
  rw [om_add]
  exact Submodule.add_mem_sup (h.2.2 g y hy) (h'.2.2 g z hz)
end IsSub
end GlobalTheory.ThetaGLSub
