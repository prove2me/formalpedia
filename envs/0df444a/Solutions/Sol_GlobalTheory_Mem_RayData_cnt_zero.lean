-- Prove2me | solution 1 for GlobalTheory.Mem.RayData.cnt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:05:41.748323+00:00
-- url     : https://prove2.me/submissions/9dd218f0-4553-400f-924c-17467cdb6f01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem
open NumberField IsDedekindDomain
attribute [instance] RayData.grp RayData.fin
open GlobalTheory.Mem.RayData
variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
namespace GlobalTheory.Mem.RayData
theorem _root_.solution (hM : 2 ≤ M) (c : D.G) : D.cnt c 0 = 0 := by
  have : IsEmpty {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = 0 ∧
      D.cls I = c} :=
    ⟨fun I => RayCl.ne_bot_of_cop hM I.2.1 (Ideal.absNorm_eq_zero_iff.mp I.2.2.1)⟩
  rw [cnt, Nat.card_of_isEmpty, Nat.cast_zero]
end GlobalTheory.Mem.RayData
