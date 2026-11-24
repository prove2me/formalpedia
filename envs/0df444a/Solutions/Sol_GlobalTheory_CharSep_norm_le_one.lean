-- Prove2me | solution 1 for GlobalTheory.CharSep.norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:43.834187+00:00
-- url     : https://prove2.me/submissions/a3375db8-44a4-434d-95e2-87c252a47e7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryAndSeparates
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.CharSep
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CharSep
theorem _root_.solution (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) (x : k) : ‖ψ0 x‖ ≤ 1 := by
  obtain ⟨B, hB⟩ := (SplitWeil.isCompact_int k).exists_bound_of_continuousOn
    (f := fun y => ψ0 (x * y)) (hc.comp (continuous_const.mul continuous_id)).continuousOn
  have hpow : ∀ m : ℕ, ‖ψ0 x‖ ^ m ≤ B := fun m => by
    have hm : ((m : k)) ∈ 𝒪[k] := by
      simpa using (Subring.natCast_mem (𝒪[k]) m)
    have := hB _ hm
    rwa [show x * (m : k) = m • x by rw [nsmul_eq_mul, mul_comm], AddChar.map_nsmul_eq_pow, norm_pow] at this
  by_contra h
  push_neg at h
  obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop B |>.exists
  exact absurd (hpow m) (not_le.mpr hm)
end GlobalTheory.CharSep
