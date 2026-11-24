-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisTwist.twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:53.778218+00:00
-- url     : https://prove2.me/submissions/9f6c1b23-5411-4ae0-ab1d-54f28e59db54

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_Descend
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistOfSectionLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTwist_twRep_cont
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTwist_sec_twist
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTwist_leftGood_cast
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTwist_wall_twist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisTwist
open PositivityTheory.RgEis
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K : Subgroup G} {c₀ : G → ℂ}
namespace GlobalTheory.CompanionTheory.RgEisTwist
theorem _root_.solution : SecLaw → Twist := by
  intro _ G _ _ _ _ _ Γ K S P P' c c₀ η η' β ξ N _ h _ _ _
  refine ⟨fun hA W _ _ _ ρ hρ => ?_, fun hA W _ _ _ ρ hρ => ?_, fun hA W _ _ _ ρ hρ => ?_⟩
  · obtain ⟨R, D, Op, H, hw⟩ := hA W (twRep h K ρ) (twRep_cont h hρ)
    unfold HasWall
    rw [secSp_twist h ρ P c]
    exact ⟨R, D, _, _, wall_twist h hw⟩
  · obtain ⟨R, D, Op, H, hw, ⟨a, ha0, ha⟩, O, hO, hOp⟩ := hA W (twRep h K ρ) (twRep_cont h hρ)
    unfold HasFirst
    rw [secSp_twist h ρ S c]
    refine ⟨R, D, _, _, wall_twist h hw, ⟨a, ha0, fun g w => ?_⟩,
      fun z => (castL (secSp_twist h ρ P' c).symm).comp (O z), leftGood_cast _ hO, fun z hz => ?_⟩
    · rw [ContinuousLinearMap.smul_apply, ha g w, sec_twist h, ContinuousLinearMap.smul_apply, smul_comm]
    · change (castL (secSp_twist h ρ P' c).symm).comp (Op z) = _
      rw [hOp z hz, ContinuousLinearMap.comp_smul]
  · obtain ⟨R, D, Op, H, hw, hd, T, hT⟩ := hA W (twRep h K ρ) (twRep_cont h hρ)
    unfold HasLast
    rw [secSp_twist h ρ P c]
    refine ⟨R, D, _, _, wall_twist h hw, hd,
      (castL (secSp_twist h ρ S c).symm).comp T, fun g w => ?_⟩
    rw [ContinuousLinearMap.smul_apply, hT g w, sec_twist h, ContinuousLinearMap.smul_apply, smul_comm]
    rfl
end GlobalTheory.CompanionTheory.RgEisTwist
