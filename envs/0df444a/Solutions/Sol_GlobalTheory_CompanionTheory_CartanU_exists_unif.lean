-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartanU.exists_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:21:42.573374+00:00
-- url     : https://prove2.me/submissions/4247b428-0692-47f0-9063-3b73d12f4a53

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsometricLatticeCongruenceSubgroups
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartanU
namespace GlobalTheory.CompanionTheory.CartanU
theorem _root_.solution (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] :
    ∃ p : L, p ≠ 0 ∧ ‖p‖ < 1 ∧ ∀ a : L, ‖a‖ < 1 → ‖a‖ ≤ ‖p‖ := by
  obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one L
  have hclosed : IsClosed ({a : L | ‖x‖ ≤ ‖a‖} ∩ Metric.ball 0 1) :=
    (isClosed_le continuous_const continuous_norm).inter (IsUltrametricDist.isClopen_ball (0 : L) 1).isClosed
  have hcomp : IsCompact ({a : L | ‖x‖ ≤ ‖a‖} ∩ Metric.ball 0 1) :=
    (isCompact_closedBall (0 : L) 1).of_isClosed_subset hclosed
      (fun a ha => Metric.ball_subset_closedBall ha.2)
  obtain ⟨p, hpA, hmax⟩ := hcomp.exists_isMaxOn ⟨x, le_refl ‖x‖, by simpa using hx1⟩
    continuous_norm.continuousOn
  have hp1 : ‖p‖ < 1 := by simpa using hpA.2
  have hxp : ‖x‖ ≤ ‖p‖ := hpA.1
  refine ⟨p, fun h => ?_, hp1, fun a ha => ?_⟩
  · rw [h, norm_zero] at hxp; linarith
  · by_cases h : ‖x‖ ≤ ‖a‖
    · exact hmax ⟨h, by simpa using ha⟩
    · exact (not_le.1 h).le.trans hxp
end GlobalTheory.CompanionTheory.CartanU
