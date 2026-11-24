-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermPlane.exists_uniformiser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:38:20.959406+00:00
-- url     : https://prove2.me/submissions/b289542b-c842-4b5b-a6ba-ac0e0c36e05f

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PlaneOfHenselAndPairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermPlane
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.HermPlane
theorem _root_.solution [ProperSpace L] :
    ∃ p : L, p ≠ 0 ∧ ‖p‖ < 1 ∧ ∀ a : L, ‖a‖ < 1 → ‖a‖ ≤ ‖p‖ := by
  obtain ⟨a, ha0, ha1⟩ := NormedField.exists_norm_lt_one L
  have hK : IsCompact (Metric.ball (0 : L) 1) :=
    (isCompact_closedBall (0 : L) 1).of_isClosed_subset
      (IsUltrametricDist.isClopen_ball (0 : L) 1).isClosed Metric.ball_subset_closedBall
  have hne : (Metric.ball (0 : L) 1).Nonempty := ⟨0, by simp⟩
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne (continuous_norm.continuousOn)
  have hle : ∀ b : L, ‖b‖ < 1 → ‖b‖ ≤ ‖p‖ := fun b hb => hmax (by simpa using hb)
  have hp1 : ‖p‖ < 1 := by simpa using hp
  refine ⟨p, ?_, hp1, hle⟩
  intro h0
  have := hle a ha1
  rw [h0, norm_zero] at this
  linarith
end GlobalTheory.CompanionTheory.HermPlane
