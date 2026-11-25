-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuTorBound.unitary_conj_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:05:23.039097+00:00
-- url     : https://prove2.me/submissions/604bee4c-2fb6-40d4-ab29-60d0847c2ba9

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix CompanionTheory.Bmu Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuTorBound
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GlobalTheory.CompanionTheory.BmuTorBound
theorem _root_.solution {n : ℕ} (R B : Mat n) (hR : Rᴴ * R = 1) : ‖Rᴴ * B * R‖ ≤ (n : ℝ) ^ 2 * ‖B‖ := by
  have hU : R ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.mpr hR
  have he : ∀ i j, ‖R i j‖ ≤ 1 := fun i j => entry_norm_bound_of_unitary hU i j
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  have h1 : ∀ l, ‖(Rᴴ * B) i l‖ ≤ n * ‖B‖ := by
    intro l
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ ‖B‖ ?_).trans (by simp)
    intro x _
    rw [norm_mul, Matrix.conjTranspose_apply, norm_star]
    calc ‖R x i‖ * ‖B x l‖ ≤ 1 * ‖B‖ :=
          mul_le_mul (he x i) (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) zero_le_one
      _ = ‖B‖ := one_mul _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (n * ‖B‖) ?_).trans (by simp [sq, mul_assoc])
  intro x _
  rw [norm_mul]
  calc ‖(Rᴴ * B) i x‖ * ‖R x j‖ ≤ n * ‖B‖ * 1 :=
        mul_le_mul (h1 x) (he x j) (norm_nonneg _) (by positivity)
    _ = n * ‖B‖ := mul_one _
end GlobalTheory.CompanionTheory.BmuTorBound
