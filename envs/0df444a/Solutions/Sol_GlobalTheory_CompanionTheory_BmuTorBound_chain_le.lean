-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuTorBound.chain_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:39:23.164012+00:00
-- url     : https://prove2.me/submissions/4281a08d-f383-4150-908b-323835c85957

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorBound
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero


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
theorem _root_.solution {n : ℕ} (d : Fin n → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hs : ∀ (j : ℕ) (hj : j + 1 < n), d ⟨j, by omega⟩ ≤ M * d ⟨j + 1, hj⟩) (j m : ℕ) (h : j + m < n) :
    d ⟨j, by omega⟩ ≤ M ^ m * d ⟨j + m, h⟩ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := ih (by omega)
    have h2 := hs (j + m) h
    calc d ⟨j, by omega⟩ ≤ M ^ m * d ⟨j + m, by omega⟩ := h1
      _ ≤ M ^ m * (M * d ⟨j + m + 1, h⟩) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = M ^ (m + 1) * d ⟨j + (m + 1), h⟩ := by rw [pow_succ, mul_assoc]; rfl
end GlobalTheory.CompanionTheory.BmuTorBound
