-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuWordBd.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:56:26.91865+00:00
-- url     : https://prove2.me/submissions/007f4f51-a5f6-41a0-8c95-fa2298213c2e

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordLengthBoundOfLinear
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuWordBd_exists_basis_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuWordBd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GlobalTheory.CompanionTheory.BmuWordBd
theorem _root_.solution {n : ℕ} (Hm : Mat n) :
    ∃ (N : ℕ) (b : Fin N → Mat n) (κ : ℝ), 0 ≤ κ ∧ (∀ i, Lie Hm (b i)) ∧
      ∀ X, Lie Hm X → ∃ c : Fin N → ℝ, X = ∑ i, c i • b i ∧ ∀ i, |c i| ≤ κ * ‖X‖ := by
  obtain ⟨N, b, κ, hκ, hb, hX⟩ := exists_basis_sub (lieSub Hm)
  exact ⟨N, b, κ, hκ, hb, fun X hXL => hX X hXL⟩
end GlobalTheory.CompanionTheory.BmuWordBd
