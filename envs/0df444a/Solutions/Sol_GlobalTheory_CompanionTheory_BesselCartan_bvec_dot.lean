-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCartan.bvec_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:37:16.854488+00:00
-- url     : https://prove2.me/submissions/e3828473-0192-4040-8971-6258d5810472

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselCartan
open scoped ComplexOrder
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.BesselCartan
theorem _root_.solution {m : ℕ} (i j : Fin m) : star (bvec i) ⬝ᵥ bvec j = if i = j then (1 : ℂ) else 0 := by
  have hbv : ∀ {m : ℕ} (i : Fin m), bvec i = Pi.single i (1 : ℂ) := fun _ => rfl
  by_cases h : i = j
  · subst h
    simp [hbv, dotProduct_single]
  · simp [hbv, h, dotProduct_single, Pi.single_apply, Ne.symm h]
end GlobalTheory.CompanionTheory.BesselCartan
