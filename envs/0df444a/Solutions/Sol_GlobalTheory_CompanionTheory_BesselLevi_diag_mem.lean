-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselLevi.diag_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:01:32.760447+00:00
-- url     : https://prove2.me/submissions/babc8c5c-7d2e-47ca-a567-cca2045cd89a

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LeviDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselLevi
namespace GlobalTheory.CompanionTheory.BesselLevi
theorem _root_.solution (k r : ℕ) (d : Fin (2 * r + k + 1) → ℂ) (hd : ∀ i, conj (d i) * d (pr k r i) = 1) :
    Matrix.diagonal d ∈ UH (Hq k r) := by
  rw [mem_iff]
  intro i j
  rw [Finset.sum_eq_single i]
  · by_cases h : pr k r i = j
    · subst h
      simp [hd]
    · simp [h]
  · intro x _ hx
    simp [hx]
  · simp
end GlobalTheory.CompanionTheory.BesselLevi
