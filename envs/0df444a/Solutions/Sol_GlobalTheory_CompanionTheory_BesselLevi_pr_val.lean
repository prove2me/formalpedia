-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselLevi.pr_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:58:34.816246+00:00
-- url     : https://prove2.me/submissions/ad868534-d3fa-4b62-8bee-fcf3214df94e

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LeviDecomposition

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
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    ((i.val ≤ r ∨ r + k ≤ i.val) ∧ (pr k r i).val + i.val = 2 * r + k) ∨
      (r < i.val ∧ i.val < r + k ∧ (pr k r i).val = i.val) := by
  unfold pr
  have := i.isLt
  by_cases h : outer k r i
  · rw [if_pos h]
    left
    refine ⟨h, ?_⟩
    simp only
    omega
  · rw [if_neg h]
    unfold outer at h
    right
    omega
end GlobalTheory.CompanionTheory.BesselLevi
