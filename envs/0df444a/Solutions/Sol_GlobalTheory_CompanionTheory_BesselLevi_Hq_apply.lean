-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselLevi.Hq_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:15:49.555276+00:00
-- url     : https://prove2.me/submissions/6fa0537a-74ff-4ff1-a139-b51fe50ce24e

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LeviDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_pr_val

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
theorem _root_.solution (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hq k r i j = if pr k r i = j then 1 else 0 := by
  have h1 := pr_val k r i
  unfold Hq
  by_cases h : outer k r i
  · rw [if_pos h]
    unfold outer at h
    refine if_congr ?_ rfl rfl
    rw [Fin.ext_iff]
    omega
  · rw [if_neg h]
    unfold outer at h
    refine if_congr ?_ rfl rfl
    rw [Fin.ext_iff, Fin.ext_iff]
    omega
end GlobalTheory.CompanionTheory.BesselLevi
