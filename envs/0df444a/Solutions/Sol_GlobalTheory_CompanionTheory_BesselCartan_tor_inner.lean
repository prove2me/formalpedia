-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCartan.tor_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:59:13.570711+00:00
-- url     : https://prove2.me/submissions/391a258f-4017-4113-a6db-66d38163b49e

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
theorem _root_.solution (k r : ℕ) (u : ℝ) (i : Fin (2 * r + k + 1)) (hi : ¬ outer k r i) : tor k r u i = 1 := by
  have hout : outer k r i ↔ ((i : ℕ) ≤ r ∨ r + k ≤ (i : ℕ)) := Iff.rfl
  rw [hout] at hi
  unfold GlobalTheory.CompanionTheory.BesselCartan.tor
  split_ifs <;> first | rfl | omega
end GlobalTheory.CompanionTheory.BesselCartan
