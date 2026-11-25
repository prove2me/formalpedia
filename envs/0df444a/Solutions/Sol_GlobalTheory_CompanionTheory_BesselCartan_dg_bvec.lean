-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCartan.dg_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:57:26.829377+00:00
-- url     : https://prove2.me/submissions/47b8ec7e-e0ff-49f8-8a1d-5ee05f392988

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
theorem _root_.solution {m : ℕ} (d : Fin m → ℝ) (i : Fin m) : dg d *ᵥ bvec i = (d i : ℂ) • bvec i := by
  have hbv : ∀ {m : ℕ} (i : Fin m), bvec i = Pi.single i (1 : ℂ) := fun _ => rfl
  have hdg : ∀ {m : ℕ} (d : Fin m → ℝ), dg d = Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) := fun _ => rfl
  rw [hdg, hbv]
  funext m
  by_cases h : m = i
  · subst h
    simp [Matrix.mulVec_diagonal]
  · simp [Matrix.mulVec_diagonal, Pi.single_apply, h]
end GlobalTheory.CompanionTheory.BesselCartan
