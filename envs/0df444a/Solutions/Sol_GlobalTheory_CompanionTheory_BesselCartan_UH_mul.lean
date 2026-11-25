-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCartan.UH_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:32:28.735348+00:00
-- url     : https://prove2.me/submissions/b69178b5-fe11-493e-8e12-bc2917333aa9

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
theorem _root_.solution {m : ℕ} {H g h : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UH H) (hh : h ∈ UH H) : g * h ∈ UH H := by
  have hUH : ∀ {m : ℕ} (H g : Matrix (Fin m) (Fin m) ℂ), g ∈ UH H ↔ gᴴ * H * g = H := fun _ _ => Iff.rfl
  rw [hUH] at hg hh ⊢
  calc (g * h)ᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = H := by rw [hg, hh]
end GlobalTheory.CompanionTheory.BesselCartan
