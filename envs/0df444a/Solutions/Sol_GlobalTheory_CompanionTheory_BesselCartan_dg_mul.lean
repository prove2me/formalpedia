-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCartan.dg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:55:28.174239+00:00
-- url     : https://prove2.me/submissions/a873b4ff-8577-4607-b36a-b6449a552e0a

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
theorem _root_.solution (k r : ℕ) (u : ℝ) (hu : u ≠ 0) : dg (tor k r u⁻¹) * dg (tor k r u) = 1 := by
  have hdg : ∀ {m : ℕ} (d : Fin m → ℝ), dg d = Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) := fun _ => rfl
  have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu
  rw [hdg, hdg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [GlobalTheory.CompanionTheory.BesselCartan.tor]
  split_ifs <;> push_cast <;> simp [hu']
end GlobalTheory.CompanionTheory.BesselCartan
