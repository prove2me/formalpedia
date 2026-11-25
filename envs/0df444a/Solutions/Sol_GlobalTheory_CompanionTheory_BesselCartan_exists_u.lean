-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCartan.exists_u
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:38:02.479391+00:00
-- url     : https://prove2.me/submissions/f5821762-3330-4b05-8b1c-e9dafa30d9b7

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
theorem _root_.solution (N : ℝ) (hN : 2 ≤ N) : ∃ u : ℝ, 0 < u ∧ u ≤ 1 ∧ u⁻¹ ^ 2 + u ^ 2 = N := by
  have hd0 : 0 ≤ N ^ 2 - 4 := by nlinarith
  set d := Real.sqrt (N ^ 2 - 4) with hd
  have hdsq : d ^ 2 = N ^ 2 - 4 := Real.sq_sqrt hd0
  have hdlt : d < N := by
    rw [hd]
    exact (Real.sqrt_lt' (by linarith)).mpr (by linarith)
  have hdge : N - 2 ≤ d := by
    have h1 : (N - 2) ^ 2 ≤ N ^ 2 - 4 := by nlinarith
    calc N - 2 = Real.sqrt ((N - 2) ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ d := Real.sqrt_le_sqrt h1
  set s := (N - d) / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  have hprod : s * (N - s) = 1 := by
    rw [hs]
    linear_combination (-1 / 4 : ℝ) * hdsq
  have hinv : N - s = s⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hprod)
  refine ⟨Real.sqrt s, Real.sqrt_pos.mpr hs0, ?_, ?_⟩
  · calc Real.sqrt s ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hs1
      _ = 1 := Real.sqrt_one
  · rw [inv_pow, Real.sq_sqrt hs0.le, ← hinv]
    ring
end GlobalTheory.CompanionTheory.BesselCartan
