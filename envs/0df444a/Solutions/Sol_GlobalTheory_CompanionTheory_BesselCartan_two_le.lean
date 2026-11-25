-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCartan.two_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:38:55.277605+00:00
-- url     : https://prove2.me/submissions/4f91e4cc-697d-45e4-a66f-92ff4bfd5d6b

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_dot_herm
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply


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
theorem _root_.solution (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1) (y : Fin n → ℂ)
    (h : star y ⬝ᵥ H *ᵥ y = -2) : ∃ N : ℝ, 2 ≤ N ∧ star y ⬝ᵥ y = N := by
  have hS : star (H *ᵥ y) ⬝ᵥ (H *ᵥ y) = star y ⬝ᵥ y := by
    rw [GlobalTheory.CompanionTheory.BesselCartan.dot_herm H hH, Matrix.mulVec_mulVec, hHH, Matrix.one_mulVec]
  have hC : star (H *ᵥ y) ⬝ᵥ y = -2 := by
    rw [GlobalTheory.CompanionTheory.BesselCartan.dot_herm H hH, h]
  have hnn := dotProduct_star_self_nonneg (y + H *ᵥ y)
  rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add, hS, hC, h] at hnn
  have h2 : (0 : ℂ) ≤ 2 * (star y ⬝ᵥ y) - 4 := by
    convert hnn using 1
    ring
  obtain ⟨hre, him⟩ := Complex.le_def.mp h2
  simp at hre him
  refine ⟨(star y ⬝ᵥ y).re, by linarith, ?_⟩
  apply Complex.ext
  · simp
  · simp
    linarith
end GlobalTheory.CompanionTheory.BesselCartan
