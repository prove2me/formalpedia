-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuRootVec.frame_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:37:14.137253+00:00
-- url     : https://prove2.me/submissions/0830f6c6-8af7-4242-ae2b-278e47da10fb

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_RootVectors
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_Hq_row
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_col_of_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuRootVec
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.BmuRootVec
theorem _root_.solution {Γ : Mat (2 * r + k + 1)} (hΓ : Γᴴ * Hpk k r * Γ = Hq k r)
    {i i' : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) (h : i.val + i'.val = 2 * r + k)
    (hf : Γ *ᵥ bvec i = bvec i) (l : Fin (2 * r + k + 1)) : Γ i' l = if l = i' then 1 else 0 := by
  have h1 := congrFun (congrFun hΓ i) l
  rw [Hq_row (i' := i') (by simp only [outer]; omega) h, Matrix.mul_assoc, Matrix.mul_apply,
    Finset.sum_eq_single i, conjTranspose_apply, col_of_mulVec hf, if_pos rfl, star_one, one_mul,
    Matrix.mul_apply, Finset.sum_eq_single i'] at h1
  · rw [← h1]
    have : Hpk k r i i' = 1 := by
      simp only [Hpk]
      split_ifs <;> first | rfl | omega
    rw [this, one_mul]
  · intro b _ hb
    have hb' : b.val ≠ i'.val := fun e => hb (Fin.ext e)
    have : Hpk k r i b = 0 := by
      simp only [Hpk]
      split_ifs <;> first | rfl | omega
    rw [this, zero_mul]
  · simp
  · intro b _ hb
    rw [conjTranspose_apply, col_of_mulVec hf, if_neg hb, star_zero, zero_mul]
  · simp
end GlobalTheory.CompanionTheory.BmuRootVec
