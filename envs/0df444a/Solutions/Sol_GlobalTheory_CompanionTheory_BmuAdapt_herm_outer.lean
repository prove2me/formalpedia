-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuAdapt.herm_outer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:33:18.997982+00:00
-- url     : https://prove2.me/submissions/2eb6a748-87c3-4262-bee9-0a31e3155f2f

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AdaptExists
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_herm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuAdapt
namespace GlobalTheory.CompanionTheory.BmuAdapt
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val)
    (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) : herm (Hpk k r) (bvec i) z = 0 := by
  unfold herm dotProduct
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j.val < r ∨ r + k < j.val
  · simp [hz j hj]
  · have : Hpk k r j i = 0 := by
      have := i.isLt
      simp only [Hpk, Fin.ext_iff]
      split_ifs <;> first | (exfalso; omega) | rfl
    simp [bvec, this]
end GlobalTheory.CompanionTheory.BmuAdapt
