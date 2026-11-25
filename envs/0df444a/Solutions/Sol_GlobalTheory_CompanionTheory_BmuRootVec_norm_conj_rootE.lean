-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuRootVec.norm_conj_rootE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:29:53.215586+00:00
-- url     : https://prove2.me/submissions/ca03e1e6-0259-4c59-a0ca-8182e7d9bb4e

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_RootVectors
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_mul_single_mul_entry
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply


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
theorem _root_.solution {R : Mat (2 * r + k + 1)} (hR : Rᴴ * R = 1) (a : Fin r) (κ : ℂ) :
    ‖Rᴴ * rootE k r a κ * R‖ ≤ 2 * ‖κ‖ := by
  have hb : ∀ i j, ‖R i j‖ ≤ 1 := fun i j =>
    entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 hR) i j
  have key : ∀ (p q i l : Fin (2 * r + k + 1)) (c : ℂ), ‖(Rᴴ * single p q c * R) i l‖ ≤ ‖c‖ := by
    intro p q i l c
    rw [mul_single_mul_entry, norm_mul, norm_mul, conjTranspose_apply, norm_star]
    calc ‖R p i‖ * ‖c‖ * ‖R q l‖ ≤ 1 * ‖c‖ * 1 := by gcongr <;> apply hb
      _ = ‖c‖ := by ring
  rw [Matrix.norm_le_iff (by positivity)]
  intro i l
  rw [rootE, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
  refine (norm_sub_le _ _).trans ?_
  have h1 := key (eI k r a) (nxt k r a) i l κ
  have h2 := key (nxtS k r a) (esI k r a) i l (conj κ)
  rw [Complex.norm_conj] at h2
  linarith
end GlobalTheory.CompanionTheory.BmuRootVec
