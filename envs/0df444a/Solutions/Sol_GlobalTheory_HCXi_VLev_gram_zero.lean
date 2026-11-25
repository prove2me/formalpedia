-- Prove2me | solution 1 for GlobalTheory.HCXi.VLev.gram_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:04:02.025838+00:00
-- url     : https://prove2.me/submissions/36a1851e-40ec-4e91-8201-72bc70b29ce6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLeviStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeLeviRecursion
import Theorems.Thm_GlobalTheory_HCXi_VLev_det_gram_cons
import Theorems.Thm_GlobalTheory_HCXi_VLev_gram_eq
import Theorems.Thm_GlobalTheory_HCXi_VLev_fvec_zero
import Theorems.Thm_GlobalTheory_HCXi_VLev_star_e0_dotProduct_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.VLev
variable {k r' : ℕ} (M : Mat k (1 + r')) (h : Mat k r') (a : ℂ) (hM0 : M *ᵥ e0 k r' = a • e0 k r')
  (hM : ∀ w : Fin (2 * r' + k + 1) → ℂ, ∃ c : ℂ, M *ᵥ liftVec k 1 r' w = liftVec k 1 r' (h *ᵥ w) + c • e0 k r')
include hM0
namespace GlobalTheory.HCXi.VLev
theorem _root_.solution (j : Fin (1 + r' + 1)) (hj : j.val = 0) : gram k (1 + r') M j = Complex.normSq a := by
  obtain ⟨j, hj'⟩ := j
  simp only at hj
  subst hj
  rw [gram_eq]
  rw [det_gram_cons (m := 0) (e0 k r') (star_e0_dotProduct_self k r') Fin.elim0 (fun b => b.elim0) a Fin.elim0 _
    (by rw [fvec_zero _ _ _ rfl, hM0]) (fun b => b.elim0)]
  simp
end GlobalTheory.HCXi.VLev
