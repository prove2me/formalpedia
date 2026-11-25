-- Prove2me | solution 1 for GlobalTheory.HCXi.VLev.gram_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:36:22.559719+00:00
-- url     : https://prove2.me/submissions/b32cdeff-24b5-4775-b70f-636da05be400

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLeviStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeLeviRecursion
import Theorems.Thm_GlobalTheory_HCXi_VLev_det_gram_cons
import Theorems.Thm_GlobalTheory_HCXi_VLev_gram_eq
import Theorems.Thm_GlobalTheory_HCXi_VLev_fvec_zero
import Theorems.Thm_GlobalTheory_HCXi_VLev_fvec_succ
import Theorems.Thm_GlobalTheory_HCXi_VLev_star_e0_dotProduct_self
import Theorems.Thm_GlobalTheory_HCXi_VLev_star_e0_dotProduct_lift
import Theorems.Thm_PI_QnLevBasicsW_dot_lift


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
include hM
namespace GlobalTheory.HCXi.VLev
theorem _root_.solution (j : Fin (1 + r' + 1)) (b : Fin (r' + 1)) (hj : j.val = b.val + 1) :
    gram k (1 + r') M j = Complex.normSq a * gram k r' h b := by
  obtain ⟨j, hj'⟩ := j
  simp only at hj
  subst hj
  choose c hc using hM
  rw [gram_eq, gram_eq]
  rw [det_gram_cons (m := b.val + 1) (e0 k r') (star_e0_dotProduct_self k r')
    (fun i => liftVec k 1 r' (h *ᵥ fvec k r' (isoVec k r') (Fin.castLE (Nat.succ_le_of_lt b.isLt) i)))
    (fun _ => star_e0_dotProduct_lift _ _ _) a
    (fun i => c (fvec k r' (isoVec k r') (Fin.castLE (Nat.succ_le_of_lt b.isLt) i))) _
    (by rw [fvec_zero _ _ _ rfl, hM0])
    (fun i => by rw [fvec_succ _ _ _ (Fin.castLE (Nat.succ_le_of_lt b.isLt) i) rfl, hc])]
  simp only [PI.QnLevBasicsW.dot_lift, Complex.re_ofReal_mul]
end GlobalTheory.HCXi.VLev
