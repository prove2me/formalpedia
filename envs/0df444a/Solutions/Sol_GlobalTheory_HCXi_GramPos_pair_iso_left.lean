-- Prove2me | solution 1 for GlobalTheory.HCXi.GramPos.pair_iso_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:44:27.942871+00:00
-- url     : https://prove2.me/submissions/b189767c-1c76-45b5-9e75-512fc378063a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuous
import Theorems.Thm_GlobalTheory_HCXi_GramPos_bvec_pair

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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.GramPos
namespace GlobalTheory.HCXi.GramPos
theorem _root_.solution (k r : ℕ) (M : Mat k r) (j) :
    star (isoVec k r) ⬝ᵥ M *ᵥ bvec j =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (M (wI k r 0) j + M (wI k r (Fin.last k)) j) := by
  rw [isoVec, star_smul, star_add, smul_dotProduct, add_dotProduct, bvec_pair, bvec_pair]
  simp
end GlobalTheory.HCXi.GramPos
