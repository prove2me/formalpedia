-- Prove2me | solution 1 for GlobalTheory.HCXi.VLev.star_e0_dotProduct_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:58:27.303942+00:00
-- url     : https://prove2.me/submissions/f71ed25d-3ac0-4b90-8707-f4127a24a7f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLeviStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeLeviRecursion
import Theorems.Thm_GlobalTheory_HCXi_VLev_star_e0_dotProduct

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
namespace GlobalTheory.HCXi.VLev
theorem _root_.solution (k r' : ℕ) : star (e0 k r') ⬝ᵥ e0 k r' = 1 := by
  rw [star_e0_dotProduct]; simp [e0, bvec]
end GlobalTheory.HCXi.VLev
