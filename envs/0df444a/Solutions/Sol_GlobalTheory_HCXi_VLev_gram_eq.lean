-- Prove2me | solution 1 for GlobalTheory.HCXi.VLev.gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:31:52.788999+00:00
-- url     : https://prove2.me/submissions/b7825fca-6188-4fc2-8966-a316a845efef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLeviStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeLeviRecursion

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
theorem _root_.solution (k r : ℕ) (g : Mat k r) (j : Fin (r + 1)) :
    gram k r g j = (Matrix.of fun i i' : Fin (j.val + 1) =>
      star (g *ᵥ fvec k r (isoVec k r) (Fin.castLE (Nat.succ_le_of_lt j.isLt) i)) ⬝ᵥ
        (g *ᵥ fvec k r (isoVec k r) (Fin.castLE (Nat.succ_le_of_lt j.isLt) i'))).det.re := by
  unfold gram
  congr 2
end GlobalTheory.HCXi.VLev
