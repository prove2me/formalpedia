-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.charpoly_actU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:59:47.605846+00:00
-- url     : https://prove2.me/submissions/f24bba5e-5d46-4b9f-973f-43d6c4a167cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_starU_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ}
namespace GlobalTheory.JR.HermInv
theorem _root_.solution (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) :
    (actU g X).1.1.charpoly = X.1.1.charpoly := by
  show (g.1 * X.1.1 * star g.1).charpoly = _
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, starU_mul g, one_mul]
end GlobalTheory.JR.HermInv
