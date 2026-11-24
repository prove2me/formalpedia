-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.semiconj_of_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:59:51.370335+00:00
-- url     : https://prove2.me/submissions/bdde0e45-545a-4fac-bbc7-6ad0a5c80eb8

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
theorem _root_.solution (g : Matrix.unitaryGroup (Fin r) E) (X₁ X₂ : Hn r F E) (hact : actU g X₁ = X₂) :
    g.1 * X₁.1.1 = X₂.1.1 * g.1 := by
  have e1 : g.1 * X₁.1.1 * star g.1 = X₂.1.1 := congrArg (fun Y : Hn r F E => Y.1.1) hact
  rw [← e1, mul_assoc _ (star g.1), starU_mul, mul_one]
end GlobalTheory.JR.HermInv
