-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.mul_starU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:59:49.371922+00:00
-- url     : https://prove2.me/submissions/421eec31-5677-4503-b866-e9f05afae3d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive

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
theorem _root_.solution (g : Matrix.unitaryGroup (Fin r) E) : g.1 * star g.1 = 1 := Matrix.mem_unitaryGroup_iff.1 g.2
end GlobalTheory.JR.HermInv
