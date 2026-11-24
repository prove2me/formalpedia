-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.comp_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:59:49.782566+00:00
-- url     : https://prove2.me/submissions/a4aaaa48-9410-4644-a1ab-fdb482452f03

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
theorem _root_.solution {K L : Type} [CommRing K] [CommRing L] (f : K →+* L) (p : Fin r → K) :
    (companion p).map f = companion (fun i => f (p i)) := by
  ext i j
  simp only [map_apply, companion, of_apply]
  split_ifs <;> simp
end GlobalTheory.JR.HermInv
