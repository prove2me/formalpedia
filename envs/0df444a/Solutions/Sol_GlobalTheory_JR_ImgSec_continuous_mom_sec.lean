-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.continuous_mom_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:19:52.787788+00:00
-- url     : https://prove2.me/submissions/7bd8a526-6fe3-4149-938b-d8f5c485413f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Theorems.Thm_GlobalTheory_JR_ImgSec_continuous_companion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ImgSec
variable {k : Type} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] {r : ℕ}
namespace GlobalTheory.JR.ImgSec
theorem _root_.solution (n : ℕ) : Continuous (fun a : Inv r k => mom (sec a) n) := by
  simp only [mom, sec]
  exact (continuous_fst.comp continuous_snd).dotProduct
    (((continuous_companion.comp continuous_fst).pow n).matrix_mulVec continuous_const)
end GlobalTheory.JR.ImgSec
