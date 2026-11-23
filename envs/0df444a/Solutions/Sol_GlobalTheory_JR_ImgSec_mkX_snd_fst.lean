-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.mkX_snd_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:10.057385+00:00
-- url     : https://prove2.me/submissions/224f02e5-f3e0-4eb4-82ff-144a36ed4538

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector

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
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}
namespace GlobalTheory.JR.ImgSec
theorem _root_.solution (a : Inv r F) (h : Matrix (Fin r) (Fin r) E) : (mkX a h).2.1 = h *ᵥ e1 := rfl
end GlobalTheory.JR.ImgSec
