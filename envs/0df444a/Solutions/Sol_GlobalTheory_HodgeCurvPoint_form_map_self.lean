-- Prove2me | solution 1 for GlobalTheory.HodgeCurvPoint.form_map_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:58:31.689613+00:00
-- url     : https://prove2.me/submissions/0e090f8a-e170-4a3a-a263-b47a906753f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBound
import Theorems.Thm_GlobalTheory_HodgeCurvPoint_re_form_map
import Theorems.Thm_GlobalTheory_HodgeCurvPoint_isHermitian_map
import Theorems.Thm_GlobalTheory_HermFrame_conj_form


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeCurvPoint
variable {g : ℕ}
namespace GlobalTheory.HodgeCurvPoint
theorem _root_.solution {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.IsSymm) (v : Fin g → ℂ) :
    form (M.map ofReal) v v = (((fun j => (v j).re) ⬝ᵥ M *ᵥ (fun j => (v j).re) +
      (fun j => (v j).im) ⬝ᵥ M *ᵥ (fun j => (v j).im) : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [re_form_map, ofReal_re]
  · rw [ofReal_im]
    exact Complex.conj_eq_iff_im.mp (conj_form (isHermitian_map hM) v v)
end GlobalTheory.HodgeCurvPoint
