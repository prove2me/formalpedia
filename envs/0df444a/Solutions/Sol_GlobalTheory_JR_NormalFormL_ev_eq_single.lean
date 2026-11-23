-- Prove2me | solution 1 for GlobalTheory.JR.NormalFormL.ev_eq_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:47.427707+00:00
-- url     : https://prove2.me/submissions/e6a6efd5-2a27-4def-99b1-817e612a7391

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}
namespace GlobalTheory.JR.NormalFormL
theorem _root_.solution (i : ℕ) (hi : i < r) : ev r k i = Pi.single (⟨i, hi⟩ : Fin r) 1 := by
  funext j
  simp only [ev, Pi.single_apply, Fin.ext_iff]
end GlobalTheory.JR.NormalFormL
