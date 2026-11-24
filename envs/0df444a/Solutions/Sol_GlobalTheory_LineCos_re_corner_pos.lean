-- Prove2me | solution 1 for GlobalTheory.LineCos.re_corner_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:24:41.777858+00:00
-- url     : https://prove2.me/submissions/45c5ea51-5cd7-4f68-a996-b8225c8ffe37

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Theorems.Thm_GlobalTheory_LineCos_re_hform_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LineCos
namespace GlobalTheory.LineCos
theorem _root_.solution {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) : 0 < (G 0 0).re := by
  have := re_hform_pos hG (a := Pi.single 0 1) (by simp)
  simpa [hform, Fin.sum_univ_two, Pi.single_apply] using this
end GlobalTheory.LineCos
