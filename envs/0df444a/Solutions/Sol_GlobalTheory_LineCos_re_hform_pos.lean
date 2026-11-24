-- Prove2me | solution 1 for GlobalTheory.LineCos.re_hform_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:00:44.172472+00:00
-- url     : https://prove2.me/submissions/f42d2341-672a-4fd6-970a-2d8ed4b8f403

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Theorems.Thm_GlobalTheory_LineCos_hform_self

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
theorem _root_.solution {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) {a : Fin 2 → ℂ} (ha : a ≠ 0) :
    0 < (hform G a a).re := by
  have hne : (starRingEnd ℂ ∘ a) ≠ 0 := fun h => ha (funext fun i => by
    simpa using congrFun h i)
  have := hG.dotProduct_mulVec_pos hne
  rw [hform_self]
  exact (Complex.pos_iff.1 this).1
end GlobalTheory.LineCos
