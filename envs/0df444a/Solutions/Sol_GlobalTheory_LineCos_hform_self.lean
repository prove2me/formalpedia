-- Prove2me | solution 1 for GlobalTheory.LineCos.hform_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:45:08.668799+00:00
-- url     : https://prove2.me/submissions/3cd41835-083e-49a2-8386-daaf3125ff85

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq

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
theorem _root_.solution (G : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin 2 → ℂ) :
    hform G a a = star (starRingEnd ℂ ∘ a) ⬝ᵥ (G *ᵥ (starRingEnd ℂ ∘ a)) := by
  simp only [hform, dotProduct, mulVec, Fin.sum_univ_two, Function.comp_apply, Pi.star_apply, RCLike.star_def,
    Complex.conj_conj]
  ring
end GlobalTheory.LineCos
