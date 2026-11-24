-- Prove2me | solution 1 for GlobalTheory.multiDiff_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:38:54.886932+00:00
-- url     : https://prove2.me/submissions/613a8bdd-4f8c-48e8-9f97-3c6e1b1f6e6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]
namespace GlobalTheory
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ ≃ ι) (g : ι → G)
    (φ : G → M) : multiDiff (g ∘ e) φ = multiDiff g φ := by
  simp only [multiDiff_eq_shiftAct, Function.comp]
  rw [Equiv.prod_comp e (fun i ↦ diffElt (g i))]
end GlobalTheory
