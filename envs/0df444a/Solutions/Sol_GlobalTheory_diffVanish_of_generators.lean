-- Prove2me | solution 1 for GlobalTheory.diffVanish_of_generators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:38:03.081798+00:00
-- url     : https://prove2.me/submissions/60ea56f5-ede9-4423-bbb8-5a384183f241

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
theorem _root_.solution {S : Set G} (hS : AddSubgroup.closure S = ⊤) {n : ℕ}
    {φ : G → M} (h : ∀ g : Fin n → G, (∀ i, g i ∈ S) → multiDiff g φ = 0) :
    DiffVanish n φ := fun g ↦ by
  rw [multiDiff_eq_shiftAct]
  exact shiftAct_eq_zero_of_generators hS h (by simpa using prod_diffElt_mem univ g)
end GlobalTheory
