-- Prove2me | solution 1 for GlobalTheory.multiDiff_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:24.02457+00:00
-- url     : https://prove2.me/submissions/458d15af-34be-439d-9287-eee15e58f04b

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
theorem _root_.solution {ι H : Type*} [Fintype ι] [AddCommGroup H] (f : H →+ G) (g : ι → H)
    (φ : G → M) : multiDiff g (φ ∘ f) = multiDiff (f ∘ g) φ ∘ f := by
  ext x; simp only [multiDiff, Function.comp, map_sum, map_sub]
end GlobalTheory
