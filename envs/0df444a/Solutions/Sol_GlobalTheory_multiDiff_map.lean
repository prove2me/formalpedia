-- Prove2me | solution 1 for GlobalTheory.multiDiff_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:44.109022+00:00
-- url     : https://prove2.me/submissions/825b5f52-4df7-413b-aaf2-bc46c1d52d61

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
theorem _root_.solution {ι N : Type*} [Fintype ι] [AddCommGroup N] (f : M →+ N) (g : ι → G)
    (φ : G → M) : multiDiff g (f ∘ φ) = f ∘ multiDiff g φ := by
  ext x; simp only [multiDiff, Function.comp, map_sum, map_zsmul]
end GlobalTheory
