-- Prove2me | solution 1 for GlobalTheory.mem_matroid_closure_of_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:40:42.05783+00:00
-- url     : https://prove2.me/submissions/e1dedf05-93d2-4e73-95a6-30b3d16b3cae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsAlgebraicIndependentRatiosOfGenericZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k κ : Type} [Field k] [Field κ] [Algebra k κ]
    {S : Set κ} {x : κ} (hx : x ∈ Algebra.adjoin k S) :
    x ∈ (AlgebraicIndependent.matroid k κ).closure S := by
  rw [AlgebraicIndependent.matroid_closure_eq]
  exact isAlgebraic_algebraMap (⟨x, hx⟩ : Algebra.adjoin k S)
end GlobalTheory
