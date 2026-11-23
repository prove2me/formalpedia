-- Prove2me | solution 1 for GroundTheory.Global.inner_toMixed_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:28.531253+00:00
-- url     : https://prove2.me/submissions/e2b1ca16-6c7a-4a53-8903-565395bf1cbf

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real ENNReal SchwartzMap
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (x y : mixedSpace K) :
    ⟪(euclidean.toMixed K).symm x, (euclidean.toMixed K).symm y⟫ =
      ∑ w, x.1 w * y.1 w + ∑ w, (conj (x.2 w) * y.2 w).re := by
  simp [euclidean.toMixed, PiLp.inner_apply, real_inner_eq_re_inner]
  congr 1 <;> exact Finset.sum_congr rfl fun w _ => by ring
end GroundTheory.Global
