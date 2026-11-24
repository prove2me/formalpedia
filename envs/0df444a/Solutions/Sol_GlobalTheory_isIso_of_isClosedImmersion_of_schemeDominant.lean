-- Prove2me | solution 1 for GlobalTheory.isIso_of_isClosedImmersion_of_schemeDominant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:02.002362+00:00
-- url     : https://prove2.me/submissions/8f72c563-b0c3-479e-bce3-07999cb1a596

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
noncomputable section
variable {T' T P : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (i : T ⟶ P) [IsClosedImmersion i]
    [IsSchemeTheoreticallyDominant i] : IsIso i :=
  IsClosedImmersion.isIso_of_ker_eq i (𝟙 P) i (by simp) (by simp [i.ker_eq_bot])
end GlobalTheory
