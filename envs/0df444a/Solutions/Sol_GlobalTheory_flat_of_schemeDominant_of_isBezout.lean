-- Prove2me | solution 1 for GlobalTheory.flat_of_schemeDominant_of_isBezout
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:14.42771+00:00
-- url     : https://prove2.me/submissions/8f80292e-3bc6-43df-9ccf-6635a20b1f38

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
theorem _root_.solution {O : CommRingCat.{u}} [IsDomain O] [IsBezout O]
    (d : T' ⟶ T) (s : T ⟶ Spec O) [IsSchemeTheoreticallyDominant d] [QuasiCompact d]
    [Flat (d ≫ s)] : Flat s :=
  flat_of_schemeDominant_of_torsionFree_flat
    (fun _ _ _ ↦ Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr) d s
end GlobalTheory
