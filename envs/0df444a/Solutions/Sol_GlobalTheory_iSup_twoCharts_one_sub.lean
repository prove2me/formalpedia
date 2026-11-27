-- Prove2me | solution 1 for GlobalTheory.iSup_twoCharts_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:53.563099+00:00
-- url     : https://prove2.me/submissions/b91a1dbd-f507-4927-9a45-1f8ac90fbe90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe t v u
noncomputable section
open GlobalTheory
variable {X Y : Scheme.{u}} {ι : Type}
variable {A : CommRingCat.{u}} (M : ModuleCat.{u} A)
variable (f g : A)
namespace GlobalTheory
theorem _root_.solution : ⨆ i, twoCharts f (1 - f) i = ⊤ :=
  (iSup_basicOpenFamily_eq_top_iff _).2 (span_range_pair_one_sub f)
end GlobalTheory
