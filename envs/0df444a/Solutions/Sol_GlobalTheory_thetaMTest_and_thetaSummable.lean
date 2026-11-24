-- Prove2me | solution 1 for GlobalTheory.thetaMTest_and_thetaSummable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:42.861894+00:00
-- url     : https://prove2.me/submissions/58feb1c7-5b78-4ee8-964d-fa786f1c2fa6

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMulDotProductLeOfIsCompactThetaDomain
import Theorems.Thm_GlobalTheory_thetaMTest_holds
import Theorems.Thm_GlobalTheory_thetaSummable_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix ReciprocityTheory.PTheta
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι]
open Complex Matrix
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : _root_.ReciprocityTheory.PTheta.ThetaMTestStatement ∧ _root_.ReciprocityTheory.PTheta.ThetaSummableStatement :=
  ⟨_root_.GlobalTheory.thetaMTest_holds, _root_.GlobalTheory.thetaSummable_holds⟩
end _root_.GlobalTheory
end GlobalTheory
