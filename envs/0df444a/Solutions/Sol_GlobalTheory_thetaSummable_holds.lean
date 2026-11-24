-- Prove2me | solution 1 for GlobalTheory.thetaSummable_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:20.759641+00:00
-- url     : https://prove2.me/submissions/21e601d1-ee8a-4fb3-bf87-baa2b8cc5bac

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMulDotProductLeOfIsCompactThetaDomain
import Theorems.Thm_GlobalTheory_thetaMTest_holds

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
theorem _root_.solution : _root_.ReciprocityTheory.PTheta.ThetaSummableStatement := by
  have hM := _root_.GlobalTheory.thetaMTest_holds
  unfold _root_.ReciprocityTheory.PTheta.ThetaMTestStatement at hM
  unfold _root_.ReciprocityTheory.PTheta.ThetaSummableStatement
  intro ι _ a b z τ hτ
  obtain ⟨u, hu, hbound⟩ := hM ι a {(z, (τ : ι → ι → ℂ))} isCompact_singleton
    (fun p hp => by
      obtain rfl : p = (z, (τ : ι → ι → ℂ)) := hp
      exact hτ)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun l => hbound b _ (Set.mem_singleton _) l) hu
end _root_.GlobalTheory
end GlobalTheory
