-- Prove2me | solution 1 for GlobalTheory.IsLocalCommGroupLaw.hasFDerivAt_logChart_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:23:19.785374+00:00
-- url     : https://prove2.me/submissions/5cad80dd-bf74-4bc0-8b27-680e5f94587b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
open GlobalTheory.IsLocalCommGroupLaw
variable {m : V × V → V}
variable (h : IsLocalCommGroupLaw m)
include h
variable [CompleteSpace V]
variable [FiniteDimensional ℂ V]
namespace GlobalTheory.IsLocalCommGroupLaw
theorem _root_.solution :
    HasFDerivAt h.logChart.symm (ContinuousLinearMap.id ℂ V) 0 := by
  have := h.hasStrictFDerivAt_log.to_localInverse.hasFDerivAt
  rwa [h.log_zero] at this
end GlobalTheory.IsLocalCommGroupLaw
