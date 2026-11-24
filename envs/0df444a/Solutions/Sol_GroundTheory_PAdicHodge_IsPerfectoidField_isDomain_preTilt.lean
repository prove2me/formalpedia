-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.isDomain_preTilt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:33.55181+00:00
-- url     : https://prove2.me/submissions/da634edf-6bc1-4d8c-8da9-27c23c42409a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open NNReal
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution : IsDomain (PreTilt (normInteger K) p) :=
  PreTilt.isDomain K NormedField.valuation (normInteger K) normInteger_integers p
end GroundTheory.PAdicHodge.IsPerfectoidField
