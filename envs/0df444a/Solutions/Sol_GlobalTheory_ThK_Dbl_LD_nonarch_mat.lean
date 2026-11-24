-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.nonarch_mat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:21.402455+00:00
-- url     : https://prove2.me/submissions/61c5ed47-d813-4771-a986-4af13725a2b0

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_nonarch_pi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM Matrix
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]
  [NonarchimedeanAddGroup k] [LocallyCompactSpace k] {c : k → ℂ} {ϖ : k}
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution (n d : ℕ) : NonarchimedeanAddGroup (Matrix (Fin n) (Fin d) k) :=
  haveI := nonarch_pi (Fin d) k
  nonarch_pi (Fin n) (Fin d → k)
end GlobalTheory.ThK.Dbl.LD
