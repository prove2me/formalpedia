-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.extc_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:39.227294+00:00
-- url     : https://prove2.me/submissions/d1714061-12b7-4c4c-aeb9-c853f0d6c16f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
open GlobalTheory.BK.PhiMod
variable {O K l e a ι} (P : PhiMod O K l e a ι)
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution {B : Subalgebra O K⟦X⟧} (h : A O K ≤ B) (τ : ZMod a) :
    P.extc B τ = Submodule.span B (P.Lcomp τ : Set (ι → K⟦X⟧)) := by
  refine le_antisymm (Submodule.span_mono Submodule.subset_span) (Submodule.span_le.2 fun v hv => ?_)
  obtain ⟨m, hm, rfl⟩ := P.mem_extc.1 hv
  exact P.mem_extc.2 ⟨m, fun i => h (hm i), rfl⟩
end GlobalTheory.BK.PhiMod
