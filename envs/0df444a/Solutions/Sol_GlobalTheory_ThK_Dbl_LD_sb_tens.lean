-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.sb_tens
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:18.702133+00:00
-- url     : https://prove2.me/submissions/2c9a56f1-cfca-4e59-99a5-192d42b2e0a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y] {f : X → ℂ} {g : Y → ℂ}
    (hf : f ∈ SB X) (hg : g ∈ SB Y) : (fun z : X × Y => f z.1 * g z.2) ∈ SB (X × Y) := by
  refine ⟨(hf.1.comp_continuous continuous_fst).mul (hg.1.comp_continuous continuous_snd),
    HasCompactSupport.intro (IsCompact.prod hf.2 hg.2) fun z hz => ?_⟩
  rcases not_and_or.1 hz with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]
end GlobalTheory.ThK.Dbl.LD
