-- Prove2me | solution 1 for GlobalTheory.PhiGam.Inh.pull_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:27:08.497674+00:00
-- url     : https://prove2.me/submissions/481fccf1-1a1e-4b2b-a516-26a383c90bc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Theorems.Thm_GlobalTheory_PhiGam_Inh_mem_stdLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam.Inh
variable {k : Type} [Field k]
namespace GlobalTheory.PhiGam.Inh
theorem _root_.solution {l : ℕ} (R : RingPG k l) : pull (lin R.φ) (stdLat k) = stdLat k := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := mem_stdLat.1 hx
    obtain ⟨b, hb⟩ := R.φ_int a
    exact mem_stdLat.2 ⟨b, hb.symm⟩
  · refine Submodule.span_le.2 ?_
    rintro _ rfl
    exact Submodule.subset_span ⟨1, Submodule.mem_span_singleton_self _, map_one R.φ⟩
end GlobalTheory.PhiGam.Inh
