-- Prove2me | solution 1 for GlobalTheory.PhiGam.Inh.isLat_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:07:39.171933+00:00
-- url     : https://prove2.me/submissions/fa28a4c9-c1de-4944-9d5c-22e764330e44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv

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
theorem _root_.solution : IsLat (stdLat k) := by
  refine ⟨Submodule.fg_span_singleton _, eq_top_iff.2 fun x _ => ?_⟩
  have h1 : (1 : k⸨X⸩) ∈ Submodule.span k⸨X⸩ (stdLat k : Set k⸨X⸩) :=
    Submodule.subset_span (Submodule.mem_span_singleton_self _)
  simpa using Submodule.smul_mem _ x h1
end GlobalTheory.PhiGam.Inh
