-- Prove2me | solution 1 for GlobalTheory.PhiGam.Inh.mem_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:08.682481+00:00
-- url     : https://prove2.me/submissions/b7f4a32e-4c8b-43bf-a85c-1deb96b8bce1

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
theorem _root_.solution {x : k⸨X⸩} : x ∈ stdLat k ↔ ∃ a : k⟦X⟧, (a : k⸨X⸩) = x := by
  simp [stdLat, Submodule.mem_span_singleton, Algebra.smul_def]
end GlobalTheory.PhiGam.Inh
