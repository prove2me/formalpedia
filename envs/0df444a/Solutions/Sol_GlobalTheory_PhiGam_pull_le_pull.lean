-- Prove2me | solution 1 for GlobalTheory.PhiGam.pull_le_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:05:27.206173+00:00
-- url     : https://prove2.me/submissions/1785bd0a-c745-4350-9e1b-0ff5de85740d

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
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
variable [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V]
omit [IsScalarTower k⟦X⟧ k⸨X⸩ V]
namespace GlobalTheory.PhiGam
theorem _root_.solution [Module k V] (f : V →ₗ[k] V) {N N' : Submodule k⟦X⟧ V} (h : N ≤ N') :
    pull f N ≤ pull f N' :=
  Submodule.span_mono (Set.image_mono h)
end GlobalTheory.PhiGam
