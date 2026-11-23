-- Prove2me | solution 1 for GlobalTheory.PhiGam.mem_sh_iff_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:08.614677+00:00
-- url     : https://prove2.me/submissions/4ef99838-73d1-4c43-8056-1e3a3de8e821

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
namespace GlobalTheory.PhiGam
theorem _root_.solution {a : ℤ} {N : Submodule k⟦X⟧ V} {x : V} :
    x ∈ sh a N ↔ ∃ y ∈ N, vv k ^ a • y = x := Iff.rfl
end GlobalTheory.PhiGam
