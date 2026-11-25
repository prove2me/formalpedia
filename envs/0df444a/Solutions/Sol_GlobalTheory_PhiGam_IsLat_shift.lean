-- Prove2me | solution 1 for GlobalTheory.PhiGam.IsLat.shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:05:17.382054+00:00
-- url     : https://prove2.me/submissions/189e07aa-b936-4fff-b7dc-67807a522ae3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Theorems.Thm_GlobalTheory_PhiGam_vv_ne_zero
import Theorems.Thm_GlobalTheory_PhiGam_mem_sh_iff_exists

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
namespace IsLat
theorem _root_.solution {N : Submodule k⟦X⟧ V} (h : IsLat N) (a : ℤ) : IsLat (sh a N) := by
  refine ⟨h.1.map _, eq_top_iff.2 ?_⟩
  rw [← h.2]
  refine Submodule.span_le.2 fun y hy => ?_
  have h1 : vv k ^ a • y ∈ Submodule.span k⸨X⸩ (sh a N : Set V) :=
    Submodule.subset_span (mem_sh_iff_exists.2 ⟨y, hy, rfl⟩)
  exact (Submodule.smul_mem_iff _ (zpow_ne_zero a (vv_ne_zero k))).1 h1
end IsLat
end GlobalTheory.PhiGam
