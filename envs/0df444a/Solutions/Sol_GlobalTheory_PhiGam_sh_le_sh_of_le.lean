-- Prove2me | solution 1 for GlobalTheory.PhiGam.sh_le_sh_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:27:09.999571+00:00
-- url     : https://prove2.me/submissions/48c92427-60e5-41bf-a8d0-9bfb3b46cc3c

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
theorem _root_.solution {a b : ℤ} (h : b ≤ a) (N : Submodule k⟦X⟧ V) : sh a N ≤ sh b N := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨m, rfl⟩ := Int.le.dest h
  refine mem_sh_iff_exists.2 ⟨(PowerSeries.X ^ m : k⟦X⟧) • y, N.smul_mem _ hy, ?_⟩
  change _ = vv k ^ (b + m) • y
  rw [← algebraMap_smul k⸨X⸩ (PowerSeries.X ^ m : k⟦X⟧) y, smul_smul, zpow_add₀ (vv_ne_zero k), zpow_natCast,
    map_pow]
  congr 3
  exact (vv_eq_coe_X k).symm
end GlobalTheory.PhiGam
