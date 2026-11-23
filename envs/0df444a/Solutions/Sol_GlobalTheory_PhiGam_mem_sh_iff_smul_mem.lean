-- Prove2me | solution 1 for GlobalTheory.PhiGam.mem_sh_iff_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:59:17.926548+00:00
-- url     : https://prove2.me/submissions/d4366e84-0b45-4cfe-8a7a-2d533c5eb7fc

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
theorem _root_.solution {a : ℤ} {N : Submodule k⟦X⟧ V} {x : V} :
    x ∈ sh a N ↔ vv k ^ (-a) • x ∈ N := by
  have hv := vv_ne_zero k
  constructor
  · rintro ⟨y, hy, rfl⟩
    change vv k ^ (-a) • vv k ^ a • y ∈ N
    rwa [smul_smul, ← zpow_add₀ hv, neg_add_cancel, zpow_zero, one_smul]
  · intro h
    refine mem_sh_iff_exists.2 ⟨_, h, ?_⟩
    rw [smul_smul, ← zpow_add₀ hv, add_neg_cancel, zpow_zero, one_smul]
end GlobalTheory.PhiGam
