-- Prove2me | solution 1 for GlobalTheory.PhiGam.condC_iff_nab_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:05:23.146455+00:00
-- url     : https://prove2.me/submissions/70b80fdc-d504-4e58-a7c5-7ea172152f5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Theorems.Thm_GlobalTheory_PhiGam_mem_sh_iff_smul_mem
import Theorems.Thm_GlobalTheory_PhiGam_nab_apply_eq

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
namespace GlobalTheory.PhiGam
theorem _root_.solution [Module k V] [IsScalarTower k k⸨X⸩ V] [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V]
    (g : V →ₗ[k] V) (N : Submodule k⟦X⟧ V) : CondC g N ↔ ∀ x ∈ N, nab g x ∈ N := by
  simp only [CondC, mem_sh_iff_smul_mem, nab_apply_eq, zpow_neg_one]
end GlobalTheory.PhiGam
