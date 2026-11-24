-- Prove2me | solution 1 for GlobalTheory.PhiGam.sh_sh_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:27:10.76981+00:00
-- url     : https://prove2.me/submissions/6ce99c61-d49c-4249-9485-fcffbddcd43b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Theorems.Thm_GlobalTheory_PhiGam_vv_ne_zero
import Theorems.Thm_GlobalTheory_PhiGam_mem_sh_iff_smul_mem

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
theorem _root_.solution (a b : ℤ) (N : Submodule k⟦X⟧ V) : sh a (sh b N) = sh (a + b) N := by
  ext x
  simp only [mem_sh_iff_smul_mem, smul_smul, ← zpow_add₀ (vv_ne_zero k), neg_add_rev]
end GlobalTheory.PhiGam
