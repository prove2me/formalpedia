-- Prove2me | solution 1 for GlobalTheory.PhiGam.Inh.nab_mem_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:42:31.905409+00:00
-- url     : https://prove2.me/submissions/f1ca14ec-9b67-4e4c-b4e8-13286b08e64a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Theorems.Thm_GlobalTheory_PhiGam_vv_ne_zero
import Theorems.Thm_GlobalTheory_PhiGam_mem_sh_iff_exists
import Theorems.Thm_GlobalTheory_PhiGam_nab_apply_eq
import Theorems.Thm_GlobalTheory_PhiGam_Inh_mem_stdLat
import Theorems.Thm_GlobalTheory_PhiGam_Inh_condC_stdLat

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
theorem _root_.solution {l : ℕ} (R : RingPG k l) {x : k⸨X⸩} (hx : x ∈ stdLat k) :
    nab (lin R.γ) x ∈ sh 1 (stdLat k) := by
  obtain ⟨a, rfl⟩ := mem_stdLat.1 hx
  obtain ⟨κ, -, hκ⟩ := R.γ_v
  set s : k⟦X⟧ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) a
  obtain ⟨t, ht⟩ := R.γ_int s
  obtain ⟨y, hy, hy'⟩ := mem_sh_iff_exists.1 (condC_stdLat R _ (mem_stdLat.2 ⟨s, rfl⟩))
  have ha : (a : k⸨X⸩) = vv k * (s : k⸨X⸩) + algebraMap k k⸨X⸩ (PowerSeries.constantCoeff a) := by
    conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const a, map_add, map_mul, ← vv_eq_coe_X]
    rfl
  refine mem_sh_iff_exists.2 ⟨_, Submodule.sub_mem _ hy (mem_stdLat.2 ⟨κ * t, rfl⟩), ?_⟩
  have hv := vv_ne_zero k
  rw [lin_apply, ht, zpow_one, smul_eq_mul] at hy'
  rw [nab_apply_eq, lin_apply, ha, map_add R.γ, map_mul R.γ, AlgHom.commutes, hκ, ht, zpow_one, smul_eq_mul,
    smul_eq_mul, map_mul, eq_inv_mul_iff_mul_eq₀ hv]
  linear_combination vv k * hy'
end GlobalTheory.PhiGam.Inh
