-- Prove2me | solution 1 for GlobalTheory.PhiGam.Inh.condC_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:27:07.679744+00:00
-- url     : https://prove2.me/submissions/d3be2580-5925-4288-b3f8-8613f63d66a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Theorems.Thm_GlobalTheory_PhiGam_mem_sh_iff_exists
import Theorems.Thm_GlobalTheory_PhiGam_Inh_mem_stdLat

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
theorem _root_.solution {l : ℕ} (R : RingPG k l) : CondC (lin R.γ) (stdLat k) := by
  intro x hx
  obtain ⟨a, rfl⟩ := mem_stdLat.1 hx
  obtain ⟨κ, -, hκ⟩ := R.γ_v
  set s : k⟦X⟧ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) a
  obtain ⟨t, ht⟩ := R.γ_int s
  have ha : (a : k⸨X⸩) = vv k * (s : k⸨X⸩) + algebraMap k k⸨X⸩ (PowerSeries.constantCoeff a) := by
    conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const a, map_add, map_mul, ← vv_eq_coe_X]
    rfl
  refine mem_sh_iff_exists.2 ⟨_, mem_stdLat.2 ⟨(1 - κ * PowerSeries.X) * t - s, rfl⟩, ?_⟩
  rw [lin_apply, ha, map_add R.γ, map_mul R.γ, AlgHom.commutes, hκ, ht, zpow_one, smul_eq_mul, map_sub, map_mul,
    map_sub, map_mul, map_one, ← vv_eq_coe_X]
  ring
end GlobalTheory.PhiGam.Inh
