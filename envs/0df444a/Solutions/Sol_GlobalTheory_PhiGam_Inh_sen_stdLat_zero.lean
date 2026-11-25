-- Prove2me | solution 1 for GlobalTheory.PhiGam.Inh.sen_stdLat_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:07:41.555819+00:00
-- url     : https://prove2.me/submissions/ed5c2ca5-7bfa-4f86-88af-362ae54db5cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Theorems.Thm_GlobalTheory_PhiGam_mem_sh_iff_exists
import Theorems.Thm_GlobalTheory_PhiGam_Inh_mem_stdLat
import Theorems.Thm_GlobalTheory_PhiGam_Inh_nab_mem_stdLat

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
theorem _root_.solution {l : ℕ} (R : RingPG k l) : sen (lin R.γ) (stdLat k) 0 = 1 := by
  rw [sen, qmult, gmult]
  have hP : (stdLat k).restrictScalars k ⊓ ⨆ m : ℕ, ((sh 1 (stdLat k)).restrictScalars k).comap
      ((nab (lin R.γ) - algebraMap k (Module.End k k⸨X⸩) 0) ^ m) = (stdLat k).restrictScalars k := by
    refine inf_eq_left.2 fun y hy => Submodule.mem_iSup_of_mem 1 ?_
    rw [Submodule.mem_comap, pow_one, map_zero, sub_zero]
    exact nab_mem_stdLat R hy
  rw [hP]
  let f : (stdLat k).restrictScalars k →ₗ[k] k := (HahnSeries.coeff.linearMap (0 : ℤ)) ∘ₗ Submodule.subtype _
  have h0 : ∀ a : k⟦X⟧, (a : k⸨X⸩).coeff 0 = PowerSeries.constantCoeff a := fun a => by
    rw [PowerSeries.coeff_coe]; simp
  have hk : ((sh 1 (stdLat k)).restrictScalars k).submoduleOf ((stdLat k).restrictScalars k) = f.ker := by
    ext ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := mem_stdLat.1 hy
    change (a : k⸨X⸩) ∈ sh 1 (stdLat k) ↔ (a : k⸨X⸩).coeff 0 = 0
    rw [h0, mem_sh_iff_exists, ← PowerSeries.X_dvd_iff, zpow_one, vv_eq_coe_X]
    constructor
    · rintro ⟨z, hz, h⟩
      obtain ⟨b, rfl⟩ := mem_stdLat.1 hz
      exact ⟨b, HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by rw [map_mul]; exact h.symm)⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b, mem_stdLat.2 ⟨b, rfl⟩, (map_mul _ _ _).symm⟩
  have hs : Function.Surjective f := fun c =>
    ⟨⟨_, mem_stdLat.2 ⟨PowerSeries.C c, rfl⟩⟩, (h0 _).trans (PowerSeries.constantCoeff_C c)⟩
  rw [hk, (f.quotKerEquivOfSurjective hs).finrank_eq, Module.finrank_self]
end GlobalTheory.PhiGam.Inh
