-- Prove2me | solution 1 for ModPForms.mem_modPMod_of_map_mem_modPMod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/5d61446c-8971-5165-a0f1-08338c9589ef

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_mem_modPMod_of_map_mem_modPMod

set_option autoImplicit false

namespace FltWs24
namespace Descent

variable {K L : Type} [Field K] [Field L]

noncomputable def coeffwise (r : L →+ K) (φ : PowerSeries L) : PowerSeries K :=
  PowerSeries.mk fun n => r (PowerSeries.coeff n φ)

@[scoped simp] theorem coeff_coeffwise (r : L →+ K) (φ : PowerSeries L) (n : ℕ) :
    PowerSeries.coeff n (coeffwise r φ) = r (PowerSeries.coeff n φ) := by
  rw [coeffwise, PowerSeries.coeff_mk]

theorem coeffwise_add (r : L →+ K) (φ ψ : PowerSeries L) :
    coeffwise r (φ + ψ) = coeffwise r φ + coeffwise r ψ := by
  ext n; simp

theorem coeffwise_zero (r : L →+ K) : coeffwise r (0 : PowerSeries L) = 0 := by
  ext n; simp

end FltWs24.Descent
p2m_reactivate "P2MW.S_ModPForms_mem_modPMod_of_map_mem_modPMod.FltWs24 P2MW.S_ModPForms_mem_modPMod_of_map_mem_modPMod.FltWs24.Descent"
p2m_reactivate "P2MW.S_ModPForms_mem_modPMod_of_map_mem_modPMod.FltWs24"

open FltWs24.Descent in
theorem solution
    (N : ℕ) (k : ℤ) (K L : Type) [Field K] [Field L] (i : K →+* L)
    (ψ : PowerSeries K) (h : PowerSeries.map i ψ ∈ ModPForms.modPMod N k L) :
    ψ ∈ ModPForms.modPMod N k K := by

  letI : Algebra K L := i.toAlgebra
  have hi : ∀ c : K, algebraMap K L c = i c := fun _ => rfl
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (by
      intro a b hab
      exact i.injective hab))
  have hri : ∀ c : K, r (i c) = c := fun c => by
    have := LinearMap.congr_fun hr c
    simpa [hi] using this

  have hRmap : ∀ (μ : L) (v : PowerSeries K), coeffwise r.toAddMonoidHom (μ • PowerSeries.map i v) = r μ • v := by
    intro μ v
    ext n
    rw [coeff_coeffwise, LinearMap.toAddMonoidHom_coe, map_smul, PowerSeries.coeff_map, smul_eq_mul, map_smul, smul_eq_mul,
      show μ * i (PowerSeries.coeff n v) = (PowerSeries.coeff n v) • μ by
        rw [Algebra.smul_def, hi, mul_comm],
      map_smul, smul_eq_mul, mul_comm]

  have key : ∀ φ ∈ ModPForms.modPMod N k L, ∀ μ : L, coeffwise r.toAddMonoidHom (μ • φ) ∈ ModPForms.modPMod N k K := by
    intro φ hφ
    unfold ModPForms.modPMod at hφ ⊢
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      intro μ
      obtain ⟨f, a, ha, rfl⟩ := hx
      have hv : (PowerSeries.mk fun n => ((a n : ℤ) : L)) =
          PowerSeries.map i (PowerSeries.mk fun n => ((a n : ℤ) : K)) := by
        ext n
        rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk, map_intCast]
      rw [hv, hRmap]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, a, ha, rfl⟩)
    | zero => intro μ; rw [smul_zero, coeffwise_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      intro μ
      rw [smul_add, coeffwise_add]
      exact Submodule.add_mem _ (hx μ) (hy μ)
    | smul ν x _ hx => intro μ; rw [smul_smul]; exact hx (μ * ν)

  have h1 := key _ h 1
  rw [one_smul] at h1
  have hRψ : coeffwise r.toAddMonoidHom (PowerSeries.map i ψ) = ψ := by
    ext n
    rw [coeff_coeffwise, LinearMap.toAddMonoidHom_coe, PowerSeries.coeff_map, hri]
  rwa [hRψ] at h1

end S_ModPForms_mem_modPMod_of_map_mem_modPMod
end P2MW
export P2MW.S_ModPForms_mem_modPMod_of_map_mem_modPMod (solution)
