-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.const_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/322589ca-9aee-5edc-98f6-e07fe29af8a8

import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] {π : W} (hπ : π ∈ nonZeroDivisors W) :
    const π π ∈ nonZeroDivisors (UVCrossingModel W π) :=
  by

  have hCnzd : ∀ h : MvPowerSeries (Fin 2) W, MvPowerSeries.C π * h = 0 → h = 0 := by
    intro h hh
    ext m
    have := congrArg (MvPowerSeries.coeff m) hh
    rw [MvPowerSeries.coeff_C_mul, map_zero] at this
    rw [map_zero]
    exact (mem_nonZeroDivisors_iff.mp hπ).1 _ this
  have core : ∀ x : UVCrossingModel W π, x * const π π = 0 → x = 0 := by
    intro x hx
    obtain ⟨f, rfl⟩ := mk_surjective π x
    have hmem : f * MvPowerSeries.C π ∈ uvCrossingIdeal W π := by
      have h0 : mk π (f * MvPowerSeries.C π) = 0 := by rw [map_mul]; exact hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp h0
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hmem
    set q : W →+* W ⧸ Ideal.span {π} := Ideal.Quotient.mk (Ideal.span {π}) with hq
    have hCπ : MvPowerSeries.map (σ := Fin 2) q (MvPowerSeries.C π) = 0 := by
      rw [MvPowerSeries.map_C]
      rw [show q π = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π)]
      exact map_zero _
    have hg' := congrArg (MvPowerSeries.map (σ := Fin 2) q) hg
    rw [map_mul, map_mul, map_sub, hCπ, mul_zero, sub_zero, map_mul,
      MvPowerSeries.map_X, MvPowerSeries.map_X] at hg'
    have hXX : (MvPowerSeries.X 0 * MvPowerSeries.X 1 :
        MvPowerSeries (Fin 2) (W ⧸ Ideal.span {π})) ∈
        nonZeroDivisors (MvPowerSeries (Fin 2) (W ⧸ Ideal.span {π})) :=
      mul_mem MvPowerSeries.X_mem_nonzeroDivisors MvPowerSeries.X_mem_nonzeroDivisors
    have hqg : MvPowerSeries.map (σ := Fin 2) q g = 0 := by
      have h1 : MvPowerSeries.map (σ := Fin 2) q g *
          (MvPowerSeries.X 0 * MvPowerSeries.X 1) = 0 := by
        rw [mul_comm]; exact hg'.symm
      exact (mem_nonZeroDivisors_iff.mp hXX).2 _ h1
    have hdvd : ∀ m, π ∣ MvPowerSeries.coeff m g := by
      intro m
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
      show q (MvPowerSeries.coeff m g) = 0
      rw [← MvPowerSeries.coeff_map, hqg, map_zero]
    obtain ⟨g₁, hg₁⟩ : ∃ g₁ : MvPowerSeries (Fin 2) W, g = MvPowerSeries.C π * g₁ := by
      refine ⟨fun m => (hdvd m).choose, MvPowerSeries.ext fun m => ?_⟩
      rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_apply]
      exact (hdvd m).choose_spec
    have hkey : MvPowerSeries.C π * (f -
          ((MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C π) * g₁)) = 0 := by
      rw [mul_sub, mul_comm (MvPowerSeries.C π) f, hg, hg₁]
      ring
    have hf : f = (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C π) * g₁ :=
      sub_eq_zero.mp (hCnzd _ hkey)
    have hfmem : f ∈ uvCrossingIdeal W π := by
      rw [hf]
      exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hfmem
  rw [mem_nonZeroDivisors_iff]
  constructor
  · intro x hx
    exact core x (by rwa [mul_comm] at hx)
  · intro x hx
    exact core x hx

end S_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors (solution)
