-- Prove2me | solution 1 for MasulloRH.split_padic_product_norm_unit_shell_not_coordinate_units
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T10:21:18.366758+00:00
-- url     : https://prove2.me/submissions/fa86e0d1-efbd-44df-8c71-bc0bd3d003c9

import Mathlib
open MeasureTheory
theorem solution (p : ℕ) [hp : Fact p.Prime]
    [MeasurableSpace (ℚ_[p] × ℚ_[p])]
    (μ : Measure (ℚ_[p] × ℚ_[p])) [μ.IsOpenPosMeasure] :
    let S : Set (ℚ_[p] × ℚ_[p]) :=
      {z | ‖z.1‖ = (p : ℝ)⁻¹ ∧ ‖z.2‖ = (p : ℝ)}
    IsOpen S ∧ ((p : ℚ_[p]),(p : ℚ_[p])⁻¹) ∈ S ∧ 0 < μ S ∧
      ∀ z ∈ S, ‖z.1 * z.2‖ = 1 ∧
        (∃ v : ℤ_[p]ˣ, ((v : ℤ_[p]) : ℚ_[p]) = z.1 * z.2) ∧
        ∀ u : ℤ_[p]ˣ, ((u : ℤ_[p]) : ℚ_[p]) ≠ z.1 ∧
          ((u : ℤ_[p]) : ℚ_[p]) ≠ z.2 := by
  let S : Set (ℚ_[p] × ℚ_[p]) := {z | ‖z.1‖ = (p : ℝ)⁻¹ ∧ ‖z.2‖ = (p : ℝ)}
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpos : (0:ℝ) < p := by linarith
  have op (r : ℝ) (hr : 0 < r) : IsOpen {y : ℚ_[p] | ‖y‖ = r} := by
    apply Metric.isOpen_iff.mpr
    intro x hx
    change ‖x‖ = r at hx
    refine ⟨r, hr, ?_⟩
    intro y hy
    have hd : ‖y-x‖ < r := by simpa [Metric.mem_ball,dist_eq_norm_sub] using hy
    exact (Padic.norm_eq_of_norm_sub_lt_right (hd.trans_eq hx.symm)).trans hx
  have hs : IsOpen S :=
    (op _ (inv_pos.mpr hpos)).prod (op _ hpos)
  have hc : ((p : ℚ_[p]),(p : ℚ_[p])⁻¹) ∈ S := by
    change ‖(p : ℚ_[p])‖ = _ ∧ ‖(p : ℚ_[p])⁻¹‖ = _
    rw [norm_inv,Padic.norm_p,inv_inv]
    exact ⟨rfl,rfl⟩
  refine ⟨hs,hc,hs.measure_pos μ ⟨_,hc⟩,?_⟩
  intro z hz
  change ‖z.1‖ = (p:ℝ)⁻¹ ∧ ‖z.2‖ = (p:ℝ) at hz
  have hprod : ‖z.1 * z.2‖ = 1 := by rw [norm_mul,hz.1,hz.2,inv_mul_cancel₀ hpos.ne']
  let v : ℤ_[p] := ⟨z.1 * z.2,hprod.le⟩
  have hv : IsUnit v := PadicInt.isUnit_iff.mpr hprod
  refine ⟨hprod,⟨hv.unit,?_⟩,?_⟩
  · change ((hv.unit : ℤ_[p]) : ℚ_[p]) = (v : ℚ_[p])
    rw [hv.unit_spec]
  · intro u
    have hu : ‖((u : ℤ_[p]) : ℚ_[p])‖ = 1 := by
      change ‖(u : ℤ_[p])‖ = 1
      exact PadicInt.norm_units u
    constructor
    · intro he
      have hh : (p:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
      rw [he,hz.1] at hu
      exact hh.ne hu
    · intro he
      rw [he,hz.2] at hu
      exact hp1.ne' hu
