-- Prove2me | solution 1 for LearnNoConc.ERM.eq_5_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:59:09.486257+00:00
-- url     : https://prove2.me/submissions/927fb9eb-b9ff-4af9-8e0f-ead2a508e9f9

import Mathlib
import Definitions.Def_LearnNoConc_ERM_Setting

open MeasureTheory
open scoped ENNReal

open LearnNoConc.ERM in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (ν : Measure (Ω × ℝ)) [IsProbabilityMeasure ν]
    (F : Set (Ω → ℝ)) (hF2 : ∀ f ∈ F, MemLp f 2 (ν.map Prod.fst)) (hFconv : Convex ℝ F)
    (hY : MemLp (fun z : Ω × ℝ => z.2) 2 ν) (fstar : Ω → ℝ) (hfstar : fstar ∈ F)
    (N : ℕ) (hN : 0 < N) (z : Fin N → Ω × ℝ) (γ α : ℝ) (hα : 0 < α)
    (h54 : ∀ f ∈ F, eLpNorm (f - fstar) 2 (ν.map Prod.fst) = ENNReal.ofReal α →
      |multDev ν fstar z f| ≤ 4 * γ * α ^ 2) :
    ∀ f ∈ F, ENNReal.ofReal α ≤ eLpNorm (f - fstar) 2 (ν.map Prod.fst) →
      |multDev ν fstar z f|
        ≤ 4 * γ * ((eLpNorm (f - fstar) 2 (ν.map Prod.fst)).toReal) ^ 2 := by
  intro f hf hle
  have hfin : eLpNorm (f - fstar) 2 (ν.map Prod.fst) ≠ ⊤ :=
    ((hF2 f hf).sub (hF2 fstar hfstar)).eLpNorm_ne_top
  obtain ⟨R, hR⟩ : ∃ R, R = (eLpNorm (f - fstar) 2 (ν.map Prod.fst)).toReal := ⟨_, rfl⟩
  rw [← hR]
  have hαR : α ≤ R := by
    rw [hR]; exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hle
  have hRpos : 0 < R := lt_of_lt_of_le hα hαR
  set c := α / R with hc
  have hc0 : 0 < c := div_pos hα hRpos
  have hc1 : c ≤ 1 := by rw [hc, div_le_one hRpos]; exact hαR
  obtain ⟨g, hg⟩ : ∃ g : Ω → ℝ, g = (1 - c) • fstar + c • f := ⟨_, rfl⟩
  have hgF : g ∈ F := by
    rw [hg]; exact hFconv hfstar hf (by linarith) hc0.le (by ring)
  have hgf : g - fstar = c • (f - fstar) := by
    rw [hg]; funext x; simp; ring
  have hgnorm : eLpNorm (g - fstar) 2 (ν.map Prod.fst) = ENNReal.ofReal α := by
    rw [hgf, eLpNorm_const_smul, Real.enorm_eq_ofReal hc0.le,
      ← ENNReal.ofReal_toReal hfin, ← hR, ← ENNReal.ofReal_mul hc0.le, hc,
      div_mul_cancel₀ _ hRpos.ne']
  have hpt : ∀ x, g x - fstar x = c * (f x - fstar x) := by
    intro x
    have := congrFun hgf x
    simpa using this
  have hmd : multDev ν fstar z g = c * multDev ν fstar z f := by
    unfold multDev
    simp_rw [hpt]
    have e1 : ∀ w : Ω × ℝ, (fstar w.1 - w.2) * (c * (f w.1 - fstar w.1)) =
        c * ((fstar w.1 - w.2) * (f w.1 - fstar w.1)) := fun w => by ring
    simp_rw [e1]
    rw [integral_const_mul]
    rw [← Finset.mul_sum]
    ring
  have hb := h54 g hgF hgnorm
  rw [hmd, abs_mul, abs_of_pos hc0] at hb
  have hγ : 0 ≤ γ := by
    have : 0 ≤ 4 * γ * α ^ 2 := le_trans (mul_nonneg hc0.le (abs_nonneg _)) hb
    have hα2 : 0 < α ^ 2 := by positivity
    nlinarith
  have hfR : |multDev ν fstar z f| ≤ 4 * γ * α * R := by
    have e : c * |multDev ν fstar z f| * R = α * |multDev ν fstar z f| := by
      rw [hc]; field_simp
    have := mul_le_mul_of_nonneg_right hb hRpos.le
    rw [e] at this
    have h2 : α * |multDev ν fstar z f| ≤ α * (4 * γ * α * R) := by nlinarith
    exact le_of_mul_le_mul_left h2 hα
  have : 4 * γ * α * R ≤ 4 * γ * R ^ 2 := by nlinarith [mul_nonneg hγ hRpos.le]
  linarith
