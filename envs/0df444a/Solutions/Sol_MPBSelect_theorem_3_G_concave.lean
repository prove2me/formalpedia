-- Prove2me | solution 1 for MPBSelect.theorem_3_G_concave
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T05:24:45.437204+00:00
-- url     : https://prove2.me/submissions/f1dca31c-daf7-4764-80b9-f45b204f74d0

import Mathlib
import Definitions.Def_MPBSelect_Problem
import Definitions.Def_MPBSelect_Problem_G
import Definitions.Def_MPBSelect_Problem_ldr

namespace Aux_MPBSelect_t3

theorem bound (a c u v l : ℝ) (ha : 0 < a) (hc : 0 < c) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u * v / (a * v + c * u) ≤ (1 - l) ^ 2 * u / a + l ^ 2 * v / c := by
  rcases (show 0 ≤ a * v + c * u by positivity).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; positivity
  · rw [div_le_iff₀ hpos]
    have key : ((1 - l) ^ 2 * u / a + l ^ 2 * v / c) * (a * v + c * u) - u * v
        = ((1 - l) * c * u - l * a * v) ^ 2 / (a * c) := by
      field_simp <;> ring
    have : 0 ≤ ((1 - l) * c * u - l * a * v) ^ 2 / (a * c) := by positivity
    linarith

theorem attain (a c U V : ℝ) (ha : 0 < a) (hc : 0 < c) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ∃ l : ℝ, (1 - l) ^ 2 * U / a + l ^ 2 * V / c = U * V / (a * V + c * U) := by
  rcases (show 0 ≤ a * V + c * U by positivity).eq_or_lt with h0 | hpos
  · have hU0 : U = 0 := by nlinarith
    have hV0 : V = 0 := by nlinarith
    exact ⟨0, by rw [hU0, hV0]; simp⟩
  · refine ⟨c * U / (c * U + a * V), ?_⟩
    have hT : c * U + a * V ≠ 0 := by linarith
    field_simp <;> ring

theorem conc2 (a c u1 v1 u2 v2 μ ν : ℝ) (ha : 0 < a) (hc : 0 < c) (hu1 : 0 ≤ u1) (hv1 : 0 ≤ v1)
    (hu2 : 0 ≤ u2) (hv2 : 0 ≤ v2) (hμ : 0 ≤ μ) (hν : 0 ≤ ν) :
    μ * (u1 * v1 / (a * v1 + c * u1)) + ν * (u2 * v2 / (a * v2 + c * u2)) ≤
      (μ * u1 + ν * u2) * (μ * v1 + ν * v2) /
        (a * (μ * v1 + ν * v2) + c * (μ * u1 + ν * u2)) := by
  obtain ⟨l, hl⟩ := attain a c (μ * u1 + ν * u2) (μ * v1 + ν * v2) ha hc (by positivity)
    (by positivity)
  rw [← hl]
  have h1 := mul_le_mul_of_nonneg_left (bound a c u1 v1 l ha hc hu1 hv1) hμ
  have h2 := mul_le_mul_of_nonneg_left (bound a c u2 v2 l ha hc hu2 hv2) hν
  have e : (1 - l) ^ 2 * (μ * u1 + ν * u2) / a + l ^ 2 * (μ * v1 + ν * v2) / c
      = μ * ((1 - l) ^ 2 * u1 / a + l ^ 2 * v1 / c) + ν * ((1 - l) ^ 2 * u2 / a + l ^ 2 * v2 / c) := by
    ring
  rw [e]
  linarith

end Aux_MPBSelect_t3

open MPBSelect in
theorem solution {k B : ℕ} (P : Problem k B) :
    (∀ (i : Fin k) (b : Fin B), i ≠ P.ib b →
      ConcaveOn ℝ {α : Fin k → Fin B → ℝ | ∀ j c, 0 ≤ α j c} (fun α => P.G α i b)) ∧
    ConcaveOn ℝ {α : Fin k → Fin B → ℝ | ∀ j c, 0 ≤ α j c} P.ldr := by
  have hconv : Convex ℝ {α : Fin k → Fin B → ℝ | ∀ j c, 0 ≤ α j c} := by
    intro α hα β hβ μ ν hμ hν _
    show ∀ j c, 0 ≤ (μ • α + ν • β) j c
    intro j c
    have h1 := hα j c
    have h2 := hβ j c
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    positivity
  have part1 : ∀ (i : Fin k) (b : Fin B), i ≠ P.ib b →
      ConcaveOn ℝ {α : Fin k → Fin B → ℝ | ∀ j c, 0 ≤ α j c} (fun α => P.G α i b) := by
    intro i b hi
    have ha : 0 < P.lam i b ^ 2 := pow_pos (P.lam_pos i b) 2
    have hc : 0 < P.lam (P.ib b) b ^ 2 := pow_pos (P.lam_pos (P.ib b) b) 2
    have hD : 0 ≤ (P.y i b - P.y (P.ib b) b) ^ 2 / 2 := by positivity
    have hG : ∀ α : Fin k → Fin B → ℝ, (∀ j c, 0 ≤ α j c) →
        P.G α i b = (P.y i b - P.y (P.ib b) b) ^ 2 / 2 *
          (α i b * α (P.ib b) b / (P.lam i b ^ 2 * α (P.ib b) b + P.lam (P.ib b) b ^ 2 * α i b)) := by
      intro α hα
      unfold Problem.G
      split_ifs with h
      · obtain ⟨hu, hv⟩ := h
        field_simp <;> ring
      · rcases (hα i b).eq_or_lt with hu | hu
        · rw [← hu]; simp
        · rcases (hα (P.ib b) b).eq_or_lt with hv | hv
          · rw [← hv]; simp
          · exact absurd ⟨hu, hv⟩ h
    refine ⟨hconv, fun α hα β hβ μ ν hμ hν hμν => ?_⟩
    have hmem := hconv hα hβ hμ hν hμν
    simp only [smul_eq_mul]
    rw [hG _ hmem, hG _ hα, hG _ hβ]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := Aux_MPBSelect_t3.conc2 _ _ (α i b) (α (P.ib b) b) (β i b) (β (P.ib b) b) μ ν ha hc
      (hα i b) (hα _ b) (hβ i b) (hβ _ b) hμ hν
    nlinarith [mul_le_mul_of_nonneg_left this hD]
  refine ⟨part1, hconv, fun a ha b hb μ ν hμ hν hμν => ?_⟩
  unfold Problem.ldr
  simp only [smul_eq_mul]
  apply Finset.le_inf'
  intro x hx
  have hxne : x.1 ≠ P.ib x.2 := (Finset.mem_filter.mp hx).2.2
  have hcx := (part1 x.1 x.2 hxne).2 ha hb hμ hν hμν
  simp only [smul_eq_mul] at hcx
  have hW : 0 ≤ P.W x.1 x.2 := by
    unfold Problem.W
    split_ifs <;> exact le_trans zero_le_one (le_max_right _ _)
  have h1 := Finset.inf'_le (fun x => P.W x.1 x.2 * P.G a x.1 x.2) hx
  have h2 := Finset.inf'_le (fun x => P.W x.1 x.2 * P.G b x.1 x.2) hx
  nlinarith [mul_le_mul_of_nonneg_left hcx hW, mul_le_mul_of_nonneg_left h1 hμ,
    mul_le_mul_of_nonneg_left h2 hν]
