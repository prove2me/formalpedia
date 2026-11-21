-- Prove2me | solution 1 for MasulloRH.cofinal_prime_slack_bounds_off_line_zero_count
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:59:12.794763+00:00
-- url     : https://prove2.me/submissions/aeb5ff97-da76-432c-b963-636a413960c4

-- Quantitative zero-count consequence of the finite prime certificates.
import Theorems.Thm_MasulloRH_off_line_reference_half_weight_error
import Theorems.Thm_MasulloRH_cofinal_prime_slack_iff_off_line_mass_le
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH ArithmeticFunction Set Filter Topology

theorem solution (τ : ℝ) :
    let f := fun j : ℕ => vonMangoldt j/(j:ℝ)^(5/2:ℝ) - vonMangoldt j/(j:ℝ)^(3:ℝ)
    let C := Real.log 2/2 + Real.pi/4 - 37/30
    let Z := {z : ZetaZerosInTraceStrip (1/2) // z.val.re = 1/2}
    let M := fun F : Finset Z => ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val.val:ℝ) *
      ((z.val.val.im^2-5)/(2*(z.val.val.im^2+25/4)*(z.val.val.im^2+4)))
    (∀ k : ℕ, ∃ N ≥ k, ∃ F : Finset Z,
      C + (∑ j ∈ Finset.range N,f j) ≤ M F + τ + 1/((k:ℝ)+1)) →
    ∀ (H : ℝ) (S : Finset {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2}),
      (∀ z ∈ S, |z.val.val.im| ≤ H) →
      (∑ z ∈ S,(analyticOrderNatAt riemannZeta z.val.val : ℝ)) ≤
        (200000001/100000000 : ℝ)*τ*(1+H^2) := by
  classical
  dsimp only
  intro hc H S hS
  let A : Set (ZetaZerosInTraceStrip (1/2)) := {z | z.val.re ≠ 1/2}
  let w (z : A) := zeroDecayWeight (1/2) z.val
  let W := ∑' z,w z
  let K := ∑' z : A,(zeroResolventTerm (1/2) 3 z.val).re
  have hK : K ≤ τ := (cofinal_prime_slack_iff_off_line_mass_le τ).mpr hc
  have he : (1+99998^2)*(W/2-K) ≤ 16*W := off_line_reference_half_weight_error.2
  have hw (z : A) : 0 ≤ w z := by dsimp [w,zeroDecayWeight]; positivity
  have hW0 : 0 ≤ W := tsum_nonneg hw
  have hW : W ≤ (200000001/100000000 : ℝ)*τ := by linarith only [hK,he,hW0]
  have hs : Summable w := (weighted_zero_summability (1/2) (by norm_num)).subtype A
  let S' : Finset A := S
  haveI : (SummationFilter.unconditional A).NeBot := ⟨Filter.atTop_neBot⟩
  have hpartial : (∑ z ∈ S',w z) ≤ W := hs.sum_le_tsum S' (fun z _ => hw z)
  calc
    _ ≤ ∑ z ∈ S,w z*(1+H^2) := by
      apply Finset.sum_le_sum
      intro z hz
      have hab := hS z hz
      have ht : z.val.val.im^2 ≤ H^2 := by
        nlinarith only [sq_abs z.val.val.im,mul_self_le_mul_self (abs_nonneg _) hab]
      have hid : w z*(1+z.val.val.im^2) = (analyticOrderNatAt riemannZeta z.val.val:ℝ) := by
        dsimp [w,zeroDecayWeight]; field_simp
      rw [←hid]
      exact mul_le_mul_of_nonneg_left (by linarith only [ht]) (hw z)
    _ = (∑ z ∈ S,w z)*(1+H^2) := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hpartial.trans hW) (by positivity)
