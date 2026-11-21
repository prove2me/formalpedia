-- Prove2me | solution 1 for MasulloRH.single_prime_certificate_verifies_height_via_quartets
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T04:37:39.676225+00:00
-- url     : https://prove2.me/submissions/56b50f46-997c-4f2a-b2ac-bcf3d57d1b51

-- Explicit height test from one prime cutoff and one finite critical-line witness.
import Theorems.Thm_MasulloRH_single_prime_certificate_controls_all_cutoffs
import Theorems.Thm_MasulloRH_cofinal_prime_slack_verifies_height_via_quartets
import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH ArithmeticFunction
open Set Filter Topology MeasureTheory

theorem solution (N : ℕ) (hN : 2 ≤ N) (ε : ℝ) :
    let f := fun j : ℕ => vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ)
    let C := Real.log 2/2 + Real.pi/4 - 37/30
    let Z := {z : ZetaZerosInTraceStrip (1/2) // z.val.re = 1/2}
    let M := fun F : Finset Z => ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val.val:ℝ) *
      ((z.val.val.im^2-5)/(2*(z.val.val.im^2+25/4)*(z.val.val.im^2+4)))
    ∀ F : Finset Z, C+(∑ j ∈ Finset.range (N+1), f j) ≤ M F + ε →
      ∀ H : ℝ, (200000001/100000000 : ℝ)*(ε+((2/3)*Real.log N+4/9)*(N:ℝ)^(-(3/2):ℝ))*(1+H^2) < 4 →
        ∀ z : ZetaZerosInTraceStrip (1/2), |z.val.im| ≤ H → z.val.re = 1/2 := by
  classical
  dsimp only
  intro F hc
  let τ := ε+((2/3)*Real.log N+4/9)*(N:ℝ)^(-(3/2):ℝ)
  apply cofinal_prime_slack_verifies_height_via_quartets τ
  intro k
  refine ⟨k,le_rfl,F,?_⟩
  have h := single_prime_certificate_controls_all_cutoffs N hN ε F hc k
  dsimp only at h
  exact h.trans (le_add_of_nonneg_right (by positivity))
