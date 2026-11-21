-- Prove2me | solution 1 for MasulloRH.cofinal_prime_slack_verifies_height_via_quartets
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T04:14:43.737906+00:00
-- url     : https://prove2.me/submissions/0859d5cb-44f3-4191-a833-805ed73bd7be

-- New finite-height consequence. The analytic-order positivity argument is due to marozols.
import Theorems.Thm_MasulloRH_cofinal_prime_slack_bounds_off_line_zero_count
import Theorems.Thm_MasulloRH_off_line_zero_has_four_distinct_symmetries
import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH ArithmeticFunction Set Filter Topology

private theorem multiplicity_pos (ρ : ZetaZerosInTraceStrip (1/2)) :
    0 < analyticOrderNatAt riemannZeta ρ.val := by
  have h1 : ρ.val ≠ 1 := fun h => by
    have hr := congrArg Complex.re h
    simp only [Complex.one_re] at hr
    linarith [ρ.prop.2.2.1]
  have hA := analyticOn_riemannZeta
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hfin := hA.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
    (show (2:ℂ) ∈ ({1}:Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)
  apply Nat.pos_of_ne_zero
  unfold analyticOrderNatAt
  exact fun h => (ENat.toNat_eq_zero.mp h).elim
    ((hA _ h1).analyticOrderAt_ne_zero.mpr ρ.prop.1) hfin


theorem solution (τ : ℝ) :
    let f := fun j : ℕ => vonMangoldt j/(j:ℝ)^(5/2:ℝ) - vonMangoldt j/(j:ℝ)^(3:ℝ)
    let C := Real.log 2/2 + Real.pi/4 - 37/30
    let Z := {z : ZetaZerosInTraceStrip (1/2) // z.val.re = 1/2}
    let M := fun F : Finset Z => ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val.val:ℝ) *
      ((z.val.val.im^2-5)/(2*(z.val.val.im^2+25/4)*(z.val.val.im^2+4)))
    (∀ k : ℕ, ∃ N ≥ k, ∃ F : Finset Z,
      C + (∑ j ∈ Finset.range N,f j) ≤ M F + τ + 1/((k:ℝ)+1)) →
    ∀ H : ℝ, (200000001/100000000 : ℝ)*τ*(1+H^2) < 4 →
      ∀ z : ZetaZerosInTraceStrip (1/2), |z.val.im| ≤ H → z.val.re = 1/2 := by
  classical
  dsimp only
  intro hc H hsmall z hH
  by_contra hz
  obtain ⟨S,hcard,hS⟩ := off_line_zero_has_four_distinct_symmetries z hz
  have hc' := cofinal_prime_slack_bounds_off_line_zero_count τ hc H S
    (fun u hu => (hS u hu).le.trans hH)
  have hfour : (4:ℝ) ≤ ∑ u ∈ S,(analyticOrderNatAt riemannZeta u.val.val : ℝ) := by
    calc
      (4:ℝ) = ∑ _u ∈ S,(1:ℝ) := by simp [hcard]
      _ ≤ _ := Finset.sum_le_sum (fun u _ => by exact_mod_cast multiplicity_pos u.val)
  linarith only [hc',hsmall,hfour]
