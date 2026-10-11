-- Prove2me | solution 1 for MarginalUtility.law_of_diminishing_marginal_utility
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T10:01:02.206304+00:00
-- url     : https://prove2.me/submissions/f0852663-1bc0-41a6-92e6-fcdffa71ea90

import Mathlib
import Definitions.Def_MarginalUtility_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology Set

open MarginalUtility

theorem solution (U : ℝ → ℝ) (D : Set ℝ)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hU : HasDiminishingMarginalUtility U D) :
    StrictAntiOn (marginalUtility U) D ∧
      ∀ x h : ℝ, 0 < h → x ∈ D → x + 2 * h ∈ D →
        utilityChange U (x + h) (x + 2 * h) < utilityChange U x (x + h) := by
  simp only [HasDiminishingMarginalUtility] at hU
  obtain ⟨hUd, hUdd, hUddlt⟩ := hU
  -- Convexity transports any closed interval between two points of D into D.
  have hIcc (a b : ℝ) (ha : a ∈ D) (hb : b ∈ D) : Set.Icc a b ⊆ D :=
    Icc_subset_segment.trans (hDc.segment_subset ha hb)
  -- (i): the marginal utility U' is strictly decreasing on D, by the mean value
  -- theorem applied to U' between any a < b in D.
  have hanti : StrictAntiOn (deriv U) D := by
    intro a ha b hb hab
    obtain ⟨c, hc, heq⟩ := exists_deriv_eq_slope (f := deriv U) hab
      (hUdd.continuousOn.mono (hIcc a b ha hb))
      (hUdd.mono fun t ht => hIcc a b ha hb ⟨ht.1.le, ht.2.le⟩)
    have hcmem : c ∈ D := hIcc a b ha hb ⟨hc.1.le, hc.2.le⟩
    -- the MVT slope (U' b - U' a)/(b - a) equals U'' c < 0, hence
    -- U' b - U' a < 0 by clearing the (positive) denominator.
    have hd : (deriv U b - deriv U a) / (b - a) < 0 := by
      rw [← heq]
      exact hUddlt c hcmem
    have hneg : deriv U b - deriv U a < 0 := by
      field_simp at hd
      linarith
    linarith
  refine ⟨fun a ha b hb hab => hanti ha hb hab, ?_⟩
  intro x h hpos hx hx2
  have hx1 : x + h ∈ D :=
    hIcc x (x + 2 * h) hx hx2 ⟨(by linarith : x < x + h).le, (by linarith : x + h < x + 2 * h).le⟩
  have hI1 : Set.Icc x (x + h) ⊆ D := hIcc x (x + h) hx hx1
  have hI2 : Set.Icc (x + h) (x + 2 * h) ⊆ D := hIcc (x + h) (x + 2 * h) hx1 hx2
  obtain ⟨c1, hc1, heq1⟩ := exists_deriv_eq_slope (f := U) (by linarith)
    (hUd.continuousOn.mono hI1)
    (hUd.mono fun t ht => hI1 ⟨ht.1.le, ht.2.le⟩)
  obtain ⟨c2, hc2, heq2⟩ := exists_deriv_eq_slope (f := U) (by linarith)
    (hUd.continuousOn.mono hI2)
    (hUd.mono fun t ht => hI2 ⟨ht.1.le, ht.2.le⟩)
  have hc1D : c1 ∈ D := hI1 ⟨hc1.1.le, hc1.2.le⟩
  have hc2D : c2 ∈ D := hI2 ⟨hc2.1.le, hc2.2.le⟩
  have hcdiff : c1 < c2 := by
    have h1 : c1 < x + h := hc1.2
    have h2 : x + h < c2 := hc2.1
    linarith
  have hderlt : deriv U c2 < deriv U c1 := hanti hc1D hc2D hcdiff
  -- both intervals have length exactly h
  have h2a : (x + h) - x = h := by ring
  have h2b : (x + 2 * h) - (x + h) = h := by ring
  have e1 : h * deriv U c1 = U (x + h) - U x := by
    rw [heq1, h2a]
    field_simp
    all_goals first | ring | linarith
  have e2 : h * deriv U c2 = U (x + 2 * h) - U (x + h) := by
    rw [heq2, h2b]
    field_simp
    all_goals first | ring | linarith
  have hgoal : h * deriv U c2 < h * deriv U c1 := mul_lt_mul_of_pos_left hderlt hpos
  rw [e1, e2] at hgoal
  show U (x + 2 * h) - U (x + h) < U (x + h) - U x
  exact hgoal
