-- Prove2me | solution 1 for Kyprianou.Ch01.continuousUpperPassageDiscountedExpLimitPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:14:35.991719+00:00
-- url     : https://prove2.me/submissions/9d656fa3-f38f-4cf0-b76d-1908eccea31b

import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_continuousFirstUpperContactFromBelowPublic
import Theorems.Thm_Kyprianou_Ch01_discountedResidualVanishingAtInfinityPublic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 Filter
open scoped NNReal
set_option autoImplicit false

/-- Finite first passage makes the capped exponential eventually constant. -/
private theorem finiteCase
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (x theta q : ℝ) (hx : 0 < x)
    (hcont : Continuous (fun t : ℝ≥0 => X t ω))
    (hzero : X 0 ω = 0)
    (hex : ∃ t : ℝ≥0, 0 < t ∧ x < X t ω) :
    Tendsto (fun N : ℕ =>
      let T : ℝ≥0 := N
      let tauT : ℝ≥0 :=
        match firstUpperPassage X x ω with
        | none => T
        | some t => min t T
      Real.exp (theta * X tauT ω - q * (tauT : ℝ)))
      atTop (nhds (Real.exp (theta * x) *
        passageLaplace (firstUpperPassage X x) q ω)) := by
  classical
  let S : Set ℝ≥0 := {t | 0 < t ∧ x < X t ω}
  let u : ℝ≥0 := sInf S
  have hpass : firstUpperPassage X x ω = (u : WithTop ℝ≥0) := by
    simp [firstUpperPassage, hex, u, S] <;> rfl
  have hcontact : X u ω = x := by
    apply continuousFirstUpperContactFromBelowPublic
      (fun t : ℝ≥0 => X t ω) hcont x
    · simpa only [hzero] using hx
    · exact hex
  obtain ⟨N0, hN0⟩ := exists_nat_ge u
  have hevent : ∀ᶠ N : ℕ in atTop, u ≤ (N : ℝ≥0) := by
    filter_upwards [eventually_ge_atTop N0] with N hN
    exact le_trans hN0 (by exact_mod_cast hN)
  have heventEq :
      (fun N : ℕ =>
        let T : ℝ≥0 := N
        let tauT : ℝ≥0 :=
          match firstUpperPassage X x ω with
          | none => T
          | some t => min t T
        Real.exp (theta * X tauT ω - q * (tauT : ℝ))) =ᶠ[atTop]
        (fun _ : ℕ => Real.exp (theta * x - q * (u : ℝ))) := by
    filter_upwards [hevent] with N hN
    simp [hpass, min_eq_left hN, hcontact]
  have htarget : Real.exp (theta * x) *
      passageLaplace (firstUpperPassage X x) q ω =
      Real.exp (theta * x - q * (u : ℝ)) := by
    simp [passageLaplace, hpass, sub_eq_add_neg, Real.exp_add]
  rw [htarget]
  exact (tendsto_const_nhds : Tendsto
    (fun _ : ℕ => Real.exp (theta * x - q * (u : ℝ))) atTop
    (nhds (Real.exp (theta * x - q * (u : ℝ))))).congr' heventEq.symm

/-- Infinite-horizon stopped exponential limit for an individual continuous path. -/
theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (x theta q : ℝ) (hx : 0 < x) (hθ : 0 ≤ theta) (hq : 0 < q)
    (hcont : Continuous (fun t : ℝ≥0 => X t ω))
    (hzero : X 0 ω = 0) :
    Tendsto (fun N : ℕ =>
      let T : ℝ≥0 := N
      let tauT : ℝ≥0 :=
        match firstUpperPassage X x ω with
        | none => T
        | some t => min t T
      Real.exp (theta * X tauT ω - q * (tauT : ℝ)))
      atTop (nhds (Real.exp (theta * x) *
        passageLaplace (firstUpperPassage X x) q ω)) := by
  classical
  by_cases hex : ∃ t : ℝ≥0, 0 < t ∧ x < X t ω
  · exact finiteCase X ω x theta q hx hcont hzero hex
  · have hpass : firstUpperPassage X x ω = ⊤ := by
      simp [firstUpperPassage, hex]
    have hbound (N : ℕ) : X (N : ℝ≥0) ω ≤ x := by
      by_contra hc
      have hgt : x < X (N : ℝ≥0) ω := lt_of_not_ge hc
      have hNpos : (0 : ℝ≥0) < N := by
        by_contra hz
        have hN0 : (N : ℝ≥0) = 0 :=
          le_antisymm (le_of_not_gt hz) (by positivity)
        rw [hN0, hzero] at hgt
        linarith
      exact hex ⟨N, hNpos, hgt⟩
    have hlim := discountedResidualVanishingAtInfinityPublic
      (fun N : ℕ => X (N : ℝ≥0) ω) x theta q hbound hθ hq
    simpa [hpass, passageLaplace] using hlim
