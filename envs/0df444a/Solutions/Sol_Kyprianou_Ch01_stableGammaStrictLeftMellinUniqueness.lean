-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftMellinUniqueness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:32:56.968222+00:00
-- url     : https://prove2.me/submissions/86191fdb-3ce6-4360-892e-10551f8a7b5d

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftMellinRhsHolomorphic__9c159f
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftComplexRealAxisAnchor
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftRealAxisPhaseAlgebra
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set Filter Kyprianou.Ch01
open scoped Topology
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (hanalytic : AnalyticOnNhd ℂ
      (fun w : ℂ =>
        ∫ r in Set.Ioi (0 : ℝ),
          Complex.exp (w * (r : ℂ)) *
            ((r ^ (-alpha) : ℝ) : ℂ) ∂volume)
      {w : ℂ | w.re < 0}) :
    ∀ w : ℂ, w.re < 0 →
      (∫ r in Set.Ioi (0 : ℝ),
          Complex.exp (w * (r : ℂ)) *
            ((r ^ (-alpha) : ℝ) : ℂ) ∂volume) =
        ((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
          Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (-w))
    := by
  intro w hwre
  let U : Set ℂ := {z | z.re < 0}
  let F : ℂ → ℂ := fun z =>
    ∫ r in Set.Ioi (0 : ℝ),
      Complex.exp (z * (r : ℂ)) *
        ((r ^ (-alpha) : ℝ) : ℂ) ∂volume
  let G : ℂ → ℂ := fun z =>
    ((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
      Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (-z))
  have hF : AnalyticOnNhd ℂ F U := hanalytic
  have hG : AnalyticOnNhd ℂ G U :=
    Kyprianou.Ch01.stableGammaStrictLeftMellinRhsHolomorphic alpha
  have hconn : IsPreconnected U := (convex_halfSpace_re_lt 0).isPreconnected
  have hz0 : (-1 : ℂ) ∈ U := by simp [U]
  have haxis : ∀ u : ℝ, 0 < u → F (-(u : ℂ)) = G (-(u : ℂ)) := by
    intro u hu
    calc
      F (-(u : ℂ)) =
        (((((1 / u) ^ (1 - alpha)) * Real.Gamma (1 - alpha) : ℝ)) : ℂ) :=
          Kyprianou.Ch01.stableGammaStrictLeftComplexRealAxisAnchor alpha u h0 h1 hu
      _ = G (-(u : ℂ)) := by
        dsimp [G]
        rw [neg_neg]
        exact Kyprianou.Ch01.stableGammaStrictLeftRealAxisPhaseAlgebra alpha u hu
  have hreal : ∃ᶠ u : ℝ in 𝓝[≠] (1 : ℝ),
      F (-(u : ℂ)) = G (-(u : ℂ)) := by
    have hpos : ∀ᶠ u : ℝ in 𝓝[≠] (1 : ℝ), 0 < u :=
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
        nhdsWithin_le_nhds
    exact hpos.frequently.mono (fun u hu => haxis u hu)
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] (-1 : ℂ), F z = G z := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hxs, heq⟩ := hreal
    refine ⟨fun n => -(xs n : ℂ), ?_, fun n => heq n⟩
    rw [tendsto_nhdsWithin_iff] at hxs ⊢
    constructor
    · have hcast : Tendsto (fun n => (xs n : ℂ)) atTop (nhds (1 : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 1).comp hxs.1
      simpa using hcast.neg
    · filter_upwards [hxs.2] with n hn
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hn
  have h := hF.eqOn_of_preconnected_of_frequently_eq hG hconn hz0 hfreq
  exact h hwre
