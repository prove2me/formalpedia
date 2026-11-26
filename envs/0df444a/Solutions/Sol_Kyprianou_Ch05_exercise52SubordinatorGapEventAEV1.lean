-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52SubordinatorGapEventAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:29:25.514622+00:00
-- url     : https://prove2.me/submissions/9b3656da-0bd7-44b7-a7ef-fb94cd52a907

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_exercise52PassageToRationalGapV1
import Theorems.Thm_Kyprianou_Ch05_exercise52RationalGapToPassageV1
import Theorems.Thm_Kyprianou_Ch05_exercise52StrictUpperClockFactsV1
import Theorems.Thm_Kyprianou_Ch05_exercise52RationalGapAllTimesV1
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05

open Topology
/-- Characterise strict passage with a positive undershoot and overshoot by a rational gap. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X Xleft : NNReal → Omega → ℝ) (deathX : Omega → WithTop NNReal)
    (hX : IsKilledSubordinator P X deathX 0)
    (hLeft : IsLeftLimitVersion P X Xleft)
    (x u y : ℝ) (hx : 0 < x) (hu : 0 < u) (hy : 0 < y) :
    ∀ᵐ w ∂P,
      (PassageFinite X deathX x w ∧ passageOvershoot X deathX x w ∈ Ioi u ∧
        passageUndershoot X Xleft deathX x w ∈ Ioi y) ↔
      (fun t => X t w) ∈ {g : NNReal → ℝ | ∃ a b : ℚ, (a : ℝ) < x - y ∧ x + u < (b : ℝ) ∧
      (∀ q : ℚ, g (Real.toNNReal q) ≤ (a : ℝ) ∨ (b : ℝ) ≤ g (Real.toNNReal q)) ∧
      ∃ q : ℚ, (b : ℝ) ≤ g (Real.toNNReal q)} := by
  filter_upwards [hX.1.1.cadlag_ae, hX.1.2, hLeft] with w hc hm hl
  have h0 : X 0 w = 0 := congrFun hX.1.1.start_zero w
  have hr (t : NNReal) : ContinuousWithinAt (fun v => X v w) (Ici t) t := (hc t).1
  let T : WithTop NNReal := strictUpcrossing X deathX x w
  have hT : T = sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ x < X t w} := by
    unfold T strictUpcrossing
    congr 1
    ext v
    simp only [hX.2.2.2.1 rfl w, Set.mem_image, Set.mem_setOf_eq, WithTop.coe_lt_top, true_and]
    constructor
    · rintro ⟨t,ht,he⟩
      exact ⟨t,he.symm,ht.1,ht.2⟩
    · rintro ⟨t,he,ht,hx'⟩
      exact ⟨t,⟨ht,hx'⟩,he.symm⟩
  have hFacts (s : NNReal) (hs : T = ↑s) :=
    exercise52StrictUpperClockFactsV1 (fun t => X t w) h0 hr x hx s (hs.symm.trans hT)
  change (T ≠ ⊤ ∧ u < X (T.untopD 0) w - x ∧
      y < x - Xleft (T.untopD 0) w) ↔ _
  constructor
  · rintro ⟨ht, ho, hu'⟩
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp ht
    have hts : T = ↑s := hs.symm
    rw [hts, WithTop.untopD_coe] at ho hu'
    obtain ⟨hs0, hpre, hat⟩ := hFacts s hts
    exact exercise52PassageToRationalGapV1 (fun t => X t w) (fun t => Xleft t w)
      hm s hs0 (hl s hs0) x u y hx hu hy ho hu'
  · rintro ⟨a,b,ha,hb,hgap,q,hq⟩
    have hgap' := (exercise52RationalGapAllTimesV1 (fun t => X t w) hr a b).2 hgap
    have hhit : x < X (Real.toNNReal q) w := by linarith
    have hq0 : 0 < Real.toNNReal q := by
      by_contra! hn
      have he : Real.toNNReal q = 0 := le_antisymm hn bot_le
      rw [he,h0] at hhit
      linarith
    have hle : T ≤ (↑(Real.toNNReal q) : WithTop NNReal) := by
      rw [hT]
      exact sInf_le ⟨Real.toNNReal q,rfl,hq0,hhit⟩
    have ht : T ≠ ⊤ := ne_of_lt (hle.trans_lt (WithTop.coe_lt_top _))
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp ht
    have hts : T = ↑s := hs.symm
    obtain ⟨hs0,hpre,hat⟩ := hFacts s hts
    have hh := exercise52RationalGapToPassageV1 (fun t => X t w) (fun t => Xleft t w)
      hm s hs0 (hl s hs0) x u y hx hu hy hr hpre hat ⟨a,b,ha,hb,hgap,q,hq⟩
    refine ⟨ht, ?_, ?_⟩
    · rw [hts, WithTop.untopD_coe]; exact hh.1
    · rw [hts, WithTop.untopD_coe]; exact hh.2
