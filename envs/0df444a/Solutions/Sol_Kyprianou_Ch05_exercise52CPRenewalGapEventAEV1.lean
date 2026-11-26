-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52CPRenewalGapEventAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:38:12.961025+00:00
-- url     : https://prove2.me/submissions/cd677ac6-6262-43f9-a0ae-9c85cdef07c2

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonDriverArrivalStrictMonoDivergesPublic
import Theorems.Thm_levy_foundations_compoundDriverFirstArrivalPos
import Theorems.Thm_Kyprianou_Ch05_exercise52PositiveDriverMarksAEV1
import Theorems.Thm_Kyprianou_Ch05_exercise52RationalJumpCountSurjectiveV1
import Theorems.Thm_Kyprianou_Ch05_exercise52DiscreteRenewalGapV1
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
/-- Identify rational-time observations with the entire discrete renewal sequence. -/
theorem solution
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    [IsProbabilityMeasure Q] (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hPos : F (Iic 0) = 0)
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q)
    (x u y : ℝ) (hx : 0 < x) (hu : 0 < u) (hy : 0 < y) :
    ∀ᵐ w ∂Q, (u < renewalOvershoot marks x w ∧ y < renewalUndershoot marks x w) ↔
      (fun (t : NNReal) => ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) w) ∈ {g : NNReal → ℝ | ∃ a b : ℚ, (a : ℝ) < x - y ∧ x + u < (b : ℝ) ∧
      (∀ q : ℚ, g (Real.toNNReal q) ≤ (a : ℝ) ∨ (b : ℝ) ≤ g (Real.toNNReal q)) ∧
      ∃ q : ℚ, (b : ℝ) ≤ g (Real.toNNReal q)} := by
  have hd' : ProbabilityTheory.IsCompoundPoissonDriver arrival marks 1 F Q :=
    ⟨hd.measurable_interarrival,hd.measurable_mark,hd.indep,hd.law_interarrival,hd.law_mark⟩
  obtain ⟨hm,ht⟩ := Kyprianou.Ch01.compoundPoissonDriverArrivalStrictMonoDivergesPublic
    Q 1 one_pos arrival marks F hd'
  have hp := levy_foundations_compoundDriverFirstArrivalPos hd one_pos
  have hmarks := exercise52PositiveDriverMarksAEV1 Q arrival marks F hPos hd
  filter_upwards [hm,ht,hp,hmarks] with w hmono htop hzero hpos
  let T := fun n => ProbabilityTheory.arrival arrival n w
  let S := fun n => renewalEpoch marks n w
  have hsurj := exercise52RationalJumpCountSurjectiveV1 T hmono htop
    (show 0 < T 0 from hzero)
  have hsmono : Monotone S := monotone_nat_of_le_succ fun n => by
    change (∑ k ∈ Finset.range n, marks k w) ≤ ∑ k ∈ Finset.range (n+1), marks k w
    rw [Finset.sum_range_succ]
    linarith [hpos n]
  have hs0 : S 0 = 0 := by simp [S,renewalEpoch]
  have hval (q : ℚ) :
      ProbabilityTheory.compoundPoisson 0 arrival marks (Real.toNNReal q : ℝ) w =
        S (ProbabilityTheory.jumpCount T (Real.toNNReal q : ℝ)) := by
    simp [ProbabilityTheory.compoundPoisson,ProbabilityTheory.piecewisePath,S,T,renewalEpoch]
  change (u < S (sInf {k : ℕ | 0 < k ∧ x < S k}) - x ∧
    y < x - S (sInf {k : ℕ | 0 < k ∧ x < S k}-1)) ↔ _
  have hgap := exercise52DiscreteRenewalGapV1 S hsmono hs0 x u y hx hu hy
  dsimp only at hgap
  rw [hgap]
  simp only [mem_setOf_eq,hval]
  constructor
  · rintro ⟨a,b,ha,hb,hg,k,hk⟩
    obtain ⟨q,hq⟩ := hsurj k
    change ProbabilityTheory.jumpCount T (Real.toNNReal q : ℝ) = k at hq
    exact ⟨a,b,ha,hb,fun q => hg _,q,by rw [hq]; exact hk⟩
  · rintro ⟨a,b,ha,hb,hg,q,hq⟩
    refine ⟨a,b,ha,hb,?_,_,hq⟩
    intro k
    obtain ⟨r,hr⟩ := hsurj k
    change ProbabilityTheory.jumpCount T (Real.toNNReal r : ℝ) = k at hr
    simpa only [hr] using hg r
