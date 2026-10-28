-- Prove2me | solution 1 for MarkovProcess.IsKolmogorovProcess.ae_eq_continuousGlobalDyadicFloorLimit_nat_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:45:22.948387+00:00
-- url     : https://prove2.me/submissions/dc464a5a-5a5a-4fdd-8335-4fbdf2a62c69

import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Continuity_GlobalDyadicFloorModification
import Definitions.Def_MarkovProcess_Continuity_KolmogorovTimeShift
import Definitions.Def_MarkovProcess_Continuity_ShiftedUnitModification
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.LocallyFinite
import Theorems.Thm_MarkovProcess_IsKolmogorovProcess_ae_continuous_unitDyadicFloorLimit
import Theorems.Thm_MarkovProcess_IsKolmogorovProcess_ae_eq_unitDyadicFloorLimit
import Theorems.Thm_MarkovProcess_locallyFinite_nnrealUnitInterval
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic floor approximation and the unit-interval continuous modification

This file merges the following former modules, one section each:

* `DyadicFloorApproximation`: Left dyadic approximations of unit-interval times
* `DyadicFloorPair`: Comparing two dyadic floor approximations
* `DyadicFloorSampleCauchy`: Cauchy control of dyadic floor samples
* `DyadicFloorDenseTime`: Dyadic floor samples at dyadic times
* `DyadicFloorSampleLimit`: Limits of dyadic floor samples
* `DyadicFloorLimitControl`: Uniform control of dyadic floor-sample limits
* `DyadicFloorLimitPath`: The canonical unit-interval dyadic-floor limit path
* `DyadicFloorConvergenceInMeasure`: Convergence in measure of dyadic floor samples
* `DyadicFloorUnitModification`: A continuous modification on the unit interval
-/

namespace MarkovProcess

section DyadicFloorApproximation


noncomputable section















end

end DyadicFloorApproximation

section DyadicFloorPair

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


noncomputable section









end

end DyadicFloorPair

section DyadicFloorSampleCauchy

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]







end DyadicFloorSampleCauchy

section DyadicFloorDenseTime


noncomputable section















end

end DyadicFloorDenseTime

section DyadicFloorSampleLimit

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E] [T2Space E] [CompleteSpace E]



end DyadicFloorSampleLimit

section DyadicFloorLimitControl

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]









end

end DyadicFloorLimitControl

section DyadicFloorLimitPath

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [PseudoMetricSpace E] [CompleteSpace E]











end

end DyadicFloorLimitPath

section DyadicFloorConvergenceInMeasure

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]



@[simp]
theorem unitIccOfNNRat_val (t : NNRat) (ht : t ≤ 1) :
    (unitIccOfNNRat t ht).1 = (t : ℝ) :=
  rfl
end DyadicFloorConvergenceInMeasure
end MarkovProcess

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Nonnegative-rational time shifts

This file translates a dense-time process by a nonnegative rational time.  Translation is an
isometry of `NNRat`, so the Kolmogorov increment condition is preserved with exactly the same
exponents and constant.  The final definitions and identities identify the unit-interval
dyadic samples and canonical limit for the shifted process with samples of the original process
on the interval starting at the shift.

No global path is glued here, and no measurability of the canonical limit or modification-law
assertion is made.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

variable {Ω E : Type*}



@[simp]
theorem timeShift_apply (k q : NNRat) (X : NNRat → Ω → E) (ω : Ω) :
    timeShift k X q ω = X (k + q) ω :=
  rfl

/-- Nonnegative-rational translation preserves the Kolmogorov condition without changing its
exponents or constant. -/
theorem IsKolmogorovProcess.timeShift
    {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]
    {P : Measure Ω} {X : NNRat → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (k : NNRat) :
    IsKolmogorovProcess (timeShift k X) P p q M where
  measurablePair s t := hX.measurablePair (k + s) (k + t)
  kolmogorovCondition s t := by
    have hdist : dist (k + s) (k + t) = dist s t := by
      rw [NNRat.dist_eq, NNRat.dist_eq, Rat.dist_eq, Rat.dist_eq]
      push_cast
      rw [add_sub_add_left_eq_sub]
    simpa only [timeShift, edist_dist, hdist] using!
      hX.kolmogorovCondition (k + s) (k + t)
  p_pos := hX.p_pos
  q_pos := hX.q_pos
end MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# A global continuous modification assembled from canonical unit paths

The nonnegative real half-line is covered by the closed unit intervals `[n, n + 1]`.  On each
piece we use the canonical dyadic-floor limit of the process shifted by `n`.  Exact endpoint
identities make these pieces compatible, so `Set.liftCover` gives an honest raw global path.
On the simultaneous probability-one event where every canonical unit piece is continuous, local
finiteness of the closed cover makes the raw path continuous.  A single constant global fallback
then gives a total path which is continuous for every sample.

No measurability of the path-valued map, path-space law, Markov property, or Hunt-process claim is
asserted here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]







omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem MarkovProcess.continuous_nnrealUnitCoordinate (n : ℕ) : Continuous (nnrealUnitCoordinate n) := by
  apply continuous_induced_rng.2
  exact (NNReal.continuous_coe.comp continuous_subtype_val).sub continuous_const









omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
@[simp]
theorem MarkovProcess.globalDyadicFloorLimit_coe
    (X : NNRat → Ω → E) (ω : Ω) (n : ℕ) (x : nnrealUnitInterval n) :
    globalDyadicFloorLimit X ω x = globalDyadicFloorPiece X ω n x :=
  Set.liftCover_coe x

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- If every canonical unit piece is continuous, then the raw global path is continuous. -/
theorem MarkovProcess.continuous_globalDyadicFloorLimit_of_forall
    {X : NNRat → Ω → E} {ω : Ω}
    (h : ∀ n : ℕ, Continuous (shiftedUnitDyadicFloorLimit n X ω)) :
    Continuous (globalDyadicFloorLimit X ω) := by
  apply locallyFinite_nnrealUnitInterval.continuous iUnion_nnrealUnitInterval
  · exact fun n ↦ isClosed_Icc
  · intro n
    rw [continuousOn_iff_continuous_domRestrict]
    have hpiece : Continuous (globalDyadicFloorPiece X ω n) :=
      (h n).comp (continuous_nnrealUnitCoordinate n)
    apply hpiece.congr
    intro x
    simpa only [Set.domRestrict_apply] using (globalDyadicFloorLimit_coe X ω n x).symm

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Almost surely, all natural-shift canonical pieces are simultaneously continuous. -/
theorem MarkovProcess.IsKolmogorovProcess.ae_forall_continuous_shiftedUnitDyadicFloorLimit
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, Continuous (shiftedUnitDyadicFloorLimit n X ω) := by
  rw [ae_all_iff]
  intro n
  simpa only [shiftedUnitDyadicFloorLimit] using
    IsKolmogorovProcess.ae_continuous_unitDyadicFloorLimit
      (IsKolmogorovProcess.timeShift hX n) hγ hγq

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Almost surely, the raw global dyadic-floor path is continuous. -/
theorem MarkovProcess.IsKolmogorovProcess.ae_continuous_globalDyadicFloorLimit
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, Continuous (globalDyadicFloorLimit X ω) := by
  filter_upwards
    [IsKolmogorovProcess.ae_forall_continuous_shiftedUnitDyadicFloorLimit hX hγ hγq]
      with ω hω
  exact continuous_globalDyadicFloorLimit_of_forall hω






theorem solution
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) (n : ℕ) (t : NNRat) (ht : t ≤ 1) :
    X (n + t) =ᵐ[P] fun ω ↦
      continuousGlobalDyadicFloorLimit X ω (↑((n : NNRat) + t) : ℝ≥0) := by
  let x : ℝ≥0 := ↑((n : NNRat) + t)
  have hx : x ∈ nnrealUnitInterval n := by
    have hl : (n : NNRat) ≤ (n : NNRat) + t := le_add_of_nonneg_right t.2
    have hu : (n : NNRat) + t ≤ (n : NNRat) + 1 := by
      simpa only [add_comm] using add_le_add_left ht (n : NNRat)
    constructor
    · dsimp only [x]
      exact_mod_cast hl
    · dsimp only [x]
      exact_mod_cast hu
  have hcoord : nnrealUnitCoordinate n ⟨x, hx⟩ = unitIccOfNNRat t ht := by
    apply Subtype.ext
    simp only [nnrealUnitCoordinate, unitIccOfNNRat_val, x]
    push_cast
    ring_nf
    change (((t : NNRat) : ℝ≥0) : ℝ) = (t : ℝ)
    exact_mod_cast rfl
  filter_upwards
    [IsKolmogorovProcess.ae_eq_unitDyadicFloorLimit
      (IsKolmogorovProcess.timeShift hX n) hγ hγq t ht,
      IsKolmogorovProcess.ae_continuous_globalDyadicFloorLimit hX hγ hγq]
      with ω hident hcont
  rw [continuousGlobalDyadicFloorLimit, if_pos hcont]
  rw [show (↑((n : NNRat) + t) : ℝ≥0) = x by rfl,
    globalDyadicFloorLimit_coe X ω n ⟨x, hx⟩, globalDyadicFloorPiece, hcoord]
  simpa only [timeShift_apply] using! hident
