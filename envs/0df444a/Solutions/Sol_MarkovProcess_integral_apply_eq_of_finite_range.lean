-- Prove2me | solution 1 for MarkovProcess.integral_apply_eq_of_finite_range
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:28:43.682615+00:00
-- url     : https://prove2.me/submissions/50922d09-ad3c-4856-aaaa-b65c52f5bd85

import Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
import Definitions.Def_MarkovProcess_V3H_Path_StoppingTimeDyadicCeiling_2d75c809
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Instances.NNReal.Lemmas

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Optional stopping in continuous time, at a bounded finite stopping time

Mathlib's optional stopping theorem is discrete-time.  This file proves the continuous-time
statement the library consumes: if `M` is a real-valued martingale for a filtration indexed by
`ℝ≥0`, bounded on bounded time intervals and right continuous in time along every sample point,
and `T` is a finite stopping time bounded by a deterministic horizon `K`, then

  `∫ omega, M (T omega) omega ∂mu = ∫ omega, M 0 omega ∂mu`

(`integral_stoppedValue_eq_of_locallyBounded`, with the uniformly bounded case
`integral_stoppedValue_eq_of_le`).

For a supermartingale the corresponding expectation is at most its initial expectation
(`integral_stoppedValue_le_of_locallyBounded` and `integral_stoppedValue_le_of_le`).

The proof samples a supermartingale on the dyadic grid and applies Mathlib's
`Submartingale.expected_stoppedValue_mono` after negation.  The dyadic ceilings `T_n` of a finite
stopping time are stopping times with finite range that decrease to `T`
(`Path/StoppingTimeDyadicCeiling.lean`), so dominated convergence and right continuity give the
supermartingale inequality.  Applying that inequality to a martingale and its negation gives the
martingale equality.

Nothing here is specific to path space: the statements are for an arbitrary measurable space with
a filtration indexed by `ℝ≥0`.  No optional-stopping result for unbounded stopping times is
asserted.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section

variable {Omega : Type*} {m : MeasurableSpace Omega} {mu : Measure Omega}
  {ℱ : Filtration NNReal m} {M : NNReal → Omega → ℝ}

section FiniteRange

variable [IsFiniteMeasure mu]

/-- A function of a time-valued map with values in a finite set is the sum of the indicators of
the level sets. -/
private theorem apply_eq_sum_indicator {S : Omega → NNReal} {V : Finset NNReal}
    (hSV : ∀ omega, S omega ∈ V) (g : NNReal → Omega → ℝ) (omega : Omega) :
    g (S omega) omega = ∑ v ∈ V, Set.indicator {eta | S eta = v} (g v) omega := by
  rw [Finset.sum_eq_single_of_mem (S omega) (hSV omega)]
  · rw [Set.indicator_of_mem (Set.mem_ofPred_eq ▸ rfl)]
  · intro v _ hv
    exact Set.indicator_of_notMem (fun h ↦ hv h.symm) _

/-- The level sets of a stopping time with finite range are events of the filtration at the
corresponding time. -/
theorem measurableSet_eq_of_finite_range {S : Omega → NNReal}
    (hS : IsStoppingTime ℱ fun omega ↦ ((S omega : NNReal) : WithTop NNReal))
    (hfin : (Set.range S).Finite) (v : NNReal) :
    MeasurableSet[ℱ v] {omega | S omega = v} := by
  have hcount : (Set.range fun omega ↦ ((S omega : NNReal) : WithTop NNReal)).Countable := by
    refine (hfin.countable.image (fun w : NNReal ↦ (w : WithTop NNReal))).mono ?_
    rintro _ ⟨omega, rfl⟩
    exact ⟨S omega, ⟨omega, rfl⟩, rfl⟩
  have hset : {omega | S omega = v} =
      {omega | ((S omega : NNReal) : WithTop NNReal) = (v : WithTop NNReal)} := by
    ext omega
    simp only [Set.mem_ofPred_eq, WithTop.coe_eq_coe]
  rw [hset]
  exact hS.measurableSet_eq_of_countable_range hcount v





end FiniteRange

section DyadicApproximation













end DyadicApproximation

section OptionalStopping

variable [IsFiniteMeasure mu]









end OptionalStopping

end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Optional stopping in continuous time, at a bounded finite stopping time

Mathlib's optional stopping theorem is discrete-time.  This file proves the continuous-time
statement the library consumes: if `M` is a real-valued martingale for a filtration indexed by
`ℝ≥0`, bounded on bounded time intervals and right continuous in time along every sample point,
and `T` is a finite stopping time bounded by a deterministic horizon `K`, then

  `∫ omega, M (T omega) omega ∂mu = ∫ omega, M 0 omega ∂mu`

(`integral_stoppedValue_eq_of_locallyBounded`, with the uniformly bounded case
`integral_stoppedValue_eq_of_le`).

For a supermartingale the corresponding expectation is at most its initial expectation
(`integral_stoppedValue_le_of_locallyBounded` and `integral_stoppedValue_le_of_le`).

The proof samples a supermartingale on the dyadic grid and applies Mathlib's
`Submartingale.expected_stoppedValue_mono` after negation.  The dyadic ceilings `T_n` of a finite
stopping time are stopping times with finite range that decrease to `T`
(`Path/StoppingTimeDyadicCeiling.lean`), so dominated convergence and right continuity give the
supermartingale inequality.  Applying that inequality to a martingale and its negation gives the
martingale equality.

Nothing here is specific to path space: the statements are for an arbitrary measurable space with
a filtration indexed by `ℝ≥0`.  No optional-stopping result for unbounded stopping times is
asserted.
-/

open Filter MeasureTheory Topology
open scoped NNReal



variable {Omega : Type*} {m : MeasurableSpace Omega} {mu : Measure Omega}
  {ℱ : Filtration NNReal m} {M : NNReal → Omega → ℝ}


variable [IsFiniteMeasure mu]







namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution (hM : Martingale M ℱ mu)
    (hMint : ∀ t : NNReal, Integrable (M t) mu) {S : Omega → NNReal}
    (hS : IsStoppingTime ℱ fun omega ↦ ((S omega : NNReal) : WithTop NNReal))
    (hfin : (Set.range S).Finite) {u : NNReal} (hu : ∀ omega, S omega ≤ u) :
    ∫ omega, M (S omega) omega ∂mu = ∫ omega, M u omega ∂mu := by
  have hSV : ∀ omega, S omega ∈ hfin.toFinset := fun omega ↦
    hfin.mem_toFinset.mpr ⟨omega, rfl⟩
  have hmeas : ∀ v : NNReal, MeasurableSet[ℱ v] {omega | S omega = v} :=
    measurableSet_eq_of_finite_range hS hfin
  have hmeas' : ∀ v : NNReal, MeasurableSet {omega | S omega = v} := fun v ↦
    ℱ.le v _ (hmeas v)
  have hind : ∀ (g : NNReal → Omega → ℝ), (∀ t : NNReal, Integrable (g t) mu) →
      ∫ omega, g (S omega) omega ∂mu =
        ∑ v ∈ hfin.toFinset, ∫ omega in {omega | S omega = v}, g v omega ∂mu := by
    intro g hg
    have hsum : ∫ omega, g (S omega) omega ∂mu =
        ∫ omega, ∑ v ∈ hfin.toFinset, Set.indicator {eta | S eta = v} (g v) omega ∂mu :=
      integral_congr_ae (Eventually.of_forall fun omega ↦ apply_eq_sum_indicator hSV g omega)
    rw [hsum, integral_finsetSum _ fun v _ ↦ (hg v).indicator (hmeas' v)]
    exact Finset.sum_congr rfl fun v _ ↦ integral_indicator (hmeas' v)
  rw [hind M hMint, hind (fun _ ↦ M u) fun _ ↦ hMint u]
  refine Finset.sum_congr rfl fun v hv ↦ ?_
  have hle : v ≤ u := by
    obtain ⟨omega, rfl⟩ := hfin.mem_toFinset.mp hv
    exact hu omega
  rw [← setIntegral_condExp (ℱ.le v) (hMint u) (hmeas v)]
  exact (setIntegral_congr_ae (hmeas' v) ((hM.2 v u hle).mono fun _ hx _ ↦ hx)).symm
