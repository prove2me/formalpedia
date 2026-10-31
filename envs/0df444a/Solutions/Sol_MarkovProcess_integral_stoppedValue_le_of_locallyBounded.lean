-- Prove2me | solution 1 for MarkovProcess.integral_stoppedValue_le_of_locallyBounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:28:51.136168+00:00
-- url     : https://prove2.me/submissions/24f7f477-1ab8-44c2-a26e-deaeba27c4af

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
# Dyadic ceiling approximation of finite stopping times

The level-`n` dyadic ceiling of a nonnegative time is the least point of the grid `2⁻ⁿ ℕ` that is
at least the time.  Composed with a finite `NNReal`-valued stopping time it produces stopping
times with countable range that decrease to the original time.  This is ordinary stopping-time
infrastructure and proves no restart identity; the restart identity obtained from this
approximation is in `Trajectory/FellerStoppingRestart.lean`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section





/-- The real coercion of a dyadic ceiling is its defining quotient. -/
private theorem coe_dyadicCeiling (n : ℕ) (t : NNReal) :
    ((dyadicCeiling n t : NNReal) : ℝ) = (⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℝ) / 2 ^ n := rfl

/-- The real coercion of a dyadic floor is its defining quotient. -/
private theorem coe_dyadicFloor (n : ℕ) (t : NNReal) :
    ((dyadicFloor n t : NNReal) : ℝ) = (⌊(2 ^ n : ℝ) * (t : ℝ)⌋₊ : ℝ) / 2 ^ n := rfl

/-- The level-`n` dyadic ceiling is at least the time it approximates. -/
theorem le_dyadicCeiling (n : ℕ) (t : NNReal) : t ≤ dyadicCeiling n t := by
  rw [← NNReal.coe_le_coe, coe_dyadicCeiling, le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
  calc (t : ℝ) * 2 ^ n = (2 ^ n : ℝ) * (t : ℝ) := by ring
    _ ≤ (⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℝ) := Nat.le_ceil _

/-- The level-`n` dyadic floor is at most the time it approximates. -/
theorem dyadicFloor_le (n : ℕ) (t : NNReal) : dyadicFloor n t ≤ t := by
  rw [← NNReal.coe_le_coe, coe_dyadicFloor, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
  calc (⌊(2 ^ n : ℝ) * (t : ℝ)⌋₊ : ℝ) ≤ (2 ^ n : ℝ) * (t : ℝ) := Nat.floor_le (by positivity)
    _ = (t : ℝ) * 2 ^ n := by ring

/-- The level-`n` dyadic ceiling overshoots by at most one grid step. -/
theorem dyadicCeiling_le_add (n : ℕ) (t : NNReal) :
    dyadicCeiling n t ≤ t + (2 ^ n : NNReal)⁻¹ := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hinv : ((2 : ℝ) ^ n)⁻¹ * 2 ^ n = 1 := inv_mul_cancel₀ (ne_of_gt h2)
  rw [← NNReal.coe_le_coe, coe_dyadicCeiling, NNReal.coe_add, NNReal.coe_inv, NNReal.coe_pow,
    NNReal.coe_ofNat, div_le_iff₀ h2]
  calc (⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℝ) ≤ (2 ^ n : ℝ) * (t : ℝ) + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
    _ = ((t : ℝ) + ((2 : ℝ) ^ n)⁻¹) * 2 ^ n := by rw [add_mul, hinv]; ring

/-- The ceiling comparison rewritten as an inequality between natural indices. -/
private theorem dyadicCeiling_le_iff_nat (n : ℕ) (t i : NNReal) :
    dyadicCeiling n t ≤ i ↔ ⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ ≤ ⌊(2 ^ n : ℝ) * (i : ℝ)⌋₊ := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hfloor : ⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ ≤ ⌊(2 ^ n : ℝ) * (i : ℝ)⌋₊ ↔
      ((⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℕ) : ℝ) ≤ (2 ^ n : ℝ) * (i : ℝ) :=
    Nat.le_floor_iff (by positivity)
  rw [← NNReal.coe_le_coe, coe_dyadicCeiling, div_le_iff₀ h2, hfloor,
    mul_comm ((2 : ℝ) ^ n) (i : ℝ)]

/-- The floor comparison rewritten as the same inequality between natural indices. -/
private theorem le_dyadicFloor_iff_nat (n : ℕ) (t i : NNReal) :
    t ≤ dyadicFloor n i ↔ ⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ ≤ ⌊(2 ^ n : ℝ) * (i : ℝ)⌋₊ := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [← NNReal.coe_le_coe, coe_dyadicFloor, le_div_iff₀ h2, Nat.ceil_le,
    mul_comm ((2 : ℝ) ^ n) (t : ℝ)]

/-- The dyadic ceiling lies below a time exactly when the time's dyadic floor lies above. -/
theorem dyadicCeiling_le_iff (n : ℕ) (t i : NNReal) :
    dyadicCeiling n t ≤ i ↔ t ≤ dyadicFloor n i :=
  (dyadicCeiling_le_iff_nat n t i).trans (le_dyadicFloor_iff_nat n t i).symm



/-- The dyadic ceilings of a fixed time converge to that time. -/
theorem tendsto_dyadicCeiling (t : NNReal) :
    Tendsto (fun n ↦ dyadicCeiling n t) atTop (𝓝 t) := by
  have hhalf : ((2 : NNReal))⁻¹ < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_inv, NNReal.coe_ofNat, NNReal.coe_one]
    norm_num
  have hinv : Tendsto (fun n : ℕ ↦ (2 ^ n : NNReal)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hhalf
  have hupper : Tendsto (fun n : ℕ ↦ t + (2 ^ n : NNReal)⁻¹) atTop (𝓝 t) := by
    simpa only [add_zero] using tendsto_const_nhds.add hinv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n ↦ le_dyadicCeiling n t) (fun n ↦ dyadicCeiling_le_add n t)





/-- A dyadic ceiling is the grid point at its ceiling index. -/
theorem dyadicGrid_ceilingIndex (n : ℕ) (t : NNReal) :
    dyadicGrid n (dyadicCeilingIndex n t) = dyadicCeiling n t :=
  rfl



/-- The dyadic grid is strictly monotone in its index. -/
theorem strictMono_dyadicGrid (n : ℕ) : StrictMono (dyadicGrid n) := by
  intro k l hkl
  rw [← NNReal.coe_lt_coe]
  exact div_lt_div_of_pos_right (Nat.cast_lt.mpr hkl) (by positivity)



variable {Omega : Type*} {m : MeasurableSpace Omega}







/-- The dyadic ceiling of a finite stopping time is a stopping time for the same filtration. -/
theorem isStoppingTime_dyadicCeiling {f : Filtration NNReal m} {T : Omega → NNReal}
    (hT : IsStoppingTime f (fun omega ↦ (T omega : WithTop NNReal))) (n : ℕ) :
    IsStoppingTime f (fun omega ↦ (dyadicCeiling n (T omega) : WithTop NNReal)) := by
  intro i
  refine (f.mono (dyadicFloor_le n i) _ (hT (dyadicFloor n i))).congr ?_
  ext omega
  simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
  exact (dyadicCeiling_le_iff n (T omega) i).symm

end

end MarkovProcess


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

/-- The value of an adapted process at a stopping time with finite range is measurable. -/
theorem stronglyMeasurable_apply_of_finite_range (hadapted : StronglyAdapted ℱ M) {S : Omega → NNReal}
    (hS : IsStoppingTime ℱ fun omega ↦ ((S omega : NNReal) : WithTop NNReal))
    (hfin : (Set.range S).Finite) :
    StronglyMeasurable fun omega ↦ M (S omega) omega := by
  have hSV : ∀ omega, S omega ∈ hfin.toFinset := fun omega ↦
    hfin.mem_toFinset.mpr ⟨omega, rfl⟩
  have hsum : (fun omega ↦ M (S omega) omega) =
      fun omega ↦ ∑ v ∈ hfin.toFinset, Set.indicator {eta | S eta = v} (M v) omega := by
    funext omega
    exact apply_eq_sum_indicator hSV M omega
  rw [hsum]
  refine Finset.stronglyMeasurable_fun_sum _ fun v _ ↦ ?_
  exact ((hadapted v).mono (ℱ.le v)).indicator
    (ℱ.le v _ (measurableSet_eq_of_finite_range hS hfin v))



end FiniteRange

section DyadicApproximation

/-- Sampling an `NNReal` filtration on a dyadic grid gives a discrete filtration. -/
private def dyadicFiltration (n : ℕ) (ℱ : Filtration NNReal m) : Filtration ℕ m where
  seq k := ℱ (dyadicGrid n k)
  mono' _ _ hkl := ℱ.mono (monotone_dyadicGrid n hkl)
  le' k := ℱ.le (dyadicGrid n k)

/-- The dyadic ceiling index is a stopping time for the sampled filtration. -/
private theorem isStoppingTime_dyadicCeilingIndex {T : Omega → NNReal}
    (hT : IsStoppingTime ℱ fun omega ↦ ((T omega : NNReal) : WithTop NNReal)) (n : ℕ) :
    IsStoppingTime (dyadicFiltration n ℱ)
      (fun omega ↦ (dyadicCeilingIndex n (T omega) : ℕ∞)) := by
  intro k
  have hstop := isStoppingTime_dyadicCeiling hT n (dyadicGrid n k)
  change MeasurableSet[ℱ (dyadicGrid n k)]
    {omega | (dyadicCeilingIndex n (T omega) : ℕ∞) ≤ k}
  convert hstop using 1
  ext omega
  simp only [Set.mem_ofPred_eq, ENat.natCast_le_natCast]
  rw [← dyadicGrid_ceilingIndex]
  rw [WithTop.coe_le_coe]
  exact (strictMono_dyadicGrid n).le_iff_le.symm

/-- Sampling a supermartingale at dyadic grid points gives a discrete supermartingale. -/
private theorem dyadicSample_supermartingale (hM : Supermartingale M ℱ mu) (n : ℕ) :
    Supermartingale (fun k ↦ M (dyadicGrid n k)) (dyadicFiltration n ℱ) mu := by
  refine ⟨fun k ↦ hM.1 (dyadicGrid n k), ?_, fun k ↦ hM.2.2 (dyadicGrid n k)⟩
  intro k l hkl
  exact hM.2.1 _ _ (monotone_dyadicGrid n hkl)

/-- One dyadic grid step is at most one. -/
private theorem inv_two_pow_le_one (n : ℕ) : ((2 : NNReal) ^ n)⁻¹ ≤ 1 := by
  rw [← NNReal.coe_le_coe, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_one]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- The dyadic ceiling of a time bounded by `K` is bounded by `K + 1`. -/
private theorem dyadicCeiling_le_add_one (n : ℕ) {t K : NNReal} (ht : t ≤ K) :
    dyadicCeiling n t ≤ K + 1 :=
  (dyadicCeiling_le_add n t).trans (add_le_add ht (inv_two_pow_le_one n))

/-- At each dyadic level, the ceilings of times bounded by a fixed horizon form a finite set. -/
private theorem finite_range_dyadicCeiling (n : ℕ) {S : Omega → NNReal} {K : NNReal}
    (hSK : ∀ omega, S omega ≤ K) :
    (Set.range fun omega ↦ dyadicCeiling n (S omega)).Finite := by
  refine Set.Finite.subset ((Set.finite_Iic (⌈(2 ^ n : ℝ) * (K : ℝ)⌉₊)).image
    (dyadicGrid n)) ?_
  rintro _ ⟨omega, rfl⟩
  refine ⟨⌈(2 ^ n : ℝ) * (S omega : ℝ)⌉₊, Set.mem_Iic.mpr (Nat.ceil_le_ceil ?_), rfl⟩
  exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (hSK omega))
    (by positivity : (0 : ℝ) ≤ 2 ^ n)

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
theorem solution (hM : Supermartingale M ℱ mu)
    (hbound : ∀ v : NNReal, ∃ C : ℝ, ∀ t ≤ v, ∀ omega, ‖M t omega‖ ≤ C)
    (hright : ∀ (omega : Omega) (v : NNReal),
      ContinuousWithinAt (fun t : NNReal ↦ M t omega) (Set.Ici v) v)
    {T : Omega → NNReal}
    (hT : IsStoppingTime ℱ fun omega ↦ ((T omega : NNReal) : WithTop NNReal))
    {K : NNReal} (hTK : ∀ omega, T omega ≤ K) :
    ∫ omega, M (T omega) omega ∂mu ≤ ∫ omega, M 0 omega ∂mu := by
  have hstopfin : ∀ n : ℕ, (Set.range fun omega ↦ dyadicCeiling n (T omega)).Finite := fun n ↦
    finite_range_dyadicCeiling n hTK
  have hstep : ∀ n : ℕ,
      ∫ omega, M (dyadicCeiling n (T omega)) omega ∂mu ≤ ∫ omega, M 0 omega ∂mu := by
    intro n
    let G := dyadicFiltration n ℱ
    let X : ℕ → Omega → ℝ := fun k ↦ -M (dyadicGrid n k)
    let S : Omega → ℕ∞ := fun omega ↦ dyadicCeilingIndex n (T omega)
    have hsub : Submartingale X G mu := by
      change Submartingale (-(fun k ↦ M (dyadicGrid n k))) G mu
      exact (dyadicSample_supermartingale hM n).neg
    have hS : IsStoppingTime G S := isStoppingTime_dyadicCeilingIndex hT n
    have hSK : ∀ omega, S omega ≤
        (dyadicCeilingIndex n K : ℕ) := by
      intro omega
      change (dyadicCeilingIndex n (T omega) : ℕ∞) ≤
        (dyadicCeilingIndex n K : ℕ∞)
      exact WithTop.coe_le_coe.mpr (Nat.ceil_le_ceil (mul_le_mul_of_nonneg_left
        (NNReal.coe_le_coe.mpr (hTK omega)) (by positivity : (0 : ℝ) ≤ 2 ^ n)))
    have hoptional := hsub.expected_stoppedValue_mono
      (isStoppingTime_const G 0) hS (fun _ ↦ bot_le) hSK
    change (∫ omega, -M (dyadicGrid n 0) omega ∂mu) ≤
      ∫ omega, -M (dyadicGrid n (dyadicCeilingIndex n (T omega))) omega ∂mu at hoptional
    rw [show dyadicGrid n 0 = 0 by
      apply NNReal.eq
      simp only [dyadicGrid, Nat.cast_zero, zero_div, NNReal.coe_zero]
      rfl] at hoptional
    have hgrid :
        (∫ omega, M (dyadicGrid n (dyadicCeilingIndex n (T omega))) omega ∂mu) ≤
          ∫ omega, M 0 omega ∂mu := by
      simpa only [integral_neg, neg_le_neg_iff] using hoptional
    calc
      ∫ omega, M (dyadicCeiling n (T omega)) omega ∂mu =
          ∫ omega, M (dyadicGrid n (dyadicCeilingIndex n (T omega))) omega ∂mu := by
        refine integral_congr_ae (Eventually.of_forall fun omega ↦ ?_)
        change M (dyadicCeiling n (T omega)) omega =
          M (dyadicGrid n (dyadicCeilingIndex n (T omega))) omega
        rw [dyadicGrid_ceilingIndex]
      _ ≤ ∫ omega, M 0 omega ∂mu := hgrid
  obtain ⟨C, hC⟩ := hbound (K + 1)
  have hptw : ∀ᵐ omega ∂mu, Tendsto (fun n ↦ M (dyadicCeiling n (T omega)) omega) atTop
      (𝓝 (M (T omega) omega)) := by
    refine Eventually.of_forall fun omega ↦ ?_
    have hnbhd : Tendsto (fun n ↦ dyadicCeiling n (T omega)) atTop (𝓝[≥] (T omega)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (tendsto_dyadicCeiling (T omega))
        (Eventually.of_forall fun n ↦ Set.mem_Ici.mpr (le_dyadicCeiling n (T omega)))
    exact Tendsto.comp (hright omega (T omega)) hnbhd
  have hlim := tendsto_integral_of_dominated_convergence (μ := mu) (fun _ ↦ C)
    (F := fun n omega ↦ M (dyadicCeiling n (T omega)) omega)
    (f := fun omega ↦ M (T omega) omega)
    (fun n ↦ (stronglyMeasurable_apply_of_finite_range hM.1
      (isStoppingTime_dyadicCeiling hT n) (hstopfin n)).aestronglyMeasurable)
    (integrable_const C)
    (fun n ↦ Eventually.of_forall fun omega ↦
      hC _ (dyadicCeiling_le_add_one n (hTK omega)) omega)
    hptw
  exact le_of_tendsto hlim (Eventually.of_forall hstep)
