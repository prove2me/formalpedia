-- Prove2me | solution 1 for Kyprianou.Ch04.bvTruncatedPathCompactBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-25T06:46:45.408146+00:00
-- url     : https://prove2.me/submissions/6f4aef42-87da-4938-9d6f-3afbf6f1d415

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
open Kyprianou.Ch04

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hRep : forall t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (hLeft : ∀ u : NNReal, 0 < u →
      Tendsto (fun v : NNReal => X v omega) (nhdsWithin u (Set.Iio u))
        (nhds (Xleft u omega)))
    (t : NNReal) :
    let j : Set.Ioc (0 : NNReal) t → ℝ := fun s => X s omega - Xleft s omega
    let P : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
    let Q : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) < u then j s else 0
    let M := |X 0 omega| + |c| * (t : ℝ) + ∑' s, |j s|
    0 ≤ M ∧
      (∀ S u, u ≤ t → |P S u| ≤ M ∧ |Q S u| ≤ M) ∧
      (∀ u, u ≤ t → |X u omega| ≤ M) ∧
      (∀ u, 0 < u → u ≤ t → |Xleft u omega| ≤ M) := by
  intro j P Q M
  set g : NNReal → ℝ := fun s => X s omega - Xleft s omega with hg
  have hsum : Summable (fun s : Set.Ioc (0 : NNReal) t => |j s|) := (hRep t).1
  have hT0 : 0 ≤ ∑' s, |j s| := tsum_nonneg (fun _ => abs_nonneg _)
  have hct : ∀ u : NNReal, u ≤ t → |c * (u : ℝ)| ≤ |c| * (t : ℝ) := by
    intro u hu
    rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg u)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hu) (abs_nonneg c)
  have hfin : ∀ (S : Finset (Set.Ioc (0 : NNReal) t)) (p : Set.Ioc (0 : NNReal) t → Prop)
      [DecidablePred p], |∑ s ∈ S, if p s then j s else 0| ≤ ∑' s, |j s| := by
    intro S p _
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum (g := fun s => |j s|) (fun s _ => ?_))
      (hsum.sum_le_tsum S (fun _ _ => abs_nonneg _))
    split_ifs <;> simp
  have hbound : ∀ u : NNReal, u ≤ t → ∀ r : ℝ, |r| ≤ ∑' s, |j s| →
      |X 0 omega + c * (u : ℝ) + r| ≤ M := by
    intro u hu r hr
    calc |X 0 omega + c * (u : ℝ) + r| ≤ |X 0 omega| + |c * (u : ℝ)| + |r| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ M := by
          have := hct u hu
          show _ ≤ |X 0 omega| + |c| * (t : ℝ) + ∑' s, |j s|
          linarith
  have hM0 : 0 ≤ M := by
    show 0 ≤ |X 0 omega| + |c| * (t : ℝ) + ∑' s, |j s|
    have := abs_nonneg (X 0 omega)
    have : 0 ≤ |c| * (t : ℝ) := mul_nonneg (abs_nonneg c) (NNReal.coe_nonneg t)
    linarith
  -- comparison of jump sums over sub-intervals
  have hsub : ∀ u : NNReal, u ≤ t →
      |∑' s : Set.Ioc (0 : NNReal) u, g s| ≤ ∑' s, |j s| := by
    intro u hu
    have hsu : Summable (fun s : Set.Ioc (0 : NNReal) u => |g s|) := (hRep u).1
    have hn : |∑' s : Set.Ioc (0 : NNReal) u, g s| ≤ ∑' s : Set.Ioc (0 : NNReal) u, |g s| := by
      have := norm_tsum_le_tsum_norm (f := fun s : Set.Ioc (0 : NNReal) u => g s)
        (by simpa only [Real.norm_eq_abs] using hsu)
      simpa only [Real.norm_eq_abs] using this
    refine hn.trans ?_
    have e1 : ∑' s : Set.Ioc (0 : NNReal) u, |g s| =
        ∑' s, (Set.Ioc (0 : NNReal) u).indicator (fun s => |g s|) s :=
      tsum_subtype (Set.Ioc (0 : NNReal) u) (fun s => |g s|)
    have e2 : ∑' s, |j s| =
        ∑' s, (Set.Ioc (0 : NNReal) t).indicator (fun s => |g s|) s :=
      tsum_subtype (Set.Ioc (0 : NNReal) t) (fun s => |g s|)
    rw [e1, e2]
    have hst : Summable ((Set.Ioc (0 : NNReal) t).indicator (fun s => |g s|)) :=
      (summable_subtype_iff_indicator).mp hsum
    have hle : ∀ s, (Set.Ioc (0 : NNReal) u).indicator (fun s => |g s|) s ≤
        (Set.Ioc (0 : NNReal) t).indicator (fun s => |g s|) s :=
      fun s => Set.indicator_le_indicator_of_subset (Set.Ioc_subset_Ioc_right hu)
        (fun _ => abs_nonneg _) s
    have hsu' : Summable ((Set.Ioc (0 : NNReal) u).indicator (fun s => |g s|)) :=
      (summable_subtype_iff_indicator).mp hsu
    exact hsu'.tsum_le_tsum hle hst
  have hXb : ∀ u, u ≤ t → |X u omega| ≤ M := by
    intro u hu
    rw [(hRep u).2]
    exact hbound u hu _ (hsub u hu)
  refine ⟨hM0, fun S u hu => ⟨hbound u hu _ (hfin S _), hbound u hu _ (hfin S _)⟩, hXb, ?_⟩
  intro u hu0 hut
  have h1 : Tendsto (fun v : NNReal => |X v omega|) (nhdsWithin u (Set.Iio u))
      (nhds |Xleft u omega|) := (hLeft u hu0).abs
  have : (nhdsWithin u (Set.Iio u)).NeBot := nhdsWithin_Iio_self_neBot' ⟨0, hu0⟩
  exact le_of_tendsto h1 (eventually_nhdsWithin_of_forall
    fun v hv => hXb v (le_trans (le_of_lt hv) hut))
