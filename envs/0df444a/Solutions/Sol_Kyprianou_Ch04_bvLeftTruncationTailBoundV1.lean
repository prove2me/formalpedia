-- Prove2me | solution 1 for Kyprianou.Ch04.bvLeftTruncationTailBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:29:56.929692+00:00
-- url     : https://prove2.me/submissions/9d165656-6af0-4726-9d55-f6d0fac0f927

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvRightTruncationTailBoundV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteTruncationLeftLimitV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter
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
    let Q : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) < u then j s else 0
    ∀ (S : Finset (Set.Ioc (0 : NNReal) t)) (u : NNReal), 0 < u → u ≤ t →
      |Xleft u omega - Q S u| ≤ (∑' s, |j s|) - ∑ s ∈ S, |j s| := by
  classical
  intro j Q S u hu ht
  let P : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
    fun S v => X 0 omega + c * (v : ℝ) + ∑ s ∈ S, if (s : NNReal) ≤ v then j s else 0
  have hP : Tendsto (P S) (nhdsWithin u (Set.Iio u)) (nhds (Q S u)) :=
    Kyprianou.Ch04.bvFiniteTruncationLeftLimitV1
      (fun s : Set.Ioc (0 : NNReal) t => (s : NNReal)) j (X 0 omega) c S u hu
  haveI : (nhdsWithin u (Set.Iio u)).NeBot :=
    nhdsWithin_Iio_neBot' ⟨0, hu⟩ le_rfl
  apply le_of_tendsto ((hLeft u hu).sub hP).abs
  filter_upwards [self_mem_nhdsWithin (s := Set.Iio u) (a := u)] with v hv
  exact Kyprianou.Ch04.bvRightTruncationTailBoundV1
    X Xleft omega c hRep t S v (hv.le.trans ht)
