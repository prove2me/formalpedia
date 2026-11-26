-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_sup_aemeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:40:46.661142+00:00
-- url     : https://prove2.me/submissions/de12806f-6333-4fbc-a1ff-a894090cc18b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_sections
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_right_continuous_bounded
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P,
      forall t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => X s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (Xleft t omega)))
    (f : Real × Real -> Real)
    (hfJointC1 : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (hfSpaceC2 : forall s : NNReal,
      ContDiff Real 2 (fun x : Real => f ((s : Real), x)))
    (hfSpaceSecondContinuous :
      ContinuousOn
        (fun z : Real × Real =>
          iteratedDeriv 2 (fun x : Real => f (z.1, x)) z.2)
        (Set.prod (Set.Ici (0 : Real)) Set.univ)) :
    ∀ (T : NNReal) (m : ℕ),
    let E : ℕ → NNReal → Omega → ℝ := fun n t omega =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m : ℝ) + 1) - 1))
      (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
       (f (z.1,Xleft (Real.toNNReal z.1) omega + z.2) -
        f (z.1,Xleft (Real.toNNReal z.1) omega) -
        z.2 * fderiv ℝ f (z.1,Xleft (Real.toNNReal z.1) omega) (0,1) -
        iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2)
          * chi z.2 ∂(pathJumpMeasure X Xleft omega)) - (∑ k ∈ Finset.range n,
       let dx := X (v (k+1)) omega - X (v k) omega
       (f ((v k : ℝ),X (v (k+1)) omega) - f ((v k : ℝ),X (v k) omega) -
        deriv (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx -
        iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx^2 / 2)
          * chi dx)
    let B : ℕ → Omega → ℝ := fun n w =>
      sSup (Set.range (fun t : Set.Iic T => |E n t w|))
    ∀ n, AEStronglyMeasurable (B n) P := by
  intro T m E B n
  classical
  have hm := Kyprianou.Ch04.ito43_cutoff_sections P X hLevy Xleft hLeft
    f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous T m
  have hr := Kyprianou.Ch04.ito43_cutoff_right_continuous_bounded P X hLevy Xleft
    hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous T m
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (α := NNReal)
  let S := insert (0 : NNReal) (range u)
  have hS : Dense S := hu.mono (subset_insert _ _)
  have hc : S.Countable := (countable_range u).insert _
  haveI : Countable {s : NNReal // s ∈ S ∧ s ≤ T} :=
    (hc.mono (fun _ h => h.1)).to_subtype
  let D : Omega → ℝ := fun w =>
    max (⨆ s : {s : NNReal // s ∈ S ∧ s ≤ T}, |E n s.1 w|) (|E n T w|)
  have hD : AEMeasurable D P :=
    (AEMeasurable.iSup (fun s : {s : NNReal // s ∈ S ∧ s ≤ T} =>
      (hm n s.1).abs)).max (hm n T).abs
  apply hD.aestronglyMeasurable.congr
  filter_upwards [hr] with w hw
  have heq : B n w = (⨆ s : Icc (0 : NNReal) T, |E n s.1 w|) := by
    change sSup _ = sSup _
    congr 1
    ext z
    simp only [mem_range, Subtype.exists, mem_Icc, mem_Iic, zero_le, true_and]
  have hb : BddAbove (range (fun s : Icc (0 : NNReal) T => |E n s.1 w|)) :=
    (hw n).2.mono (by rintro _ ⟨s,rfl⟩; exact ⟨⟨s.1,s.2.2⟩,rfl⟩)
  symm
  rw [heq, AvramDividend.Classical.dense_timeSup_with_endpoint
    (fun t => |E n t w|) (hw n).1 S hS (mem_insert _ _) T hb]
