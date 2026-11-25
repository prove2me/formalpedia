-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42FixedLipschitzGridLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T17:14:26.325584+00:00
-- url     : https://prove2.me/submissions/ce847fd9-bb23-4600-8cf2-3b753a7f02db

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42GridCoefficientBoundV1
import Theorems.Thm_Kyprianou_Ch04_exercise42GridCoefficientAELimitV1
import Theorems.Thm_Kyprianou_Ch04_exercise42GridCellIntegralV1
import Theorems.Thm_Kyprianou_Ch04_exercise42GridDCTIntegralV1
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open ProbabilityTheory Set Topology
open scoped Topology
open Kyprianou.Ch04

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hd : 0 < c) (hzero : X 0 omega = 0)
    (hCadlag : IsCadlag (fun t : NNReal => X t omega))
    (hLeft : ∀ t : NNReal, 0 < t →
      Tendsto (fun s : NNReal => X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (hNeg : ∀ t : NNReal, 0 < t → X t omega ≤ Xleft t omega)
    (hRep : ∀ t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (U : NNReal → Real) (K : NNReal) (hU : LipschitzWith K U)
    (hU0 : 0 ≤ U 0) (hUp : ∀ s : NNReal, 0 < s → 0 < U s)
    (f : Real × Real → Real)
    (hf : ContDiffOn Real 1 f (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (t : NNReal) :
    Tendsto (fun n : Nat => ∑ k ∈ Finset.range n,
        let u : NNReal := t * (k : NNReal) / (n : NNReal)
        let v : NNReal := t * ((k + 1 : Nat) : NNReal) / (n : NNReal)
        fderiv Real f (U u, X u omega) (1, 0) * (U v - U u))
      atTop (nhds (∫ s in Set.Icc (0 : Real) (t : Real),
        fderiv Real f (U s.toNNReal, X s.toNNReal omega) (1, 0) *
          deriv (fun z : Real => U z.toNNReal) s ∂volume)) := by
  by_cases ht : t = 0
  · subst t
    simp
  have htP : 0 < t := pos_iff_ne_zero.mpr ht
  obtain ⟨C, hC, hb⟩ := exercise42GridCoefficientBoundV1 X Xleft omega c hd hzero hCadlag hLeft hNeg hRep U K hU hU0 hUp f hf t
  let g : NNReal → ℝ := fun s => fderiv ℝ f (U s, X s omega) (1, 0)
  have hp := exercise42GridCoefficientAELimitV1 X Xleft omega c hd hzero hCadlag hLeft hNeg hRep U K hU hU0 hUp f hf t htP
  have hlim := exercise42GridDCTIntegralV1 t htP U g K hU C hC hb hp
  have he := exercise42GridCellIntegralV1 t htP U g K hU C hC hb
  apply (tendsto_add_atTop_iff_nat 2).1
  apply hlim.congr'
  filter_upwards with n
  exact he n
