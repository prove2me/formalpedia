-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_levy_nat_grid_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:00:58.150331+00:00
-- url     : https://prove2.me/submissions/b8ec78dd-8baa-4897-850f-c8c401db6229

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (u : ℕ → NNReal) (hu : Monotone u) :
    iIndepFun (fun k : ℕ => fun w => X (u (k+1)) w-X (u k) w) P := by
  classical
  rw [iIndepFun_iff_finset]
  intro S
  let N : ℕ := S.sup id + 1
  let j : S → Fin N := fun k => ⟨k.1,Nat.lt_succ_of_le (Finset.le_sup (f := id) k.2)⟩
  have hj : Function.Injective j := by
    intro a b h
    exact Subtype.ext (congrArg Fin.val h)
  have hi := hX.indep_increments N (fun k : Fin (N+1) => u k.val) (fun _ _ h => hu h)
  have H := hi.precomp hj
  exact H
