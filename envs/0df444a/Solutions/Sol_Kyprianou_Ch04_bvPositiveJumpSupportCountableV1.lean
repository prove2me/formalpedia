-- Prove2me | solution 1 for Kyprianou.Ch04.bvPositiveJumpSupportCountableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:53:10.244898+00:00
-- url     : https://prove2.me/submissions/703e0d28-5e33-4ac0-a3d6-d51cef6556ef

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega)
    (hSum : ∀ t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|)) :
    ({s : NNReal | 0 < s ∧ X s omega ≠ Xleft s omega}).Countable := by
  classical
  let J : Set NNReal := {s | 0 < s ∧ X s omega ≠ Xleft s omega}
  let K (n : ℕ) : Set NNReal :=
    Subtype.val '' Function.support
      (fun s : Set.Ioc (0 : NNReal) (n : NNReal) => |X s omega - Xleft s omega|)
  have hK (n : ℕ) : (K n).Countable :=
    ((hSum (n : NNReal)).countable_support).image Subtype.val
  change J.Countable
  apply (Set.countable_iUnion hK).mono
  intro s hs
  obtain ⟨n, hn⟩ := exists_nat_ge s
  refine Set.mem_iUnion.mpr ⟨n, ⟨⟨s, ⟨hs.1, hn⟩⟩, ?_, rfl⟩⟩
  simpa [Function.mem_support, abs_ne_zero, sub_ne_zero] using hs.2
