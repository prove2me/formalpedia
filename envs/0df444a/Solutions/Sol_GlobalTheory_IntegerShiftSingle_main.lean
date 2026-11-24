-- Prove2me | solution 1 for GlobalTheory.IntegerShiftSingle.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:07:20.01454+00:00
-- url     : https://prove2.me/submissions/112c2847-4d34-44ae-8ec5-b790045a94ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ShiftSingleInt
import Theorems.Thm_GlobalTheory_IntegerShiftSingle_shift_single_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegerShiftSingle
universe u_1 u_2 u_3
namespace GlobalTheory.IntegerShiftSingle
theorem _root_.solution {ι : Type u_1} {R : Type u_2} {E : Type u_3} [Fintype ι] [inst : DecidableEq ι] [inst_1 : Ring R]
    {F : (ι → R) → E} : (∀ (i : ι) (x : ι → R), F (x + Pi.single i (1 : R)) = F x) →
    ∀ (n : ι → ℤ) (x : ι → R), F (x + fun (i : ι) ↦ (↑(n i) : R)) = F x := by
  intro h n x
  have key : ∀ s : Finset ι, ∀ y : ι → R, F (y + ∑ i ∈ s, Pi.single i ((n i : ℤ) : R)) = F y := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      intro y
      rw [Finset.sum_insert ha, ← add_assoc, ih, shift_single_int h]
  have hsum : (fun i : ι => ((n i : ℤ) : R)) = ∑ i ∈ Finset.univ, Pi.single i ((n i : ℤ) : R) := by
    rw [Finset.univ_sum_single]
  rw [hsum]
  exact key Finset.univ x
end GlobalTheory.IntegerShiftSingle
