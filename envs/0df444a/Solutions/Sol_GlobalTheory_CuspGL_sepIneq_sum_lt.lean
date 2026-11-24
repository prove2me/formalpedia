-- Prove2me | solution 1 for GlobalTheory.CuspGL.sepIneq_sum_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:05:32.623168+00:00
-- url     : https://prove2.me/submissions/dd1dcd39-de23-44e2-a9f7-6dd06f9f62ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SeparationNumericalIneqCuspidalGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution (q n : ℕ) (hq : 2 ≤ q) :
    ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) < q ^ (n / 2 + 1) := by
  have hinj : Set.InjOn (fun p => n / p) (n.primeFactors : Set ℕ) := by
    intro a ha b hb hab
    have ha' := Nat.mem_primeFactors.1 (Finset.mem_coe.1 ha)
    have hb' := Nat.mem_primeFactors.1 (Finset.mem_coe.1 hb)
    have h1 := Nat.div_div_self ha'.2.1 ha'.2.2
    have h2 := Nat.div_div_self hb'.2.1 hb'.2.2
    simp only at hab
    rw [← h1, ← h2, hab]
  calc ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) ≤ ∑ p ∈ n.primeFactors, q ^ (n / p) :=
        Finset.sum_le_sum fun p _ => Nat.sub_le _ _
    _ = ∑ k ∈ n.primeFactors.image (fun p => n / p), q ^ k :=
        (Finset.sum_image (f := fun k => q ^ k) hinj).symm
    _ < q ^ (n / 2 + 1) := by
        apply Nat.geomSum_lt hq
        intro k hk
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hk
        have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
        exact Nat.lt_succ_of_le (Nat.div_le_div_left hp2 (by norm_num))
end GlobalTheory.CuspGL
