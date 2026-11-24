-- Prove2me | solution 1 for GlobalTheory.perfection_frobenius_solve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:42:17.990486+00:00
-- url     : https://prove2.me/submissions/6a69b436-d7ed-4b34-99d1-9b0fd7b4fb39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PerfectionExistsUniqueSubMatrixFrobeniusEq
import Theorems.Thm_GlobalTheory_sub_apply_bijective_of_iterate_eq_zero
import Theorems.Thm_GlobalTheory_perfLevelOp_coeff
import Theorems.Thm_GlobalTheory_perfLevelOp_frobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] (Q : Matrix ι ι (Perfection S p)), (∀ n : ℕ, ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k))^[K] z = 0) → ∀ c : ι → Perfection S p, ∃! x : ι → Perfection S p, x - Q.mulVec (fun k => frobenius (Perfection S p) p (x k)) = c := by
  intro p _ S _ _ ι _ Q hnil c
  have bij : ∀ n, Function.Bijective (fun z => z - perfLevelOp p S Q n z) := by
    intro n
    obtain ⟨K, hK⟩ := hnil n
    exact sub_apply_bijective_of_iterate_eq_zero _ K hK
  let z : ℕ → ι → S := fun n => Function.surjInv (bij n).2 (fun i => Perfection.coeff S p n (c i))
  have hz : ∀ n, z n - perfLevelOp p S Q n (z n) = fun i => Perfection.coeff S p n (c i) :=
    fun n => Function.surjInv_eq (bij n).2 _
  have compat : ∀ n k, z (n + 1) k ^ p = z n k := by
    intro n
    have h : (fun k => frobenius S p (z (n + 1) k)) = z n := by
      apply (bij n).1
      show (fun k => frobenius S p (z (n + 1) k))
          - perfLevelOp p S Q n (fun k => frobenius S p (z (n + 1) k)) = z n - perfLevelOp p S Q n (z n)
      rw [← perfLevelOp_frobenius, hz (n + 1), hz n]
      ext i
      simp [frobenius_def, Perfection.coeff_pow_p']
    intro k
    have := congrFun h k
    simpa [frobenius_def] using this
  let x : ι → Perfection S p := fun k => ⟨fun n => z n k, fun n => compat n k⟩
  refine ⟨x, ?_, ?_⟩
  · funext i
    apply Perfection.ext
    intro n
    have h1 := congrFun (perfLevelOp_coeff p S Q n x) i
    have hx : (fun i => Perfection.coeff S p n (x i)) = z n := rfl
    rw [hx, hz n] at h1
    exact h1
  · intro y hy
    funext k
    apply Perfection.ext
    intro n
    have h2 : (fun i => Perfection.coeff S p n (y i)) = z n := by
      apply (bij n).1
      show (fun i => Perfection.coeff S p n (y i))
          - perfLevelOp p S Q n (fun i => Perfection.coeff S p n (y i)) = z n - perfLevelOp p S Q n (z n)
      rw [← perfLevelOp_coeff, hy, hz n]
    exact congrFun h2 k
end GlobalTheory
