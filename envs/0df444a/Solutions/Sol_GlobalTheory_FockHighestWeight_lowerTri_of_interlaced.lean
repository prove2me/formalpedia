-- Prove2me | solution 1 for GlobalTheory.FockHighestWeight.lowerTri_of_interlaced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:09:36.578415+00:00
-- url     : https://prove2.me/submissions/e7e36888-09df-44b5-bf3c-866c61e44c27

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriOfInterlaced
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.FockHighestWeight
variable {r n : ℕ}
namespace GlobalTheory.FockHighestWeight
theorem _root_.solution {m : Fin r × Fin n →₀ ℕ} (hm : Interlaced m) : LowerTri m := by
  have key : ∀ k : ℕ, ∀ (s : Fin n), s.val = k → ∀ a : Fin r, a.val < s.val → m (a, s) = 0 := by
    intro k
    induction k with
    | zero => intro s hs a ha; omega
    | succ k ih =>
      intro s hs a ha
      have hk : k < n := by have := s.2; omega
      have h := hm ⟨k, hk⟩ s hs a
      have h0 : ∑ b : Fin r with b < a, m (b, (⟨k, hk⟩ : Fin n)) = 0 := by
        refine Finset.sum_eq_zero fun b hb => ?_
        have hb' : b.val < a.val := (Finset.mem_filter.mp hb).2
        exact ih ⟨k, hk⟩ rfl b (by simp only; omega)
      rw [h0] at h
      have h1 : m (a, s) ≤ ∑ b : Fin r with b ≤ a, m (b, s) :=
        Finset.single_le_sum (f := fun b => m (b, s)) (fun _ _ => Nat.zero_le _) (by simp)
      omega
  intro a s h
  exact key s.val s rfl a h
end GlobalTheory.FockHighestWeight
