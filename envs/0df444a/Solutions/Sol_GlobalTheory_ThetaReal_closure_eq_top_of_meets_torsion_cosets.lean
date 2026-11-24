-- Prove2me | solution 1 for GlobalTheory.ThetaReal.closure_eq_top_of_meets_torsion_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:43:35.513236+00:00
-- url     : https://prove2.me/submissions/264f24be-0b04-4f98-9780-437f449ce504

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ClosureZmodPowEqTopOfMeetsTorsionCosets
import Theorems.Thm_GlobalTheory_ThetaReal_zmod_pow_exists_nsmul_of_nsmul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ThetaReal
namespace GlobalTheory.ThetaReal
theorem _root_.solution :
    ∀ (κ : Type) (n J M : ℕ), 1 ≤ n → 2 ≤ J → M = n ^ J → ∀ X : Set (κ → ZMod M),
      (∀ a : κ → ZMod M, ∃ y : κ → ZMod M, n • y = 0 ∧ a + y ∈ X) →
      AddSubgroup.closure X = ⊤ := by
  intro κ n J M hn hJ hM X hX
  subst hM
  have step : ∀ a : κ → ZMod (n ^ J), ∃ w : κ → ZMod (n ^ J),
      a + n • w ∈ AddSubgroup.closure X := by
    intro a
    obtain ⟨y, hy, hay⟩ := hX a
    have : ∀ i, ∃ w : ZMod (n ^ J), y i = n • w := fun i =>
      zmod_pow_exists_nsmul_of_nsmul_eq_zero n J hn hJ (y i) (congrFun hy i)
    choose w hw using this
    refine ⟨w, ?_⟩
    have : n • w = y := funext fun i => (hw i).symm
    rw [this]
    exact AddSubgroup.subset_closure hay
  have ind : ∀ (i : ℕ) (a : κ → ZMod (n ^ J)), ∃ w : κ → ZMod (n ^ J),
      a + n ^ i • w ∈ AddSubgroup.closure X := by
    intro i
    induction i with
    | zero => intro a; exact ⟨-a, by simp⟩
    | succ i ih =>
      intro a
      obtain ⟨w, hw⟩ := ih a
      obtain ⟨v, hv⟩ := step (-w)
      refine ⟨v, ?_⟩
      have h := (AddSubgroup.closure X).add_mem hw ((AddSubgroup.closure X).nsmul_mem hv (n ^ i))
      have e : a + n ^ i • w + n ^ i • (-w + n • v) = a + n ^ (i + 1) • v := by
        rw [smul_add, smul_neg, smul_smul, pow_succ]; abel
      rwa [e] at h
  rw [eq_top_iff]
  intro a _
  obtain ⟨w, hw⟩ := ind J a
  have : n ^ J • w = 0 := by
    funext i
    show n ^ J • w i = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rwa [this, add_zero] at hw
end GlobalTheory.ThetaReal
