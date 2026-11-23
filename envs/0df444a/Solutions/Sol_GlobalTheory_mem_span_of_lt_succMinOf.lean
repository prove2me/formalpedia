-- Prove2me | solution 1 for GlobalTheory.mem_span_of_lt_succMinOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:33.050643+00:00
-- url     : https://prove2.me/submissions/6a26567e-1320-43f1-bf1c-6cd1ad09d64a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Theorems.Thm_GlobalTheory_succMinOf_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open GlobalTheory
variable {K : Type*} [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {N : V → ℝ} {S : Set V} {n : ℕ}
namespace GlobalTheory
theorem _root_.solution {v : Fin n → V} (hv : LinearIndependent K v) (hS : ∀ j, v j ∈ S)
    (hN : ∀ j : Fin n, N (v j) ≤ succMinOf K N S (j + 1)) {i : ℕ} (hi : i ≤ n) {x : V}
    (hx : x ∈ S) (hx0 : 0 ≤ N x) (h : N x < succMinOf K N S (i + 1)) :
    x ∈ span K (v '' {j | (j : ℕ) < i}) := by
  have hrank : (n : Cardinal) ≤ Module.rank K (span K S) :=
    natCast_le_rank_span_iff.2 ⟨v, hv, hS⟩
  have key : ∀ i ≤ n, succMinOf K N S i ≤ N x → N x < succMinOf K N S (i + 1) →
      x ∈ span K (v '' {j | (j : ℕ) < i}) := by
    intro i hi h1 h2
    by_contra hx'
    have hw : LinearIndependent K (fun j : Fin i => v (Fin.castLE hi j)) :=
      hv.comp _ (Fin.castLE_injective hi)
    have hr : Set.range (fun j : Fin i => v (Fin.castLE hi j)) = v '' {j | (j : ℕ) < i} := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩; exact ⟨_, j.2, rfl⟩
      · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩
    have hli : LinearIndependent K
        (Fin.cons x (fun j : Fin i => v (Fin.castLE hi j)) : Fin (i + 1) → V) :=
      linearIndependent_finCons.2 ⟨hw, by rwa [hr]⟩
    refine absurd (succMinOf_le_of_linearIndependent (N := N) (S := S) (i := i + 1) hli (by simp)
      hx0 ?_ ?_) (not_le.2 h2)
    · intro k
      refine Fin.cases hx (fun j => hS _) k
    · intro k
      refine Fin.cases le_rfl (fun j => ?_) k
      exact (hN _).trans ((succMinOf_mono (show (j : ℕ) + 1 ≤ i from j.2)
        ((Nat.cast_le.2 hi).trans hrank)).trans h1)
  induction i with
  | zero => exact key 0 hi (succMinOf_zero.le.trans hx0) h
  | succ m ih =>
    rcases lt_or_ge (N x) (succMinOf K N S (m + 1)) with h1 | h1
    · have hsub : {j : Fin n | (j : ℕ) < m} ⊆ {j : Fin n | (j : ℕ) < m + 1} :=
        fun j hj => Nat.lt_succ_of_lt hj
      exact span_mono (Set.image_mono hsub) (ih (Nat.le_of_succ_le hi) h1)
    · exact key (m + 1) hi h1 h
end GlobalTheory
