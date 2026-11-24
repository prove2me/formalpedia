-- Prove2me | solution 1 for GlobalTheory.UnipotentBorder.udl_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:01:45.430626+00:00
-- url     : https://prove2.me/submissions/abc2903c-c213-4aec-8128-22a261fe824d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Theorems.Thm_GlobalTheory_UnipotentBorder_last_row
import Theorems.Thm_GlobalTheory_UnipotentBorder_last_col
import Theorems.Thm_GlobalTheory_UnipotentBorder_top_block
import Theorems.Thm_GlobalTheory_UnipotentBorder_IsUU_top
import Theorems.Thm_GlobalTheory_UnipotentBorder_IsLU_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentBorder
open Matrix
variable {O : Type} [CommRing O]
namespace GlobalTheory.UnipotentBorder
theorem _root_.solution : ∀ (n : ℕ) (U U' L L' : Matrix (Fin n) (Fin n) O) (D D' : Fin n → Oˣ),
    IsUU U → IsUU U' → IsLU L → IsLU L' →
    U * diagonal (fun i => (D i : O)) * L = U' * diagonal (fun i => (D' i : O)) * L' →
    U = U' ∧ D = D' ∧ L = L' := by
  intro n
  induction n with
  | zero =>
    intro U U' L L' D D' _ _ _ _ _
    exact ⟨Matrix.ext fun i _ ↦ i.elim0, funext fun i ↦ i.elim0, Matrix.ext fun i _ ↦ i.elim0⟩
  | succ n ih =>
    intro U U' L L' D D' hU hU' hL hL' h

    have hrow : ∀ j, (D (Fin.last n) : O) * L (Fin.last n) j = (D' (Fin.last n) : O) * L' (Fin.last n) j :=
      fun j ↦ (last_row hU D (L := L) j).symm.trans
        ((congrFun (congrFun h _) j).trans (last_row hU' D' (L := L') j))
    have hcol : ∀ i, U i (Fin.last n) * (D (Fin.last n) : O) = U' i (Fin.last n) * (D' (Fin.last n) : O) :=
      fun i ↦ (last_col hL D (U := U) i).symm.trans
        ((congrFun (congrFun h i) _).trans (last_col hL' D' (U := U') i))
    have hDl : D (Fin.last n) = D' (Fin.last n) := by
      have e := hrow (Fin.last n)
      rw [(hL _ _).2 rfl, (hL' _ _).2 rfl, mul_one, mul_one] at e
      exact Units.ext e
    have hLl : ∀ j, L (Fin.last n) j = L' (Fin.last n) j := fun j ↦ by
      have e := hrow j
      rw [hDl] at e
      exact (Units.mul_right_inj (D' (Fin.last n))).1 e
    have hUl : ∀ i, U i (Fin.last n) = U' i (Fin.last n) := fun i ↦ by
      have e := hcol i
      rw [hDl] at e
      exact (Units.mul_left_inj (D' (Fin.last n))).1 e

    have htop : U.submatrix Fin.castSucc Fin.castSucc * diagonal (fun k : Fin n ↦ ((D ∘ Fin.castSucc) k : O)) *
        L.submatrix Fin.castSucc Fin.castSucc =
        U'.submatrix Fin.castSucc Fin.castSucc * diagonal (fun k : Fin n ↦ ((D' ∘ Fin.castSucc) k : O)) *
        L'.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      have e1 := top_block U L D i j
      have e2 := top_block U' L' D' i j
      rw [h, e2, hUl, hDl, hLl] at e1
      exact (add_right_cancel e1).symm
    obtain ⟨hU0, hD0, hL0⟩ := ih _ _ _ _ (D ∘ Fin.castSucc) (D' ∘ Fin.castSucc)
      hU.top hU'.top hL.top hL'.top htop
    refine ⟨?_, ?_, ?_⟩
    · ext i j
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · exact congrFun (congrFun hU0 i) j
        · exact hUl _
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · rw [(hU _ _).1 (Fin.castSucc_lt_last j), (hU' _ _).1 (Fin.castSucc_lt_last j)]
        · rw [(hU _ _).2 rfl, (hU' _ _).2 rfl]
    · funext k
      rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
      · exact congrFun hD0 k
      · exact hDl
    · ext i j
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · exact congrFun (congrFun hL0 i) j
        · rw [(hL _ _).1 (Fin.castSucc_lt_last i), (hL' _ _).1 (Fin.castSucc_lt_last i)]
      · exact hLl j
end GlobalTheory.UnipotentBorder
