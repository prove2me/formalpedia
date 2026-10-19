-- Prove2me | solution 1 for OAI.CPTSeparation.Projection.card_sq_le_projections
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T21:16:49.21196+00:00
-- url     : https://prove2.me/submissions/933b4470-2382-44a5-a5dd-ca99e4d5a4da

import Mathlib
import Definitions.Def_OAIQWCPT000

section
-- module Solutions.OAIQW_CPTSeparation.Flows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Projection

open Finset

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

private theorem ind_sq {α : Type*} [DecidableEq α] (S : Finset α) (a : α) :
    ind S a ^ 2 = ind S a := by simp [ind]

private theorem sum_ind {α : Type*} [DecidableEq α] [Fintype α] (S : Finset α) :
    ∑ a, ind S a = S.card := by simp [ind]

theorem card_sq_le_projections_oai (R : Finset (X × Y × Z)) :
    R.card^2 ≤ (R.image (fun v => (v.1,v.2.1))).card *
      (R.image (fun v => (v.1,v.2.2))).card * (R.image (fun v => (v.2.1,v.2.2))).card := by
  let A := R.image (fun v => (v.1,v.2.1))
  let B := R.image (fun v => (v.1,v.2.2))
  let D := R.image (fun v => (v.2.1,v.2.2))
  let a (p : X × Y) := ind A p
  let b (p : X × Z) := ind B p
  let d (p : Y × Z) := ind D p
  let c (p : X × Y) := ∑ k, b (p.1,k) * d (p.2,k)
  have hr : R.card ≤ ∑ p, a p * c p := by
    rw [←sum_ind R]
    simp only [Fintype.sum_prod_type]
    dsimp [c]
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    dsimp [a,b,d]
    by_cases h : (i,j,k) ∈ R
    · have ha : (i,j) ∈ A := mem_image.mpr ⟨(i,j,k),h,rfl⟩
      have hb : (i,k) ∈ B := mem_image.mpr ⟨(i,j,k),h,rfl⟩
      have hd : (j,k) ∈ D := mem_image.mpr ⟨(i,j,k),h,rfl⟩
      simp [ind,h,ha,hb,hd]
    · simp [ind,h]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := (univ : Finset (X × Y))) a c
  have ha : ∑ p : X × Y, a p^2 = A.card := by simp only [a,ind_sq,sum_ind]
  have hc : ∑ p : X × Y, c p^2 ≤ B.card * D.card := by
    calc
      _ ≤ ∑ p : X × Y, (∑ k, b (p.1,k)^2) * (∑ k, d (p.2,k)^2) := by
        apply Finset.sum_le_sum
        intro p _
        exact Finset.sum_mul_sq_le_sq_mul_sq univ (fun k => b (p.1,k)) (fun k => d (p.2,k))
      _ = B.card * D.card := by
        simp only [b,d,ind_sq,Fintype.sum_prod_type]
        rw [←Finset.sum_mul_sum]
        rw [←Fintype.sum_prod_type,←Fintype.sum_prod_type,sum_ind,sum_ind]
  calc
    R.card^2 ≤ (∑ p, a p*c p)^2 := Nat.pow_le_pow_left hr 2
    _ ≤ (∑ p, a p^2) * ∑ p, c p^2 := hcs
    _ ≤ A.card * (B.card*D.card) := by rw [ha]; exact Nat.mul_le_mul_left _ hc
    _ = _ := by dsimp [A,B,D]; simp only [mul_assoc]

end CPTSeparation.Projection

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.CPTSeparation.Projection.card_sq_le_projections_oai.{u_1, u_2, u_3} := @OAI.CPTSeparation.Projection.card_sq_le_projections_oai.{u_1, u_2, u_3}
