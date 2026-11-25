-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.cechAcyclic_discPresheaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:26.482717+00:00
-- url     : https://prove2.me/submissions/0c5020e4-f59e-4fa2-9c83-ea1a7502760d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ev_congr
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ev_d
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cons_comp_succAbove_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cons_comp_succAbove_succ
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ev_homotopy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u v
variable {X : TopCat.{u}} {ι : Type w}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
variable (A : X → AddCommGrpCat.{u})

namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution : CechAcyclic (discPresheaf A) U := by
  intro n σ hσ
  refine ⟨homotopy U A σ, funext fun i => funext fun y => ?_⟩
  obtain ⟨x, hx⟩ := y
  have hJ := mem_inter_cons U i hx
  have hcoc : ev A x hJ (d (discPresheaf A) U (n + 1) σ
      (Fin.cons (chosenIdx U x (exists_mem_of_mem_inter U i hx)) i)) = 0 := by
    rw [hσ]
    rfl
  rw [ev_d, Fin.sum_univ_succ] at hcoc
  change ev A x hx (d (discPresheaf A) U n (homotopy U A σ) i) = ev A x hx (σ i)
  rw [ev_d]
  rw [Fin.val_zero, pow_zero, one_smul,
    ev_congr A σ (cons_comp_succAbove_zero _ i) x _ hx] at hcoc
  rw [eq_neg_of_add_eq_zero_left hcoc, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, neg_neg, ev_homotopy]
  exact congrArg _ (ev_congr A σ (cons_comp_succAbove_succ _ i k).symm x _ _)
end GroundTheory.Arith.SchemeCoh
