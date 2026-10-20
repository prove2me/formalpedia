-- Prove2me | solution 2 for OAI.ThreeState.TreeClauses.Tree.productPMF_list
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:28:05.901578+00:00
-- url     : https://prove2.me/submissions/f4c3d47c-eacd-4004-bd4a-8b5b1d5a2732

import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products
import Definitions.Def_OAI_Probability_ThreeStateClauses_Degradation
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularLaw

open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Tree
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators ENNReal
open ThreeState.TreeClauses.Experiment
theorem h50c_productPMF_cons {α : Type*} {n : ℕ} (p : Fin (n+1) → PMF α) :
    productPMF p = (p 0).bind (fun a ↦ (productPMF (fun j ↦ p j.succ)).map (Fin.cons a)) := by
  classical
  ext v
  rw [PMF.bind_apply, productPMF_apply, Fin.prod_univ_succ]
  have hin : ∀ a, ((productPMF (fun j ↦ p j.succ)).map (Fin.cons a)) v =
      if a = v 0 then ∏ j : Fin n, p j.succ (v j.succ) else 0 := by
    intro a
    rw [PMF.map_apply]
    split_ifs with ha
    · subst ha
      rw [tsum_eq_single (Fin.tail v)]
      · rw [if_pos (Fin.cons_self_tail v).symm, productPMF_apply]; rfl
      · intro w hw
        rw [if_neg]
        intro h; apply hw; rw [h]; simp
    · refine ENNReal.tsum_eq_zero.2 fun w => ?_
      rw [if_neg]
      intro h; apply ha; rw [h]; simp
  simp_rw [hin]
  rw [tsum_eq_single (v 0)]
  · simp
  · intro a ha; simp [ha]

theorem solution {α : Type} (p : PMF α) (n : ℕ) :
    (productPMF (fun _ : Fin n ↦ p)).map List.ofFn = iidList p n := by
  induction n with
  | zero =>
    have : (productPMF (fun _ : Fin 0 ↦ p)) = PMF.pure (fun j => Fin.elim0 j) := by
      ext v; simp [PMF.pure_apply]; exact funext fun j => Fin.elim0 j
    rw [this, PMF.pure_map]; simp [iidList]
  | succ n ih =>
    rw [h50c_productPMF_cons, PMF.map_bind, iidList]
    congr 1; funext a
    rw [PMF.map_comp, ← ih, PMF.map_comp]
    congr 1; funext w; simp [List.ofFn_succ]

