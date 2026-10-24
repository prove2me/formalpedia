-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.exists_common_weight_degree.common_multiple
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:53:14.359811+00:00
-- url     : https://prove2.me/submissions/5eac0746-2f86-4f4f-bce3-dbf962cf5566

import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

open Finset

theorem solution
    (d : Nat) (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real)) :
    ∃ q : Real, 0 < q ∧
      ∀ i : Fin d, ∃ e : Nat, 0 < e ∧ (w i : Real) * (e : Real) = q := by
  classical
  let q : Real := ∏ i : Fin d, ((w i).num : Real)
  refine ⟨q, ?_, ?_⟩
  · dsimp [q]
    apply Finset.prod_pos
    intro i hi
    have hweight : (w i : Real) = ((w i).num : Real) / (w i).den := by
      symm
      exact_mod_cast (w i).num_divInt_den
    have hd : 0 < ((w i).den : Real) := by
      exact_mod_cast (w i).den_pos
    have hnum : ((w i).num : Real) = (w i : Real) * (w i).den := by
      rw [hweight]
      field_simp [ne_of_gt hd]
    rw [hnum]
    exact mul_pos (hw i) hd
  · intro i
    let e : Nat := (w i).den * ∏ j ∈ Finset.univ.erase i, (w j).num.toNat
    have hweight : (w i : Real) = ((w i).num : Real) / (w i).den := by
      symm
      exact_mod_cast (w i).num_divInt_den
    have hd : 0 < ((w i).den : Real) := by
      exact_mod_cast (w i).den_pos
    have hnumReal (j : Fin d) : 0 < ((w j).num : Real) := by
      have hjweight : (w j : Real) = ((w j).num : Real) / (w j).den := by
        symm
        exact_mod_cast (w j).num_divInt_den
      have hjd : 0 < ((w j).den : Real) := by
        exact_mod_cast (w j).den_pos
      have hjnum : ((w j).num : Real) = (w j : Real) * (w j).den := by
        rw [hjweight]
        field_simp [ne_of_gt hjd]
      rw [hjnum]
      exact mul_pos (hw j) hjd
    have hnumNat (j : Fin d) : 0 < (w j).num := by
      exact_mod_cast hnumReal j
    have htoNat (j : Fin d) : ((w j).num.toNat : Real) = ((w j).num : Real) := by
      have hto : ((w j).num.toNat : Int) = (w j).num :=
        Int.toNat_of_nonneg (le_of_lt (hnumNat j))
      exact_mod_cast hto
    have hothers :
        (∏ j ∈ Finset.univ.erase i, ((w j).num.toNat : Real)) =
          ∏ j ∈ Finset.univ.erase i, ((w j).num : Real) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact htoNat j
    have hprod :
        (∏ j ∈ Finset.univ.erase i, ((w j).num : Real)) *
          ((w i).num : Real) = q := by
      dsimp [q]
      rw [← Finset.prod_erase_mul Finset.univ
        (fun j : Fin d => ((w j).num : Real)) (Finset.mem_univ i)]
    refine ⟨e, ?_, ?_⟩
    · dsimp [e]
      apply Nat.mul_pos (w i).den_pos
      apply Finset.prod_pos
      intro j hj
      have hn : 0 < ((w j).num.toNat : Real) := by
        rw [htoNat]
        exact hnumReal j
      exact_mod_cast hn
    · dsimp [e]
      have he :
          (e : Real) =
            (w i).den * ∏ j ∈ Finset.univ.erase i, ((w j).num : Real) := by
        dsimp [e]
        push_cast
        rw [hothers]
      rw [hweight, he]
      have hdenne : (w i).den ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (w i).den_pos)
      field_simp [hdenne]
      nlinarith [hprod]