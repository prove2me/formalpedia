-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.rational_weight_vector_scale_exists
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T18:14:00.414082+00:00
-- url     : https://prove2.me/submissions/7cc20acf-d677-428a-9c32-ffd8faab8b1b

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum

theorem solution
    {m : Nat} (w : Fin (m + 1) -> Real)
    (hpos : forall i : Fin (m + 1), 0 < w i)
    (hrat : forall i : Fin (m + 1), exists r : Rat, (r : Real) = w i) :
    exists R : Rat, exists T : Fin m -> Nat, exists e : Fin (m + 1) -> Nat,
      And (0 < R) (And (forall i : Fin (m + 1), 0 < e i)
        (And (forall i : Fin m, w i.succ <= (T i : Real) * w 0)
          (forall i : Fin (m + 1), (R : Real) = (e i : Real) * w i))) := by
  classical
  let r : Fin (m + 1) -> Rat := fun i => Classical.choose (hrat i)
  have hr (i : Fin (m + 1)) : (r i : Real) = w i :=
    Classical.choose_spec (hrat i)
  have hnum (i : Fin (m + 1)) : 0 < (r i).num := by
    apply Rat.num_pos.mpr
    exact Rat.cast_pos.mp (by rw [hr]; exact hpos i)
  let n : Fin (m + 1) -> Nat := fun i => (r i).num.natAbs
  have hnint (i : Fin (m + 1)) : (n i : Int) = (r i).num :=
    Int.natAbs_of_nonneg (hnum i).le
  have hn (i : Fin (m + 1)) : 0 < n i := by
    have h : (0 : Int) < (n i : Int) := by rw [hnint]; exact hnum i
    exact_mod_cast h
  have hnreal (i : Fin (m + 1)) : (n i : Real) = ((r i).num : Real) := by
    exact_mod_cast hnint i
  have hden (i : Fin (m + 1)) : ((r i).den : Real) * w i = (n i : Real) := by
    rw [← hr, Rat.cast_def, hnreal, mul_comm]
    exact div_mul_cancel₀ _ (by exact_mod_cast (r i).den_ne_zero)
  let N : Nat := Finset.univ.prod n
  let e : Fin (m + 1) -> Nat := fun i =>
    (Finset.univ.erase i).prod n * (r i).den
  have hN : 0 < N := Finset.prod_pos (fun i _ => hn i)
  have he (i : Fin (m + 1)) : 0 < e i :=
    Nat.mul_pos (Finset.prod_pos (fun j _ => hn j)) (r i).den_pos
  have hscale (i : Fin (m + 1)) : (N : Real) = (e i : Real) * w i := by
    calc
      (N : Real) = (((Finset.univ.erase i).prod n : Nat) : Real) * (n i : Real) := by
        exact_mod_cast (Finset.prod_erase_mul Finset.univ n (Finset.mem_univ i)).symm
      _ = (((Finset.univ.erase i).prod n : Nat) : Real) * (((r i).den : Real) * w i) := by
        rw [hden]
      _ = (e i : Real) * w i := by
        simp only [e, Nat.cast_mul, mul_assoc]
  refine ⟨(N : Rat), (fun _ => e 0), e, ?_, he, ?_, ?_⟩
  · exact_mod_cast hN
  · intro i
    calc
      w i.succ = 1 * w i.succ := (one_mul _).symm
      _ <= (e i.succ : Real) * w i.succ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt (he i.succ))
          (hpos i.succ).le
      _ = (e 0 : Real) * w 0 := (hscale i.succ).symm.trans (hscale 0)
  · intro i
    simpa only [Rat.cast_natCast] using hscale i
