-- Prove2me | solution 1 for InfoLossLAR.WorstCase.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T23:22:22.189969+00:00
-- url     : https://prove2.me/submissions/9cc92a41-8687-41f5-a252-ea8e9bd9924c

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_FixedT
set_option autoImplicit false
open scoped BigOperators
open InfoLossLAR.WorstCase

namespace PathSmith
private theorem last_ne_castSucc {n : ℕ} (i : Fin n) : Fin.last n ≠ i.castSucc := (Fin.castSucc_ne_last i).symm

private def partialSums (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℤ :=
  fun i j => if j ≤ i then 1 else 0
private def P (q n : ℕ) := partialSums n * TDef63 q (n+1)
private def shear (q n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℤ :=
  fun i j => if i=j then 1 else if j=Fin.last n then -(P q n i j) else 0

private theorem partialSums_det (n : ℕ) : (partialSums n).det=1 := by
  rw [Matrix.det_of_isLowerTriangular _ (by intro i j h; exact if_neg (not_le.mpr h))]
  simp [partialSums]

private theorem shear_det (q n : ℕ) : (shear q n).det=1 := by
  rw [Matrix.det_of_isUpperTriangular (by
    intro i j h
    change j < i at h
    have hj : j≠Fin.last n := fun hj => (not_lt.mpr (Fin.le_last i)) (hj ▸ h)
    simp [shear,ne_of_gt h,hj])]
  simp [shear]

private theorem p_edge (q n : ℕ) (i : Fin (n+1)) (j : Fin n) :
    P q n i j.castSucc = if i=j.castSucc then 1 else 0 := by
  have he (k : Fin (n+1)) :
      TDef63 q (n+1) k j.castSucc = (if k=j.castSucc then 1 else 0) - (if k=j.succ then 1 else 0) := by
    have hh : j.val+1<n+1 := by omega
    have hs : k.val=j.val+1 ↔ k=j.succ := by change k.val = j.succ.val ↔ _; exact (Fin.ext_iff (a := k) (b := j.succ)).symm
    unfold TDef63
    simp only [Fin.val_castSucc,if_pos hh,hs]
    split_ifs <;> (first | omega | simp_all [Fin.ext_iff])
  simp only [P,Matrix.mul_apply,he,mul_sub,mul_ite,mul_one,mul_zero,Finset.sum_sub_distrib,
    Finset.sum_ite_eq',Finset.mem_univ,if_true,partialSums]
  split_ifs <;> simp_all [Fin.ext_iff,Fin.le_def] <;> omega

private theorem p_last (q n : ℕ) (hq : q ≤ n+1) :
    P q n (Fin.last n) (Fin.last n)=q := by
  have hr : (Finset.range (n+1)).filter (·<q)=Finset.range q := by
    ext k; simp only [Finset.mem_filter,Finset.mem_range]; omega
  simp only [P,Matrix.mul_apply,partialSums,Fin.le_last,if_true,one_mul,TDef63,Fin.val_last,
    lt_self_iff_false,if_false]
  rw [Fin.sum_univ_eq_sum_range (fun k => if k<q then (1:ℤ) else 0),
      ← Finset.sum_filter, hr]
  simp

private theorem smith (q n : ℕ) (hq : q ≤ n+1) :
    partialSums n * TDef63 q (n+1) * shear q n = smithDiag q n (n+1) := by
  change P q n * shear q n = _
  ext i j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [Matrix.mul_apply,Fin.sum_univ_castSucc]
    simp_rw [p_edge]
    refine Fin.lastCases ?_ (fun b => ?_) i
    · simp [shear,last_ne_castSucc,p_last q n hq,smithDiag]
    · simp [shear,Fin.castSucc_ne_last,Finset.sum_ite_eq,ite_mul,smithDiag]
  · rw [Matrix.mul_apply]
    have hsh (i : Fin (n+1)) : shear q n i k.castSucc = if i=k.castSucc then 1 else 0 := by
      simp [shear,Fin.castSucc_ne_last]
    simp only [hsh,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true,p_edge]
    by_cases h : i=k.castSucc
    · subst i; simp [smithDiag,k.isLt]
    · simp [smithDiag,h]

private theorem last_apply (n : ℕ) (z : Fin (n+1) → ℤ) :
    (partialSums n).mulVec z (Fin.last n) = ∑ i, z i := by
  simp [Matrix.mulVec,dotProduct,partialSums,Fin.le_last]

private theorem image (q n : ℕ) (hq : q ≤ n+1) (z : Fin (n+1) → ℤ) :
    z ∈ imageLattice (TDef63 q (n+1)) ↔ (q:ℤ) ∣ ∑ j,z j := by
  constructor
  · rintro ⟨x,rfl⟩
    refine ⟨x (Fin.last n),?_⟩
    change ∑ i,(TDef63 q (n+1)).mulVec x i = _
    rw [←last_apply,Matrix.mulVec_mulVec]
    change (P q n).mulVec x (Fin.last n) = _
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_castSucc,p_edge,last_ne_castSucc,p_last q n hq]
  · rintro ⟨k,hk⟩
    let v := (partialSums n).mulVec z
    let y : Fin (n+1) → ℤ := Fin.lastCases k (fun i => v i.castSucc)
    refine ⟨(shear q n).mulVec y,?_⟩
    change (TDef63 q (n+1)).mulVec ((shear q n).mulVec y) = z
    apply Matrix.mulVec_injective_of_det_ne_zero (show (partialSums n).det≠0 by rw [partialSums_det]; decide)
    rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,smith q n hq]
    funext i
    rw [smithDiag,Matrix.mulVec_diagonal]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [y,last_apply] using hk.symm
    · simp [y,v]

private theorem index_eq (q n : ℕ) (hq : q ≤ n+1) :
    (imageLattice (TDef63 q (n+1))).toAddSubgroup.index = q := by
  let h : (Fin (n+1) → ℤ) →+ ZMod q :=
    { toFun := fun x => ((∑ j,x j : ℤ) : ZMod q)
      map_zero' := by simp
      map_add' := by intro x y; simp [Finset.sum_add_distrib] }
  have he : (imageLattice (TDef63 q (n+1))).toAddSubgroup = h.ker := by
    ext z
    change z ∈ imageLattice (TDef63 q (n+1)) ↔ ((∑ j,z j : ℤ) : ZMod q)=0
    rw [image q n hq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hs : Function.Surjective h := by
    intro a; obtain ⟨k,rfl⟩ := ZMod.intCast_surjective a
    refine ⟨Pi.single (0:Fin (n+1)) k,?_⟩
    simp [h,Pi.single_apply]
  rw [he,AddSubgroup.index_ker,AddMonoidHom.range_eq_top.mpr hs,AddSubgroup.card_top,Nat.card_zmod]

end PathSmith

open PathSmith in
theorem solution (q d : ℕ) (hq : q.Prime) (_hq2 : q ≠ 2) (hdq : q ≤ d) :
    (∀ z : Fin d → ℤ, z ∈ imageLattice (TDef63 q d) ↔ (q : ℤ) ∣ ∑ j, z j) ∧
    (imageLattice (TDef63 q d)).toAddSubgroup.index = q ∧
    IsRoundingMatrix q (d - 1) d (TDef63 q d) := by
  cases d with
  | zero => have := hq.pos; omega
  | succ n =>
    refine ⟨image q n hdq,index_eq q n hdq,⟨⟨partialSums n,shear q n,by omega,?_,?_,smith q n hdq⟩⟩⟩
    · rw [partialSums_det]; exact isUnit_one
    · rw [shear_det]; exact isUnit_one
