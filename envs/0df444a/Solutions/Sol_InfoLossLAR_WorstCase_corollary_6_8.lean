-- Prove2me | solution 1 for InfoLossLAR.WorstCase.corollary_6_8
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T23:22:29.09971+00:00
-- url     : https://prove2.me/submissions/9f3d585b-ddc2-4a1d-a098-559900861860

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_FixedT
import Theorems.Thm_InfoLossLAR_WorstCase_lemma_6_7
import Theorems.Thm_InfoLossLAR_WorstCase_lemma_6_4
import Theorems.Thm_InfoLossLAR_WorstCase_lemma_6_2
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
open InfoLossLAR.WorstCase
namespace TreeTransportProof
variable {d : ℕ} (T : OrientedTree d) (σ : T.G.edgeSet ⊕ Unit ≃ Fin d)
private def extM (v : Fin d → ℤ) := (T.extended v).submatrix id σ.symm
private theorem coordinates (v : Fin d → ℤ) (a : Fin d → ℤ) :
    (extM T σ v).mulVec a =
      T.incidence.mulVec (fun e => a (σ (.inl e))) + a (σ (.inr ())) • v := by
  classical
  funext i
  change (∑ j : Fin d, (T.extended v i (σ.symm j)) * a j) = _
  rw [← Equiv.sum_comp σ (fun j => T.extended v i (σ.symm j) * a j)]
  simp [Fintype.sum_sum_type,OrientedTree.extended,Matrix.mulVec,dotProduct,mul_comm]

private theorem detT {q d : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (hd : q ≤ d) :
    |(TDef63 q d).det| = (q:ℤ) := by
  obtain ⟨S⟩ := (lemma_6_4 q d hq h2 hd).2.2
  have hs := congrArg Matrix.det S.smith
  rw [Matrix.det_mul,Matrix.det_mul] at hs
  have hdiag : (smithDiag q (d-1) d).det = (q:ℤ) := by
    cases d with
    | zero => have := hq.pos; omega
    | succ n =>
      rw [smithDiag,Matrix.det_diagonal,Fin.prod_univ_castSucc]
      simp [Fin.isLt]
  rw [hdiag] at hs
  apply_fun abs at hs
  rcases Int.isUnit_iff.mp S.U_unimod with h|h <;>
    rcases Int.isUnit_iff.mp S.V_unimod with k|k <;> simpa [h,k,abs_mul] using hs
private theorem intPreimage {d : ℕ} (T : Matrix (Fin d) (Fin d) ℤ)
    (hn : (T.det : ℚ) ≠ 0) (y : Fin d → ℤ) (hy : y ∈ imageLattice T) :
    ∃ x : Fin d → ℤ, (fun i => (x i : ℚ)) = (T.map (Int.cast : ℤ → ℚ))⁻¹.mulVec (fun i => (y i : ℚ)) := by
  obtain ⟨x,hx⟩ := hy
  change T.mulVec x = y at hx
  subst y
  have hu : IsUnit ((T.map (Int.cast : ℤ → ℚ)).det) := by rw [← Int.cast_det]; exact hn.isUnit
  have hv : (fun i => ((T.mulVec x i : ℤ):ℚ)) = (T.map (Int.cast : ℤ → ℚ)).mulVec (fun i => (x i : ℚ)) := by
    funext i
    simp [Matrix.mulVec,dotProduct]
  refine ⟨x, ?_⟩
  rw [hv,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hu,Matrix.one_mulVec]
end TreeTransportProof
open TreeTransportProof
theorem solution (q d : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hdq : q ≤ d)
    (𝒯 : OrientedTree d) (Redge : Matrix 𝒯.G.edgeSet 𝒯.G.edgeSet ℤ)
    (v : Fin d → ℤ) (hv : ∑ i, v i = (q : ℤ))
    (z₀ : Fin d → ℤ) (hz₀ : (q : ℤ) ∣ ∑ i, z₀ i)
    (σ : 𝒯.G.edgeSet ⊕ Unit ≃ Fin d) :
    let Dbar : Matrix (Fin d) (Fin d) ℤ := (𝒯.extended v).submatrix id σ.symm
    let Rbar : Matrix (Fin d) (Fin d) ℤ :=
      (Matrix.fromBlocks Redge 0 0 (1 : Matrix Unit Unit ℤ)).submatrix σ.symm σ.symm
    let DT : Matrix (Fin d) (Fin d) ℤ := Dbar * Rbar
    let Q : Matrix (Fin d) (Fin d) ℚ := TinvQ q d * DT.map (Int.cast : ℤ → ℚ)
    let β : Fin d → ℚ := (TinvQ q d).mulVec (fun i => (z₀ i : ℚ))
    |Dbar.det| = (q : ℤ) ∧
    (∀ x : Fin d → ℤ, DT.mulVec x ∈ imageLattice (TDef63 q d)) ∧
    z₀ ∈ imageLattice (TDef63 q d) ∧
    (DT.det = (q : ℤ) * Redge.det ∨ DT.det = -((q : ℤ) * Redge.det)) ∧
    Q.det = ((Dbar.det * Rbar.det : ℤ) : ℚ) / (((TDef63 q d).det : ℤ) : ℚ) ∧
    (Q.det = (Redge.det : ℚ) ∨ Q.det = -(Redge.det : ℚ)) ∧
    (∃ Qz : Matrix (Fin d) (Fin d) ℤ, Qz.map (Int.cast : ℤ → ℚ) = Q ∧
      (¬ (q : ℤ) ∣ Redge.det → IsUnit (matModq q Qz).det)) ∧
    (∃ βz : Fin d → ℤ, (fun i => (βz i : ℚ)) = β) ∧
    (∀ x : Fin d → ℤ, DT.mulVec x + z₀ ∈ imageLattice (TDef63 q d) ∧
      modq q (DT.mulVec x + z₀) ∈ H0 q d) := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  intro Dbar Rbar DT Q β
  have hA : |Dbar.det| = (q:ℤ) := (lemma_6_7 d 𝒯 v σ).trans (by rw [hv,abs_of_nonneg (Int.natCast_nonneg _)])
  have hM : Rbar.det = Redge.det := by
    dsimp only [Rbar]
    rw [Matrix.det_submatrix_equiv_self,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,mul_one]
  have hT := detT hq hq2 hdq
  have hTd : ((TDef63 q d).det : ℚ) ≠ 0 := by
    exact_mod_cast (show (TDef63 q d).det ≠ 0 by intro h; rw [h,abs_zero] at hT; have := hq.pos; omega)
  have hI := (lemma_6_4 q d hq hq2 hdq).1
  have hcol (x : Fin d → ℤ) : DT.mulVec x ∈ imageLattice (TDef63 q d) := by
    let a := Rbar.mulVec x
    have hvec : DT.mulVec x = 𝒯.incidence.mulVec (fun e => a (σ (.inl e))) + a (σ (.inr ())) • v := by
      change (Dbar * Rbar).mulVec x = _
      rw [← Matrix.mulVec_mulVec]
      exact coordinates 𝒯 σ v a
    have hz : 𝒯.incidence.mulVec (fun e => a (σ (.inl e))) ∈ zeroSumLattice d := by
      rw [← (lemma_6_2 d 𝒯).2.2.2.1]
      exact ⟨_,rfl⟩
    change (∑ i, 𝒯.incidence.mulVec (fun e => a (σ (.inl e))) i)=0 at hz
    apply (hI _).2
    rw [hvec]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,← Finset.mul_sum,hz,zero_add,hv]
    exact dvd_mul_left _ _
  have hz := (hI z₀).2 hz₀
  have hD : DT.det = Dbar.det * Redge.det := by simp [DT,hM]
  have hQ : Q.det = ((Dbar.det * Rbar.det : ℤ) : ℚ) / (((TDef63 q d).det : ℤ) : ℚ) := by
    simp [Q,TinvQ,DT,Matrix.det_mul,Matrix.det_nonsing_inv,← Int.cast_det,div_eq_inv_mul]
  have hAs : Dbar.det = (q:ℤ) ∨ Dbar.det = -(q:ℤ) := eq_or_eq_neg_of_abs_eq (by simpa using hA)
  have hTs : (TDef63 q d).det = (q:ℤ) ∨ (TDef63 q d).det = -(q:ℤ) := eq_or_eq_neg_of_abs_eq (by simpa using hT)
  have hDsign : DT.det = (q:ℤ) * Redge.det ∨ DT.det = -((q:ℤ) * Redge.det) := by rcases hAs with h|h <;> simp [hD,h]
  have hQsign : Q.det = (Redge.det:ℚ) ∨ Q.det = -(Redge.det:ℚ) := by
    have hqr : (q:ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
    rw [hQ,hM]
    rcases hAs with ha|ha <;> rcases hTs with ht|ht <;> simp [ha,ht,hqr] <;> right <;> field_simp
  refine ⟨hA,hcol,hz,hDsign,hQ,hQsign,?_,intPreimage (TDef63 q d) hTd z₀ hz,?_⟩
  · have he (j : Fin d) : DT.col j ∈ imageLattice (TDef63 q d) := by simpa using hcol (Pi.single j 1)
    choose cols hc using fun j => intPreimage (TDef63 q d) hTd (DT.col j) (he j)
    let Z : Matrix (Fin d) (Fin d) ℤ := fun i j => cols j i
    have hZ : Z.map (Int.cast : ℤ → ℚ) = Q := by
      ext i j
      exact congrFun (hc j) i
    refine ⟨Z,hZ,fun hn => ?_⟩
    have hzd : (Z.det : ℚ) = Q.det := (Int.cast_det Z).trans (congrArg Matrix.det hZ)
    have hzdi : Z.det = Redge.det ∨ Z.det = -Redge.det := by rcases hQsign with h|h <;> [left;right] <;> exact_mod_cast hzd.trans h
    rw [matModq,← Int.cast_det]
    apply isUnit_iff_ne_zero.mpr
    rcases hzdi with h|h <;> simpa [h,ZMod.intCast_zmod_eq_zero_iff_dvd] using hn
  · intro x
    have hm := (imageLattice (TDef63 q d)).add_mem (hcol x) hz
    refine ⟨hm,?_⟩
    change (∑ i, ((DT.mulVec x + z₀) i : ZMod q)) = 0
    rw [← Int.cast_sum]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 ((hI _).1 hm)
