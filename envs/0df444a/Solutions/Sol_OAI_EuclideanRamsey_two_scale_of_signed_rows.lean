-- Prove2me | solution 1 for OAI.EuclideanRamsey.two_scale_of_signed_rows
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:35:05.352195+00:00
-- url     : https://prove2.me/submissions/5482df5e-5766-48d2-89d2-40d7b73a334c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/GramCompletion.lean:L123-L178
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.two_scale_of_signed_rows. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows
import Theorems.Thm_OAI_EuclideanRamsey_normalized_signed_rows

-- ---- from OAI.Combinatorics.EuclideanRamsey.GramCompletion ----
namespace OAI

universe uIndex uRow uColor

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
namespace EuclideanRamsey
lemma trace_gram_complement {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (η : ℝ) (hη : B.trace ≤ η) :
    (η • (1 : Matrix ι ι ℝ)-B).PosSemidef := by
  let e := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hB.1.eigenvectorUnitary
  have he (i : ι) : hB.1.eigenvalues i ≤ η := by
    apply le_trans _ hη
    rw [hB.1.trace_eq_sum_eigenvalues]
    simpa using (Finset.single_le_sum (fun j _ => hB.eigenvalues_nonneg j) (Finset.mem_univ i))
  have hD : (diagonal (fun i => η-hB.1.eigenvalues i)).PosSemidef :=
    posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (he i))
  have hd : e (diagonal (fun i => η-hB.1.eigenvalues i)) = η • 1-B := by
    have hr : diagonal (fun i => η-hB.1.eigenvalues i) =
        η • (1 : Matrix ι ι ℝ)-diagonal hB.1.eigenvalues := by
      ext i j
      by_cases h : i=j <;> simp [h]
    rw [hr,map_sub,map_smul,map_one]
    congr 1
    exact hB.1.spectral_theorem.symm
  rw [← hd]
  exact hD.mul_mul_conjTranspose_same _

lemma exists_gram_sqrt {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P.PosSemidef) :
    ∃ R : Matrix ι ι ℝ,R*R.transpose=P := by
  let R := CFC.sqrt P
  have hr : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  refine ⟨R,?_⟩
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial,hr.1.eq]
  exact CFC.sqrt_mul_sqrt_self P hP.nonneg

lemma gram_fromCols {ι : Type uIndex} {τ : Type uRow} {κ : Type uColor} [Fintype τ] [Fintype κ]
    (U : Matrix ι τ ℝ) (R : Matrix ι κ ℝ) :
    (U.fromCols R)*(U.fromCols R).transpose = U*U.transpose+R*R.transpose := by
  ext i j
  simp [Matrix.mul_apply,Matrix.fromCols,Matrix.transpose_apply,Fintype.sum_sum_type]

theorem complete_gram_pair {d : ℕ} {τ : Type uRow} [Fintype τ]
    (U V : Matrix (Fin d) τ ℝ) (η : ℝ) (hη : 0 < η)
    (hdiff : U*U.transpose-V*V.transpose=1)
    (htrace : (V*V.transpose).trace < η) :
    ∃ R : Matrix (Fin d) (Fin d) ℝ,
      let c := (Real.sqrt (1+η))⁻¹
      (c • (U.fromCols R))*(c • (U.fromCols R)).transpose=1 ∧
      (c • (V.fromCols R))*(c • (V.fromCols R)).transpose=
        (η/(1+η)) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have hB : (V*V.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose V
  obtain ⟨R,hR⟩ := exists_gram_sqrt _ (trace_gram_complement _ hB η htrace.le)
  refine ⟨R,?_⟩
  dsimp only
  have he (A : Matrix (Fin d) τ ℝ) :
      ((Real.sqrt (1+η))⁻¹ • A.fromCols R)*
      ((Real.sqrt (1+η))⁻¹ • A.fromCols R).transpose =
      (1/(1+η)) • (A*A.transpose+R*R.transpose) := by
    rw [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,gram_fromCols]
    congr 1
    rw [← _root_.mul_inv_rev,← sq,Real.sq_sqrt (by linarith)]
    simp
  rw [he,he,hR]
  have hU : U*U.transpose+(η • 1-V*V.transpose)=(1+η) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [add_smul,one_smul,← hdiff]
    abel
  rw [hU,smul_smul,one_div_mul_cancel (by linarith : 1+η ≠ 0),one_smul]
  constructor
  · rfl
  · have hv : V*V.transpose+(η • 1-V*V.transpose)=η • (1 : Matrix (Fin d) (Fin d) ℝ) := by abel
    rw [hv,smul_smul]
    congr 1
    ring
end EuclideanRamsey

namespace EuclideanRamsey
open Matrix
lemma row_gram_distance {d : ℕ} {τ : Type uRow} [Fintype τ]
    (v : τ → ℝ) (U : Matrix (Fin d) τ ℝ) (q : ℝ)
    (hU : U*U.transpose=q • (1 : Matrix (Fin d) (Fin d) ℝ))
    (a b : Fin d → ℝ) :
    (∑ x,((v x+∑ j,a j*U j x)-(v x+∑ j,b j*U j x))^2) =
      q*(∑ j,(a j-b j)^2) := by
  have he (x : τ) : (v x+∑ j,a j*U j x)-(v x+∑ j,b j*U j x) =
      (U.transpose *ᵥ (a-b)) x := by
    simp only [Matrix.mulVec,Matrix.transpose_apply,dotProduct,Pi.sub_apply,
      mul_sub,Finset.sum_sub_distrib]
    simp only [mul_comm]
    ring
  simp only [he,pow_two]
  change (U.transpose *ᵥ (a-b)) ⬝ᵥ (U.transpose *ᵥ (a-b)) = _
  have hquad : (U.transpose *ᵥ (a-b)) ⬝ᵥ (U.transpose *ᵥ (a-b)) =
      (a-b) ⬝ᵥ ((U*U.transpose) *ᵥ (a-b)) := by
    rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec (a-b) U]
    congr 1
    exact (Matrix.vecMul_transpose U.transpose (a-b)).symm
  rw [hquad,hU,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul]
  simp only [smul_eq_mul,dotProduct,Pi.sub_apply]

theorem two_scale_of_signed_rows {α : Type} [DecidableEq α] {d s : ℕ}
    (hd : 0 < d) (hs : 0 < s) (a : Fin s → EuclideanSpace ℝ (Fin d))
    (v : α → ℝ) (g : α → Fin d → ℝ) (f : α →₀ ℚ)
    (ζ η : ℝ) (hζ : 0 < ζ) (hη : 0 < η)
    (heval : ∀ i,f.mapDomain (fun x => v x+∑ j,a i j*g x j)=0)
    (hmom : ∀ j l,f.sum (fun x q => (q:ℝ)*g x j*g x l)=ζ*(if j=l then 1 else 0))
    (hneg : f.sum (fun x q => max (-(q:ℝ)) 0*(∑ j,(g x j)^2)) < η*ζ) :
    ∃ (ℓ : ℕ),1 ≤ ℓ ∧ ∃ (f' g' : Fin s → EuclideanSpace ℝ (Fin ℓ)),
      (∀ i j,‖f' i-f' j‖^2=‖a i-a j‖^2) ∧
      (∀ i j,‖g' i-g' j‖^2=(η/(1+η))*‖a i-a j‖^2) ∧
      ∀ i,∃ σ : Equiv.Perm (Fin ℓ),∀ x,g' i (σ x)=f' i x := by
  classical
  obtain ⟨τ,hτ,vp,vn,U,V,hdiff,htrace,hperm⟩ :=
    normalized_signed_rows hs (fun i j => a i j) v g f ζ η hζ heval hmom hneg
  let := hτ
  obtain ⟨R,hR1,hR2⟩ := complete_gram_pair U V η hη hdiff htrace
  let c := (Real.sqrt (1+η))⁻¹
  let Up := c • U.fromCols R
  let Un := c • V.fromCols R
  let cp : τ ⊕ Fin d → ℝ := fun x => c*Sum.elim vp (fun _ => 0) x
  let cn : τ ⊕ Fin d → ℝ := fun x => c*Sum.elim vn (fun _ => 0) x
  let ip (i : Fin s) (x : τ ⊕ Fin d) := cp x+∑ j,a i j*Up j x
  let ineg (i : Fin s) (x : τ ⊕ Fin d) := cn x+∑ j,a i j*Un j x
  have hperm' (i : Fin s) : ∃ σ : Equiv.Perm (τ ⊕ Fin d),∀ x,ineg i (σ x)=ip i x := by
    obtain ⟨σ,hσ⟩ := hperm i
    refine ⟨Equiv.sumCongr σ (Equiv.refl _),?_⟩
    intro x
    cases x with
    | inl x =>
      have h := congrArg (fun r : ℝ => c*r) (hσ x)
      simpa [ineg,ip,cn,cp,Up,Un,Finset.mul_sum,mul_add,mul_assoc,mul_comm,mul_left_comm] using h
    | inr x => simp [ineg,ip,cn,cp,Up,Un]
  let ℓ := Fintype.card (τ ⊕ Fin d)
  let e := Fintype.equivFin (τ ⊕ Fin d)
  let fp (i : Fin s) : EuclideanSpace ℝ (Fin ℓ) := WithLp.toLp 2 (fun x => ip i (e.symm x))
  let fn (i : Fin s) : EuclideanSpace ℝ (Fin ℓ) := WithLp.toLp 2 (fun x => ineg i (e.symm x))
  have hd' : Nonempty (τ ⊕ Fin d) := ⟨Sum.inr ⟨0,hd⟩⟩
  refine ⟨ℓ,Fintype.card_pos_iff.mpr hd',fp,fn,?_,?_,?_⟩
  · intro i j
    have h := row_gram_distance cp Up 1 (by simpa only [one_smul] using hR1) (a i) (a j)
    rw [one_mul] at h
    simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,fp,WithLp.ofLp_sub,
      Pi.sub_apply]
    rw [e.symm.sum_comp (fun x => (ip i x-ip j x)^2)]
    exact h
  · intro i j
    have h := row_gram_distance cn Un (η/(1+η)) hR2 (a i) (a j)
    simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,fn,WithLp.ofLp_sub,
      Pi.sub_apply]
    rw [e.symm.sum_comp (fun x => (ineg i x-ineg j x)^2)]
    exact h
  · intro i
    obtain ⟨σ,hσ⟩ := hperm' i
    refine ⟨e.symm.trans (σ.trans e),?_⟩
    intro x
    simpa [fp,fn,Equiv.trans_apply] using hσ (e.symm x)
end EuclideanRamsey

namespace EuclideanRamsey
open scoped BigOperators
end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.two_scale_of_signed_rows := @_root_.OAI.EuclideanRamsey.two_scale_of_signed_rows
