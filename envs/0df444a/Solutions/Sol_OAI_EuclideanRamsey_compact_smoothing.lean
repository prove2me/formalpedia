-- Prove2me | solution 1 for OAI.EuclideanRamsey.compact_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:07:56.223891+00:00
-- url     : https://prove2.me/submissions/4d61d648-7c4f-4629-84e9-196c5c9c2fb7

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/SmoothingMatrix.lean:L173-L234
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.compact_smoothing. The node keeps its source
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
import Theorems.Thm_OAI_EuclideanRamsey_exists_split_smoothing

-- ---- from OAI.Combinatorics.EuclideanRamsey.Hessian ----
namespace OAI

universe uDomain uCodomain uIndex uColor uAction

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial

open scoped BigOperators
open Matrix MeasureTheory
namespace EuclideanRamsey

section Hessian
variable {E : Type uDomain} {F : Type uCodomain} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hessianB_eq (f : E → ℝ) (x v w : E) :
    hessianB f x v w = iteratedFDeriv ℝ 2 f x ![v,w] := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  rfl

end Hessian

section Trace
variable {E : Type uDomain} {ι : Type uIndex} {κ : Type uColor} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [Fintype κ]

end Trace

section MatrixContraction

end MatrixContraction

section Split
variable {E : Type uDomain} {H : Type uAction} [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]

end Split

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.SmoothingMatrix ----
namespace OAI

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace EuclideanRamsey
lemma covariance_splitting {k d : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    (U : Matrix (Fin d) (Fin k) ℝ) (hC : C.IsSymm)
    (hU : U * C * U.transpose = 1) :
    let R := C * U.transpose
    let Z := 1 - R * U
    U * R = 1 ∧ U * Z = 0 ∧ C = R * R.transpose + Z * C * Z.transpose := by
  dsimp only
  let R := C * U.transpose
  have hR : U * R = 1 := by simpa only [R, ← Matrix.mul_assoc] using hU
  have hRt : R.transpose = U * C := by simp only [R, Matrix.transpose_mul,
    Matrix.transpose_transpose, hC.eq]
  have hRR : R.transpose * U.transpose = 1 := by
    rw [← Matrix.transpose_mul, hR, Matrix.transpose_one]
  refine ⟨hR, ?_, ?_⟩
  · change U * (1 - R * U) = 0
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hR, Matrix.one_mul, sub_self]
  · change C = R * R.transpose + (1 - R * U) * C * (1 - R * U).transpose
    have ht : (1 - R * U).transpose = 1 - U.transpose * R.transpose := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul]
    have h1 : R * U * C = R * R.transpose := by rw [hRt, Matrix.mul_assoc]
    have h2 : C * (U.transpose * R.transpose) = R * R.transpose := by
      rw [← Matrix.mul_assoc]
    have h3 : R * R.transpose * (U.transpose * R.transpose) = R * R.transpose := by
      rw [ Matrix.mul_assoc, ← Matrix.mul_assoc R.transpose, hRR, Matrix.one_mul]
    simp only [ht, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      h1, h2, h3]
    abel

end EuclideanRamsey

open scoped BigOperators
open MeasureTheory Matrix
namespace EuclideanRamsey

end EuclideanRamsey
namespace EuclideanRamsey
open MeasureTheory Matrix
open scoped BigOperators

theorem compact_smoothing : CompactSmoothing := by
  intro k d hd C U hC hU η hη
  let R := C * U.transpose
  let Z : Matrix (Fin k) (Fin k) ℝ := 1-R*U
  obtain ⟨hUR,hUZ,hsplit⟩ := covariance_splitting C U hC hU
  change U*R=1 at hUR
  change U*Z=0 at hUZ
  change C=R*R.transpose+Z*C*Z.transpose at hsplit
  let H := EuclideanSpace ℝ (Fin d)
  let eH : H ≃ₗ[ℝ] (Fin d → ℝ) := (EuclideanSpace.equiv (Fin d) ℝ).toLinearEquiv
  let u : (Fin k → ℝ) →ₗ[ℝ] H := eH.symm.toLinearMap.comp (Matrix.toLin' U)
  let r : H →ₗ[ℝ] (Fin k → ℝ) := (Matrix.toLin' R).comp eH.toLinearMap
  have hur : u.comp r = LinearMap.id := by
    apply LinearMap.ext
    intro y
    simp only [u,r,LinearMap.comp_apply,Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, hUR, Matrix.one_mulVec]
    exact eH.symm_apply_apply y
  let V := LinearMap.ker u
  let e : (Fin k → ℝ) ≃L[ℝ] H×V := (rightInverseSplit u r hur).toContinuousLinearEquiv
  let eh : OrthonormalBasis (Fin d) ℝ H := EuclideanSpace.basisFun (Fin d) ℝ
  have hRv (j : Fin d) : r (eh j) = fun l => R l j := by
    change R.mulVec (eH (eh j)) = _
    have h : eH (eh j) = Pi.single j 1 := by
      change ((EuclideanSpace.basisFun (Fin d) ℝ) j).ofLp = _
      rw [EuclideanSpace.basisFun_apply]
      rfl
    rw [h, Matrix.mulVec_single]
    simp
    rfl
  have hZv (j : Fin k) : (fun l => Z l j) ∈ LinearMap.ker u := by
    rw [LinearMap.mem_ker]
    change eH.symm (U.mulVec (fun l => Z l j)) = 0
    have h : U.mulVec (fun l => Z l j) = 0 := by
      ext a
      change (U*Z) a j = 0
      rw [hUZ]; rfl
    rw [h,map_zero]
  let z : Fin k → V := fun j => ⟨fun l => Z l j,hZv j⟩
  have hR (j : Fin d) : e (fun l => R l j) = (eh j,0) := by
    rw [← hRv]
    exact rightInverseSplit_apply_R u r hur (eh j)
  have hZ (j : Fin k) : e (fun l => Z l j) = (0,z j) := by
    apply Prod.ext
    · exact hZv j
    · apply Subtype.ext
      change (fun l => Z l j) - r (u (fun l => Z l j)) = _
      rw [show u (fun l => Z l j) = 0 from hZv j,map_zero,sub_zero]
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  have hn : 1 ≤ Module.finrank ℝ H := by simpa [H] using hd
  obtain ⟨b,hbs,hbk,hbp,hbm,hsmall⟩ := exists_split_smoothing hn C R Z hsplit e eh z hR hZ hη
  refine ⟨b,hbs,hbk,hbp,hbm,?_⟩
  have hw (x : Fin k → ℝ) : ‖(e x).1‖^2 = gradientWeight U x := by
    change ‖eH.symm (U.mulVec x)‖^2 = _
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  have hop (x : Fin k → ℝ) : secondOperator C (fun j => Pi.single j 1) b x =
      stencilDifferential C b x := by simp only [secondOperator,stencilDifferential,hessianB_eq]
  simpa only [hw,hop] using hsmall

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
open scoped BigOperators
open MeasureTheory Matrix
open MeasureTheory Matrix
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.compact_smoothing := @_root_.OAI.EuclideanRamsey.compact_smoothing
