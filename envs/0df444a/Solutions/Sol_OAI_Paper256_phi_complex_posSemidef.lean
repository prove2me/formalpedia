-- Prove2me | solution 1 for OAI.Paper256.phi_complex_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:24:05.397286+00:00
-- url     : https://prove2.me/submissions/5e893577-26d5-4d86-aac4-784d70111d23

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/ComplexPositive.lean:L81-L94
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.phi_complex_posSemidef. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Theorems.Thm_OAI_Paper256_posSemidef_three_of_principal_minors

-- ---- from OAI.Analysis.HyperbolicCones.FormBasic ----
namespace OAI

/-! Exact identities for the Choi–Lam form. -/

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

universe u

namespace Paper256

theorem qMatrix_isHermitian (y : Fin 3 → ℝ) : (qMatrix y).IsHermitian := by
  show (qMatrix y)ᴴ = qMatrix y
  ext i j
  by_cases hij : i = j
  · subst j
    simp [qMatrix, Matrix.conjTranspose_apply]
  · simp [qMatrix, Matrix.conjTranspose_apply, hij, Ne.symm hij, mul_comm]

theorem zMatrix_isHermitian (z : Fin 3 → ℝ) : (zMatrix z).IsHermitian := by
  show (zMatrix z)ᴴ = zMatrix z
  ext i j
  by_cases hij : i = j
  · subst j
    simp [zMatrix, Matrix.conjTranspose_apply]
  · simp [zMatrix, Matrix.conjTranspose_apply, hij, Ne.symm hij, mul_comm]

theorem qMatrix_quadratic (z y : Fin 3 → ℝ) :
    dotProduct z (qMatrix y *ᵥ z) = choiLam z y := by
  simp [dotProduct, Matrix.mulVec, qMatrix, choiLam, Fin.sum_univ_succ]
  ring

theorem zMatrix_quadratic (z y : Fin 3 → ℝ) :
    dotProduct y (zMatrix z *ᵥ y) = choiLam z y := by
  simp [dotProduct, Matrix.mulVec, zMatrix, choiLam, Fin.sum_univ_succ]
  ring

theorem zMatrix_diag_nonnegative (z : Fin 3 → ℝ) (i : Fin 3) :
    0 ≤ zMatrix z i i := by
  simp only [zMatrix, ↓reduceIte]
  positivity

theorem zMatrix_principal_minor_two (z : Fin 3 → ℝ) (i : Fin 3) :
    Matrix.det ((zMatrix z).submatrix
      (fun j : Fin 2 => if j = 0 then i else i + 1)
      (fun j : Fin 2 => if j = 0 then i else i + 1)) =
      (z i ^ 2) ^ 2 + z (i + 2) ^ 2 * (z i ^ 2 + z (i + 1) ^ 2) := by
  fin_cases i <;> simp [Matrix.det_fin_two, Matrix.submatrix, zMatrix,
    Fin.reduceAdd, Fin.reduceEq] <;> ring

theorem zMatrix_principal_minor_two_nonnegative (z : Fin 3 → ℝ) (i : Fin 3) :
    0 ≤ Matrix.det ((zMatrix z).submatrix
      (fun j : Fin 2 => if j = 0 then i else i + 1)
      (fun j : Fin 2 => if j = 0 then i else i + 1)) := by
  rw [zMatrix_principal_minor_two]
  positivity

theorem zMatrix_det (z : Fin 3 → ℝ) :
    Matrix.det (zMatrix z) =
      (z 0 ^ 2) ^ 2 * z 1 ^ 2 + (z 1 ^ 2) ^ 2 * z 2 ^ 2 +
        (z 2 ^ 2) ^ 2 * z 0 ^ 2 - 3 * z 0 ^ 2 * z 1 ^ 2 * z 2 ^ 2 := by
  simp [Matrix.det_fin_three, zMatrix]
  ring

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.FormPositive ----
namespace OAI

/-! Positivity of the Choi--Lam form, including its principal-minor argument. -/

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

namespace Paper256

theorem cyclic_cubic_nonnegative (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a - 3 * a * b * c := by
  have aux (a b c : ℝ) (hc : 0 ≤ c) (hca : c ≤ a) (hcb : c ≤ b) :
      0 ≤ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a - 3 * a * b * c := by
    have h := add_nonneg
      (mul_nonneg hc (add_nonneg (sq_nonneg (a - b))
        (mul_nonneg (sub_nonneg.mpr hca) (sub_nonneg.mpr hcb))))
      (mul_nonneg (sq_nonneg (a - c)) (sub_nonneg.mpr hcb))
    nlinarith only [h]
  rcases le_total a b with hab | hba
  · rcases le_total a c with hac | hca
    · nlinarith only [aux b c a ha hab hac]
    · exact aux a b c hc hca (hca.trans hab)
  · rcases le_total b c with hbc | hcb
    · nlinarith only [aux c a b hb hbc hba]
    · exact aux a b c hc (hcb.trans hba) hcb

theorem zMatrix_det_nonnegative (z : Fin 3 → ℝ) : 0 ≤ Matrix.det (zMatrix z) := by
  rw [zMatrix_det]
  exact cyclic_cubic_nonnegative _ _ _ (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)

theorem zMatrix_posSemidef (z : Fin 3 → ℝ) : (zMatrix z).PosSemidef := by
  apply posSemidef_three_of_principal_minors _ (zMatrix_isHermitian z)
    (zMatrix_diag_nonnegative z)
  · have h := zMatrix_principal_minor_two_nonnegative z 0
    simp [Matrix.det_fin_two, Matrix.submatrix, zMatrix, Fin.reduceAdd] at h ⊢
    nlinarith only [h]
  · have h := zMatrix_principal_minor_two_nonnegative z 2
    simp [Matrix.det_fin_two, Matrix.submatrix, zMatrix, Fin.reduceAdd, Fin.reduceEq] at h ⊢
    nlinarith only [h]
  · have h := zMatrix_principal_minor_two_nonnegative z 1
    simp [Matrix.det_fin_two, Matrix.submatrix, zMatrix, Fin.reduceAdd, Fin.reduceEq] at h ⊢
    nlinarith only [h]
  · exact zMatrix_det_nonnegative z

theorem choiLam_nonnegative (z y : Fin 3 → ℝ) : 0 ≤ choiLam z y := by
  have h := (zMatrix_posSemidef z).dotProduct_mulVec_nonneg y
  simpa only [star_trivial, zMatrix_quadratic] using h

theorem qMatrix_posSemidef (y : Fin 3 → ℝ) : (qMatrix y).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (qMatrix_isHermitian y) fun z => ?_
  simpa only [star_trivial, qMatrix_quadratic] using choiLam_nonnegative z y

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.PolynomialEvaluation ----
namespace OAI

noncomputable section

open Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator

universe u v

namespace Paper256

theorem qMatrix_map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (y : Fin 3 → R) :
    (qMatrix y).map f = qMatrix (fun i => f (y i)) := by
  ext i j
  by_cases h : i = j <;> simp [qMatrix, h]

theorem phi_map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (y : Fin 3 → R) (X : Mat 4 R) :
    (phi y X).map f = phi (fun i => f (y i)) (X.map f) := by
  ext i j
  have hq (a b : Fin 3) : f (qMatrix y a b) = qMatrix (fun k => f (y k)) a b :=
    congrFun (congrFun (qMatrix_map f y) a) b
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [phi, Matrix.trace, Matrix.diag, Matrix.mul_apply, hq]
    · simp [phi, hq]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [phi, hq]
    · simp [phi, hq]

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.MatrixComplex ----
namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Matrix

namespace Paper256

theorem isHermitian_complexify {n : ℕ} (A : Mat n ℝ) (hA : A.IsHermitian) :
    (A.map Complex.ofReal).IsHermitian :=
  hA.map _ (by intro x; simp)

theorem complex_quadratic_re {n : ℕ} (A : Mat n ℝ) (w : Fin n → ℂ) :
    (dotProduct (star w) (A.map Complex.ofReal *ᵥ w)).re =
      dotProduct (fun i => (w i).re) (A *ᵥ fun i => (w i).re) +
      dotProduct (fun i => (w i).im) (A *ᵥ fun i => (w i).im) := by
  have ht (i j : Fin n) : (star (w i) * ((A i j : ℂ) * w j)).re =
      (w i).re * (A i j * (w j).re) + (w i).im * (A i j * (w j).im) := by
    simp [Complex.mul_re, Complex.mul_im]
  simp only [dotProduct, mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum,
    Complex.re_sum, ht, Finset.sum_add_distrib]

theorem posSemidef_complexify {n : ℕ} (A : Mat n ℝ) (hA : A.PosSemidef) :
    (A.map Complex.ofReal).PosSemidef := by
  have hh := isHermitian_complexify A hA.isHermitian
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro w
  apply RCLike.nonneg_iff.2
  refine ⟨?_, hh.im_star_dotProduct_mulVec_self w⟩
  rw [show RCLike.re (dotProduct (star w) (A.map Complex.ofReal *ᵥ w)) =
    (dotProduct (star w) (A.map Complex.ofReal *ᵥ w)).re from rfl, complex_quadratic_re]
  exact add_nonneg (by simpa using hA.dotProduct_mulVec_nonneg (fun i => (w i).re))
    (by simpa using hA.dotProduct_mulVec_nonneg (fun i => (w i).im))

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.ComplexPositive ----
namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Matrix

universe u

namespace Paper256

theorem qMatrix_transpose {R : Type u} [CommRing R] (y : Fin 3 → R) :
    (qMatrix y)ᵀ = qMatrix y := by
  ext i j
  by_cases h : i = j
  · subst j; rfl
  · simp [qMatrix, h, Ne.symm h, mul_comm]

theorem phi_transpose {R : Type u} [CommRing R] (y : Fin 3 → R) (X : Mat 4 R) :
    phi y Xᵀ = (phi y X)ᵀ := by
  have hQ (i j : Fin 3) : qMatrix y j i = qMatrix y i j :=
    congrFun (congrFun (qMatrix_transpose y) i) j
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  · change Matrix.trace (qMatrix y * (X.submatrix Fin.succ Fin.succ)ᵀ) =
      Matrix.trace (qMatrix y * X.submatrix Fin.succ Fin.succ)
    conv_lhs => rw [← qMatrix_transpose y]
    rw [← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm]
  · simp only [phi, Fin.cases_zero, Fin.cases_succ, Matrix.transpose_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hQ]
    ring
  · simp only [phi, Fin.cases_zero, Fin.cases_succ, Matrix.transpose_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hQ]
    ring
  · simp only [phi, Fin.cases_succ, Matrix.transpose_apply]
    rw [hQ]

theorem phi_conjTranspose (y : Fin 3 → ℝ) (X : Mat 4 ℂ) :
    (phi (fun i => (y i : ℂ)) X)ᴴ = phi (fun i => (y i : ℂ)) Xᴴ := by
  change ((phi (fun i => (y i : ℂ)) X)ᵀ).map (starRingEnd ℂ) = _
  rw [← phi_transpose, phi_map]
  have hy : (fun i => (starRingEnd ℂ) (y i : ℂ)) = (fun i => (y i : ℂ)) :=
    funext fun i => Complex.conj_ofReal (y i)
  rw [hy]
  rfl

theorem phi_complex_rank_one (y : Fin 3 → ℝ) (u v : Fin 4 → ℂ) :
    dotProduct (star u)
        (phi (fun i => (y i : ℂ)) (vecMulVec v (star v)) *ᵥ u) =
      dotProduct (star (fun i : Fin 3 => v 0 * u i.succ - u 0 * v i.succ))
        (qMatrix (fun i => (y i : ℂ)) *ᵥ
          (fun i : Fin 3 => v 0 * u i.succ - u 0 * v i.succ)) := by
  simp [dotProduct, mulVec, phi, qMatrix, Matrix.trace, Matrix.mul_apply,
    Matrix.submatrix, vecMulVec, Fin.sum_univ_succ]
  ring

theorem phi_complex_outer_posSemidef (y : Fin 3 → ℝ) (v : Fin 4 → ℂ) :
    (phi (fun i => (y i : ℂ)) (vecMulVec v (star v))).PosSemidef := by
  have hq : (qMatrix (fun i => (y i : ℂ))).PosSemidef := by
    have h := posSemidef_complexify (qMatrix y) (qMatrix_posSemidef y)
    change ((qMatrix y).map (algebraMap ℝ ℂ)).PosSemidef at h
    rw [qMatrix_map] at h
    exact h
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · show (phi (fun i => (y i : ℂ)) (vecMulVec v (star v)))ᴴ = _
    rw [phi_conjTranspose, (posSemidef_vecMulVec_self_star v).isHermitian.eq]
  · intro u
    rw [phi_complex_rank_one]
    exact hq.dotProduct_mulVec_nonneg _

theorem phi_complex_posSemidef (y : Fin 3 → ℝ) (X : Mat 4 ℂ) (hX : X.PosSemidef) :
    (phi (fun i => (y i : ℂ)) X).PosSemidef := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  have hx : X = ∑ i, vecMulVec (star (B i)) (B i) := by
    rw [hB]
    ext i j
    simp [Matrix.mul_apply, Matrix.sum_apply, vecMulVec]
  rw [hx]
  change ((phiLinear (fun i => (y i : ℂ))) (∑ i, vecMulVec (star (B i)) (B i))).PosSemidef
  rw [map_sum]
  apply Matrix.posSemidef_sum
  intro i _
  change (phi (fun i => (y i : ℂ)) (vecMulVec (star (B i)) (B i))).PosSemidef
  simpa only [star_star] using phi_complex_outer_posSemidef y (star (B i))

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Matrix


theorem solution : type_of% @_root_.OAI.Paper256.phi_complex_posSemidef := @_root_.OAI.Paper256.phi_complex_posSemidef
