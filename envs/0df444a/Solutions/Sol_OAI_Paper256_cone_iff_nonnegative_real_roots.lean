-- Prove2me | solution 1 for OAI.Paper256.cone_iff_nonnegative_real_roots
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:29:12.252744+00:00
-- url     : https://prove2.me/submissions/4675396d-f61b-4735-94e7-f927b11173b5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/ConeRoots.lean:L10-L25
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.cone_iff_nonnegative_real_roots. The node keeps its source
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
import Theorems.Thm_OAI_Paper256_phi_complex_posSemidef
import Theorems.Thm_OAI_Paper256_positive_map_resolvent_isUnit

-- ---- from OAI.Analysis.HyperbolicCones.MatrixBasic ----
namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

universe u

namespace Paper256

theorem matrixValue_inverse {K : Type u} [Field K] (X Z : Mat 4 K) (y : Fin 3 → K)
    (hX : IsUnit (Matrix.det X)) :
    matrixValue X Z y = Matrix.det X ^ 4 * Matrix.det (Z - phi y X⁻¹) := by
  have hadj : X.adjugate = X.det • X⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hX, one_smul]
  rw [matrixValue, hadj, phi_smul, ← smul_sub, Matrix.det_smul]
  rfl

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

theorem matrixValue_map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (X Z : Mat 4 R) (y : Fin 3 → R) :
    f (matrixValue X Z y) = matrixValue (X.map f) (Z.map f) (fun i => f (y i)) := by
  unfold matrixValue
  rw [f.map_det]
  congr 1
  have hp := phi_map f y X.adjugate
  have ha : X.adjugate.map f = (X.map f).adjugate := f.map_adjugate X
  rw [ha] at hp
  ext i j
  have hp' := congrFun (congrFun hp i) j
  simpa [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, f.map_det] using
    congrArg (fun z => f X.det * f (Z i j) - z) hp'

theorem symmetricCoordinates_map {R : Type u} {S : Type v} (f : R → S) (v : SymIndex → R) :
    (symmetricCoordinates v).map f = symmetricCoordinates (fun i => f (v i)) := by
  ext i j
  by_cases h : i ≤ j <;> simp [symmetricCoordinates, h]

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

theorem complex_resolvent_isUnit {n : ℕ} (A : Mat n ℝ) (hA : A.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) : IsUnit (z • (1 : Mat n ℂ) - A.map Complex.ofReal) := by
  by_contra hn
  apply hz
  apply (isHermitian_complexify A hA).isSelfAdjoint.im_eq_zero_of_mem_spectrum
  simpa only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one] using hn

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

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.LineEvaluation ----
namespace OAI

noncomputable section

open Matrix Polynomial MvPolynomial
open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

theorem polynomial_eval₂ {K : Type u} [CommRing K] (f : ℝ →+* K) (v : Coord → K) :
    MvPolynomial.eval₂ f v polynomial = matrixValue
      (symmetricCoordinates fun ij => v (Sum.inl (Sum.inl ij)))
      (symmetricCoordinates fun ij => v (Sum.inl (Sum.inr ij)))
      (fun i => v (Sum.inr i)) := by
  change (MvPolynomial.eval₂Hom f v) (matrixValue _ _ _) = _
  rw [matrixValue_map, symmetricCoordinates_map, symmetricCoordinates_map]
  simp

theorem symmetricCoordinates_affine {K : Type u} [CommRing K]
    (f : ℝ →+* K) (X : Sym 4) (t : K) :
    symmetricCoordinates (fun ij => f ((1 : Mat 4 ℝ) ij.val.1 ij.val.2) * t -
      f ((X : Mat 4 ℝ) ij.val.1 ij.val.2)) =
        t • (1 : Mat 4 K) - (X : Mat 4 ℝ).map f := by
  classical
  ext i j
  have hX : (X : Mat 4 ℝ).IsHermitian := X.property
  have hsym : (X : Mat 4 ℝ) j i = (X : Mat 4 ℝ) i j := by
    simpa using hX.apply i j
  by_cases h : i ≤ j
  · simp [symmetricCoordinates, h, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
      mul_comm]
  · simp [symmetricCoordinates, h, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
      eq_comm, hsym, mul_comm]

theorem linePolynomial_eval₂ {K : Type u} [CommRing K]
    (f : ℝ →+* K) (X Z : Sym 4) (y : Fin 3 → ℝ) (t : K) :
    (linePolynomial ((X, Z), y)).eval₂ f t = matrixValue
      (t • (1 : Mat 4 K) - (X : Mat 4 ℝ).map f)
      (t • (1 : Mat 4 K) - (Z : Mat 4 ℝ).map f)
      (fun i => -f (y i)) := by
  let g := Polynomial.eval₂RingHom f t
  have hg : g.comp Polynomial.C = f := by
    ext a
    simp [g]
  change g ((MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (coordinates basePoint i) * Polynomial.X -
      Polynomial.C (coordinates ((X, Z), y) i))) polynomial) = _
  rw [MvPolynomial.map_eval₂Hom, hg]
  change MvPolynomial.eval₂ f _ polynomial = _
  rw [polynomial_eval₂]
  simp only [g, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  change matrixValue
    (symmetricCoordinates (fun ij => f ((1 : Mat 4 ℝ) ij.val.1 ij.val.2) * t -
      f ((X : Mat 4 ℝ) ij.val.1 ij.val.2)))
    (symmetricCoordinates (fun ij => f ((1 : Mat 4 ℝ) ij.val.1 ij.val.2) * t -
      f ((Z : Mat 4 ℝ) ij.val.1 ij.val.2)))
    (fun i => f 0 * t - f (y i)) = _
  rw [symmetricCoordinates_affine, symmetricCoordinates_affine]
  simp

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.Hyperbolicity ----
namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator ComplexOrder
open Matrix

namespace Paper256

theorem matrixValue_nonzero_nonreal (X Z : Sym 4) (y : Fin 3 → ℝ)
    (z : ℂ) (hz : z.im ≠ 0) :
    matrixValue (z • (1 : Mat 4 ℂ) - (X : Mat 4 ℝ).map Complex.ofReal)
      (z • (1 : Mat 4 ℂ) - (Z : Mat 4 ℝ).map Complex.ofReal)
      (fun i => -(y i : ℂ)) ≠ 0 := by
  have hu := complex_resolvent_isUnit (X : Mat 4 ℝ) X.property z hz
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hh := positive_map_resolvent_isUnit
    ((X : Mat 4 ℝ).map Complex.ofReal) ((Z : Mat 4 ℝ).map Complex.ofReal)
    (isHermitian_complexify _ X.property) (isHermitian_complexify _ Z.property)
    (phiLinear (fun i => ((-y) i : ℂ)))
    (fun M => phi_conjTranspose (-y) M)
    (fun M hM => phi_complex_posSemidef (-y) M hM) z hz
  change IsUnit (z • (1 : Mat 4 ℂ) - (Z : Mat 4 ℝ).map Complex.ofReal -
    phi (fun i => ((-y) i : ℂ))
      ((z • (1 : Mat 4 ℂ) - (X : Mat 4 ℝ).map Complex.ofReal)⁻¹)) at hh
  simp only [Pi.neg_apply, Complex.ofReal_neg] at hh
  rw [matrixValue_inverse _ _ _ hd]
  exact mul_ne_zero (pow_ne_zero 4 hd.ne_zero)
    ((Matrix.isUnit_iff_isUnit_det _).1 hh).ne_zero

theorem linePolynomial_complex_roots_real (x : Ambient) (z : ℂ)
    (hz : (linePolynomial x).aeval z = 0) : z.im = 0 := by
  rcases x with ⟨⟨X, Z⟩, y⟩
  by_contra hn
  apply matrixValue_nonzero_nonreal X Z y z hn
  change (linePolynomial ((X, Z), y)).eval₂ (algebraMap ℝ ℂ) z = 0 at hz
  rw [linePolynomial_eval₂] at hz
  exact hz

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.LineShift ----
namespace OAI

noncomputable section

namespace Paper256

theorem real_aeval (p : Polynomial ℝ) (t : ℝ) :
    p.aeval (t : ℂ) = Complex.ofReal (p.eval t) :=
  Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval t p

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.ConeRoots ----
namespace OAI

noncomputable section

namespace Paper256

theorem cone_iff_nonnegative_real_roots (x : Ambient) : x ∈ cone ↔
    ∀ t : ℝ, (linePolynomial x).eval t = 0 → 0 ≤ t := by
  constructor
  · intro hx t ht
    have hc : (linePolynomial x).aeval (t : ℂ) = 0 := by rw [real_aeval, ht]; rfl
    exact (hx (t : ℂ) hc).2
  · intro hx z hz
    have hi := linePolynomial_complex_roots_real x z hz
    refine ⟨hi, hx z.re ?_⟩
    have he : (z.re : ℂ) = z := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using hi.symm
    have hr : Complex.ofReal ((linePolynomial x).eval z.re) = 0 := by
      rw [← real_aeval, he, hz]
    exact_mod_cast hr

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256


theorem solution : type_of% @_root_.OAI.Paper256.cone_iff_nonnegative_real_roots := @_root_.OAI.Paper256.cone_iff_nonnegative_real_roots
