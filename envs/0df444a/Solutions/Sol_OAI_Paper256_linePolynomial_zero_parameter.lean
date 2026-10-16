-- Prove2me | solution 1 for OAI.Paper256.linePolynomial_zero_parameter
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:37:24.223832+00:00
-- url     : https://prove2.me/submissions/9c4a10c6-2005-4edd-b0a8-e9d096711569

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/ZeroPolynomial.lean:L20-L36
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.linePolynomial_zero_parameter. The node keeps its source
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
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix

-- ---- from OAI.Analysis.HyperbolicCones.MatrixBasic ----
namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

universe u

namespace Paper256

theorem qMatrix_smul {R : Type u} [CommRing R] (y : Fin 3 → R) (s : R) :
    qMatrix (s • y) = s ^ 2 • qMatrix y := by
  ext i j
  by_cases h : i = j <;> simp [qMatrix, h, mul_pow] <;> ring

theorem phi_scaling_general {R : Type u} [CommRing R]
    (y : Fin 3 → R) (s : R) (X : Mat 4 R) :
    phi (s • y) X = s ^ 2 • phi y X := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [phi, qMatrix_smul, Matrix.trace, Matrix.mul_apply, Matrix.submatrix,
      ← Finset.mul_sum, mul_left_comm, mul_assoc]

theorem phi_zero_parameter {R : Type u} [CommRing R] (X : Mat 4 R) :
    phi (0 : Fin 3 → R) X = 0 := by
  simpa using phi_scaling_general (0 : Fin 3 → R) 0 X

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

-- ---- from OAI.Analysis.HyperbolicCones.ZeroPolynomial ----
namespace OAI

noncomputable section

open Matrix Polynomial
open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

theorem matrixValue_zero_parameter {K : Type u} [CommRing K] (X Z : Mat 4 K) :
    matrixValue X Z (0 : Fin 3 → K) = X.det ^ 4 * Z.det := by
  rw [matrixValue, phi_zero_parameter, sub_zero, Matrix.det_smul]
  rfl

theorem linePolynomial_zero_parameter (X Z : Sym 4) :
    linePolynomial ((X, Z), (0 : Fin 3 → ℝ)) =
      (X : Mat 4 ℝ).charpoly ^ 4 * (Z : Mat 4 ℝ).charpoly := by
  apply Polynomial.funext
  intro t
  have he := linePolynomial_eval₂ (RingHom.id ℝ) X Z (0 : Fin 3 → ℝ) t
  simp only [Polynomial.eval₂_id, RingHom.id_apply, Pi.zero_apply,
    neg_zero] at he
  rw [he]
  change matrixValue (t • 1 - (X : Mat 4 ℝ)) (t • 1 - (Z : Mat 4 ℝ))
    (0 : Fin 3 → ℝ) = _
  rw [matrixValue_zero_parameter]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Matrix.eval_charpoly]
  have hs : Matrix.scalar (Fin 4) t = t • (1 : Mat 4 ℝ) := by
    ext i j
    simp [Matrix.scalar, Matrix.diagonal, Matrix.one_apply, Matrix.smul_apply]
  rw [hs]

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Matrix Polynomial
open scoped Matrix.Norms.L2Operator


theorem solution : type_of% @_root_.OAI.Paper256.linePolynomial_zero_parameter := @_root_.OAI.Paper256.linePolynomial_zero_parameter
