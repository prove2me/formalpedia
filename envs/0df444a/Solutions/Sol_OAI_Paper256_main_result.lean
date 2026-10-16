-- Prove2me | solution 1 for OAI.Paper256.main_result
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:09:10.251682+00:00
-- url     : https://prove2.me/submissions/e694821e-c22a-485f-8ba7-ea476821fc0e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/Main.lean:L23-L34
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.Paper256.main_result.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_Paper256_main_result) verbatim and is proved by it.
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
import Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSmooth
import Definitions.Def_OAI_Analysis_HyperbolicCones_TangentBasic
import Theorems.Thm_OAI_Paper256_BlockPencil_normalized_exists
import Theorems.Thm_OAI_Paper256_NormalizedPencil_tangent_identity
import Theorems.Thm_OAI_Paper256_basePoint_mem_interior_cone
import Theorems.Thm_OAI_Paper256_cone_positive_slice_of_inverse_order
import Theorems.Thm_OAI_Paper256_cone_zero_slice
import Theorems.Thm_OAI_Paper256_impossible_of_tangent_formula
import Theorems.Thm_OAI_Paper256_interior_line_pair
import Theorems.Thm_OAI_Paper256_pencil_compression_positive
import Theorems.Thm_OAI_Paper256_phi_complex_posSemidef
import Theorems.Thm_OAI_Paper256_polynomial_homogeneous
import Theorems.Thm_OAI_Paper256_positive_map_resolvent_isUnit
import Theorems.Thm_OAI_Paper256_rawBlockPencil_exists

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

-- ---- from OAI.Analysis.HyperbolicCones.PencilKernel ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

universe u

namespace Paper256

theorem posSemidef_pair_kernel {n : ℕ} {A H : Mat n ℝ}
    (hplus : (A + H).PosSemidef) (hminus : (A - H).PosSemidef)
    (v : Fin n → ℝ) (hv : A *ᵥ v = 0) : H *ᵥ v = 0 := by
  have hp := hplus.dotProduct_mulVec_nonneg v
  have hm := hminus.dotProduct_mulVec_nonneg v
  simp only [star_trivial, add_mulVec, sub_mulVec, hv, zero_add, zero_sub,
    dotProduct_neg] at hp hm
  have hz : v ⬝ᵥ ((A + H) *ᵥ v) = 0 := by
    simp only [add_mulVec, hv, zero_add]
    linarith
  have hh := (hplus.dotProduct_mulVec_zero_iff v).mp (by simpa only [star_trivial] using hz)
  simpa only [add_mulVec, hv, zero_add] using hh

theorem pencil_common_kernel {N : ℕ} (K : Set Ambient)
    (L : Ambient →ₗ[ℝ] Sym N) (hL : K = {x | (L x : Mat N ℝ).PosSemidef})
    (he : basePoint ∈ interior K) (x : Ambient) (v : Fin N → ℝ)
    (hv : (L basePoint : Mat N ℝ) *ᵥ v = 0) :
    (L x : Mat N ℝ) *ᵥ v = 0 := by
  obtain ⟨ε, hε, hp, hm⟩ := interior_line_pair he x
  rw [hL] at hp hm
  have hp' : ((L basePoint : Mat N ℝ) + ε • (L x : Mat N ℝ)).PosSemidef := by
    simpa using hp
  have hm' : ((L basePoint : Mat N ℝ) - ε • (L x : Mat N ℝ)).PosSemidef := by
    simpa using hm
  have hz := posSemidef_pair_kernel hp' hm' v hv
  rw [smul_mulVec] at hz
  exact (smul_eq_zero.mp hz).resolve_left hε.ne'

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.PencilRepresentation ----
namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem zero_slice_proper (K : Set Ambient)
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    (((-1, 1), 0) : Ambient) ∉ K := by
  intro h
  have hp := ((hzero (-1) 1).mp h).1
  have hd := hp.diag_nonneg (i := (0 : Fin 4))
  norm_num at hd

theorem representation_compression {n : ℕ} (K : Set Ambient)
    (L : Ambient →ₗ[ℝ] Sym n) (hL : K = {x | (L x : Mat n ℝ).PosSemidef})
    (he : basePoint ∈ interior K) (hproper : ∃ x : Ambient, x ∉ K) :
    ∃ m : ℕ, 0 < m ∧ ∃ C : Ambient →ₗ[ℝ] Sym m,
      (C basePoint : Mat m ℝ).PosDef ∧ K = {x | (C x : Mat m ℝ).PosSemidef} := by
  have hb : (L basePoint : Mat n ℝ).PosSemidef := by
    have h := interior_subset he
    rwa [hL] at h
  have hn : ∃ x : Ambient, ¬(L x : Mat n ℝ).PosSemidef := by
    simpa only [hL, mem_ofPred_eq] using hproper
  obtain ⟨m, hm, C, hC, hrep⟩ := pencil_compression_positive L basePoint hb
    (pencil_common_kernel K L hL he) hn
  refine ⟨m, hm, C, hC, ?_⟩
  ext x
  rw [hL]
  exact hrep x

theorem representation_compression_of_zero_slice {n : ℕ} (K : Set Ambient)
    (L : Ambient →ₗ[ℝ] Sym n) (hL : K = {x | (L x : Mat n ℝ).PosSemidef})
    (he : basePoint ∈ interior K)
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    ∃ m : ℕ, 0 < m ∧ ∃ C : Ambient →ₗ[ℝ] Sym m,
      (C basePoint : Mat m ℝ).PosDef ∧ K = {x | (C x : Mat m ℝ).PosSemidef} :=
  representation_compression K L hL he ⟨(((-1, 1), 0) : Ambient), zero_slice_proper K hzero⟩

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.PencilSplit ----
namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem blockPencil_exists (K : Set Ambient) (m : ℕ) (_hm : 0 < m)
    (C : Ambient →ₗ[ℝ] Sym m) (hC : (C basePoint : Mat m ℝ).PosDef)
    (hrep : K = {x | (C x : Mat m ℝ).PosSemidef})
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    Nonempty (BlockPencil K) := by
  obtain ⟨P⟩ := rawBlockPencil_exists K C hC hrep hzero
  exact ⟨P.normalize⟩

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.Coordinates ----
namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

namespace Paper256

theorem symIndex_card : Fintype.card SymIndex = 10 := by decide

theorem symmetric_finrank : Module.finrank ℝ (Sym 4) = 10 := by
  rw [symmetricCoordinateEquiv.finrank_eq]
  simp [symIndex_card]

theorem ambient_finrank : Module.finrank ℝ Ambient = 23 := by
  simp [Ambient, Module.finrank_prod, symmetric_finrank]

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

theorem symmetricCoordinates_entries (X : Sym 4) :
    symmetricCoordinates (fun ij => (X : Mat 4 ℝ) ij.val.1 ij.val.2) = (X : Mat 4 ℝ) := by
  exact congrArg Subtype.val (symmetricCoordinateEquiv.left_inv X)

theorem polynomial_evaluation (X Z : Sym 4) (y : Fin 3 → ℝ) :
    MvPolynomial.eval (coordinates ((X, Z), y)) polynomial =
      matrixValue (X : Mat 4 ℝ) (Z : Mat 4 ℝ) y := by
  let f := MvPolynomial.eval₂Hom (RingHom.id ℝ) (coordinates ((X, Z), y))
  change f (matrixValue _ _ _) = _
  rw [matrixValue_map, symmetricCoordinates_map, symmetricCoordinates_map]
  simp [f, coordinates, symmetricCoordinates_entries]

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

-- ---- from OAI.Analysis.HyperbolicCones.PolynomialBasic ----
namespace OAI

noncomputable section

open Matrix MvPolynomial
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem polynomial_basePoint : MvPolynomial.eval (coordinates basePoint) polynomial = 1 := by
  change MvPolynomial.eval (coordinates (((1 : Sym 4), 1), 0)) polynomial = 1
  rw [polynomial_evaluation]
  simp [matrixValue, phi_zero_parameter]

theorem polynomial_ne_zero : polynomial ≠ 0 := by
  intro h
  have hp := polynomial_basePoint
  simp [h] at hp

theorem polynomial_totalDegree : polynomial.totalDegree = 20 :=
  polynomial_homogeneous.totalDegree polynomial_ne_zero

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.InverseOrder ----
namespace OAI

/-! Simultaneous spectral comparison of a positive matrix and its scalar shifts. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix
namespace Paper256

theorem matrix_cfc_affine {n : ℕ} (H : Sym n) (a b : ℝ) :
    cfc (fun x : ℝ => a + b * x) (H : Mat n ℝ) =
      a • (1 : Mat n ℝ) + b • (H : Mat n ℝ) := by
  calc
    _ = algebraMap ℝ (Mat n ℝ) a + cfc (fun x : ℝ => b * x) (H : Mat n ℝ) :=
      cfc_const_add a (fun x : ℝ => b * x) (H : Mat n ℝ)
        (H.val.finite_real_spectrum.continuousOn _) H.property
    _ = _ := by
      have hmul : cfc (fun x : ℝ => b * x) (H : Mat n ℝ) = b • (H : Mat n ℝ) :=
        cfc_const_mul_id b (H : Mat n ℝ) H.property
      rw [hmul, Algebra.algebraMap_eq_smul_one]

theorem posDef_inverse_eq_cfc {n : ℕ} (H : Sym n) (hH : (H : Mat n ℝ).PosDef) :
    (H : Mat n ℝ)⁻¹ = cfc (fun x : ℝ => x⁻¹) (H : Mat n ℝ) := by
  have hi := cfc_inv (fun x : ℝ => x) (H : Mat n ℝ)
    (fun x hx => (posDef_real_spectrum_positive hH hx).ne')
    (H.val.finite_real_spectrum.continuousOn _) H.property
  have hid : cfc (fun x : ℝ => x) (H : Mat n ℝ) = (H : Mat n ℝ) :=
    cfc_id' ℝ (H : Mat n ℝ) H.property
  rw [hid, ← Matrix.nonsing_inv_eq_ringInverse] at hi
  exact hi.symm

theorem posDef_shift_inverse_eq_cfc {n : ℕ} (H : Sym n)
    (hH : (H : Mat n ℝ).PosDef) (t : ℝ) (ht : 0 ≤ t) :
    ((H : Mat n ℝ) + t • 1)⁻¹ =
      cfc (fun x : ℝ => (x + t)⁻¹) (H : Mat n ℝ) := by
  have hi := cfc_inv (fun x : ℝ => x + t) (H : Mat n ℝ)
    (fun x hx => (add_pos_of_pos_of_nonneg (posDef_real_spectrum_positive hH hx) ht).ne')
    (H.val.finite_real_spectrum.continuousOn _) H.property
  have hshift : cfc (fun x : ℝ => x + t) (H : Mat n ℝ) =
      (H : Mat n ℝ) + t • 1 := by
    simpa only [add_comm, one_mul, one_smul] using matrix_cfc_affine H t 1
  rw [hshift, ← Matrix.nonsing_inv_eq_ringInverse] at hi
  exact hi.symm

theorem posDef_inverse_sub_shift_inverse_posSemidef {n : ℕ} (H : Sym n)
    (hH : (H : Mat n ℝ).PosDef) (t : ℝ) (ht : 0 ≤ t) :
    ((H : Mat n ℝ)⁻¹ - ((H : Mat n ℝ) + t • 1)⁻¹).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [sub_nonneg, posDef_inverse_eq_cfc H hH, posDef_shift_inverse_eq_cfc H hH t ht]
  apply cfc_mono _ (H.val.finite_real_spectrum.continuousOn _)
    (H.val.finite_real_spectrum.continuousOn _)
  intro x hx
  exact inv_anti₀ (posDef_real_spectrum_positive hH hx) (le_add_of_nonneg_right ht)

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.ConePositive ----
namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem cone_positive_slice (X Z : Sym 4) (y : Fin 3 → ℝ) (hX : (X : Mat 4 ℝ).PosDef) :
    ((X, Z), y) ∈ cone ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef := by
  have h := cone_positive_slice_of_inverse_order X Z y hX
    (fun t ht => posDef_inverse_sub_shift_inverse_posSemidef X hX t ht)
  simp only [coneResidual, zero_smul, add_zero] at h
  change ((X, Z), y) ∈ cone ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef at h
  exact h

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.Pencil ----
namespace OAI

noncomputable section

namespace Paper256

theorem pencil_normalization (N : ℕ) (_hN : 0 < N) (L : Ambient →ₗ[ℝ] Sym N)
    (hL : cone = {x | (L x : Mat N ℝ).PosSemidef}) : Nonempty NormalizedPencil := by
  obtain ⟨m, hm, C, hC, hrep⟩ := representation_compression_of_zero_slice cone L hL
    basePoint_mem_interior_cone cone_zero_slice
  obtain ⟨P⟩ := blockPencil_exists cone m hm C hC hrep cone_zero_slice
  exact P.normalized_exists cone_positive_slice

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.TangentObstruction ----
namespace OAI

namespace Paper256

theorem NormalizedPencil.impossible (P : NormalizedPencil) : False := by
  obtain ⟨v, T, hv, hv0, hformula⟩ := P.tangent_identity
  exact impossible_of_tangent_formula P v T hv hv0 hformula

end Paper256

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.Main ----
namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem cone_not_spectrahedral (N : ℕ) (hN : 0 < N) (L : Ambient →ₗ[ℝ] Sym N) :
    cone ≠ {x | (L x : Mat N ℝ).PosSemidef} := by
  intro hL
  obtain ⟨P⟩ := pencil_normalization N hN L hL
  exact P.impossible

/-- An explicit degree-20 hyperbolic polynomial in a 23-dimensional real space
whose closed hyperbolicity cone is not spectrahedral. -/
theorem main_result :
    Module.finrank ℝ Ambient = 23 ∧
    polynomial.IsHomogeneous 20 ∧
    polynomial.totalDegree = 20 ∧
    MvPolynomial.eval (coordinates basePoint) polynomial = 1 ∧
    (∀ (x : Ambient) (z : ℂ), (linePolynomial x).aeval z = 0 → z.im = 0) ∧
    ∀ (N : ℕ) (_hN : 0 < N) (L : Ambient →ₗ[ℝ] Sym N),
      cone ≠ {x | (L x : Mat N ℝ).PosSemidef} := by
  exact ⟨ambient_finrank, polynomial_homogeneous, polynomial_totalDegree,
    polynomial_basePoint, linePolynomial_complex_roots_real, cone_not_spectrahedral⟩

end Paper256

end

end OAI

-- ---- mission target ----
open OAI OAI.Paper256
open scoped Matrix.Norms.L2Operator
universe u
open Matrix

theorem solution :
    Module.finrank ℝ Ambient = 23 ∧
    polynomial.IsHomogeneous 20 ∧
    polynomial.totalDegree = 20 ∧
    MvPolynomial.eval (coordinates basePoint) polynomial = 1 ∧
    (∀ (x : Ambient) (z : ℂ), (linePolynomial x).aeval z = 0 → z.im = 0) ∧
    ∀ (N : ℕ) (_hN : 0 < N) (L : Ambient →ₗ[ℝ] Sym N),
      cone ≠ {x | (L x : Mat N ℝ).PosSemidef} := by
  first
    | exact OAI.Paper256.main_result
    | (apply OAI.Paper256.main_result <;> assumption)
    | (intros; apply OAI.Paper256.main_result <;> assumption)
