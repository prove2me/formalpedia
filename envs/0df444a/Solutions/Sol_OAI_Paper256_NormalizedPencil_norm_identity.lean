-- Prove2me | solution 1 for OAI.Paper256.NormalizedPencil.norm_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:02:46.843074+00:00
-- url     : https://prove2.me/submissions/e3669ae7-52b2-429c-a5b2-585b53b14e51

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/NormIdentity.lean:L16-L65
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.NormalizedPencil.norm_identity. The node keeps its source
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
import Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSmooth
import Definitions.Def_OAI_Analysis_HyperbolicCones_TangentBasic
import Theorems.Thm_OAI_Paper256_NormalizedPencil_positive_threshold
import Theorems.Thm_OAI_Paper256_inverse_sqrt_affine_scalar_tendsto
import Theorems.Thm_OAI_Paper256_kernelProjection_eq_cfc
import Theorems.Thm_OAI_Paper256_matrix_cfc_tendsto
import Theorems.Thm_OAI_Paper256_posSemidef_three_of_principal_minors

-- ---- from OAI.Analysis.HyperbolicCones.MatrixBasic ----
namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

universe u

namespace Paper256

theorem phi_rank_one (y : Fin 3 → ℝ) (u v : Vec 4) :
    dotProduct (fun i => u i) (phi y (outer v) *ᵥ (fun i => u i)) =
      choiLam (wedgeCoordinates v u) y := by
  simp [dotProduct, mulVec, phi, Matrix.trace, Matrix.mul_apply, Matrix.submatrix,
    qMatrix, outer, wedgeCoordinates, choiLam, Fin.sum_univ_succ]
  ring

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.FormBasic ----
namespace OAI

/-! Exact identities for the Choi–Lam form. -/

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

universe u

namespace Paper256

theorem zMatrix_isHermitian (z : Fin 3 → ℝ) : (zMatrix z).IsHermitian := by
  show (zMatrix z)ᴴ = zMatrix z
  ext i j
  by_cases hij : i = j
  · subst j
    simp [zMatrix, Matrix.conjTranspose_apply]
  · simp [zMatrix, Matrix.conjTranspose_apply, hij, Ne.symm hij, mul_comm]

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

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.KernelSpectrum ----
namespace OAI

/-! Spectral identities for the inverse square root. -/

noncomputable section

open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix

namespace Paper256

theorem inverseSquareRoot_commute {n : ℕ} (H : Sym n) :
    Commute (inverseSquareRoot H) (H : Mat n ℝ) := by
  rw [inverseSquareRoot_eq_cfc]
  have hid : cfc (fun x : ℝ => x) (H : Mat n ℝ) = (H : Mat n ℝ) :=
    cfc_id' ℝ (H : Mat n ℝ) H.property
  simpa only [hid] using
    cfc_commute_cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (fun x => x) (H : Mat n ℝ)

theorem inverseSquareRoot_sq {n : ℕ} (H : Sym n) (hH : (H : Mat n ℝ).PosDef) :
    inverseSquareRoot H * inverseSquareRoot H = (H : Mat n ℝ)⁻¹ := by
  have h := inverseSquareRoot_conjugate H hH
  rw [inverseSquareRoot_transpose] at h
  have hi : (inverseSquareRoot H * inverseSquareRoot H) * (H : Mat n ℝ) = 1 := by
    calc
      _ = inverseSquareRoot H * (inverseSquareRoot H * (H : Mat n ℝ)) := mul_assoc _ _ _
      _ = inverseSquareRoot H * ((H : Mat n ℝ) * inverseSquareRoot H) := by
        rw [(inverseSquareRoot_commute H).eq]
      _ = 1 := by simpa only [mul_assoc] using h
  exact (Matrix.inv_eq_left_inv hi).symm

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

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.OperatorEntries ----
namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

namespace Paper256

theorem operatorNorm_eq_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    operatorNorm A = ‖A‖ := rfl

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.KernelLimit ----
namespace OAI

/-! The inverse-square-root kernel limit for every finite positive semidefinite matrix. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Filter Topology
namespace Paper256

theorem inverseSquareRoot_affine_eq_cfc {n : ℕ} (H : Sym n) (t : ℝ) :
    inverseSquareRoot (1 + (t - 1) • H) =
      cfc (fun x : ℝ => (Real.sqrt (1 + (t - 1) * x))⁻¹) (H : Mat n ℝ) := by
  have haff : cfc (fun x : ℝ => 1 + (t - 1) * x) (H : Mat n ℝ) =
      ((1 + (t - 1) • H : Sym n) : Mat n ℝ) := by
    simpa using matrix_cfc_affine H 1 (t - 1)
  have hcomp := cfc_comp (fun x : ℝ => (Real.sqrt x)⁻¹)
    (fun x : ℝ => 1 + (t - 1) * x) (H : Mat n ℝ) H.property
    ((H.val.finite_real_spectrum.image _).continuousOn _)
    (H.val.finite_real_spectrum.continuousOn _)
  rw [haff] at hcomp
  exact (inverseSquareRoot_eq_cfc _).trans hcomp.symm

theorem inverseSquareRoot_affine_tendsto {n : ℕ} (H : Sym n)
    (hH : (H : Mat n ℝ).PosSemidef) :
    Tendsto (fun t : ℝ => inverseSquareRoot (1 + (t - 1) • H)) atTop
      (𝓝 (kernelProjection (H : Mat n ℝ))) := by
  have hc := matrix_cfc_tendsto (H : Mat n ℝ) H.property
    (fun t x : ℝ => (Real.sqrt (1 + (t - 1) * x))⁻¹)
    (fun x : ℝ => if x = 0 then 1 else 0)
    (fun i => inverse_sqrt_affine_scalar_tendsto _ (hH.eigenvalues_nonneg i))
  simpa only [← inverseSquareRoot_affine_eq_cfc, ← kernelProjection_eq_cfc] using hc

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.NormLimits ----
namespace OAI

/-! The positive affine paths used in the norm identity and their matrix limits. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Filter Topology
universe u

namespace Paper256

theorem matrix_mul_tendsto {m n k : ℕ} {T : Type u} {L : Filter T}
    {A : T → Matrix (Fin m) (Fin n) ℝ} {B : T → Matrix (Fin n) (Fin k) ℝ}
    {A₀ : Matrix (Fin m) (Fin n) ℝ} {B₀ : Matrix (Fin n) (Fin k) ℝ}
    (hA : Tendsto A L (𝓝 A₀)) (hB : Tendsto B L (𝓝 B₀)) :
    Tendsto (fun t => A t * B t) L (𝓝 (A₀ * B₀)) :=
  ((continuous_fst.matrix_mul continuous_snd).tendsto (A₀, B₀)).comp
    (hA.prodMk_nhds hB)

theorem affine_posDef {n : ℕ} (H : Sym n) (hH : (H : Mat n ℝ).PosSemidef)
    (t : ℝ) (ht : 1 ≤ t) :
    ((1 + (t - 1) • H : Sym n) : Mat n ℝ).PosDef := by
  change ((1 : Mat n ℝ) + (t - 1) • (H : Mat n ℝ)).PosDef
  exact Matrix.PosDef.one.add_posSemidef (hH.smul (sub_nonneg.mpr ht))

theorem positive_unital_map_affine_posDef {m n : ℕ} (D : Sym m →ₗ[ℝ] Sym n)
    (hD : ∀ H : Sym m, (H : Mat m ℝ).PosSemidef → (D H : Mat n ℝ).PosSemidef)
    (hI : D 1 = 1) (H : Sym m) (hH : (H : Mat m ℝ).PosSemidef)
    (t : ℝ) (ht : 1 ≤ t) :
    (D (1 + (t - 1) • H) : Mat n ℝ).PosDef := by
  simpa only [map_add, map_smul, hI] using affine_posDef (D H) (hD H hH) t ht

theorem positive_unital_map_inverseSquareRoot_tendsto {m n : ℕ}
    (D : Sym m →ₗ[ℝ] Sym n)
    (hD : ∀ H : Sym m, (H : Mat m ℝ).PosSemidef → (D H : Mat n ℝ).PosSemidef)
    (hI : D 1 = 1) (H : Sym m) (hH : (H : Mat m ℝ).PosSemidef) :
    Tendsto (fun t : ℝ => inverseSquareRoot (D (1 + (t - 1) • H))) atTop
      (𝓝 (kernelProjection (D H : Mat n ℝ))) := by
  simpa only [map_add, map_smul, hI] using
    inverseSquareRoot_affine_tendsto (D H) (hD H hH)

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.RankNorm ----
namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem outer_toEuclideanCLM {n : ℕ} (v : Vec n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (outer v) =
      InnerProductSpace.rankOne ℝ v v := by
  have h : Matrix.toEuclideanLin.symm
      (InnerProductSpace.rankOne ℝ v v).toLinearMap = outer v := by
    rw [InnerProductSpace.symm_toEuclideanLin_rankOne]
    ext i j
    simp [outer, Matrix.vecMulVec_apply]
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toEuclideanLin (outer v) x = _
  rw [← h, LinearEquiv.apply_symm_apply]
  rfl

theorem outer_mul_self {n : ℕ} (v : Vec n) (hv : ‖v‖ = 1) :
    outer v * outer v = outer v := by
  apply (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).injective
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (outer v * outer v) =
    Matrix.toEuclideanCLM (𝕜 := ℝ) (outer v)
  rw [map_mul, outer_toEuclideanCLM]
  exact InnerProductSpace.isIdempotentElem_rankOne_self hv

theorem outer_isStarProjection {n : ℕ} (v : Vec n) (hv : ‖v‖ = 1) :
    IsStarProjection (outer v) := ⟨outer_mul_self v hv, (outerSym v).property⟩

theorem one_sub_outer_posSemidef {n : ℕ} (v : Vec n) (hv : ‖v‖ = 1) :
    (1 - outer v).PosSemidef := (outer_isStarProjection v hv).one_sub.nonneg.posSemidef

theorem norm_outer_unit {n : ℕ} (v : Vec n) (hv : ‖v‖ = 1) : ‖outer v‖ = 1 := by
  rw [Matrix.cstar_norm_def, outer_toEuclideanCLM, InnerProductSpace.norm_rankOne, hv,
    mul_one]

theorem kernelProjection_one_sub_of_isStarProjection {n : ℕ} (P : Mat n ℝ)
    (hP : IsStarProjection P) : kernelProjection (1 - P) = P := by
  let φ := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)
  have hp : IsStarProjection (φ P) := hP.map φ
  have hrange : (φ P).range = (φ (1 - P)).ker := by
    rw [map_sub, map_one]
    exact LinearMap.IsIdempotentElem.range_eq_ker_one_sub
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hp.isIdempotentElem)
  have hproj : φ P = (φ (1 - P)).ker.starProjection := by
    apply (ContinuousLinearMap.IsStarProjection.ext_iff hp
      (isStarProjection_starProjection (U := (φ (1 - P)).ker))).mpr
    rw [Submodule.range_starProjection]
    exact hrange
  apply φ.injective
  change φ (kernelProjection (1 - P)) = φ P
  rw [hproj]
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toEuclideanLin (kernelProjection (1 - P)) x = _
  rw [kernelProjection, LinearEquiv.apply_symm_apply]
  rfl

theorem kernelProjection_one_sub_outer {n : ℕ} (v : Vec n) (hv : ‖v‖ = 1) :
    kernelProjection (1 - outer v) = outer v :=
  kernelProjection_one_sub_of_isStarProjection (outer v) (outer_isStarProjection v hv)

theorem outer_mul_mul_outer {n : ℕ} (u : Vec n) (A : Mat n ℝ) :
    outer u * A * outer u =
      (dotProduct (fun i => u i) (A *ᵥ fun i => u i)) • outer u := by
  change Matrix.vecMulVec (fun i => u i) (fun i => u i) * A *
    Matrix.vecMulVec (fun i => u i) (fun i => u i) = _
  rw [Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec]
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
    outer, Matrix.dotProduct_mulVec]
  ring

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.NormIdentity ----
namespace OAI

/-! The norm identity follows from the exact scalar thresholds and their rank-one limits. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Filter Topology
namespace Paper256

theorem NormalizedPencil.norm_identity (P : NormalizedPencil)
    (u v : Vec 4) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (y : Fin 3 → ℝ) :
    choiLam (wedgeCoordinates v u) y =
      operatorNorm (P.leftProjection v * P.B y * P.rightProjection u) ^ 2 := by
  let X (w : Vec 4) (t : ℝ) : Sym 4 := 1 + (t - 1) • (1 - outerSym w)
  have hH (w : Vec 4) (hw : ‖w‖ = 1) :
      ((1 - outerSym w : Sym 4) : Mat 4 ℝ).PosSemidef :=
    one_sub_outer_posSemidef w hw
  have hX (w : Vec 4) (hw : ‖w‖ = 1) (t : ℝ) (ht : 1 ≤ t) :
      (X w t : Mat 4 ℝ).PosDef := affine_posDef _ (hH w hw) t ht
  have hS (w : Vec 4) (hw : ‖w‖ = 1) :
      Tendsto (fun t => inverseSquareRoot (X w t)) atTop (𝓝 (outer w)) := by
    have h := inverseSquareRoot_affine_tendsto (1 - outerSym w) (hH w hw)
    change Tendsto (fun t => inverseSquareRoot (X w t)) atTop
      (𝓝 (kernelProjection (1 - outer w))) at h
    simpa only [kernelProjection_one_sub_outer w hw] using h
  have hXi : Tendsto (fun t => (X v t : Mat 4 ℝ)⁻¹) atTop (𝓝 (outer v)) := by
    have h := (hS v hv).mul (hS v hv)
    rw [outer_mul_self v hv] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact inverseSquareRoot_sq (X v t) (hX v hv t ht)
  let A (t : ℝ) := inverseSquareRoot (X u t) * phi y (X v t : Mat 4 ℝ)⁻¹ *
    inverseSquareRoot (X u t)
  let C (t : ℝ) := inverseSquareRoot (P.D (X v t)) * P.B y *
    inverseSquareRoot (P.E (X u t))
  have hthreshold : (fun t => ‖A t‖) =ᶠ[atTop] fun t => ‖C t‖ ^ 2 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact P.positive_threshold (X v t) (X u t) y (hX v hv t ht) (hX u hu t ht)
      (positive_unital_map_affine_posDef P.D P.D_positive P.D_unital _ (hH v hv) t ht)
      (positive_unital_map_affine_posDef P.E P.E_positive P.E_unital _ (hH u hu) t ht)
  have hphi : Tendsto (fun t => phi y (X v t : Mat 4 ℝ)⁻¹) atTop
      (𝓝 (phi y (outer v))) :=
    (phiLinear y).continuous_of_finiteDimensional.continuousAt.tendsto.comp hXi
  have hA : Tendsto A atTop (𝓝 (choiLam (wedgeCoordinates v u) y • outer u)) := by
    have h := ((hS u hu).mul hphi).mul (hS u hu)
    simpa only [outer_mul_mul_outer, phi_rank_one] using h
  have hA' : Tendsto (fun t => ‖A t‖) atTop (𝓝 (choiLam (wedgeCoordinates v u) y)) := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (choiLam_nonnegative _ _),
      norm_outer_unit u hu, mul_one] using hA.norm
  have hD : Tendsto (fun t => inverseSquareRoot (P.D (X v t))) atTop
      (𝓝 (P.leftProjection v)) :=
    positive_unital_map_inverseSquareRoot_tendsto P.D P.D_positive P.D_unital _ (hH v hv)
  have hE : Tendsto (fun t => inverseSquareRoot (P.E (X u t))) atTop
      (𝓝 (P.rightProjection u)) :=
    positive_unital_map_inverseSquareRoot_tendsto P.E P.E_positive P.E_unital _ (hH u hu)
  have hC : Tendsto C atTop (𝓝 (P.leftProjection v * P.B y * P.rightProjection u)) :=
    matrix_mul_tendsto (matrix_mul_tendsto hD tendsto_const_nhds) hE
  have heq := tendsto_nhds_unique (hA'.congr' hthreshold) (hC.norm.pow 2)
  simpa only [operatorNorm_eq_norm] using heq

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Filter Topology


theorem solution : type_of% @_root_.OAI.Paper256.NormalizedPencil.norm_identity := @_root_.OAI.Paper256.NormalizedPencil.norm_identity
