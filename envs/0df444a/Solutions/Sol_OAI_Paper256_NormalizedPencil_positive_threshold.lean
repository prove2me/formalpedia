-- Prove2me | solution 1 for OAI.Paper256.NormalizedPencil.positive_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:53:38.538162+00:00
-- url     : https://prove2.me/submissions/cd3fa5d9-7888-48b8-bad3-b22b437bcb6e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/NormCongruence.lean:L34-L60
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.NormalizedPencil.positive_threshold. The node keeps its source
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
import Theorems.Thm_OAI_Paper256_posSemidef_norm_threshold
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

-- ---- from OAI.Analysis.HyperbolicCones.MatrixLinear ----
namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder
open Matrix

universe u

namespace Paper256

theorem posSemidef_sum_outer {n : ℕ} (X : Mat n ℝ) (hX : X.PosSemidef) :
    ∃ v : Fin n → Vec n, X = ∑ i, outer (v i) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  refine ⟨fun i => WithLp.toLp 2 (B i), ?_⟩
  rw [hB]
  ext i j
  simp [Matrix.mul_apply, Matrix.sum_apply, outer]

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

-- ---- from OAI.Analysis.HyperbolicCones.MatrixPositive ----
namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder
open Matrix

namespace Paper256

theorem phi_outer_posSemidef (y : Fin 3 → ℝ) (v : Vec 4) :
    (phi y (outer v)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (phi_isHermitian y (outer v) (outerSym v).property)
  intro u
  have hr := phi_rank_one y (WithLp.toLp 2 u) v
  simpa only [star_trivial, hr] using choiLam_nonnegative
    (wedgeCoordinates v (WithLp.toLp 2 u)) y

theorem phi_posSemidef (y : Fin 3 → ℝ) (X : Mat 4 ℝ) (hX : X.PosSemidef) :
    (phi y X).PosSemidef := by
  obtain ⟨v, rfl⟩ := posSemidef_sum_outer X hX
  change ((phiLinear y) (∑ i, outer (v i))).PosSemidef
  rw [map_sum]
  exact Matrix.posSemidef_sum _ fun i _ => phi_outer_posSemidef y (v i)

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

-- ---- from OAI.Analysis.HyperbolicCones.NormThreshold ----
namespace OAI

/-! The exact scalar threshold of a positive semidefinite matrix. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix
namespace Paper256

theorem posSemidef_gram_threshold {m n : ℕ} [NeZero n]
    (C : Matrix (Fin m) (Fin n) ℝ) (r : ℝ) :
    (r • (1 : Mat n ℝ) - Cᵀ * C).PosSemidef ↔ ‖C‖ ^ 2 ≤ r := by
  have hp : (Cᵀ * C).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self C
  rw [posSemidef_norm_threshold _ hp]
  have hn : ‖Cᵀ * C‖ = ‖C‖ ^ 2 := by
    simpa only [conjTranspose_eq_transpose_of_trivial, pow_two] using
      Matrix.l2_opNorm_conjTranspose_mul_self C
  rw [hn]

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.NormCongruence ----
namespace OAI

/-! The scalar Schur thresholds are preserved by inverse-square-root congruence. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix
namespace Paper256

theorem inverseSquareRoot_congruence {n : ℕ} (Z : Sym n)
    (hZ : (Z : Mat n ℝ).PosDef) (F : Mat n ℝ) (r : ℝ) :
    (r • (Z : Mat n ℝ) - F).PosSemidef ↔
      (r • (1 : Mat n ℝ) - inverseSquareRoot Z * F * inverseSquareRoot Z).PosSemidef := by
  have heq : (inverseSquareRoot Z)ᵀ * (r • (Z : Mat n ℝ) - F) *
      inverseSquareRoot Z =
      r • (1 : Mat n ℝ) - inverseSquareRoot Z * F * inverseSquareRoot Z := by
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
      inverseSquareRoot_conjugate Z hZ, inverseSquareRoot_transpose]
  have hc := (inverseSquareRoot_isUnit Z hZ).posSemidef_star_left_conjugate_iff
    (x := r • (Z : Mat n ℝ) - F)
  simpa only [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, heq] using hc.symm

theorem inverseSquareRoot_gram {m n : ℕ} (X : Sym m) (Z : Sym n)
    (hX : (X : Mat m ℝ).PosDef) (B : Matrix (Fin m) (Fin n) ℝ) :
    (inverseSquareRoot X * B * inverseSquareRoot Z)ᵀ *
        (inverseSquareRoot X * B * inverseSquareRoot Z) =
      inverseSquareRoot Z * (Bᵀ * (X : Mat m ℝ)⁻¹ * B) * inverseSquareRoot Z := by
  rw [transpose_mul, transpose_mul, inverseSquareRoot_transpose,
    inverseSquareRoot_transpose, ← inverseSquareRoot_sq X hX]
  simp only [Matrix.mul_assoc]

theorem NormalizedPencil.positive_threshold (P : NormalizedPencil)
    (X Z : Sym 4) (y : Fin 3 → ℝ)
    (hX : (X : Mat 4 ℝ).PosDef) (hZ : (Z : Mat 4 ℝ).PosDef)
    (hDX : (P.D X : Mat P.a ℝ).PosDef) (hEZ : (P.E Z : Mat P.c ℝ).PosDef) :
    ‖inverseSquareRoot Z * phi y (X : Mat 4 ℝ)⁻¹ * inverseSquareRoot Z‖ =
      ‖inverseSquareRoot (P.D X) * P.B y * inverseSquareRoot (P.E Z)‖ ^ 2 := by
  let : NeZero P.c := ⟨Nat.ne_of_gt P.c_pos⟩
  let A := inverseSquareRoot Z * phi y (X : Mat 4 ℝ)⁻¹ * inverseSquareRoot Z
  let C := inverseSquareRoot (P.D X) * P.B y * inverseSquareRoot (P.E Z)
  have hA : A.PosSemidef := by
    have hp := (phi_posSemidef y _ hX.inv.posSemidef).conjTranspose_mul_mul_same
      (inverseSquareRoot Z)
    simpa only [conjTranspose_eq_transpose_of_trivial, inverseSquareRoot_transpose] using hp
  have hr (r : ℝ) : ‖A‖ ≤ r ↔ ‖C‖ ^ 2 ≤ r := by
    calc
      _ ↔ (r • (1 : Mat 4 ℝ) - A).PosSemidef := (posSemidef_norm_threshold A hA r).symm
      _ ↔ (r • (Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef :=
        (inverseSquareRoot_congruence Z hZ _ r).symm
      _ ↔ ((P.E (r • Z) : Mat P.c ℝ) - (P.B y)ᵀ *
          (P.D X : Mat P.a ℝ)⁻¹ * P.B y).PosSemidef := by
        simpa only [selfAdjoint.val_smul] using P.schur_equivalence X (r • Z) y hX
      _ ↔ (r • (1 : Mat P.c ℝ) - Cᵀ * C).PosSemidef := by
        have hc := inverseSquareRoot_congruence (P.E Z) hEZ
          ((P.B y)ᵀ * (P.D X : Mat P.a ℝ)⁻¹ * P.B y) r
        simpa only [map_smul, selfAdjoint.val_smul, ← inverseSquareRoot_gram (P.D X) (P.E Z) hDX] using hc
      _ ↔ ‖C‖ ^ 2 ≤ r := posSemidef_gram_threshold C r
  exact le_antisymm ((hr _).mpr le_rfl) ((hr _).mp le_rfl)

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.Paper256.NormalizedPencil.positive_threshold := @_root_.OAI.Paper256.NormalizedPencil.positive_threshold
