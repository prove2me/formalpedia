-- Prove2me | solution 1 for OAI.Paper256.cone_positive_slice_of_inverse_order
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:32:51.647991+00:00
-- url     : https://prove2.me/submissions/6f434ab3-46ba-493d-9465-39829ad5ae67

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/PositiveCore.lean:L16-L37
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.cone_positive_slice_of_inverse_order. The node keeps its source
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
import Theorems.Thm_OAI_Paper256_cone_iff_nonnegative_real_roots
import Theorems.Thm_OAI_Paper256_polynomial_homogeneous
import Theorems.Thm_OAI_Paper256_posSemidef_of_nonsingular_path
import Theorems.Thm_OAI_Paper256_posSemidef_three_of_principal_minors
import Theorems.Thm_OAI_Paper256_sym_neg_norm_le

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

-- ---- from OAI.Analysis.HyperbolicCones.PencilOrder ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem posDef_of_scalar_lower_bound {n : ℕ} {X : Mat n ℝ} {c : ℝ}
    (hc : 0 < c) (hX : c • (1 : Mat n ℝ) ≤ X) : X.PosDef := by
  have h := (Matrix.PosDef.one.smul hc).add_posSemidef hX
  simpa only [add_sub_cancel] using h

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

-- ---- from OAI.Analysis.HyperbolicCones.PolynomialScaling ----
namespace OAI

noncomputable section

open scoped BigOperators

universe u

namespace Paper256

theorem homogeneous_eval_smul {σ : Type u} [Fintype σ]
    (p : MvPolynomial σ ℝ) (d : ℕ) (hp : p.IsHomogeneous d)
    (s : ℝ) (v : σ → ℝ) :
    MvPolynomial.eval (s • v) p = s ^ d * MvPolynomial.eval v p := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hd : a.degree = d := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hp (MvPolynomial.mem_support_iff.mp ha)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [← Finsupp.degree_eq_sum, hd]
  ring

theorem coordinates_smul (s : ℝ) (x : Ambient) :
    coordinates (s • x) = s • coordinates x := by
  funext i
  rcases i with (i | i) | i <;> rfl

theorem coordinates_sub (x z : Ambient) :
    coordinates (x - z) = coordinates x - coordinates z := by
  funext i
  rcases i with (i | i) | i <;> rfl

theorem polynomial_eval_smul (s : ℝ) (x : Ambient) :
    MvPolynomial.eval (coordinates (s • x)) polynomial =
      s ^ 20 * MvPolynomial.eval (coordinates x) polynomial := by
  rw [coordinates_smul]
  exact homogeneous_eval_smul polynomial 20 polynomial_homogeneous s (coordinates x)

theorem polynomial_eval_neg (x : Ambient) :
    MvPolynomial.eval (coordinates (-x)) polynomial =
      MvPolynomial.eval (coordinates x) polynomial := by
  have h := polynomial_eval_smul (-1) x
  norm_num at h
  exact h

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.LineShift ----
namespace OAI

noncomputable section

namespace Paper256

theorem linePolynomial_eval (x : Ambient) (t : ℝ) :
    (linePolynomial x).eval t =
      MvPolynomial.eval (coordinates (t • basePoint - x)) polynomial := by
  rw [coordinates_sub, coordinates_smul]
  change (Polynomial.evalRingHom t) ((MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (coordinates basePoint i) * Polynomial.X -
      Polynomial.C (coordinates x i))) polynomial) =
    (MvPolynomial.eval₂Hom (RingHom.id ℝ)
      (t • coordinates basePoint - coordinates x)) polynomial
  rw [MvPolynomial.map_eval₂Hom]
  congr 2
  · ext r
    simp
  · ext i
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]

theorem linePolynomial_eval_neg (x : Ambient) (t : ℝ) :
    (linePolynomial x).eval (-t) =
      MvPolynomial.eval (coordinates (x + t • basePoint)) polynomial := by
  rw [linePolynomial_eval]
  have h : (-t) • basePoint - x = -(x + t • basePoint) := by
    simp [neg_add_rev, sub_eq_add_neg]
  rw [h, polynomial_eval_neg]

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.ConeRoots ----
namespace OAI

noncomputable section

namespace Paper256

theorem cone_iff_no_positive_shift (x : Ambient) : x ∈ cone ↔
    ∀ t : ℝ, 0 < t → MvPolynomial.eval (coordinates (x + t • basePoint)) polynomial ≠ 0 := by
  rw [cone_iff_nonnegative_real_roots]
  constructor
  · intro hx t ht he
    have h := hx (-t) ((linePolynomial_eval_neg x t).trans he)
    linarith
  · intro hx t ht
    by_contra hn
    have hpos : 0 < -t := by linarith
    apply hx (-t) hpos
    rw [← linePolynomial_eval_neg, neg_neg, ht]

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.ConeMatrix ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem continuousAt_symInverse {n : ℕ} (X : Sym n)
    (hX : IsUnit (X : Mat n ℝ)) : ContinuousAt symInverse X := by
  have hd : (X : Mat n ℝ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hX).ne_zero
  have hi : ContinuousAt Inv.inv (X : Mat n ℝ) :=
    continuousAt_matrix_inv _ (by
      simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hd))
  apply tendsto_subtype_rng.mpr
  exact hi.comp (f := fun H : Sym n => (H : Mat n ℝ)) (x := X)
    continuous_subtype_val.continuousAt

theorem continuous_phiSym (y : Fin 3 → ℝ) : Continuous (phiSym y) := by
  exact ((phiLinear y).continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _

theorem positive_shift {n : ℕ} (X : Sym n) (hX : (X : Mat n ℝ).PosDef)
    (t : ℝ) (ht : 0 ≤ t) : ((X + t • 1 : Sym n) : Mat n ℝ).PosDef :=
  hX.add_posSemidef (Matrix.PosSemidef.one.smul ht)

theorem continuousAt_coneResidual (X Z : Sym 4) (y : Fin 3 → ℝ) (t : ℝ)
    (ht : ((X + t • 1 : Sym 4) : Mat 4 ℝ).PosDef) :
    ContinuousAt (coneResidual X Z y) t := by
  have hX : Continuous (fun s : ℝ => X + s • (1 : Sym 4)) := by fun_prop
  have hZ : Continuous (fun s : ℝ => Z + s • (1 : Sym 4)) := by fun_prop
  have hi : ContinuousAt (fun s : ℝ => symInverse (X + s • (1 : Sym 4))) t :=
    (continuousAt_symInverse _ ht.isUnit).comp
      (f := fun s : ℝ => X + s • (1 : Sym 4)) hX.continuousAt
  exact hZ.continuousAt.sub ((continuous_phiSym y).continuousAt.comp hi)

theorem continuousOn_coneResidual (X Z : Sym 4) (y : Fin 3 → ℝ)
    (hX : (X : Mat 4 ℝ).PosDef) : ContinuousOn (coneResidual X Z y) (Ici 0) := by
  intro t ht
  exact (continuousAt_coneResidual X Z y t (positive_shift X hX t ht)).continuousWithinAt

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.ResidualOrder ----
namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem coneResidual_identity (X Z : Sym 4) (y : Fin 3 → ℝ) (t : ℝ) :
    (coneResidual X Z y t : Mat 4 ℝ) =
      (coneResidual X Z y 0 : Mat 4 ℝ) + t • 1 +
        phi y ((X : Mat 4 ℝ)⁻¹ - ((X + t • 1 : Sym 4) : Mat 4 ℝ)⁻¹) := by
  have hp := (phiLinear y).map_sub (X : Mat 4 ℝ)⁻¹
    ((X + t • 1 : Sym 4) : Mat 4 ℝ)⁻¹
  change phi y (_ - _) = phi y _ - phi y _ at hp
  rw [hp]
  change (Z : Mat 4 ℝ) + t • 1 - phi y ((X : Mat 4 ℝ) + t • 1)⁻¹ =
    ((Z : Mat 4 ℝ) + (0 : ℝ) • 1 - phi y ((X : Mat 4 ℝ) + (0 : ℝ) • 1)⁻¹) +
      t • 1 + (phi y (X : Mat 4 ℝ)⁻¹ - phi y ((X : Mat 4 ℝ) + t • 1)⁻¹)
  simp only [zero_smul, add_zero]
  module

theorem coneResidual_lower_bound (X Z : Sym 4) (y : Fin 3 → ℝ) (t : ℝ)
    (hInv : ((X : Mat 4 ℝ)⁻¹ - ((X + t • 1 : Sym 4) : Mat 4 ℝ)⁻¹).PosSemidef) :
    (coneResidual X Z y 0 : Mat 4 ℝ) + t • 1 ≤ (coneResidual X Z y t : Mat 4 ℝ) := by
  conv_rhs => rw [coneResidual_identity]
  exact le_add_of_nonneg_right (phi_posSemidef y _ hInv).nonneg

theorem coneResidual_posDef (X Z : Sym 4) (y : Fin 3 → ℝ) (t : ℝ)
    (ht : 0 < t) (h0 : (coneResidual X Z y 0 : Mat 4 ℝ).PosSemidef)
    (hInv : ((X : Mat 4 ℝ)⁻¹ - ((X + t • 1 : Sym 4) : Mat 4 ℝ)⁻¹).PosSemidef) :
    (coneResidual X Z y t : Mat 4 ℝ).PosDef := by
  rw [coneResidual_identity]
  exact (Matrix.PosDef.posSemidef_add h0 (Matrix.PosDef.one.smul ht)).add_posSemidef
    (phi_posSemidef y _ hInv)

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.ResidualBound ----
namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem posDef_of_shift_bound {n : ℕ} (H F : Sym n) (t : ℝ)
    (hbound : (H : Mat n ℝ) + t • 1 ≤ (F : Mat n ℝ))
    (ht : ‖(H : Mat n ℝ)‖ < t) : (F : Mat n ℝ).PosDef := by
  apply posDef_of_scalar_lower_bound (n := n) (X := (F : Mat n ℝ))
    (c := t - ‖(H : Mat n ℝ)‖) (sub_pos.mpr ht)
  have hnorm : ((H : Mat n ℝ) - (-‖(H : Mat n ℝ)‖) • 1).PosSemidef :=
    sym_neg_norm_le H
  have hdiff : ((F : Mat n ℝ) - ((H : Mat n ℝ) + t • 1)).PosSemidef := hbound
  change ((F : Mat n ℝ) - (t - ‖(H : Mat n ℝ)‖) • 1).PosSemidef
  convert Matrix.PosSemidef.add hdiff hnorm using 1
  module

theorem coneResidual_exists_posDef (X Z : Sym 4) (y : Fin 3 → ℝ)
    (hOrder : ∀ t : ℝ, 0 ≤ t →
      ((X : Mat 4 ℝ)⁻¹ - ((X + t • 1 : Sym 4) : Mat 4 ℝ)⁻¹).PosSemidef) :
    ∃ t : ℝ, 0 < t ∧ (coneResidual X Z y t : Mat 4 ℝ).PosDef := by
  let m := ‖(coneResidual X Z y 0 : Mat 4 ℝ)‖
  have hm : 0 ≤ m := norm_nonneg _
  have ht : 0 < m + 1 := by linarith
  refine ⟨m + 1, ht, ?_⟩
  apply posDef_of_shift_bound (coneResidual X Z y 0) (coneResidual X Z y (m + 1)) (m + 1)
    (coneResidual_lower_bound X Z y (m + 1) (hOrder (m + 1) ht.le))
  exact lt_add_one m

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.ShiftValue ----
namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem ambient_shift (X Z : Sym 4) (y : Fin 3 → ℝ) (t : ℝ) :
    (((X, Z), y) : Ambient) + t • basePoint = ((X + t • 1, Z + t • 1), y) := by
  simp [basePoint]

theorem polynomial_shift_inverse (X Z : Sym 4) (y : Fin 3 → ℝ) (t : ℝ)
    (ht : ((X + t • 1 : Sym 4) : Mat 4 ℝ).PosDef) :
    MvPolynomial.eval (coordinates ((((X, Z), y) : Ambient) + t • basePoint)) polynomial =
      ((X + t • 1 : Sym 4) : Mat 4 ℝ).det ^ 4 *
        (coneResidual X Z y t : Mat 4 ℝ).det := by
  rw [ambient_shift, polynomial_evaluation]
  exact matrixValue_inverse _ _ _ ((Matrix.isUnit_iff_isUnit_det _).mp ht.isUnit)

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.PositiveCore ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem cone_positive_slice_of_inverse_order (X Z : Sym 4) (y : Fin 3 → ℝ)
    (hX : (X : Mat 4 ℝ).PosDef)
    (hOrder : ∀ t : ℝ, 0 ≤ t →
      ((X : Mat 4 ℝ)⁻¹ - ((X + t • 1 : Sym 4) : Mat 4 ℝ)⁻¹).PosSemidef) :
    ((X, Z), y) ∈ cone ↔ (coneResidual X Z y 0 : Mat 4 ℝ).PosSemidef := by
  rw [cone_iff_no_positive_shift]
  constructor
  · intro h
    apply posSemidef_of_nonsingular_path (coneResidual X Z y)
      (continuousOn_coneResidual X Z y hX)
      (continuousAt_coneResidual X Z y 0 (by simpa using hX))
    · intro t ht
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      intro hz
      apply h t ht
      rw [polynomial_shift_inverse X Z y t (positive_shift X hX t ht.le), hz, mul_zero]
    · exact coneResidual_exists_posDef X Z y hOrder
  · intro h0 t ht
    have hXt := positive_shift X hX t ht.le
    have hFt := coneResidual_posDef X Z y t ht h0 (hOrder t ht.le)
    rw [polynomial_shift_inverse X Z y t hXt]
    exact mul_ne_zero (pow_ne_zero _ (ne_of_gt hXt.det_pos)) (ne_of_gt hFt.det_pos)

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder


theorem solution : type_of% @_root_.OAI.Paper256.cone_positive_slice_of_inverse_order := @_root_.OAI.Paper256.cone_positive_slice_of_inverse_order
