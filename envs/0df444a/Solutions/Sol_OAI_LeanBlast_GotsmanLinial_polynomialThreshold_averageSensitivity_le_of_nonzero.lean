-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.polynomialThreshold_averageSensitivity_le_of_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:21:38.54866+00:00
-- url     : https://prove2.me/submissions/d7444b5b-eba1-4e1d-9cdd-f130f6c38710

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/Main.lean:L92-L109
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.polynomialThreshold_averageSensitivity_le_of_nonzero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Walsh
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_PolynomialDegree
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_SignParity
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_EdgeRecovery
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_WalshDimensions
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_WeightedGrading
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_GradingShift
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_fourierSpace_mul
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_sensitivity_bound_of_cube_grading
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_weightedFlag_block_eq_zero_of_polynomial_degree

-- ---- from OAI.Combinatorics.GotsmanLinial.ProjectionBlocks ----
namespace OAI

/-!
# Matrix blocks of a finite orthogonal projection family

The Hilbert--Schmidt quantity below is the explicit sum of squared entry norms
rather than an ambient matrix norm instance.
-/

open scoped BigOperators ComplexConjugate
open Module

noncomputable section

namespace LeanBlast.GotsmanLinial

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

namespace OrthogonalProjectionFamily

variable {P : κ → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)

include hP

end OrthogonalProjectionFamily

variable {P : κ → Matrix ι ι ℂ}

section OperatorTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

attribute [local instance] OAI.LeanBlast.GotsmanLinial.instCompleteSpace_oAI
theorem operatorMatrix_isSelfAdjoint (b : OrthonormalBasis ι ℂ E)
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) : IsSelfAdjoint (operatorMatrix b T) := by
  have hlin : IsSelfAdjoint T.toLinearMap :=
    (ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff T).mpr hT
  exact hlin.map (LinearMap.toMatrixOrthonormal b)

/-- Transfer an actually constructed orthogonal family of Hilbert-space
projections to the matrix interface used by the block estimates. -/
theorem orthogonalProjectionFamily_operatorMatrix (b : OrthonormalBasis ι ℂ E)
    (T : κ → E →L[ℂ] E)
    (hself : ∀ k, IsSelfAdjoint (T k))
    (hidem : ∀ k, T k * T k = T k)
    (horth : ∀ r s, r ≠ s → T r * T s = 0)
    (hsum : ∑ k, T k = 1) :
    OrthogonalProjectionFamily (fun k => operatorMatrix b (T k)) where
  selfAdjoint k := operatorMatrix_isSelfAdjoint b (T k) (hself k)
  idempotent k := by rw [← operatorMatrix_mul, hidem k]
  orthogonal r s hrs := by rw [← operatorMatrix_mul, horth r s hrs, operatorMatrix_zero]
  sum_eq_one := by rw [← operatorMatrix_sum, hsum, operatorMatrix_one]

end OperatorTransport

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.CoordinateMultipliers ----
namespace OAI

/-!
# Actual diagonal sign and coordinate operators on the cube

The matrices here act on the cube with its counting inner product.  Their
continuous linear maps act on `EuclideanSpace`, so all operator-norm statements
refer to the intended Euclidean norm.  The Hilbert--Schmidt statements use the
explicit squared-entry sum `hsNormSq`.
-/

noncomputable section

open scoped BigOperators Matrix

namespace LeanBlast.GotsmanLinial

variable {n : ℕ}

theorem signMultiplier_isSelfAdjoint (h : Cube n → ℝ) :
    IsSelfAdjoint (signMultiplier h) := by
  change star (Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h)) =
    Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h)
  rw [← map_star, signMatrix_star]

theorem coordinateMultiplier_isSelfAdjoint (i : Fin n) :
    IsSelfAdjoint (coordinateMultiplier i) := signMultiplier_isSelfAdjoint _

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.Walsh ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Walsh characters of the Boolean cube

The characters are the real sign monomials, regarded as complex-valued
functions.  Counting orthogonality proves linear independence; the cardinality
comparison then gives a basis.  The degree filtration and its dimensions are
constructed from this concrete basis.
-/

noncomputable section

open scoped BigOperators symmDiff
open Finset Submodule Module

namespace LeanBlast.GotsmanLinial

theorem fourierSpace_mono (n : ℕ) : Monotone (fourierSpace n) := by
  intro k l hkl
  apply Submodule.span_mono
  rintro f ⟨S, hS, rfl⟩
  exact ⟨S, hS.trans hkl, rfl⟩

theorem fourierEuclideanSpace_mono (n : ℕ) : Monotone (fourierEuclideanSpace n) := by
  intro k l hkl
  exact Submodule.map_mono (fourierSpace_mono n hkl)

theorem fourierFlag_mono (n : ℕ) : Monotone (fourierFlag n) := by
  intro k l hkl
  cases k with
  | zero => exact bot_le
  | succ k =>
    cases l with
    | zero => omega
    | succ l => exact fourierEuclideanSpace_mono n (Nat.le_of_succ_le_succ hkl)

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.PolynomialDegree ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Polynomial degree and the Walsh filtration

The polynomial lemmas concern real multilinear
`MvPolynomial`s. Restriction to the cube is justified by an explicit monomial
expansion rather than assumed as an alternate polynomial representation.
-/

open scoped BigOperators symmDiff

namespace LeanBlast.GotsmanLinial

noncomputable section

variable {n d : ℕ}

/-- A character of degree at most `d` belongs to the corresponding filtration. -/
theorem walshChar_mem_fourierSpace {S : Finset (Fin n)} (hS : S.card ≤ d) :
    walshChar S ∈ fourierSpace n d :=
  Submodule.subset_span ⟨S, hS, rfl⟩

/-- Multiplication by one cube coordinate raises the degree by at most one. -/
theorem cubeCoord_mul_mem_fourierSpace {r : ℕ} {a : Cube n → ℂ}
    (ha : a ∈ fourierSpace n r) (i : Fin n) :
    (fun x => (cubeCoord x i : ℂ) * a x) ∈ fourierSpace n (r + 1) := by
  have hi : walshChar {i} ∈ fourierSpace n 1 :=
    walshChar_mem_fourierSpace (by simp)
  have h := fourierSpace_mul hi ha
  rw [Nat.add_comm] at h
  convert h using 1
  ext x
  simp only [Pi.mul_apply, walshChar_singleton]

end

end LeanBlast.GotsmanLinial

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.ProjectionTrace ----
namespace OAI

/-!
# Traces of actual orthogonal projections

The trace calculation uses the algebraic theorem for a projection onto a
submodule. In particular, no spectral decomposition or matrix norm instance
is needed. Matrix transport is valid in every basis, and hence in the
orthonormal basis used for the weighted grading.
-/

noncomputable section

namespace LeanBlast.GotsmanLinial

section General

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The actual orthogonal projection is algebraically a projection onto its
specified submodule. -/
theorem starProjection_isProj (K : Submodule 𝕜 E) :
    LinearMap.IsProj K K.starProjection.toLinearMap where
  map_mem := K.starProjection_apply_mem
  map_id := fun _ hx => Submodule.starProjection_eq_self_iff.mpr hx

/-- The trace of the actual orthogonal projection is the dimension of its range. -/
theorem trace_starProjection (K : Submodule 𝕜 E) :
    LinearMap.trace 𝕜 E K.starProjection.toLinearMap = (Module.finrank 𝕜 K : 𝕜) :=
  (starProjection_isProj K).trace

variable [Fintype ι] [DecidableEq ι]

/-- The matrix trace of an orthogonal projection is independent of the chosen basis. -/
theorem trace_toMatrix_starProjection (b : Module.Basis ι 𝕜 E) (K : Submodule 𝕜 E) :
    Matrix.trace (LinearMap.toMatrix b b K.starProjection.toLinearMap) =
      (Module.finrank 𝕜 K : 𝕜) := by
  rw [← LinearMap.trace_eq_matrix_trace 𝕜 b, trace_starProjection]

/-- The orthonormal matrix representation used by the grading has the correct trace. -/
theorem trace_toMatrixOrthonormal_starProjection (b : OrthonormalBasis ι 𝕜 E)
    (K : Submodule 𝕜 E) :
    Matrix.trace (LinearMap.toMatrixOrthonormal b K.starProjection.toLinearMap) =
      (Module.finrank 𝕜 K : 𝕜) :=
  trace_toMatrix_starProjection b.toBasis K

end General

section Complex

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]

end Complex

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.WalshDimensions ----
namespace OAI

/-!
Dimensions of the Walsh degree filtration, derived from the
linear independence of the concrete characters.
-/

noncomputable section

open scoped BigOperators
open Module

namespace LeanBlast.GotsmanLinial

/-- Arbitrary invertible linear changes of coordinates preserve every Fourier dimension. -/
theorem map_fourierSpace_finrank {E : Type*} [AddCommGroup E] [Module ℂ E]
    (n k : ℕ) (D : (Cube n → ℂ) ≃ₗ[ℂ] E) :
    finrank ℂ ((fourierSpace n k).map D.toLinearMap) =
      ∑ j ∈ Finset.range (k + 1), n.choose j := by
  rw [D.finrank_map_eq, fourierSpace_finrank]

/-- Passing to the counting Euclidean Hilbert space changes no dimensions. -/
theorem fourierEuclideanSpace_finrank (n k : ℕ) :
    finrank ℂ (fourierEuclideanSpace n k) =
      ∑ j ∈ Finset.range (k + 1), n.choose j := by
  exact map_fourierSpace_finrank n k (WithLp.linearEquiv 2 ℂ (Cube n → ℂ)).symm

/-- With the bottom stage inserted, stage `k` contains exactly degrees below `k`. -/
theorem fourierFlag_finrank (n k : ℕ) :
    finrank ℂ (fourierFlag n k) = ∑ j ∈ Finset.range k, n.choose j := by
  cases k with
  | zero =>
      rw [fourierFlag_zero, finrank_bot]
      simp
  | succ k => exact fourierEuclideanSpace_finrank n k

/-- The degree-`k` layer has the prescribed binomial dimension increment. -/
theorem fourierFlag_finrank_add (n k : ℕ) :
    finrank ℂ (fourierFlag n k) + n.choose k =
      finrank ℂ (fourierFlag n (k + 1)) := by
  simp only [fourierFlag_finrank]
  exact (Finset.sum_range_succ (fun j => n.choose j) k).symm

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.WeightedGrading ----
namespace OAI

/-!
# The actual weighted orthogonal grading of the cube

The construction first orthogonalizes an arbitrary finite flag of subspaces.
It then transports the concrete Walsh flag by the invertible square-root
weight and takes the orthogonal projections in the counting Hilbert space.
The resulting matrices are proved to form an orthogonal decomposition of
the identity with the prescribed binomial multiplicities.
-/

noncomputable section

open scoped BigOperators
open Module

namespace LeanBlast.GotsmanLinial

section FiniteFlag

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

attribute [local instance] OAI.LeanBlast.GotsmanLinial.instCompleteSpace_oAI_1
omit [FiniteDimensional 𝕜 E] in
theorem flagLayer_le_next (K : ℕ → Submodule 𝕜 E) (k : ℕ) :
    flagLayer K k ≤ K (k + 1) := inf_le_left

omit [FiniteDimensional 𝕜 E] in
theorem flagLayer_le_prev_orthogonal (K : ℕ → Submodule 𝕜 E) (k : ℕ) :
    flagLayer K k ≤ (K k)ᗮ := inf_le_right

theorem flagLayer_sup_prev (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (k : ℕ) :
    K k ⊔ flagLayer K k = K (k + 1) := by
  simpa only [flagLayer, inf_comm] using
    Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (hK (Nat.le_succ k))

theorem flagLayer_finrank_add (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (k : ℕ) :
    finrank 𝕜 (K k) + finrank 𝕜 (flagLayer K k) = finrank 𝕜 (K (k + 1)) := by
  change finrank 𝕜 (K k) + finrank 𝕜 (K (k + 1) ⊓ (K k)ᗮ : Submodule 𝕜 E) = _
  rw [inf_comm]
  exact Submodule.finrank_add_inf_finrank_orthogonal (hK (Nat.le_succ k))

omit [FiniteDimensional 𝕜 E] in
theorem flagLayer_isOrtho_of_lt (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    {r s : ℕ} (hrs : r < s) : flagLayer K r ⟂ flagLayer K s := by
  apply Submodule.IsOrtho.symm
  exact (flagLayer_le_prev_orthogonal K s).trans
    (Submodule.orthogonal_le ((flagLayer_le_next K r).trans (hK hrs)))

omit [FiniteDimensional 𝕜 E] in
theorem flagLayer_isOrtho (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    {r s : ℕ} (hrs : r ≠ s) : flagLayer K r ⟂ flagLayer K s := by
  rcases lt_or_gt_of_ne hrs with h | h
  · exact flagLayer_isOrtho_of_lt K hK h
  · exact (flagLayer_isOrtho_of_lt K hK h).symm

theorem flagLayer_iSup_eq_top (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    (hzero : K 0 = ⊥) (n : ℕ) (htop : K (n + 1) = ⊤) :
    (⨆ k : Fin (n + 1), flagLayer K k.val) = ⊤ := by
  let S := ⨆ k : Fin (n + 1), flagLayer K k.val
  have hle : ∀ m, m ≤ n + 1 → K m ≤ S := by
    intro m
    induction m with
    | zero => simp [hzero]
    | succ m ih =>
      intro hm
      rw [← flagLayer_sup_prev K hK m]
      exact sup_le (ih (by omega))
        (le_iSup (fun k : Fin (n + 1) => flagLayer K k.val) ⟨m, by omega⟩)
  apply top_unique
  rw [← htop]
  exact hle (n + 1) le_rfl

omit [FiniteDimensional 𝕜 E] in
theorem flagLayer_orthogonalFamily (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    (n : ℕ) :
    OrthogonalFamily 𝕜 (fun k : Fin (n + 1) => flagLayer K k.val)
      (fun k => (flagLayer K k.val).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro r s hrs
  exact flagLayer_isOrtho K hK (fun h => hrs (Fin.ext h))

theorem flagProjection_isSelfAdjoint (K : ℕ → Submodule 𝕜 E) (k : ℕ) :
    IsSelfAdjoint (flagProjection K k) :=
  isSelfAdjoint_starProjection (flagLayer K k)

theorem flagProjection_idempotent (K : ℕ → Submodule 𝕜 E) (k : ℕ) :
    flagProjection K k * flagProjection K k = flagProjection K k :=
  (flagLayer K k).isIdempotentElem_starProjection.eq

theorem flagProjection_mul_eq_zero (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    {r s : ℕ} (hrs : r ≠ s) : flagProjection K r * flagProjection K s = 0 :=
  (flagLayer_isOrtho K hK hrs).starProjection_comp_starProjection

theorem sum_flagProjection (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    (hzero : K 0 = ⊥) (n : ℕ) (htop : K (n + 1) = ⊤) :
    (∑ k : Fin (n + 1), flagProjection K k.val) = 1 := by
  ext x
  change (∑ k : Fin (n + 1), (flagLayer K k.val).starProjection) x = x
  rw [sum_apply]
  apply (flagLayer_orthogonalFamily K hK n).sum_projection_of_mem_iSup
  rw [flagLayer_iSup_eq_top K hK hzero n htop]
  trivial

theorem flagProjection_apply_mem_next (K : ℕ → Submodule 𝕜 E) (k : ℕ) (x : E) :
    flagProjection K k x ∈ K (k + 1) :=
  (flagLayer K k).starProjection_apply_mem x |>.1

theorem flagProjection_apply_eq_zero_of_mem_prev (K : ℕ → Submodule 𝕜 E)
    (k : ℕ) {x : E} (hx : x ∈ K k) : flagProjection K k x = 0 := by
  have ho : x ∈ (flagLayer K k)ᗮ :=
    Submodule.orthogonal_le (flagLayer_le_prev_orthogonal K k)
      ((K k).le_orthogonal_orthogonal hx)
  exact congrArg Subtype.val
    (Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr ho)

end FiniteFlag

section InvertibleWeights

variable {Ω : Type*} [Fintype Ω]

end InvertibleWeights

section Transport

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

theorem transportFlag_monotone (D : E ≃ₗ[𝕜] E) (F : ℕ → Submodule 𝕜 E)
    (hF : Monotone F) : Monotone (transportFlag D F) := by
  intro i j hij
  exact Submodule.map_mono (hF hij)

theorem transportFlag_finrank (D : E ≃ₗ[𝕜] E) (F : ℕ → Submodule 𝕜 E) (k : ℕ) :
    finrank 𝕜 (transportFlag D F k) = finrank 𝕜 (F k) :=
  D.finrank_map_eq (F k)

/-- The weighted construction preserves every prescribed dimension increment. -/
theorem transportFlag_layer_finrank [FiniteDimensional 𝕜 E] (D : E ≃ₗ[𝕜] E)
    (F : ℕ → Submodule 𝕜 E) (hF : Monotone F) (k d : ℕ)
    (hd : finrank 𝕜 (F k) + d = finrank 𝕜 (F (k + 1))) :
    finrank 𝕜 (flagLayer (transportFlag D F) k) = d := by
  have h := flagLayer_finrank_add (transportFlag D F) (transportFlag_monotone D F hF) k
  rw [transportFlag_finrank, transportFlag_finrank] at h
  omega

end Transport

section MatrixTransport

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]

/-- The matrix projection-family laws follow from the constructed Hilbert-space
projections, without any additional grading hypothesis. -/
theorem flagProjectionMatrix_family (b : OrthonormalBasis ι ℂ E)
    (K : ℕ → Submodule ℂ E) (hK : Monotone K) (hzero : K 0 = ⊥)
    (n : ℕ) (htop : K (n + 1) = ⊤) :
    OrthogonalProjectionFamily (fun k : Fin (n + 1) => flagProjectionMatrix b K k.val) :=
  orthogonalProjectionFamily_operatorMatrix b
    (fun k : Fin (n + 1) => flagProjection K k.val)
    (fun k => flagProjection_isSelfAdjoint K k.val)
    (fun k => flagProjection_idempotent K k.val)
    (fun _ _ hrs => flagProjection_mul_eq_zero K hK (fun h => hrs (Fin.ext h)))
    (sum_flagProjection K hK hzero n htop)

theorem trace_flagProjectionMatrix (b : OrthonormalBasis ι ℂ E)
    (K : ℕ → Submodule ℂ E) (k : ℕ) :
    Matrix.trace (flagProjectionMatrix b K k) = (finrank ℂ (flagLayer K k) : ℂ) :=
  trace_toMatrixOrthonormal_starProjection b (flagLayer K k)

end MatrixTransport

section WeightedCube

variable {n : ℕ}

theorem weightedFourierFlag_mono (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) :
    Monotone (weightedFourierFlag w hw) :=
  transportFlag_monotone _ _ (fourierFlag_mono n)

/-- Weighting preserves the exact binomial dimensions of the orthogonal layers. -/
theorem weightedFourierFlag_layer_finrank (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : ℕ) :
    finrank ℂ (flagLayer (weightedFourierFlag w hw) k) = n.choose k :=
  transportFlag_layer_finrank (sqrtWeightEquiv w hw) (fourierFlag n)
    (fourierFlag_mono n) k (n.choose k) (fourierFlag_finrank_add n k)

theorem weightedProjectionMatrix_family (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) :
    OrthogonalProjectionFamily (weightedProjectionMatrix w hw) :=
  flagProjectionMatrix_family (EuclideanSpace.basisFun (Cube n) ℂ)
    (weightedFourierFlag w hw) (weightedFourierFlag_mono w hw)
    (weightedFourierFlag_zero w hw) n (weightedFourierFlag_top w hw)

theorem weightedProjectionMatrix_trace (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : Fin (n + 1)) :
    Matrix.trace (weightedProjectionMatrix w hw k) = (n.choose k.val : ℂ) := by
  rw [weightedProjectionMatrix, trace_flagProjectionMatrix, weightedFourierFlag_layer_finrank]

theorem weightedProjectionMatrix_trace_re (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : Fin (n + 1)) :
    (Matrix.trace (weightedProjectionMatrix w hw k)).re = (n.choose k.val : ℝ) := by
  rw [weightedProjectionMatrix_trace]
  simp

end WeightedCube

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.CoordinateDegree ----
namespace OAI

/-!
# Coordinate multiplication raises the Fourier degree by at most one

The unweighted polynomial degree bound is transported to the actual diagonal matrices and continuous linear operators
on the counting-inner-product Euclidean space, including the shifted flag used
by the weighted grading construction.
-/

noncomputable section

open scoped Matrix

namespace LeanBlast.GotsmanLinial

variable {n k : ℕ}

/-- The continuous coordinate multiplier has the same degree shift in Euclidean space. -/
theorem coordinateMultiplier_mem_fourierEuclideanSpace (i : Fin n)
    {a : EuclideanSpace ℂ (Cube n)} (ha : a ∈ fourierEuclideanSpace n k) :
    coordinateMultiplier i a ∈ fourierEuclideanSpace n (k + 1) := by
  apply (mem_fourierEuclideanSpace _).2
  simpa only [coordinateMultiplier_apply] using
    cubeCoord_mul_mem_fourierSpace ((mem_fourierEuclideanSpace _).1 ha) i

/-- The shifted flag also has a one-step coordinate shift, including its bottom term. -/
theorem coordinateMultiplier_fourierFlag_shift (i : Fin n) :
    ∀ k (a : EuclideanSpace ℂ (Cube n)), a ∈ fourierFlag n k →
      coordinateMultiplier i a ∈ fourierFlag n (k + 1) := by
  intro k a ha
  cases k with
  | zero =>
      have ha0 : a = 0 := by simpa using ha
      simp [ha0]
  | succ k =>
      exact coordinateMultiplier_mem_fourierEuclideanSpace i ha

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.GradingShift ----
namespace OAI

/-!
# A degree shift is tridiagonal in the associated orthogonal grading

These lemmas retain the degree-shift premise explicitly. The cube application
discharges it using coordinate multiplication and the weighted Fourier flag.
-/

noncomputable section

namespace LeanBlast.GotsmanLinial

section FiniteFlag

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

attribute [local instance] OAI.LeanBlast.GotsmanLinial.instCompleteSpace_oAI_3
/-- An operator that raises the flag index by at most one has no blocks
strictly above the first off-diagonal. -/
theorem flagProjection_mul_shift_eq_zero
    (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (Z : E →L[𝕜] E)
    (hshift : ∀ k x, x ∈ K k → Z x ∈ K (k + 1))
    {r s : ℕ} (hrs : r + 1 < s) :
    flagProjection K s * Z * flagProjection K r = 0 := by
  ext x
  change flagProjection K s (Z (flagProjection K r x)) = 0
  apply flagProjection_apply_eq_zero_of_mem_prev
  exact hK (by omega : r + 1 + 1 ≤ s)
    (hshift (r + 1) (flagProjection K r x) (flagProjection_apply_mem_next K r x))

/-- Self-adjointness gives the other half of the band by taking adjoints. -/
theorem flagProjection_tridiagonal
    (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (Z : E →L[𝕜] E)
    (hZ : IsSelfAdjoint Z)
    (hshift : ∀ k x, x ∈ K k → Z x ∈ K (k + 1))
    {r s : ℕ} (hrs : r + 1 < s ∨ s + 1 < r) :
    flagProjection K s * Z * flagProjection K r = 0 := by
  rcases hrs with hrs | hsr
  · exact flagProjection_mul_shift_eq_zero K hK Z hshift hrs
  · have h := congrArg star (flagProjection_mul_shift_eq_zero K hK Z hshift hsr)
    simpa only [star_mul, star_zero, (flagProjection_isSelfAdjoint K r).star_eq,
      (flagProjection_isSelfAdjoint K s).star_eq, hZ.star_eq, mul_assoc] using h

/-- The band property is preserved by taking matrices or any other ring
representation of the operator algebra. -/
theorem map_flagProjection_tridiagonal
    {A : Type*} [Ring A] (F : (E →L[𝕜] E) →+* A)
    (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (Z : E →L[𝕜] E)
    (hZ : IsSelfAdjoint Z)
    (hshift : ∀ k x, x ∈ K k → Z x ∈ K (k + 1))
    {r s : ℕ} (hrs : r + 1 < s ∨ s + 1 < r) :
    F (flagProjection K s) * F Z * F (flagProjection K r) = 0 := by
  rw [← map_mul, ← map_mul, flagProjection_tridiagonal K hK Z hZ hshift hrs, map_zero]

omit [FiniteDimensional 𝕜 E] in
/-- Commutation transports a degree-shift statement through a weight map. -/
theorem shift_mem_map_of_commute
    (V : ℕ → Submodule 𝕜 E) (D Z : E →ₗ[𝕜] E)
    (hcommute : ∀ x, Z (D x) = D (Z x))
    (hshift : ∀ k x, x ∈ V k → Z x ∈ V (k + 1))
    (k : ℕ) {x : E} (hx : x ∈ (V k).map D) :
    Z x ∈ (V (k + 1)).map D := by
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨Z y, hshift k y hy, (hcommute y).symm⟩

end FiniteFlag

section MatrixFlag

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.LeanBlast.GotsmanLinial.instCompleteSpace_oAI_4
/-- The concrete matrix form consumed by the commutator estimate. -/
theorem operatorMatrix_flagProjection_tridiagonal
    (b : OrthonormalBasis ι ℂ E)
    (K : ℕ → Submodule ℂ E) (hK : Monotone K) (Z : E →L[ℂ] E)
    (hZ : IsSelfAdjoint Z)
    (hshift : ∀ k x, x ∈ K k → Z x ∈ K (k + 1))
    (n : ℕ) (r s : Fin (n + 1))
    (hrs : r.val + 1 < s.val ∨ s.val + 1 < r.val) :
    operatorMatrix b (flagProjection K s.val) * operatorMatrix b Z *
      operatorMatrix b (flagProjection K r.val) = 0 := by
  exact map_flagProjection_tridiagonal (operatorMatrixEquiv b).toRingHom
    K hK Z hZ hshift hrs

end MatrixFlag

section WeightedCube

variable {n : ℕ}

/-- Coordinate signs commute with the actual positive square-root weight. -/
theorem coordinateMultiplier_sqrtWeight_commute
    (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (i : Fin n)
    (a : EuclideanSpace ℂ (Cube n)) :
    coordinateMultiplier i (sqrtWeightEquiv w hw a) =
      sqrtWeightEquiv w hw (coordinateMultiplier i a) := by
  ext x
  simp only [coordinateMultiplier_apply, sqrtWeightEquiv_apply]
  exact mul_left_comm _ _ _

/-- The actual weighted Fourier flag retains the one-step coordinate shift. -/
theorem coordinateMultiplier_weightedFlag_shift
    (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (i : Fin n) :
    ∀ k (a : EuclideanSpace ℂ (Cube n)),
      a ∈ transportFlag (sqrtWeightEquiv w hw) (fourierFlag n) k →
      coordinateMultiplier i a ∈
        transportFlag (sqrtWeightEquiv w hw) (fourierFlag n) (k + 1) := by
  intro k a ha
  exact shift_mem_map_of_commute (fourierFlag n) (sqrtWeightEquiv w hw).toLinearMap
    (coordinateMultiplier i).toLinearMap
    (coordinateMultiplier_sqrtWeight_commute w hw i)
    (coordinateMultiplier_fourierFlag_shift i) k ha

/-- Tridiagonality for the actually constructed weighted Fourier projections,
expressed in an arbitrary orthonormal coordinate system. -/
theorem weightedFlag_operatorMatrix_tridiagonal
    (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (b : OrthonormalBasis (Cube n) ℂ (EuclideanSpace ℂ (Cube n)))
    (i : Fin n) (r s : Fin (n + 1))
    (hrs : r.val + 1 < s.val ∨ s.val + 1 < r.val) :
    flagProjectionMatrix b (transportFlag (sqrtWeightEquiv w hw) (fourierFlag n)) s.val *
      operatorMatrix b (coordinateMultiplier i) *
      flagProjectionMatrix b (transportFlag (sqrtWeightEquiv w hw) (fourierFlag n)) r.val = 0 := by
  exact operatorMatrix_flagProjection_tridiagonal b
    (transportFlag (sqrtWeightEquiv w hw) (fourierFlag n))
    (transportFlag_monotone _ _ (fourierFlag_mono n))
    (coordinateMultiplier i) (coordinateMultiplier_isSelfAdjoint i)
    (coordinateMultiplier_weightedFlag_shift w hw i) n r s hrs

/-- The raw coordinate-sign matrices are tridiagonal for the actual weighted
Fourier projection family. There is no remaining degree-shift hypothesis. -/
theorem weightedProjectionMatrix_tridiagonal
    (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (i : Fin n) (r s : Fin (n + 1))
    (hrs : r.val + 1 < s.val ∨ s.val + 1 < r.val) :
    weightedProjectionMatrix w hw s * coordinateSignMatrix i *
      weightedProjectionMatrix w hw r = 0 := by
  simpa only [weightedProjectionMatrix, weightedFourierFlag, coordinateMultiplier,
    signMultiplier, operatorMatrix_toEuclideanCLM, coordinateSignMatrix] using
    weightedFlag_operatorMatrix_tridiagonal w hw
      (EuclideanSpace.basisFun (Cube n) ℂ) i r s hrs

end WeightedCube

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.BlockVanishing ----
namespace OAI

/-!
# Vanishing of low antidiagonal blocks

The geometric step is reduced to an explicit finite sum: multiplication on
both sides by the square root of a positive weight turns the weighted pairing
into a Fourier pairing against the signed weight.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace LeanBlast.GotsmanLinial

/-- The same vanishing statement in any orthonormal matrix coordinates, ready
for the Hilbert-Schmidt block coupling. -/
theorem weightedFlag_matrixBlock_eq_zero_of_polynomial_degree
    {n d r s : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x, polynomialValue p x ≠ 0) (hrs : r + s < n - d)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ (Cube n))) :
    let K := weightedFourierFlag (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x))
    operatorMatrix b (flagProjection K s) *
      operatorMatrix b
        (signMultiplier (fun x => fullParity x * thresholdSign (polynomialValue p x))) *
      operatorMatrix b (flagProjection K r) = 0 := by
  have h := congrArg (operatorMatrix b)
    (weightedFlag_block_eq_zero_of_polynomial_degree p hp hd hnz hrs)
  simpa only [operatorMatrix_mul, operatorMatrix_zero] using h

/-- The concrete cutoff used by the finite block coupling: actual weighted
projection matrices, actual diagonal parity-modified polynomial threshold,
and no unproved construction assumptions. -/
theorem weightedProjectionMatrix_block_eq_zero_of_polynomial_degree
    {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x, polynomialValue p x ≠ 0)
    (r s : Fin (n + 1)) (hrs : r.val + s.val < n - d) :
    let w := fun x => |polynomialValue p x|
    let hw : ∀ x, 0 < w x := fun x => abs_pos.mpr (hnz x)
    weightedProjectionMatrix w hw s *
      signMatrix (fun x => fullParity x * polynomialThreshold p x) *
        weightedProjectionMatrix w hw r = 0 := by
  have h := weightedFlag_matrixBlock_eq_zero_of_polynomial_degree
    (r := r.val) (s := s.val) p hp hd hnz hrs (EuclideanSpace.basisFun (Cube n) ℂ)
  simpa only [weightedProjectionMatrix, flagProjectionMatrix, signMultiplier,
    operatorMatrix_toEuclideanCLM, polynomialThreshold] using h

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.Main ----
namespace OAI

/-!
# Assembly of the Gotsman--Linial average-sensitivity bound

The first lemmas are explicitly conditional assembly bridges. The final
theorems discharge their matrix and counting hypotheses using the concrete
weighted Boolean-cube grading and a sign-preserving constant perturbation.
-/

namespace LeanBlast.GotsmanLinial

open scoped BigOperators

/-- The bound for a polynomial without cube zeros. The projection
family and both block-vanishing properties are constructed from its absolute
value, rather than retained as hypotheses. -/
theorem polynomialThreshold_averageSensitivity_le_of_nonzero {n d : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x : Cube n, polynomialValue p x ≠ 0) :
    averageSensitivity (polynomialThreshold p) ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ) := by
  let w : Cube n → ℝ := fun x => |polynomialValue p x|
  have hw (x : Cube n) : 0 < w x := abs_pos.mpr (hnz x)
  apply sensitivity_bound_of_cube_grading (polynomialThreshold p)
    (fun x => thresholdSign_cases (polynomialValue p x))
    (weightedProjectionMatrix w hw)
    (weightedProjectionMatrix_family w hw)
    (weightedProjectionMatrix_trace_re w hw)
  · intro i
    exact weightedProjectionMatrix_tridiagonal w hw i
  · intro r s hrs
    exact weightedProjectionMatrix_block_eq_zero_of_polynomial_degree p hp hd hnz r s hrs

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.polynomialThreshold_averageSensitivity_le_of_nonzero := @_root_.OAI.LeanBlast.GotsmanLinial.polynomialThreshold_averageSensitivity_le_of_nonzero
