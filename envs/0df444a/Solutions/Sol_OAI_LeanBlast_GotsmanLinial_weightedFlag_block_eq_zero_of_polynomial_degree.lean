-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.weightedFlag_block_eq_zero_of_polynomial_degree
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:19:02.496322+00:00
-- url     : https://prove2.me/submissions/2117866a-5003-4c8e-8898-33871df16257

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/BlockVanishing.lean:L186-L207
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.weightedFlag_block_eq_zero_of_polynomial_degree. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_fourierSpace_star
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_parity_mul_mem_fourierSpaceFrom
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_polynomialValue_mem_fourierSpace
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_sqrtWeight_inner_eq_sum
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_sum_mul_eq_zero_of_fourier_separated

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

/-- The precise multiplication-conjugation rule used in the weighted pairing. -/
theorem fourierSpace_conj_mul {r s : ℕ} {a b : Cube n → ℂ}
    (ha : a ∈ fourierSpace n r) (hb : b ∈ fourierSpace n s) :
    (fun x => star (b x) * a x) ∈ fourierSpace n (r + s) := by
  simpa only [Nat.add_comm, Pi.mul_def, Pi.star_def] using
    fourierSpace_mul (fourierSpace_star hb) ha

/-- The polynomial has high Fourier support after multiplication by
full parity, with no alternate polynomial-class assumption. -/
theorem parity_polynomialValue_mem_fourierSpaceFrom {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    (fun x => walshChar Finset.univ x * (polynomialValue p x : ℂ)) ∈
      fourierSpaceFrom n (n - d) :=
  parity_mul_mem_fourierSpaceFrom (polynomialValue_mem_fourierSpace hp hd)

end

end LeanBlast.GotsmanLinial

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

end FiniteFlag

section InvertibleWeights

variable {Ω : Type*} [Fintype Ω]

end InvertibleWeights

section Transport

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

end Transport

section MatrixTransport

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]

end MatrixTransport

section WeightedCube

variable {n : ℕ}

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

/-- The threshold convention at zero is compatible with the signed absolute
value identity used to build the weighted grading. -/
theorem abs_mul_thresholdSign (t : ℝ) : |t| * thresholdSign t = t := by
  by_cases ht : 0 ≤ t
  · simp [thresholdSign, ht, abs_of_nonneg ht]
  · simp [thresholdSign, ht, abs_of_neg (lt_of_not_ge ht)]

/-- If the image of one subspace under an operator is orthogonal to a second
subspace, the corresponding projection block vanishes. -/
theorem projectionBlock_eq_zero_of_pairing
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (H : E →L[𝕜] E)
    (hpair : ∀ u ∈ U, ∀ v ∈ V, inner 𝕜 v (H u) = 0) :
    V.starProjection * H * U.starProjection = 0 := by
  ext x
  change V.starProjection (H (U.starProjection x)) = 0
  apply (Submodule.starProjection_apply_eq_zero_iff V).mpr
  intro v hv
  exact hpair _ (U.starProjection_apply_mem x) v hv

/-- Lift an orthogonality calculation on preimages through a common linear map
to a zero block between subspaces of its images. -/
theorem projectionBlock_eq_zero_of_map_pairing
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (A B U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : E →ₗ[𝕜] E) (H : E →L[𝕜] E)
    (hU : U ≤ A.map D) (hV : V ≤ B.map D)
    (hpair : ∀ a ∈ A, ∀ b ∈ B, inner 𝕜 (D b) (H (D a)) = 0) :
    V.starProjection * H * U.starProjection = 0 := by
  apply projectionBlock_eq_zero_of_pairing U V H
  intro u hu v hv
  obtain ⟨a, ha, rfl⟩ := hU hu
  obtain ⟨b, hb, rfl⟩ := hV hv
  exact hpair a ha b hb

/-- Replace the weight times the diagonal sign by the actual signed weight. -/
theorem sqrtWeight_inner_eq_sum_signedWeight
    {Ω : Type*} [Fintype Ω]
    (w h : Ω → ℝ) (q : Ω → ℂ) (hw : ∀ x, 0 ≤ w x)
    (hwq : ∀ x, (w x : ℂ) * (h x : ℂ) = q x)
    (D : EuclideanSpace ℂ Ω →ₗ[ℂ] EuclideanSpace ℂ Ω)
    (hD : ∀ a x, D a x = (Real.sqrt (w x) : ℂ) * a x)
    (H : EuclideanSpace ℂ Ω →L[ℂ] EuclideanSpace ℂ Ω)
    (hH : ∀ a x, H a x = (h x : ℂ) * a x)
    (a b : EuclideanSpace ℂ Ω) :
    inner ℂ (D b) (H (D a)) = ∑ x, star (b x) * a x * q x := by
  rw [sqrtWeight_inner_eq_sum w h hw D hD H hH]
  simp only [hwq]

/-- High Fourier support of the signed weight kills every pairing whose two
unweighted degrees have smaller total degree. -/
theorem sqrtWeight_pairing_eq_zero_of_fourier_separation
    {n r s k : ℕ} (w h : Cube n → ℝ) (q : Cube n → ℂ)
    (hw : ∀ x, 0 ≤ w x) (hwq : ∀ x, (w x : ℂ) * (h x : ℂ) = q x)
    (D : EuclideanSpace ℂ (Cube n) →ₗ[ℂ] EuclideanSpace ℂ (Cube n))
    (hD : ∀ a x, D a x = (Real.sqrt (w x) : ℂ) * a x)
    (H : EuclideanSpace ℂ (Cube n) →L[ℂ] EuclideanSpace ℂ (Cube n))
    (hH : ∀ a x, H a x = (h x : ℂ) * a x)
    (a b : EuclideanSpace ℂ (Cube n))
    (ha : WithLp.ofLp a ∈ fourierSpace n r)
    (hb : WithLp.ofLp b ∈ fourierSpace n s)
    (hq : q ∈ fourierSpaceFrom n k) (hrs : r + s < k) :
    inner ℂ (D b) (H (D a)) = 0 := by
  rw [sqrtWeight_inner_eq_sum_signedWeight w h q hw hwq D hD H hH]
  exact sum_mul_eq_zero_of_fourier_separated (fourierSpace_conj_mul ha hb) hq hrs

/-- The choices `w = |p|` and `h = parity * sign(p)` multiply to the
high-degree signed polynomial, including at a zero of the polynomial. -/
theorem polynomial_signedWeight {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Cube n) :
    ((|polynomialValue p x| : ℝ) : ℂ) *
        ((fullParity x * thresholdSign (polynomialValue p x) : ℝ) : ℂ) =
      walshChar Finset.univ x * (polynomialValue p x : ℂ) := by
  rw [Complex.ofReal_mul]
  calc
    ((|polynomialValue p x| : ℝ) : ℂ) *
        ((fullParity x : ℂ) * (thresholdSign (polynomialValue p x) : ℂ)) =
      (fullParity x : ℂ) *
        (((|polynomialValue p x| : ℝ) : ℂ) *
          (thresholdSign (polynomialValue p x) : ℂ)) := by ring
    _ = walshChar Finset.univ x * (polynomialValue p x : ℂ) := by
      rw [← Complex.ofReal_mul, abs_mul_thresholdSign]
      simp only [fullParity, walshChar, Complex.ofReal_prod]

/-- The weighted pairing vanishes for the polynomial, weight,
and parity-modified threshold sign.  No Fourier-support assumption remains. -/
theorem polynomial_sqrtWeight_pairing_eq_zero
    {n d r s : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x, polynomialValue p x ≠ 0)
    (a b : EuclideanSpace ℂ (Cube n))
    (ha : WithLp.ofLp a ∈ fourierSpace n r)
    (hb : WithLp.ofLp b ∈ fourierSpace n s) (hrs : r + s < n - d) :
    let D := sqrtWeightEquiv (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x))
    inner ℂ (D b)
      (signMultiplier (fun x => fullParity x * thresholdSign (polynomialValue p x)) (D a))
        = 0 := by
  dsimp only
  apply sqrtWeight_pairing_eq_zero_of_fourier_separation
    (fun x => |polynomialValue p x|)
    (fun x => fullParity x * thresholdSign (polynomialValue p x))
    (fun x => walshChar Finset.univ x * (polynomialValue p x : ℂ))
    (fun x => abs_nonneg (polynomialValue p x)) (polynomial_signedWeight p)
    _ (fun a x => sqrtWeightEquiv_apply _ _ a x)
    _ (fun a x => signMultiplier_apply _ a x) a b ha hb
    (parity_polynomialValue_mem_fourierSpaceFrom hp hd) hrs

/-- The operator between two subspaces of weighted low-degree spaces is zero
below the polynomial's degree cutoff. -/
theorem polynomial_projectionBlock_eq_zero
    {n d r s : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x, polynomialValue p x ≠ 0)
    (U V : Submodule ℂ (EuclideanSpace ℂ (Cube n)))
    (hU : U ≤ weightedFourierSpace (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x)) r)
    (hV : V ≤ weightedFourierSpace (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x)) s)
    (hrs : r + s < n - d) :
    V.starProjection *
      signMultiplier (fun x => fullParity x * thresholdSign (polynomialValue p x)) *
        U.starProjection = 0 := by
  apply projectionBlock_eq_zero_of_map_pairing
    (fourierEuclideanSpace n r) (fourierEuclideanSpace n s) U V
    (sqrtWeightEquiv (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x))).toLinearMap _ hU hV
  intro a ha b hb
  apply polynomial_sqrtWeight_pairing_eq_zero (r := r) (s := s) p hp hd hnz a b
  · simpa only [mem_fourierEuclideanSpace] using ha
  · simpa only [mem_fourierEuclideanSpace] using hb
  · exact hrs

/-- Low antidiagonal vanishing for the actual weighted grading constructed
from the polynomial.  All geometric hypotheses are discharged. -/
theorem weightedFlag_block_eq_zero_of_polynomial_degree
    {n d r s : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x, polynomialValue p x ≠ 0) (hrs : r + s < n - d) :
    let K := weightedFourierFlag (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x))
    flagProjection K s *
      signMultiplier (fun x => fullParity x * thresholdSign (polynomialValue p x)) *
        flagProjection K r = 0 := by
  dsimp only
  apply polynomial_projectionBlock_eq_zero (r := r) (s := s) p hp hd hnz
  · simpa only [weightedFourierFlag_succ] using
      flagLayer_le_next
        (weightedFourierFlag (fun x => |polynomialValue p x|)
          (fun x => abs_pos.mpr (hnz x))) r
  · simpa only [weightedFourierFlag_succ] using
      flagLayer_le_next
        (weightedFourierFlag (fun x => |polynomialValue p x|)
          (fun x => abs_pos.mpr (hnz x))) s
  · exact hrs

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators ComplexConjugate


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.weightedFlag_block_eq_zero_of_polynomial_degree := @_root_.OAI.LeanBlast.GotsmanLinial.weightedFlag_block_eq_zero_of_polynomial_degree
