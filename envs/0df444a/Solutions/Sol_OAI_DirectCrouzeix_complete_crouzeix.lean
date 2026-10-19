-- Prove2me | solution 1 for OAI.DirectCrouzeix.complete_crouzeix
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:50:47.877013+00:00
-- url     : https://prove2.me/submissions/013f408e-4927-404d-9a75-e0eb6191dedf

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/CompleteBound.lean:L65-L97
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.DirectCrouzeix.complete_crouzeix.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_DirectCrouzeix_complete_crouzeix) verbatim and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_NormalFamilies
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExtremalEmbedding
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DiskMapping
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PoissonBoundary
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HarmonicReflection
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HolomorphicReflection
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ConformalCollar
import Definitions.Def_OAI_Analysis_DirectCrouzeix_AnalyticCharts
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExponentialLevels
import Definitions.Def_OAI_Analysis_DirectCrouzeix_InverseExterior
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SupportNets
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Convexity
import Definitions.Def_OAI_Analysis_DirectCrouzeix_OuterApproximation
import Theorems.Thm_OAI_DirectCrouzeix_Faber_algebraGenerating_fourier
import Theorems.Thm_OAI_DirectCrouzeix_Faber_chordDenominator_ne_zero
import Theorems.Thm_OAI_DirectCrouzeix_Faber_correction_identity
import Theorems.Thm_OAI_DirectCrouzeix_Faber_faber_hilbert_coefficient_bounds
import Theorems.Thm_OAI_DirectCrouzeix_Faber_taylorCoeff_pow_mul
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_convex_quadratic_range
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_exists_expLevel_exterior
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_exists_exponential_outer
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_expLevel_holomorphic_support
import Theorems.Thm_OAI_DirectCrouzeix_analytic_domain_core
import Theorems.Thm_OAI_DirectCrouzeix_faber_expansion_of_degree
import Theorems.Thm_OAI_DirectCrouzeix_isUnit_resolvent_of_not_mem

-- ---- from OAI.Analysis.DirectCrouzeix.NumericalRange ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

theorem numericalRange_eq_image {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    numericalRange A =
      (fun u : EuclideanSpace ℂ (Fin n) => inner ℂ u
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u)) '' Metric.sphere 0 1 := by
  ext z
  simp [numericalRange, Set.mem_image]

theorem isCompact_numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    IsCompact (numericalRange A) := by
  rw [numericalRange_eq_image]
  exact (isCompact_sphere (0 : EuclideanSpace ℂ (Fin n)) 1).image
    (continuous_id.inner (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).continuous)

theorem numericalRange_nonempty {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) : (numericalRange A).Nonempty := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [numericalRange_eq_image]
  exact (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)).image _

theorem continuous_polynomialValue {m d : ℕ}
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) : Continuous (polynomialValue B) := by
  unfold polynomialValue
  exact continuous_finsetSum _ (fun k _ => (continuous_id.pow _).smul continuous_const)

theorem rangeMaximum_attained {n m d : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    ∃ z ∈ numericalRange A, ‖polynomialValue B z‖ = rangeMaximum A B := by
  have hc := (isCompact_numericalRange A).image (continuous_polynomialValue B).norm
  have hne := (numericalRange_nonempty hn A).image (fun z => ‖polynomialValue B z‖)
  obtain ⟨z, hz, he⟩ := hc.sSup_mem hne
  exact ⟨z, hz, he⟩

theorem norm_polynomialValue_le_rangeMaximum {n m d : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖polynomialValue B z‖ ≤ rangeMaximum A B := by
  apply le_csSup
  · exact (isCompact_numericalRange A).bddAbove_image
      (continuous_polynomialValue B).norm.continuousOn
  · exact ⟨z, hz, rfl⟩

open scoped MatrixOrder ComplexOrder

end DirectCrouzeix

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.Resolvent ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem quadratic_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) :
    quadratic (A + B) u = quadratic A u + quadratic B u := by
  simp [quadratic]

theorem quadratic_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) :
    quadratic (A - B) u = quadratic A u - quadratic B u := by
  simp [quadratic]

theorem quadratic_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) :
    quadratic (c • A) u = c * quadratic A u := by
  simp [quadratic]

theorem quadratic_one {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) :
    quadratic 1 u = (‖u‖ : ℂ) ^ 2 := by
  simp [quadratic, inner_self_eq_norm_sq_to_K]

theorem quadratic_star {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) :
    quadratic Aᴴ u = star (quadratic A u) := by
  simp only [quadratic, ← Matrix.star_eq_conjTranspose, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

theorem quadratic_vector_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) (c : ℂ) :
    quadratic A (c • u) = (star c * c) * quadratic A u := by
  simp [quadratic]
  ring

theorem quadratic_toLp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : Fin n → ℂ) :
    quadratic A (WithLp.toLp 2 u) = star u ⬝ᵥ (A *ᵥ u) := by
  simp [quadratic, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct_comm]

theorem posSemidef_of_unit_quadratic {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian)
    (hu : ∀ u : EuclideanSpace ℂ (Fin n), ‖u‖ = 1 → 0 ≤ (quadratic H u).re) :
    H.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro x
  refine Complex.nonneg_iff.mpr ⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩
  rw [← quadratic_toLp]
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
  change 0 ≤ (quadratic H v).re
  by_cases hv : v = 0
  · simp [hv, quadratic]
  let u : EuclideanSpace ℂ (Fin n) := ((‖v‖ : ℂ)⁻¹) • v
  have hun : ‖u‖ = 1 := norm_smul_inv_norm hv
  have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hv
  have he : (‖v‖ : ℂ) • u = v := by
    simp [u, smul_smul, hn]
  have hp := hu u hun
  rw [← he, quadratic_vector_smul]
  simpa [pow_two] using mul_nonneg (sq_nonneg ‖v‖) hp

theorem supported_matrix_posSemidef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z q : ℂ)
    (hs : ∀ w ∈ numericalRange A, 0 ≤ (star q * (z - w)).re) :
    (star q • (z • 1 - A) + q • (z • 1 - A)ᴴ).PosSemidef := by
  apply posSemidef_of_unit_quadratic
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      add_comm]
  intro u hu
  have hp := hs (quadratic A u) ⟨u, hu, rfl⟩
  rw [quadratic_add, quadratic_smul, quadratic_smul, quadratic_star,
    quadratic_sub, quadratic_smul, quadratic_one, hu]
  simp only [Complex.ofReal_one, one_pow, mul_one]
  have he : (star q * (z - quadratic A u) + q * star (z - quadratic A u)).re =
      2 * (star q * (z - quadratic A u)).re := by
    simp [Complex.mul_re]
    ring
  rw [he]
  linarith

theorem resolvent_congruence {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsUnit B) (q : ℂ) :
    Bᴴ * ((q • B⁻¹) + (q • B⁻¹)ᴴ) * B = star q • B + q • Bᴴ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det B).mp hB
  have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
  have hstar : Bᴴ * (B⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.conjTranspose_smul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [← Matrix.mul_assoc Bᴴ, hstar, Matrix.one_mul]
  exact add_comm _ _

theorem positive_resolvent_of_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z q : ℂ) (hB : IsUnit (z • 1 - A))
    (hs : ∀ w ∈ numericalRange A, 0 ≤ (star q * (z - w)).re) :
    (q • (z • 1 - A)⁻¹ + (q • (z • 1 - A)⁻¹)ᴴ).PosSemidef := by
  apply (Matrix.IsUnit.posSemidef_star_left_conjugate_iff hB).mp
  rw [Matrix.star_eq_conjTranspose, resolvent_congruence _ hB]
  exact supported_matrix_posSemidef A z q hs

theorem positive_resolvent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z q : ℂ) (hz : z ∉ numericalRange A)
    (hs : ∀ w ∈ numericalRange A, 0 ≤ (star q * (z - w)).re) :
    (q • (z • 1 - A)⁻¹ + (q • (z • 1 - A)⁻¹)ᴴ).PosSemidef :=
  positive_resolvent_of_isUnit A z q (isUnit_resolvent_of_not_mem A hz) hs

end DirectCrouzeix

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.PolynomialCalculus ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem kronecker_pow_one {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) ^ k = (A ^ k) ⊗ₖ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, ← Matrix.mul_kronecker_mul]
    simp [pow_succ]

theorem tensorPolynomial_coefficientPolynomial {n m d : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    tensorPolynomial A (coefficientPolynomial B) = tensorEvaluation A B := by
  simp only [coefficientPolynomial, map_sum, map_mul, map_pow,
    tensorPolynomial_C, tensorPolynomial_X, kronecker_pow_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, tensorEvaluation]

end DirectCrouzeix

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.HilbertSchmidt ----
namespace OAI

universe u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25
  u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem hsSq_eq_norm_hsVector_sq {ι : Type u_12} {κ : Type u_13} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : hsSq M = ‖hsVector M‖ ^ 2 := by
  simp [hsSq_eq_sum_norm_sq, EuclideanSpace.norm_sq_eq, hsVector, Fintype.sum_prod_type]

end DirectCrouzeix

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.PolynomialEnergy ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

theorem matrixPolynomialValue_scalar {m : ℕ} (p : Polynomial ℂ) (z : ℂ) :
    matrixPolynomialValue (m := m) z (scalarMatrixPolynomial p) = p.eval z • 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [scalarMatrixPolynomial,Polynomial.map_add,map_add] at *
    rw [hp,hq,Polynomial.eval_add,add_smul]
  | monomial k c =>
    simp only [scalarMatrixPolynomial,← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,map_mul,map_pow,matrixPolynomialValue_C,matrixPolynomialValue_X,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
    simp only [Algebra.algebraMap_eq_smul_one,smul_pow,one_pow,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.one_mul,smul_smul]
    rw [mul_comm]

theorem matrixPolynomialValue_faber {m N : ℕ} (b : ℕ → Polynomial ℂ)
    (C : Fin N → Matrix (Fin m) (Fin m) ℂ) (z : ℂ) :
    matrixPolynomialValue z (faberPolynomial b C) = ∑ k : Fin N, (b k).eval z • C k := by
  simp only [faberPolynomial,map_sum,map_mul,matrixPolynomialValue_C,matrixPolynomialValue_scalar,
    Matrix.mul_smul,Matrix.mul_one]

end DirectCrouzeix

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.CompactIntegrals ----
namespace OAI

universe u_87 u_88 u_89 u_90 u_91 u_92 u_93

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem continuousOn_integral_compact {α : Type u_89} {β : Type u_90} {E : Type u_91}
    [MetricSpace α] [ProperSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    [CompactSpace β] [SecondCountableTopology β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure β) [IsFiniteMeasure μ] {s : Set α} (hs : IsOpen s)
    {f : α → β → E} (hf : ContinuousOn f.uncurry (s ×ˢ univ)) :
    ContinuousOn (fun x => ∫ t, f x t ∂μ) s := by
  intro x hx
  obtain ⟨ε,hε,hsub⟩ := nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hx)
  have hc : Continuous (fun p : closedBall x ε × β => f p.1 p.2) := by
    apply hf.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    intro p
    exact ⟨hsub p.1.property,mem_univ _⟩
  have hi : Continuous (fun y : closedBall x ε => ∫ t, f y t ∂μ) := by
    simpa using continuous_parametric_integral_of_continuous (μ := μ) hc isCompact_univ
  have hi' : ContinuousOn (fun y => ∫ t, f y t ∂μ) (closedBall x ε) :=
    continuousOn_iff_continuous_domRestrict.mpr hi
  exact (hi'.continuousAt (closedBall_mem_nhds x hε)).continuousWithinAt

theorem chord_mem {s : Set ℂ} (hs : Convex ℝ s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : chord u v t ∈ s :=
  hs hu hv (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel _ _)

theorem continuous_chord : Continuous (fun p : (ℂ × ℂ) × ℝ => chord p.1.1 p.1.2 p.2) := by
  unfold chord
  fun_prop

theorem continuousOn_chordIntegral {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : ContinuousOn f s) {w : Parameter → ℂ} (hw : Continuous w) :
    ContinuousOn (fun p : ℂ × ℂ => chordIntegral f w p.1 p.2) (s ×ˢ s) := by
  apply continuousOn_integral_compact volume (hs.prod hs)
  apply (hw.comp continuous_snd).continuousOn.mul
  apply hf.comp
  · exact (continuous_chord.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).continuousOn
  · intro p hp
    exact chord_mem hconv hp.1.1 hp.1.2 p.2.property

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.DividedDifferences ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem continuousOn_correction {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {c : ℂ}
    (hH : ∀ u ∈ s, ∀ v ∈ s, chordDenominator c g u v ≠ 0) :
    ContinuousOn (fun p : ℂ × ℂ => correction c g p.1 p.2) (s ×ˢ s) := by
  have hD := continuousOn_chordIntegral hs hconv hg.deriv.continuousOn (continuous_const (y := (1:ℂ)))
  have hE := continuousOn_chordIntegral hs hconv hg.deriv.deriv.continuousOn
    (show Continuous (fun t : Parameter => ((1-(t:ℝ) : ℝ):ℂ)) by fun_prop)
  exact ((continuous_fst.mul continuous_snd).continuousOn.mul
    (hD.add (continuous_fst.continuousOn.mul hE))).div
    (continuousOn_const.sub ((continuous_fst.mul continuous_snd).continuousOn.mul hD))
    (fun p hp => hH p.1 hp.1 p.2 hp.2)

theorem hasDerivAt_exterior {s : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s)
    (c : ℂ) {ζ : ℂ} (hζ : ζ ≠ 0) (hζs : ζ⁻¹ ∈ s) :
    HasDerivAt (exterior c g) (c-ζ⁻¹^2*deriv g ζ⁻¹) ζ := by
  have hd := ((hasDerivAt_id ζ).const_mul c).add
    ((hg ζ⁻¹ hζs).differentiableAt.hasDerivAt.comp ζ (hasDerivAt_inv hζ))
  change HasDerivAt (fun z => exterior c g z) _ ζ
  simpa only [exterior, Function.comp_def, id_eq, mul_one, Pi.add_apply, inv_pow,
    div_eq_mul_inv, sub_eq_add_neg, mul_neg, mul_comm, mul_left_comm] using! hd

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.TaylorFourier ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem unitPoint_continuous : Continuous unitPoint := (fourier 1).continuous

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.FaberPolynomials ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u_106 u_107

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem analyticAt_localL {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (localL c g) 0 := by
  apply (analyticAt_const.add (analyticAt_id.mul hg)).inv
  simpa using hc

theorem analyticAt_localN {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (localN c g) 0 :=
  (analyticAt_const.sub ((analyticAt_id.pow 2).mul hg.deriv)).mul (analyticAt_localL hc hg)

theorem faberBasis_coeff (c : ℂ) (g : ℂ → ℂ) (k j : ℕ) :
    (faberBasis c g k).coeff j =
      if j ≤ k then taylorCoeff (fun u => localN c g u * localW c g u^j) k else 0 := by
  classical
  simp [faberBasis,Polynomial.coeff_monomial,Finset.sum_ite_eq']

theorem faberBasis_zero {c : ℂ} (hc : c ≠ 0) (g : ℂ → ℂ) : faberBasis c g 0 = 1 := by
  simp [faberBasis,hc]

theorem faberBasis_top_coeff {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    (faberBasis c g k).coeff k = c⁻¹ ^ k := by
  rw [faberBasis_coeff, ite_eq_left le_rfl]
  have he : (fun u => localN c g u * localW c g u^k) =
      (fun u => u^k*(localN c g u*localL c g u^k)) := by funext u; simp only [localW,mul_pow]; ring
  rw [he,taylorCoeff_pow_mul (f := fun u => localN c g u*localL c g u^k)
    ((analyticAt_localN hc hg).mul ((analyticAt_localL hc hg).pow k))]
  simp [hc]

theorem faberBasis_degree {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    (faberBasis c g k).degree = k := by
  have hn : (faberBasis c g k).coeff k ≠ 0 := by rw [faberBasis_top_coeff hc hg]; exact pow_ne_zero _ (inv_ne_zero hc)
  apply (Polynomial.degree_eq_iff_natDegree_eq (fun h => by simp [h] at hn)).mpr
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero _ hn
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [faberBasis_coeff,ite_eq_right (by omega)]

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.BoundaryKernel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_108 u_109 u_110 u_111 u_112 u_113 u_114 u_115 u_116

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem continuous_slice_right {α : Type u_113} {β : Type u_114} {E : Type u_115}
    [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace E] (f : α → β → E) (hf : Continuous f.uncurry) (x : α) :
    Continuous (f x) := by
  simpa only [Function.comp_def,Function.uncurry] using! hf.comp (continuous_const.prodMk continuous_id)

theorem unitPoint_ne_zero (t : Angle) : unitPoint t ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [unitPoint_norm]; norm_num)

theorem unitPoint_inv_mem {R : ℝ} (hR : 1 < R) (t : Angle) :
    (unitPoint t)⁻¹ ∈ ball (0:ℂ) R := by
  simpa only [mem_ball,dist_zero_right,norm_inv,unitPoint_norm,inv_one] using hR

theorem continuous_boundary {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) (c : ℂ) : Continuous (boundary c g) := by
  have hi : Continuous (fun t => (unitPoint t)⁻¹) := unitPoint_continuous.inv₀ unitPoint_ne_zero
  exact (continuous_const.mul unitPoint_continuous).add
    (hg.continuousOn.comp_continuous hi (unitPoint_inv_mem hR))

theorem continuous_boundaryCorrection {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0) :
    Continuous (boundaryCorrection c g).uncurry := by
  have hi : Continuous (fun t => (unitPoint t)⁻¹) := unitPoint_continuous.inv₀ unitPoint_ne_zero
  let f : Angle × Angle → ℂ × ℂ := fun p => ((unitPoint p.1)⁻¹,(unitPoint p.2)⁻¹)
  have hf : Continuous f := (hi.comp continuous_fst).prodMk (hi.comp continuous_snd)
  have hmaps : MapsTo f univ (ball 0 R ×ˢ ball 0 R) :=
    fun p _ => ⟨unitPoint_inv_mem hR p.1,unitPoint_inv_mem hR p.2⟩
  have he : (boundaryCorrection c g).uncurry = (fun p : ℂ × ℂ => correction c g p.1 p.2) ∘ f := rfl
  rw [he]
  exact (continuousOn_correction isOpen_ball (convex_ball 0 R) hg hH).comp_continuous hf
    (fun p => hmaps (mem_univ p))

theorem continuous_boundaryKernel {c : ℂ} {g : ℂ → ℂ}
    (hS : Continuous (boundaryCorrection c g).uncurry) : Continuous (boundaryKernel c g).uncurry := by
  exact continuous_const.add (continuous_const.mul (Complex.continuous_re.comp hS))

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.FaberEnergy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_128 u_129

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

section FaberHilbert

variable {E : Type u_128} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FaberHilbert

theorem re_circle_fraction {ζ μ : ℂ} (hζ : ‖ζ‖ = 1) (hμ : ‖μ‖ = 1)
    (hne : ζ ≠ μ) : 2 * (ζ / (ζ - μ)).re = 1 := by
  have hnζ : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using
      (show Complex.normSq ζ = 1 by rw [Complex.normSq_eq_norm_sq, hζ]; norm_num)
  have hnμ : μ.re ^ 2 + μ.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using
      (show Complex.normSq μ = 1 by rw [Complex.normSq_eq_norm_sq, hμ]; norm_num)
  have hd : Complex.normSq (ζ - μ) ≠ 0 := by
    exact mt Complex.normSq_eq_zero.mp (sub_ne_zero.mpr hne)
  rw [Complex.div_re]
  field_simp
  simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at *
  nlinarith

theorem scalarGenerating_exterior (c : ℂ) (g : ℂ → ℂ) (z : ℂ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    scalarGenerating c g z ζ⁻¹ = ζ*(c-ζ⁻¹^2*deriv g ζ⁻¹)/(exterior c g ζ-z) := by
  unfold scalarGenerating
  have he : c+ζ⁻¹*(g ζ⁻¹-z) = ζ⁻¹*(exterior c g ζ-z) := by
    simp only [exterior]; field_simp; ring
  rw [he,div_mul_eq_div_div,div_inv_eq_mul]
  ring

theorem reciprocal_fraction {ζ μ : ℂ} (hζ : ζ ≠ 0) (hμ : μ ≠ 0) :
    (1-ζ⁻¹/μ⁻¹)⁻¹ = ζ/(ζ-μ) := by
  have hquot : ζ⁻¹/μ⁻¹ = μ/ζ :=
    (div_eq_iff (inv_ne_zero hμ)).2 (by field_simp)
  have he : 1-ζ⁻¹/μ⁻¹ = (ζ-μ)/ζ := by rw [hquot]; field_simp
  rw [he,inv_div]

theorem unitPoint_injective : Function.Injective unitPoint := by
  intro t s h
  apply AddCircle.injective_toCircle (by norm_num : (1:ℝ) ≠ 0)
  apply Subtype.coe_injective
  simpa [unitPoint,fourier_apply] using h

theorem boundaryCorrection_identity {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    {t s : Angle} (hts : t ≠ s) :
    boundaryCorrection c g t s = boundaryNormal c g t/(boundary c g t-boundary c g s) -
      unitPoint t/(unitPoint t-unitPoint s) := by
  have ht := unitPoint_inv_mem hR t
  have hs := unitPoint_inv_mem hR s
  have hn : (unitPoint t)⁻¹ ≠ (unitPoint s)⁻¹ :=
    fun he => hts (unitPoint_injective (inv_injective he))
  have he := correction_identity isOpen_ball (convex_ball 0 R) hg c ht hs
    (inv_ne_zero (unitPoint_ne_zero s)) hn (hH _ ht _ hs)
  change correction c g ((unitPoint t)⁻¹) ((unitPoint s)⁻¹) =
    scalarGenerating c g (exterior c g ((unitPoint s)⁻¹)⁻¹) ((unitPoint t)⁻¹) - _ at he
  rw [inv_inv,scalarGenerating_exterior c g _ (unitPoint_ne_zero t),
    reciprocal_fraction (unitPoint_ne_zero t) (unitPoint_ne_zero s)] at he
  exact he

theorem boundaryKernel_nonneg_off_diagonal {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (hsupport : ∀ t s, 0 ≤ (conj (boundaryNormal c g t)*(boundary c g t-boundary c g s)).re)
    {t s : Angle} (hts : t ≠ s) : 0 ≤ boundaryKernel c g t s := by
  have hfrac := re_circle_fraction (unitPoint_norm t) (unitPoint_norm s)
    (fun he => hts (unitPoint_injective he))
  have hp : 0 ≤ (boundaryNormal c g t/(boundary c g t-boundary c g s)).re := by
    rw [Complex.div_re,← add_div]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simpa [Complex.mul_re] using hsupport t s
  rw [boundaryKernel,boundaryCorrection_identity hR hg hH hts,Complex.sub_re]
  linarith

theorem circle_nonneg_of_off_point (f : Angle → ℝ) (hf : Continuous f) (t : Angle)
    (h : ∀ s, s ≠ t → 0 ≤ f s) : 0 ≤ f t := by
  have hc : Continuous (fun x : ℝ => f (t+(x:Angle))) := hf.comp
    (continuous_const.add (AddCircle.continuous_mk' (1:ℝ)))
  have hlim : Tendsto (fun x : ℝ => f (t+(x:Angle))) (𝓝[>] 0) (𝓝 (f t)) := by
    simpa only [QuotientAddGroup.mk_zero,add_zero] using (hc.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with x hx
  apply h
  intro he
  have hz : (x:Angle) = 0 := by simpa using add_left_cancel (he.trans (add_zero t).symm)
  have hx0 := (AddCircle.coe_eq_zero_iff_of_mem_Ico (show x ∈ Ico (0:ℝ) 1 from ⟨hx.1.le,hx.2⟩)).mp hz
  exact (ne_of_gt hx.1) hx0

theorem boundaryKernel_nonnegative {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (hsupport : ∀ t s, 0 ≤ (conj (boundaryNormal c g t)*(boundary c g t-boundary c g s)).re) :
    ∀ t s, 0 ≤ boundaryKernel c g t s := by
  intro t s
  by_cases hts : t = s
  · subst s
    exact circle_nonneg_of_off_point _
      (continuous_slice_right _ (continuous_boundaryKernel (continuous_boundaryCorrection hR hg hH)) t) t
      (fun s hst => boundaryKernel_nonneg_off_diagonal hR hg hH hsupport (Ne.symm hst))
  · exact boundaryKernel_nonneg_off_diagonal hR hg hH hsupport hts

section BanachAlgebra

variable {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]

end BanachAlgebra

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.FaberCalculus ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_129 u_130

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

section BanachAlgebra

variable {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]

theorem ringInverse_smul {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄]
    [CompleteSpace 𝔄] {c : ℂ} (hc : c ≠ 0) (x : 𝔄) :
    Ring.inverse (c • x) = c⁻¹ • Ring.inverse x := by
  have hu : IsUnit (algebraMap ℂ 𝔄 c) := (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℂ 𝔄)
  have hi : Ring.inverse (algebraMap ℂ 𝔄 c) = algebraMap ℂ 𝔄 c⁻¹ := by
    have hm : algebraMap ℂ 𝔄 c * algebraMap ℂ 𝔄 c⁻¹ = 1 := by
      rw [← map_mul,mul_inv_cancel₀ hc,map_one]
    calc
      Ring.inverse (algebraMap ℂ 𝔄 c) = Ring.inverse (algebraMap ℂ 𝔄 c) *
          (algebraMap ℂ 𝔄 c * algebraMap ℂ 𝔄 c⁻¹) := by rw [hm,mul_one]
      _ = algebraMap ℂ 𝔄 c⁻¹ := by rw [← mul_assoc,Ring.inverse_mul_cancel _ hu,one_mul]
  rw [Algebra.smul_def,Ring.inverse_mul (Or.inl hu),hi,Algebra.smul_def,Algebra.commutes]

theorem algebraDenominator_exterior {𝔄 : Type u_129} [NormedRing 𝔄]
    [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]
    (c : ℂ) (g : ℂ → ℂ) (A : 𝔄) {u : ℂ} (hu : u ≠ 0) :
    algebraDenominator c g A u = u • (exterior c g u⁻¹ • 1 - A) := by
  simp only [algebraDenominator,exterior,inv_inv,smul_sub,smul_smul]
  congr 1
  congr 1
  field_simp

theorem algebraGenerating_exterior (c : ℂ) (g : ℂ → ℂ) (A : 𝔄) {ζ : ℂ} (hζ : ζ ≠ 0) :
    algebraGenerating c g A ζ⁻¹ = (ζ*(c-ζ⁻¹^2*deriv g ζ⁻¹)) •
      Ring.inverse (exterior c g ζ • 1 - A) := by
  rw [algebraGenerating,algebraDenominator_exterior c g A (inv_ne_zero hζ),inv_inv,
    ringInverse_smul (inv_ne_zero hζ),inv_inv,smul_smul,mul_comm]

end BanachAlgebra

end DirectCrouzeix.Faber

namespace DirectCrouzeix

open MeasureTheory Set Filter Metric

open scoped Topology ComplexConjugate MatrixOrder ComplexOrder

end DirectCrouzeix

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.ExteriorCollar ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix

open MeasureTheory Set Filter Metric

open scoped Topology ComplexConjugate MatrixOrder ComplexOrder

theorem faber_matrix_coefficient_bounds {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, Faber.chordDenominator c g u v ≠ 0)
    (hpositive : ∀ t s, 0 ≤ Faber.boundaryKernel c g t s)
    {m N : ℕ} (C : Fin N → Matrix (Fin m) (Fin m) ℂ) :
    (∑ k, hsSq (C k) ≤ polynomialEnergy (Faber.boundary c g) (faberPolynomial (Faber.faberBasis c g) C))
    ∧
      (polynomialEnergy (Faber.boundary c g) (faberPolynomial (Faber.faberBasis c g) C) ≤
        ∑ k : Fin N, faberWeight k * hsSq (C k)) := by
  have hh := Faber.faber_hilbert_coefficient_bounds hR hg hc hH hpositive (fun k => hsVector (C k))
  have he (t : Faber.Angle) :
      Faber.faberBoundarySeries c g (fun k => hsVector (C k)) t =
        hsVector (matrixPolynomialValue (Faber.boundary c g t) (faberPolynomial (Faber.faberBasis c g) C)) := by
    rw [matrixPolynomialValue_faber]
    ext p
    simp [Faber.faberBoundarySeries,hsVector,Matrix.sum_apply,Matrix.smul_apply]
  simp_rw [he,← hsSq_eq_norm_hsVector_sq] at hh
  exact hh

theorem faber_resolvent_data {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (houtside : ∀ ζ : ℂ, 1 ≤ ‖ζ‖ → Faber.exterior c g ζ ∉ numericalRange A)
    (hsupport : ∀ t, ∀ w ∈ numericalRange A,
      0 ≤ (conj (Faber.boundaryNormal c g t) * (Faber.boundary c g t-w)).re) :
    ∃ Q : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ,
      Continuous Q ∧
      (∀ k : ℕ, fourierCoeff Q (-(k:ℤ)) = Polynomial.aeval A (Faber.faberBasis c g k)) ∧
      (∀ k : ℤ, 0 < k → fourierCoeff Q k = 0) ∧
      (∀ t, (Q t+(Q t)ᴴ).PosSemidef) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Q := fun t : Faber.Angle => Faber.algebraGenerating c g A (Faber.unitPoint t)⁻¹
  have hu : ∀ u ∈ closedBall (0:ℂ) 1, IsUnit (Faber.algebraDenominator c g A u) := by
    intro u hu
    by_cases hu0 : u = 0
    · subst u
      simpa [Faber.algebraDenominator,Algebra.smul_def] using
        (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ))
    · rw [Faber.algebraDenominator_exterior c g A hu0,Algebra.smul_def]
      apply IsUnit.mul ((isUnit_iff_ne_zero.mpr hu0).map (algebraMap ℂ _))
      apply isUnit_resolvent_of_not_mem A
      apply houtside
      rw [norm_inv,one_le_inv₀ (norm_pos_iff.mpr hu0)]
      simpa [mem_closedBall,dist_zero_right] using hu
  have hd := Faber.algebraGenerating_fourier hR hc hg A hu
  refine ⟨Q,hd.1,hd.2.1,hd.2.2,?_⟩
  intro t
  have he : Q t = Faber.boundaryNormal c g t • (Faber.boundary c g t • 1-A)⁻¹ := by
    change Faber.algebraGenerating c g A (Faber.unitPoint t)⁻¹ = _
    rw [Faber.algebraGenerating_exterior c g A (Faber.unitPoint_ne_zero t)]
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rfl
  rw [he]
  exact positive_resolvent A _ _ (houtside _ (by rw [Faber.unitPoint_norm])) (hsupport t)

theorem exterior_collar_bound {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (hinj : InjOn (Faber.exterior c g) (Inv.inv ⁻¹' ball 0 R \ {0}))
    (hder : ∀ ζ : ℂ, ζ ≠ 0 → ζ⁻¹ ∈ ball 0 R → deriv (Faber.exterior c g) ζ ≠ 0)
    (hboundary : ∀ t s, 0 ≤ (conj (Faber.boundaryNormal c g t) *
      (Faber.boundary c g t-Faber.boundary c g s)).re)
    (houtside : ∀ ζ : ℂ, 1 ≤ ‖ζ‖ → Faber.exterior c g ζ ∉ numericalRange A)
    (hsupport : ∀ t, ∀ w ∈ numericalRange A,
      0 ≤ (conj (Faber.boundaryNormal c g t) * (Faber.boundary c g t-w)).re)
    (F : MatrixPolynomial m) (hF : ∀ t, ‖matrixPolynomialValue (Faber.boundary c g t) F‖ ≤ 1) :
    ‖tensorPolynomial A F‖ ≤ 2 := by
  have hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, Faber.chordDenominator c g u v ≠ 0 :=
    fun _ hu _ hv => Faber.chordDenominator_ne_zero (convex_ball 0 R) hg hc hinj hder hu hv
  have hp := Faber.boundaryKernel_nonnegative hR hg hH hboundary
  have hcs (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ) := faber_matrix_coefficient_bounds hR hg hc hH hp C
  obtain ⟨Q,hQ,hcoeff,hpos,hPSD⟩ := faber_resolvent_data hn A hR hg hc houtside hsupport
  apply analytic_domain_core hn hm A (Faber.faberBasis c g) (Faber.faberBasis_zero hc g)
    (Faber.boundary c g) (Faber.continuous_boundary hR hg c)
    (faber_expansion_of_degree hm _ (Faber.faberBasis_degree hc (hg 0 (mem_ball_self (by linarith)))))
    (fun N C => (hcs N C).1) (fun N C => (hcs N C).2) Q hQ hcoeff hpos hPSD F hF

end DirectCrouzeix

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

end Conformal

end DirectCrouzeix

end

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.DomainBound ----
namespace OAI

universe u_144 u_145

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix

open Set Filter Metric

theorem expLevel_domain_bound {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) {ι : Type u_144} [Fintype ι]
    (v : ι → ℂ) (b : ι → ℝ) (hc : IsCompact {z | Geometry.expLevel v b z ≤ 1})
    (hW : ∀ z ∈ numericalRange A, Geometry.expLevel v b z < 1)
    (F : MatrixPolynomial m)
    (hF : ∀ z, Geometry.expLevel v b z ≤ 1 → ‖matrixPolynomialValue z F‖ ≤ 1) :
    ‖tensorPolynomial A F‖ ≤ 2 := by
  obtain ⟨a,ha⟩ := numericalRange_nonempty hn A
  obtain ⟨R,hR,c,g,hc0,hg,hinj,hder,hcircle,hout⟩ :=
    Geometry.exists_expLevel_exterior v b hc (hW a ha)
  have hge (ζ : ℂ) (hζ : 1 ≤ ‖ζ‖) : 1 ≤ Geometry.expLevel v b (Faber.exterior c g ζ) := by
    rcases eq_or_lt_of_le hζ with he|hl
    · exact le_of_eq (hcircle ζ he.symm).symm
    · exact le_of_lt (hout ζ hl)
  have hs (t : Faber.Angle) (w : ℂ) (hw : Geometry.expLevel v b w ≤ 1) :
      0 ≤ (conj (Faber.boundaryNormal c g t)*(Faber.boundary c g t-w)).re := by
    have hdt := Faber.hasDerivAt_exterior hg c (Faber.unitPoint_ne_zero t) (Faber.unitPoint_inv_mem hR t)
    have hh := Geometry.expLevel_holomorphic_support v b (hW a ha) (Faber.unitPoint_norm t)
      hdt.differentiableAt.hasDerivAt (hder _ (Faber.unitPoint_ne_zero t) (Faber.unitPoint_inv_mem hR t)) hcircle hge hw
    have he : Faber.unitPoint t*deriv (Faber.exterior c g) (Faber.unitPoint t) = Faber.boundaryNormal c g t := by
      rw [hdt.deriv]; rfl
    rw [he,real_inner_eq_re_inner ℂ,RCLike.inner_apply] at hh
    change 0 ≤ ((Faber.exterior c g (Faber.unitPoint t)-w)*conj (Faber.boundaryNormal c g t)).re at hh
    simpa only [Faber.boundary,mul_comm] using hh
  apply exterior_collar_bound hn hm A hR hg hc0 hinj hder
  · intro t s
    exact hs t _ (le_of_eq (hcircle _ (Faber.unitPoint_norm s)))
  · intro ζ hζ hz
    have h1 := hge ζ hζ
    have h2 := hW _ hz
    linarith
  · intro t w hw
    exact hs t w (le_of_lt (hW w hw))
  · intro t
    exact hF _ (le_of_eq (hcircle _ (Faber.unitPoint_norm t)))

theorem expLevel_domain_bound_scaled {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) {ι : Type u_145} [Fintype ι]
    (v : ι → ℂ) (b : ι → ℝ) (hc : IsCompact {z | Geometry.expLevel v b z ≤ 1})
    (hW : ∀ z ∈ numericalRange A, Geometry.expLevel v b z < 1)
    (F : MatrixPolynomial m) {ρ : ℝ} (hρ : 0 < ρ)
    (hF : ∀ z, Geometry.expLevel v b z ≤ 1 → ‖matrixPolynomialValue z F‖ ≤ ρ) :
    ‖tensorPolynomial A F‖ ≤ 2*ρ := by
  have hb := expLevel_domain_bound hn hm A v b hc hW (((ρ⁻¹:ℝ):ℂ) • F) (by
    intro z hz
    rw [matrixPolynomialValue_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ)]
    exact (mul_le_mul_of_nonneg_left (hF z hz) (le_of_lt (inv_pos.mpr hρ))).trans_eq (inv_mul_cancel₀ (ne_of_gt hρ)))
  rw [tensorPolynomial_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ)] at hb
  have hh := mul_le_mul_of_nonneg_left hb (le_of_lt hρ)
  rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hρ),one_mul] at hh
  simpa only [mul_comm] using hh

end DirectCrouzeix

namespace DirectCrouzeix

open Set Metric

end DirectCrouzeix

end

end

end

end

end

end

end

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.CompleteBound ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix

open Set Metric

theorem convex_numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Convex ℝ (numericalRange A) :=
  Geometry.convex_quadratic_range (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).toLinearMap

theorem complete_crouzeix : UniversalBound 2 := by
  intro n m d hn hm A B
  let M := rangeMaximum A B
  have hM : 0 ≤ M := by
    obtain ⟨z,hz,he⟩ := rangeMaximum_attained hn A B
    rw [show M = ‖polynomialValue B z‖ from he.symm]
    exact norm_nonneg _
  apply le_of_forall_pos_le_add
  intro ε hε
  let ρ := M+ε/2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hMρ : M < ρ := by dsimp [ρ]; linarith
  let V := {z : ℂ | ‖polynomialValue B z‖ < ρ}
  have hV : IsOpen V := isOpen_lt (continuous_polynomialValue B).norm continuous_const
  have hWV : numericalRange A ⊆ V := by
    intro z hz
    exact lt_of_le_of_lt (norm_polynomialValue_le_rangeMaximum A B hz) hMρ
  obtain ⟨δ,hδ,hδV⟩ := (isCompact_numericalRange A).exists_thickening_subset_open hV hWV
  obtain ⟨D,v,b,hW,hc,hnear⟩ := Geometry.exists_exponential_outer (isCompact_numericalRange A)
    (numericalRange_nonempty hn A) (convex_numericalRange A) hδ
  have hbound : ∀ z, Geometry.expLevel v b z ≤ 1 →
      ‖matrixPolynomialValue z (coefficientPolynomial B)‖ ≤ ρ := by
    intro z hz
    rw [matrixPolynomialValue_coefficientPolynomial]
    apply le_of_lt
    apply hδV
    obtain ⟨w,hw,hzw⟩ := hnear z hz
    exact mem_thickening_iff.mpr ⟨w,hw,by simpa only [dist_eq_norm] using hzw⟩
  have hh := expLevel_domain_bound_scaled hn hm A v b hc hW (coefficientPolynomial B) hρ hbound
  rw [tensorPolynomial_coefficientPolynomial] at hh
  calc
    ‖tensorEvaluation A B‖ ≤ 2*ρ := hh
    _ = 2*rangeMaximum A B+ε := by dsimp [ρ,M]; ring

end DirectCrouzeix

end

end

end

end

end

end

end

end

end

end OAI

-- ---- mission target ----
open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Set Filter Metric
open Set
open scoped ComplexConjugate Matrix
open Set Metric

namespace OAI
namespace DirectCrouzeix
theorem _root_.solution : UniversalBound 2 := by
  first
    | exact OAI.DirectCrouzeix.complete_crouzeix
    | (apply OAI.DirectCrouzeix.complete_crouzeix <;> assumption)
    | (intros; apply OAI.DirectCrouzeix.complete_crouzeix <;> assumption)
end DirectCrouzeix
end OAI
