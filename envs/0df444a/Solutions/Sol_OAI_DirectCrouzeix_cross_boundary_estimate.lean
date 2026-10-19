-- Prove2me | solution 1 for OAI.DirectCrouzeix.cross_boundary_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:55:11.351534+00:00
-- url     : https://prove2.me/submissions/5614ab74-6288-4496-be37-eb0bec2de64f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/PolynomialEnergy.lean:L121-L144
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.cross_boundary_estimate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_DirectCrouzeix_tensor_entryPair

-- ---- from OAI.Analysis.DirectCrouzeix.PositiveBlocks ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem hsSq_nonneg {ι : Type u_3} {κ : Type u_4} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : 0 ≤ hsSq M := by
  exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self M).trace_nonneg).1

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

theorem hsSq_map_star {ι : Type u_22} {κ : Type u_23} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : hsSq (M.map star) = hsSq M := by
  simp [hsSq_eq_sum_norm_sq]

theorem entryPair_eq_inner {ι : Type u_30} {κ : Type u_31} [Fintype ι] [Fintype κ]
    (M C : Matrix ι κ ℂ) :
    entryPair M C = inner ℂ (hsVector (M.map star)) (hsVector C) := by
  simp [entryPair, hsVector, PiLp.inner_apply, Fintype.sum_prod_type, mul_comm]

theorem norm_entryPair_sq_le {ι : Type u_32} {κ : Type u_33} [Fintype ι] [Fintype κ]
    (M C : Matrix ι κ ℂ) : ‖entryPair M C‖ ^ 2 ≤ hsSq M * hsSq C := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (hsVector (M.map star)) (hsVector C)
  have h' := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [← entryPair_eq_inner, mul_pow, ← hsSq_eq_norm_hsVector_sq,
    ← hsSq_eq_norm_hsVector_sq, hsSq_map_star] at h'
  exact h'

theorem norm_sum_entryPair_sq_le {ρ : Type u_34} {ι : Type u_35} {κ : Type u_36} [Fintype ρ]
    [Fintype ι] [Fintype κ]
    (M C : ρ → Matrix ι κ ℂ) :
    ‖∑ k, entryPair (M k) (C k)‖ ^ 2 ≤ (∑ k, hsSq (M k)) * ∑ k, hsSq (C k) := by
  have h := norm_entryPair_sq_le
    (fun (p : ρ × ι) (j : κ) => M p.1 p.2 j)
    (fun (p : ρ × ι) (j : κ) => C p.1 p.2 j)
  rw [hsSq_eq_sum_norm_sq (fun (p : ρ × ι) (j : κ) => M p.1 p.2 j),
    hsSq_eq_sum_norm_sq (fun (p : ρ × ι) (j : κ) => C p.1 p.2 j)] at h
  simpa only [entryPair, hsSq_eq_sum_norm_sq, Fintype.sum_prod_type] using h

end DirectCrouzeix

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.CircleFourier ----
namespace OAI

universe u_47 u_48 u_49 u_50 u_51 u_52 u_53 u_54 u_55 u_56 u_57 u_58 u_59 u_60 u_61 u_62 u_63 u_64
  u_65 u_66 u_67 u_68 u_69 u_70 u_71 u_72

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

theorem continuous_integrable_compact {α : Type u_47} {E : Type u_48} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [CompactSpace α]
    [NormedAddCommGroup E] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem scalar_circle_parseval (f : BoundaryCircle → ℂ) (hf : Continuous f) :
    HasSum (fun k : ℤ => ‖fourierCoeff f k‖ ^ 2)
      (∫ t, ‖f t‖ ^ 2 ∂circleMeasure) := by
  let F : C(BoundaryCircle, ℂ) := ⟨f, hf⟩
  have h := hasSum_sq_fourierCoeff (ContinuousMap.toLp 2 circleMeasure ℂ F)
  simp_rw [fourierCoeff_toLp] at h
  have hi : (∫ t, ‖(ContinuousMap.toLp 2 circleMeasure ℂ F) t‖ ^ 2 ∂circleMeasure) =
      ∫ t, ‖f t‖ ^ 2 ∂circleMeasure := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ENNReal)) (𝕜 := ℂ) circleMeasure F]
      with t ht
    rw [ht]
    rfl
  rwa [hi] at h

theorem fourierCoeff_euclidean_apply {ι : Type u_55} [Fintype ι]
    (f : BoundaryCircle → EuclideanSpace ℂ ι) (hf : Continuous f)
    (k : ℤ) (i : ι) : (fourierCoeff f k) i = fourierCoeff (fun t => f t i) k := by
  have hi : Integrable (fun t => fourier (-k) t • f t) circleMeasure :=
    (continuous_integrable_compact _ hf).fourier_smul _
  exact ((EuclideanSpace.proj i).integral_comp_comm hi).symm

theorem euclidean_circle_parseval {ι : Type u_56} [Fintype ι]
    (f : BoundaryCircle → EuclideanSpace ℂ ι) (hf : Continuous f) :
    HasSum (fun k : ℤ => ‖fourierCoeff f k‖ ^ 2)
      (∫ t, ‖f t‖ ^ 2 ∂circleMeasure) := by
  have h (i : ι) := scalar_circle_parseval (fun t => f t i)
    ((PiLp.continuous_apply 2 (fun _ : ι => ℂ) i).comp hf)
  have hs := hasSum_sum (s := Finset.univ) (fun i _ => h i)
  simp_rw [← fourierCoeff_euclidean_apply f hf] at hs
  simp_rw [EuclideanSpace.norm_sq_eq]
  have hi (i : ι) : Integrable (fun t => ‖f t i‖ ^ 2) circleMeasure :=
    continuous_integrable_compact _
      (((PiLp.continuous_apply 2 (fun _ : ι => ℂ) i).comp hf).norm.pow 2)
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  exact hs

theorem fourierCoeff_clm {E : Type u_63} {F : Type u_64} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) (f : BoundaryCircle → E) (hf : Continuous f) (k : ℤ) :
    fourierCoeff (fun t => L (f t)) k = L (fourierCoeff f k) := by
  unfold fourierCoeff
  simp_rw [← map_smul]
  exact L.integral_comp_comm ((continuous_integrable_compact _ hf).fourier_smul _)

theorem matrix_circle_parseval {ι : Type u_65} {κ : Type u_66} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (f : BoundaryCircle → Matrix ι κ ℂ) (hf : Continuous f) :
    HasSum (fun k : ℤ => hsSq (fourierCoeff f k))
      (∫ t, hsSq (f t) ∂circleMeasure) := by
  have hp := euclidean_circle_parseval (fun t => hsCLM (f t)) (hsCLM.continuous.comp hf)
  simp_rw [fourierCoeff_clm hsCLM f hf, hsCLM_apply, ← hsSq_eq_norm_hsVector_sq] at hp
  exact hp

theorem fourierCoeff_compression {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) ℂ)
    (R : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ) (hR : Continuous R) (k : ℤ) :
    fourierCoeff (fun t => Yᴴ * R t * X) k = Yᴴ * fourierCoeff R k * X :=
  fourierCoeff_clm (compressionCLM X Y) R hR k

end DirectCrouzeix

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.BoundaryEnergy ----
namespace OAI

universe u_73 u_74 u_75 u_76 u_77 u_78 u_79 u_80 u_81 u_82 u_83 u_84 u_85 u_86

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

theorem finite_negative_bessel {ι : Type u_83} {κ : Type u_84} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (P : BoundaryCircle → Matrix ι κ ℂ) (hP : Continuous P) (N : ℕ) :
    (∑ k : Fin N, hsSq (fourierCoeff P (-(k : ℤ)))) ≤
      ∫ t, hsSq (P t) ∂circleMeasure := by
  classical
  let σ : Fin N → ℤ := fun k => -(k : ℤ)
  have hi : Function.Injective σ := by
    intro i j he
    apply Fin.ext
    exact_mod_cast neg_injective he
  have hp := matrix_circle_parseval P hP
  have hh := hp.summable.sum_le_tsum (Finset.univ.image σ) (fun _ _ => hsSq_nonneg _)
  rw [Finset.sum_image (fun i _ j _ he => hi he),hp.tsum_eq] at hh
  exact hh

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

theorem tensorPolynomial_scalar {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (p : Polynomial ℂ) :
    tensorPolynomial (m := m) A (scalarMatrixPolynomial p) = (Polynomial.aeval A p) ⊗ₖ 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [scalarMatrixPolynomial,Polynomial.map_add,map_add] at *
    rw [hp,hq,Matrix.add_kronecker]
  | monomial k c =>
    simp only [scalarMatrixPolynomial,← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,map_mul,map_pow,tensorPolynomial_C,tensorPolynomial_X,Polynomial.aeval_C,
      Polynomial.aeval_X,kronecker_pow_one,Algebra.algebraMap_eq_smul_one,
      Matrix.smul_kronecker,Matrix.kronecker_smul,← Matrix.mul_kronecker_mul,
      Matrix.smul_mul,Matrix.one_mul,Matrix.mul_one]

theorem tensorPolynomial_faber {n m N : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℕ → Polynomial ℂ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ) :
    tensorPolynomial A (faberPolynomial b C) = ∑ k : Fin N, Polynomial.aeval A (b k) ⊗ₖ C k := by
  simp only [faberPolynomial,map_sum,map_mul,tensorPolynomial_C,tensorPolynomial_scalar,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one]

theorem faber_pairing {n m N : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℕ → Polynomial ℂ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ)
    (X Y : Matrix (Fin n) (Fin m) ℂ) :
    inner ℂ (hsVector Y) (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ)
      (tensorPolynomial A (faberPolynomial b C)) (hsVector X)) =
      ∑ k : Fin N, entryPair (Yᴴ * Polynomial.aeval A (b k) * X) (C k) := by
  simp only [tensorPolynomial_faber,map_sum,sum_apply,inner_sum,tensor_entryPair]

theorem cross_boundary_estimate {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℕ → Polynomial ℂ) (h : BoundaryCircle → ℂ)
    (hexpand : ∀ G : MatrixPolynomial m, ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      G = faberPolynomial b C)
    (hlower : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      ∑ k, hsSq (C k) ≤ polynomialEnergy h (faberPolynomial b C))
    (R : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ) (hR : Continuous R)
    (hcoeff : ∀ k : ℕ, fourierCoeff R (-(k : ℤ)) = Polynomial.aeval A (b k))
    (X Y : Matrix (Fin n) (Fin m) ℂ) (G : MatrixPolynomial m) :
    ‖inner ℂ (hsVector Y) (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ)
      (tensorPolynomial A G) (hsVector X))‖ ^ 2 ≤
      (∫ t, hsSq (Yᴴ * R t * X) ∂circleMeasure) * polynomialEnergy h G := by
  obtain ⟨N,C,rfl⟩ := hexpand G
  rw [faber_pairing]
  let M := fun t => Yᴴ * R t * X
  have hM : Continuous M := (compressionCLM X Y).continuous.comp hR
  have hMc (k : ℕ) : fourierCoeff M (-(k : ℤ)) = Yᴴ * Polynomial.aeval A (b k) * X := by
    rw [fourierCoeff_compression X Y R hR,hcoeff]
  have hb := finite_negative_bessel M hM N
  simp_rw [hMc] at hb
  have hb0 : 0 ≤ ∫ t, hsSq (M t) ∂circleMeasure := integral_nonneg (fun _ => hsSq_nonneg _)
  exact (norm_sum_entryPair_sq_le _ C).trans
    ((mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg (fun _ _ => hsSq_nonneg _))).trans
      (mul_le_mul_of_nonneg_left (hlower N C) hb0))

end DirectCrouzeix

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder
open MeasureTheory


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.cross_boundary_estimate := @_root_.OAI.DirectCrouzeix.cross_boundary_estimate
