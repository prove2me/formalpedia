-- Prove2me | solution 1 for OAI.DirectCrouzeix.singular_diagonal_estimates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:56:56.795931+00:00
-- url     : https://prove2.me/submissions/59abb495-60f8-435d-a1b5-6a919a4f9797

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/PolynomialEnergy.lean:L165-L219
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.singular_diagonal_estimates. The node keeps its source
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
import Theorems.Thm_OAI_DirectCrouzeix_cross_boundary_estimate
import Theorems.Thm_OAI_DirectCrouzeix_hsSq_mul_le
import Theorems.Thm_OAI_DirectCrouzeix_tensor_entryPair
import Theorems.Thm_OAI_DirectCrouzeix_weighted_sequence_dual

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

theorem hsSq_conjTranspose {ι : Type u_14} {κ : Type u_15} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : hsSq Mᴴ = hsSq M := by
  simp only [hsSq_eq_sum_norm_sq, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

theorem hsSq_mul_le_right {ι : Type u_27} {κ : Type u_28} {τ : Type u_29} [Fintype ι] [Fintype κ]
    [Fintype τ]
    [DecidableEq τ] [DecidableEq κ] (F : Matrix ι κ ℂ) (G : Matrix κ τ ℂ) :
    hsSq (F * G) ≤ hsSq F * ‖G‖ ^ 2 := by
  simpa only [← Matrix.conjTranspose_mul, hsSq_conjTranspose,
    Matrix.l2_opNorm_conjTranspose, mul_comm] using hsSq_mul_le Gᴴ Fᴴ

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

theorem continuous_hsSq {ι : Type u_61} {κ : Type u_62} [Fintype ι] [Fintype κ] :
    Continuous (hsSq : Matrix ι κ ℂ → ℝ) := by
  change Continuous (fun M : Matrix ι κ ℂ => hsSq M)
  simp_rw [hsSq_eq_norm_hsVector_sq]
  exact hsCLM.continuous.norm.pow 2

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

theorem continuous_matrixPolynomialValue {m : ℕ} (G : MatrixPolynomial m) :
    Continuous (fun z => matrixPolynomialValue z G) :=
  (G.continuous_eval₂ (RingHom.id _)).comp (continuous_id.smul continuous_const)

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

theorem polynomialEnergy_mul_le {m : ℕ} (h : BoundaryCircle → ℂ) (hh : Continuous h)
    (F G : MatrixPolynomial m) (hF : ∀ t, ‖matrixPolynomialValue (h t) F‖ ≤ 1) :
    polynomialEnergy h (F * G) ≤ polynomialEnergy h G ∧
    polynomialEnergy h (G * F) ≤ polynomialEnergy h G := by
  have hint (H : MatrixPolynomial m) :
      Integrable (fun t => hsSq (matrixPolynomialValue (h t) H)) circleMeasure :=
    continuous_integrable_compact _
      (continuous_hsSq.comp ((continuous_matrixPolynomialValue H).comp hh))
  constructor
  · apply integral_mono (hint _) (hint _)
    intro t
    change hsSq (matrixPolynomialValue (h t) (F * G)) ≤ _
    rw [map_mul]
    exact (hsSq_mul_le _ _).trans (by
      have hn := pow_le_pow_left₀ (norm_nonneg _) (hF t) 2
      simpa using mul_le_mul_of_nonneg_right hn (hsSq_nonneg (matrixPolynomialValue (h t) G)))
  · apply integral_mono (hint _) (hint _)
    intro t
    change hsSq (matrixPolynomialValue (h t) (G * F)) ≤ _
    rw [map_mul]
    exact (hsSq_mul_le_right _ _).trans (by
      have hn := pow_le_pow_left₀ (norm_nonneg _) (hF t) 2
      simpa using mul_le_mul_of_nonneg_left hn (hsSq_nonneg (matrixPolynomialValue (h t) G)))

theorem singular_ordered_pairings {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (F G : MatrixPolynomial m) (x y : EuclideanSpace ℂ (Fin n × Fin m)) (γ : ℝ)
    (hFx : Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F) x =
      (γ : ℂ) • y)
    (hFy : ContinuousLinearMap.adjoint
      (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F)) y =
      (γ : ℂ) • x) :
    inner ℂ y (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A (F * G)) x) =
      (γ : ℂ)
      * inner ℂ x (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A G) x) ∧
    inner ℂ y (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A (G * F)) x) =
      (γ : ℂ)
      * inner ℂ y (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A G) y) := by
  simp only [map_mul,mul_apply_eq_comp]
  constructor
  · rw [← ContinuousLinearMap.adjoint_inner_left,hFy,inner_smul_left]
    simp
  · rw [hFx,map_smul,inner_smul_right]

theorem singular_diagonal_estimates {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℕ → Polynomial ℂ) (h : BoundaryCircle → ℂ) (hh : Continuous h)
    (hexpand : ∀ G : MatrixPolynomial m, ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      G = faberPolynomial b C)
    (hlower : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      ∑ k, hsSq (C k) ≤ polynomialEnergy h (faberPolynomial b C))
    (hupper : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      polynomialEnergy h (faberPolynomial b C) ≤ ∑ k : Fin N, faberWeight k * hsSq (C k))
    (R : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ) (hR : Continuous R)
    (hcoeff : ∀ k : ℕ, fourierCoeff R (-(k : ℤ)) = Polynomial.aeval A (b k))
    (F : MatrixPolynomial m) (hF : ∀ t, ‖matrixPolynomialValue (h t) F‖ ≤ 1)
    (X Y : Matrix (Fin n) (Fin m) ℂ) (γ : ℝ) (hγ : 0 < γ)
    (hFx : Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F) (hsVector X) =
      (γ : ℂ) • hsVector Y)
    (hFy : ContinuousLinearMap.adjoint
      (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F)) (hsVector Y) =
      (γ : ℂ) • hsVector X) :
    let a := ∫ t, hsSq (Yᴴ * R t * X) ∂circleMeasure
    (hsSq (Xᴴ * Polynomial.aeval A (b 0) * X) + (1/2 : ℝ) *
      ∑' k : ℕ, hsSq (Xᴴ * Polynomial.aeval A (b (k+1)) * X) ≤ a / γ^2) ∧
    (hsSq (Yᴴ * Polynomial.aeval A (b 0) * Y) + (1/2 : ℝ) *
      ∑' k : ℕ, hsSq (Yᴴ * Polynomial.aeval A (b (k+1)) * Y) ≤ a / γ^2) := by
  dsimp only
  let a := ∫ t, hsSq (Yᴴ * R t * X) ∂circleMeasure
  have ha : 0 ≤ a := integral_nonneg (fun _ => hsSq_nonneg _)
  have hdiv : 0 ≤ a / γ^2 := div_nonneg ha (sq_nonneg _)
  have htest (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ) :=
    singular_ordered_pairings A F (faberPolynomial b C) (hsVector X) (hsVector Y) γ hFx hFy
  have hbound (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ) :
      (‖∑ k : Fin N, entryPair (Xᴴ * Polynomial.aeval A (b k) * X) (C k)‖^2 ≤
        (a / γ^2) * ∑ k : Fin N, faberWeight k * hsSq (C k)) ∧
      (‖∑ k : Fin N, entryPair (Yᴴ * Polynomial.aeval A (b k) * Y) (C k)‖^2 ≤
        (a / γ^2) * ∑ k : Fin N, faberWeight k * hsSq (C k)) := by
    have hs := htest N C
    simp only [faber_pairing] at hs
    have hv := cross_boundary_estimate A b h hexpand hlower R hR hcoeff X Y
    have hl := hv (F * faberPolynomial b C)
    have hr := hv (faberPolynomial b C * F)
    rw [hs.1,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hγ,mul_pow] at hl
    rw [hs.2,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hγ,mul_pow] at hr
    have hm := polynomialEnergy_mul_le h hh F (faberPolynomial b C) hF
    have hl' := hl.trans (mul_le_mul_of_nonneg_left (hm.1.trans (hupper N C)) ha)
    have hr' := hr.trans (mul_le_mul_of_nonneg_left (hm.2.trans (hupper N C)) ha)
    constructor
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hγ)).mpr
      convert hl' using 1 ; ring
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hγ)).mpr
      convert hr' using 1 ; ring
  constructor
  · exact weighted_sequence_dual (fun k => Xᴴ * Polynomial.aeval A (b k) * X)
      (a / γ^2) hdiv (fun N C => (hbound N C).1)
  · exact weighted_sequence_dual (fun k => Yᴴ * Polynomial.aeval A (b k) * Y)
      (a / γ^2) hdiv (fun N C => (hbound N C).2)

end DirectCrouzeix

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder
open MeasureTheory


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.singular_diagonal_estimates := @_root_.OAI.DirectCrouzeix.singular_diagonal_estimates
