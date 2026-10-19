-- Prove2me | solution 1 for OAI.DirectCrouzeix.analytic_domain_core
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:59:27.720704+00:00
-- url     : https://prove2.me/submissions/fe678ecd-c1b4-44d7-ba2a-38ba57a6ae02

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/DomainCore.lean:L15-L117
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.analytic_domain_core. The node keeps its source
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
import Theorems.Thm_OAI_DirectCrouzeix_exists_singular_pair
import Theorems.Thm_OAI_DirectCrouzeix_positive_block_hsSq
import Theorems.Thm_OAI_DirectCrouzeix_singular_diagonal_estimates

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

theorem hsSq_smul {ι : Type u_16} {κ : Type u_17} [Fintype ι] [Fintype κ]
    (c : ℂ) (M : Matrix ι κ ℂ) : hsSq (c • M) = ‖c‖ ^ 2 * hsSq M := by
  simp only [hsSq_eq_sum_norm_sq, Matrix.smul_apply, smul_eq_mul, norm_mul,
    mul_pow, Finset.mul_sum]

end DirectCrouzeix

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.SingularPairs ----
namespace OAI

universe u_37 u_38 u_39 u_40

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem positive_compression_blocks {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin m) ℂ) (hR : (R + Rᴴ).PosSemidef) :
    (Matrix.fromBlocks
      (Xᴴ * R * X + (Xᴴ * R * X)ᴴ)
      ((Yᴴ * R * X + (Xᴴ * R * Y)ᴴ)ᴴ)
      (Yᴴ * R * X + (Xᴴ * R * Y)ᴴ)
      (Yᴴ * R * Y + (Yᴴ * R * Y)ᴴ)).PosSemidef := by
  have h := hR.conjTranspose_mul_mul_same (Matrix.fromCols X Y)
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols] at h
  simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    add_comm] using h

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

theorem continuous_hsSq {ι : Type u_61} {κ : Type u_62} [Fintype ι] [Fintype κ] :
    Continuous (hsSq : Matrix ι κ ℂ → ℝ) := by
  change Continuous (fun M : Matrix ι κ ℂ => hsSq M)
  simp_rw [hsSq_eq_norm_hsVector_sq]
  exact hsCLM.continuous.norm.pow 2

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

theorem fourierCoeff_star_matrix {ι : Type u_71} {κ : Type u_72} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (f : BoundaryCircle → Matrix ι κ ℂ) (hf : Continuous f) (k : ℤ) :
    fourierCoeff (fun t => (f t)ᴴ) k = (fourierCoeff f (-k))ᴴ := by
  unfold fourierCoeff
  have hh := conjugateTransposeCLM.integral_comp_comm
    ((continuous_integrable_compact _ hf).fourier_smul (-(-k)))
  simp only [conjugateTransposeCLM_apply] at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards with t
  simp only [neg_neg,Matrix.conjTranspose_smul,starRingEnd_apply,fourier_neg]

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

theorem matrix_energy_split {ι : Type u_73} {κ : Type u_74} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (f : BoundaryCircle → Matrix ι κ ℂ) (hf : Continuous f) :
    (∫ t, hsSq (f t) ∂circleMeasure) =
      (∑' n : ℕ, hsSq (fourierCoeff f (n+1))) + hsSq (fourierCoeff f 0) +
      ∑' n : ℕ, hsSq (fourierCoeff f (-(n+1))) := by
  have hp := matrix_circle_parseval f hf
  rw [← hp.tsum_eq]
  apply tsum_of_add_one_of_neg_add_one
  · exact hp.summable.comp_injective (by intro i j he; exact_mod_cast (add_right_cancel he : (i : ℤ) = j))
  · exact hp.summable.comp_injective (by intro i j he; exact_mod_cast (add_right_cancel (neg_injective he) : (i : ℤ) = j))

theorem hsSq_add_self {ι : Type u_77} {κ : Type u_78} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) :
    hsSq (A + A) = 4 * hsSq A := by
  rw [← two_smul ℂ A,hsSq_smul]
  norm_num

theorem fourierCoeff_add_star {ι : Type u_79} [Fintype ι] [DecidableEq ι]
    (P Q : BoundaryCircle → Matrix ι ι ℂ) (hP : Continuous P) (hQ : Continuous Q) (k : ℤ) :
    fourierCoeff (fun t => P t + (Q t)ᴴ) k =
      fourierCoeff P k + (fourierCoeff Q (-k))ᴴ := by
  have hQstar := conjugateTransposeCLM.continuous.comp hQ
  have hh := congrFun (fourierCoeff.add (continuous_integrable_compact _ hP)
    (continuous_integrable_compact _ hQstar)) k
  change fourierCoeff (fun t => P t + (Q t)ᴴ) k =
    fourierCoeff P k + fourierCoeff (fun t => (Q t)ᴴ) k at hh
  rwa [fourierCoeff_star_matrix Q hQ k] at hh

theorem anti_matrix_energy {ι : Type u_80} [Fintype ι] [DecidableEq ι]
    (P : BoundaryCircle → Matrix ι ι ℂ) (hP : Continuous P)
    (hpos : ∀ k : ℤ, 0 < k → fourierCoeff P k = 0) :
    (∫ t, hsSq (P t) ∂circleMeasure) = hsSq (fourierCoeff P 0) +
      ∑' n : ℕ, hsSq (fourierCoeff P (-(n+1))) := by
  rw [matrix_energy_split P hP]
  have hp : ∀ n : ℕ, fourierCoeff P (n+1) = 0 := fun n => hpos _ (by omega)
  simp only [hp,hsSq_zero,tsum_zero,zero_add]

theorem anti_diagonal_energy {ι : Type u_81} [Fintype ι] [DecidableEq ι]
    (P : BoundaryCircle → Matrix ι ι ℂ) (hP : Continuous P)
    (hpos : ∀ k : ℤ, 0 < k → fourierCoeff P k = 0)
    (hzero : (fourierCoeff P 0).IsHermitian) :
    (∫ t, hsSq (P t + (P t)ᴴ) ∂circleMeasure) =
      4 * (hsSq (fourierCoeff P 0) +
        (1/2 : ℝ) * ∑' n : ℕ, hsSq (fourierCoeff P (-(n+1)))) := by
  have hcont : Continuous (fun t => P t + (P t)ᴴ) :=
    hP.add (conjugateTransposeCLM.continuous.comp hP)
  rw [matrix_energy_split _ hcont]
  have hp : ∀ n : ℕ, fourierCoeff P (n+1) = 0 := fun n => hpos _ (by omega)
  simp only [fourierCoeff_add_star P P hP hP,neg_zero,hzero.eq,hp,neg_neg,
    Matrix.conjTranspose_zero,zero_add,add_zero,hsSq_conjTranspose,hsSq_add_self]
  ring

theorem anti_cross_energy {ι : Type u_82} [Fintype ι] [DecidableEq ι]
    (M L : BoundaryCircle → Matrix ι ι ℂ) (hM : Continuous M) (hL : Continuous L)
    (hMp : ∀ k : ℤ, 0 < k → fourierCoeff M k = 0)
    (hLp : ∀ k : ℤ, 0 < k → fourierCoeff L k = 0)
    (hzero : (fourierCoeff L 0)ᴴ = fourierCoeff M 0) :
    (∫ t, hsSq (M t) ∂circleMeasure) ≤
      ∫ t, hsSq (M t + (L t)ᴴ) ∂circleMeasure := by
  have hcont : Continuous (fun t => M t + (L t)ᴴ) :=
    hM.add (conjugateTransposeCLM.continuous.comp hL)
  rw [matrix_energy_split _ hcont,anti_matrix_energy M hM hMp]
  have hpM : ∀ n : ℕ, fourierCoeff M (n+1) = 0 := fun n => hMp _ (by omega)
  have hpL : ∀ n : ℕ, fourierCoeff L (n+1) = 0 := fun n => hLp _ (by omega)
  simp_rw [fourierCoeff_add_star M L hM hL,neg_zero,hzero,hpM,neg_neg,hpL,
    Matrix.conjTranspose_zero,zero_add,add_zero,hsSq_conjTranspose,hsSq_add_self]
  have hsum : 0 ≤ ∑' n : ℕ, hsSq (fourierCoeff L (-(n+1))) :=
    tsum_nonneg (fun _ => hsSq_nonneg _)
  nlinarith [hsSq_nonneg (fourierCoeff M 0)]

end DirectCrouzeix

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.DomainCore ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

theorem analytic_domain_core {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) (b : ℕ → Polynomial ℂ) (hb0 : b 0 = 1)
    (h : BoundaryCircle → ℂ) (hh : Continuous h)
    (hexpand : ∀ G : MatrixPolynomial m, ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      G = faberPolynomial b C)
    (hlower : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      ∑ k, hsSq (C k) ≤ polynomialEnergy h (faberPolynomial b C))
    (hupper : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      polynomialEnergy h (faberPolynomial b C) ≤ ∑ k : Fin N, faberWeight k * hsSq (C k))
    (R : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ) (hR : Continuous R)
    (hcoeff : ∀ k : ℕ, fourierCoeff R (-(k : ℤ)) = Polynomial.aeval A (b k))
    (hposfreq : ∀ k : ℤ, 0 < k → fourierCoeff R k = 0)
    (hpositive : ∀ t, (R t + (R t)ᴴ).PosSemidef)
    (F : MatrixPolynomial m) (hF : ∀ t, ‖matrixPolynomialValue (h t) F‖ ≤ 1) :
    ‖tensorPolynomial A F‖ ≤ 2 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let γ := ‖tensorPolynomial A F‖
  by_cases hγ0 : γ = 0
  · change γ ≤ 2
    rw [hγ0]
    norm_num
  have hγ : 0 < γ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hγ0)
  let T := Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F)
  have hT : ‖T‖ = γ := Matrix.l2_opNorm_toEuclideanCLM _
  obtain ⟨x,y,hx,hy,hxy,hyx⟩ := exists_singular_pair T (hT ▸ hγ)
  rw [hT] at hxy hyx
  let X := matrixify x
  let Y := matrixify y
  have hFx : T (hsVector X) = (γ : ℂ) • hsVector Y := by simpa only [X,Y,hsVector_matrixify] using hxy
  have hFy : ContinuousLinearMap.adjoint T (hsVector Y) = (γ : ℂ) • hsVector X := by
    simpa only [X,Y,hsVector_matrixify] using hyx
  let P := fun t => Xᴴ * R t * X
  let Q := fun t => Yᴴ * R t * Y
  let M := fun t => Yᴴ * R t * X
  let L := fun t => Xᴴ * R t * Y
  have hC (U V : Matrix (Fin n) (Fin m) ℂ) :
      Continuous (fun t => Vᴴ * R t * U) := (compressionCLM U V).continuous.comp hR
  have hCp (U V : Matrix (Fin n) (Fin m) ℂ) (k : ℤ) (hk : 0 < k) :
      fourierCoeff (fun t => Vᴴ * R t * U) k = 0 := by
    rw [fourierCoeff_compression U V R hR,hposfreq k hk]
    simp
  have hCc (U V : Matrix (Fin n) (Fin m) ℂ) (k : ℕ) :
      fourierCoeff (fun t => Vᴴ * R t * U) (-(k : ℤ)) = Vᴴ * Polynomial.aeval A (b k) * U := by
    rw [fourierCoeff_compression U V R hR,hcoeff]
  have hC0 (U V : Matrix (Fin n) (Fin m) ℂ) :
      fourierCoeff (fun t => Vᴴ * R t * U) 0 = Vᴴ * U := by
    simpa only [Int.natCast_zero,neg_zero,hb0,map_one,Matrix.mul_one] using hCc U V 0
  let a := ∫ t, hsSq (M t) ∂circleMeasure
  have ha : 0 ≤ a := integral_nonneg (fun _ => hsSq_nonneg _)
  have hapos : 0 < a := by
    have hv := cross_boundary_estimate A b h hexpand hlower R hR hcoeff X Y F
    change ‖inner ℂ (hsVector Y) (T (hsVector X))‖^2 ≤ a * polynomialEnergy h F at hv
    have hyHS : ‖hsVector Y‖ = 1 := by simpa only [Y,hsVector_matrixify] using hy
    rw [hFx,inner_smul_right,inner_self_eq_norm_sq_to_K,hyHS] at hv
    by_contra hnot
    have ha0 : a = 0 := le_antisymm (not_lt.mp hnot) ha
    rw [ha0,zero_mul] at hv
    have hv' : γ^2 ≤ 0 := by simpa using hv
    nlinarith [sq_pos_of_pos hγ]
  have hdiag := singular_diagonal_estimates A b h hh hexpand hlower hupper R hR hcoeff F hF X Y γ hγ hFx hFy
  change (_ ≤ a/γ^2) ∧ (_ ≤ a/γ^2) at hdiag
  have hPE : (∫ t, hsSq (P t + (P t)ᴴ) ∂circleMeasure) ≤ 4*a/γ^2 := by
    rw [anti_diagonal_energy P (hC X X) (hCp X X)]
    · have hc0 := hCc X X 0
      have hcs (k : ℕ) := hCc X X (k+1)
      simp only [Int.natCast_zero,neg_zero,Nat.cast_add,Nat.cast_one] at hc0 hcs
      simp_rw [show P = (fun t => Xᴴ * R t * X) from rfl,hc0,hcs]
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hdiag.1 (by norm_num : (0 : ℝ) ≤ 4)
    · rw [hC0 X X]
      exact Matrix.isHermitian_conjTranspose_mul_self X
  have hQE : (∫ t, hsSq (Q t + (Q t)ᴴ) ∂circleMeasure) ≤ 4*a/γ^2 := by
    rw [anti_diagonal_energy Q (hC Y Y) (hCp Y Y)]
    · have hc0 := hCc Y Y 0
      have hcs (k : ℕ) := hCc Y Y (k+1)
      simp only [Int.natCast_zero,neg_zero,Nat.cast_add,Nat.cast_one] at hc0 hcs
      simp_rw [show Q = (fun t => Yᴴ * R t * Y) from rfl,hc0,hcs]
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hdiag.2 (by norm_num : (0 : ℝ) ≤ 4)
    · rw [hC0 Y Y]
      exact Matrix.isHermitian_conjTranspose_mul_self Y
  have hME : a ≤ ∫ t, hsSq (M t + (L t)ᴴ) ∂circleMeasure := by
    apply anti_cross_energy M L (hC X Y) (hC Y X) (hCp X Y) (hCp Y X)
    rw [hC0 Y X,hC0 X Y]
    simp
  have hEcont (U V U' V' : Matrix (Fin n) (Fin m) ℂ) :
      Continuous (fun t => hsSq (Vᴴ * R t * U + (V'ᴴ * R t * U')ᴴ)) :=
    continuous_hsSq.comp ((hC U V).add (conjugateTransposeCLM.continuous.comp (hC U' V')))
  have hpi := continuous_integrable_compact circleMeasure (hEcont X X X X)
  have hqi := continuous_integrable_compact circleMeasure (hEcont Y Y Y Y)
  have hmi := continuous_integrable_compact circleMeasure (hEcont X Y Y X)
  have hblock : 2 * (∫ t, hsSq (M t + (L t)ᴴ) ∂circleMeasure) ≤
      (∫ t, hsSq (P t + (P t)ᴴ) ∂circleMeasure) +
      ∫ t, hsSq (Q t + (Q t)ᴴ) ∂circleMeasure := by
    rw [← integral_const_mul,← integral_add hpi hqi]
    exact integral_mono (hmi.const_mul 2) (hpi.add hqi)
      (fun t => positive_block_hsSq (positive_compression_blocks (R t) X Y (hpositive t)))
  have hb : 2*a ≤ 8*a/γ^2 := by
    simp only [mul_div_assoc] at hPE hQE ⊢
    linarith
  have hmul := (le_div_iff₀ (sq_pos_of_pos hγ)).mp hb
  change γ ≤ 2
  have hg2 : γ^2 ≤ 4 := by nlinarith [hapos]
  nlinarith

end DirectCrouzeix

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder
open MeasureTheory


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.analytic_domain_core := @_root_.OAI.DirectCrouzeix.analytic_domain_core
