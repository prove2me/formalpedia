-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.jacquetVector3_norm_archComponent3_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/3798dd7a-4af1-5fd2-bd6b-630ff52213d7

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Theorems.Thm_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_jacquetVector3
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_scalar_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_apply_of_infPart_eq_of_isArchCompAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_re_eq_zero_of_isArchCompAt_of_isUnitaryChar
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_norm_iteratedFDerivWithin_diagOne_le
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Matrix.Basis
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_norm_archComponent3_le

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda

open MeasureTheory

section
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_norm_archComponent3_le.LanglandsTunnell"

namespace LanglandsTunnell p2m_export "LanglandsTunnell" "RealArchParam RealArchParam.discrete RealArchParam.principal" namespace CubicInduction p2m_export "LanglandsTunnell.CubicInduction" "gaussian3 polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq AdelicGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero archComponent3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂ archRootSum archPlaceComponent3 isGL3PsiWhittakerFn_jacquetVector3 jacquetVector3_scalar_mul apply_of_infPart_eq_of_isArchCompAt re_eq_zero_of_isArchCompAt_of_isUnitaryChar exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod upperUnipotent3_inv_eq" end LanglandsTunnell.CubicInduction
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.exists_forall_neg_re_lt (M : Multiset ℂ) : ∃ c : ℝ, ∀ μ ∈ M, -μ.re < c := by
  induction M using Multiset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | cons a M ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨max c (-a.re + 1), fun μ hμ => ?_⟩
    rcases Multiset.mem_cons.mp hμ with h | h
    · rw [h]
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    · exact lt_of_lt_of_le (hc μ h) (le_max_left _ _)

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.exists_forall_twist_neg_re_lt (P : RealArchParam) :
    ∃ c : ℝ, ∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c) ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c) := by
  obtain ⟨c, hc⟩ := LanglandsTunnell.CubicInduction.exists_forall_neg_re_lt
    ((Finset.univ : Finset (ZMod 2)).val.bind fun a => (P.twist 0 a).gammaR + (P.twist 0 a).gammaC)
  refine ⟨c, fun a => ⟨fun μ hμ => hc μ ?_, fun ν hν => hc ν ?_⟩⟩
  · exact Multiset.mem_bind.mpr ⟨a, Finset.mem_val.mpr (Finset.mem_univ a), Multiset.mem_add.mpr (Or.inl hμ)⟩
  · exact Multiset.mem_bind.mpr ⟨a, Finset.mem_val.mpr (Finset.mem_univ a), Multiset.mem_add.mpr (Or.inr hν)⟩

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam RealArchParam.discrete RealArchParam.principal"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gaussian3 polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq AdelicGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero archComponent3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂ archRootSum archPlaceComponent3 isGL3PsiWhittakerFn_jacquetVector3 jacquetVector3_scalar_mul apply_of_infPart_eq_of_isArchCompAt re_eq_zero_of_isArchCompAt_of_isUnitaryChar exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod upperUnipotent3_inv_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

namespace RootSizeBound

open Matrix in

private theorem exists_eq_unip_mul_diagonal_mul_orth (m : Matrix (Fin 3) (Fin 3) ℝ) (hm : m.det ≠ 0) :
    ∃ (x y z : ℝ) (d : Fin 3 → ℝ) (k : Matrix (Fin 3) (Fin 3) ℝ), (∀ i, d i ≠ 0) ∧ k * k.transpose = 1 ∧
      m = !![1, x, z; 0, 1, y; 0, 0, 1] * Matrix.diagonal d * k := by

  set m₀ : Fin 3 → ℝ := m 0 with hm₀
  set m₁ : Fin 3 → ℝ := m 1 with hm₁
  set m₂ : Fin 3 → ℝ := m 2 with hm₂

  have hu₂ : m₂ ≠ 0 := fun h => hm (Matrix.det_eq_zero_of_row_eq_zero 2 fun j => congrFun h j)
  have hu₂sq : m₂ ⬝ᵥ m₂ ≠ 0 := fun h => hu₂ (dotProduct_self_eq_zero.mp h)

  set α : ℝ := (m₁ ⬝ᵥ m₂) / (m₂ ⬝ᵥ m₂) with hα
  set u₁ : Fin 3 → ℝ := m₁ - α • m₂ with hu₁def
  have hu₁₂ : u₁ ⬝ᵥ m₂ = 0 := by
    rw [hu₁def, sub_dotProduct, smul_dotProduct, hα, smul_eq_mul, div_mul_cancel₀ _ hu₂sq, sub_self]

  have hdet₁ : (Matrix.of ![m₀, u₁, m₂]).det = m.det := by
    have : Matrix.of ![m₀, u₁, m₂] = m.updateRow 1 (m 1 + (-α) • m 2) := by
      ext i j; fin_cases i <;> simp [u₁, m₀, m₁, m₂, Matrix.updateRow_apply, sub_eq_add_neg]
    rw [this, Matrix.det_updateRow_add_smul_self m (by decide : (1 : Fin 3) ≠ 2)]
  have hu₁ : u₁ ≠ 0 := by
    intro h; apply hm; rw [← hdet₁]
    exact Matrix.det_eq_zero_of_row_eq_zero 1 fun j => by simp [h]
  have hu₁sq : u₁ ⬝ᵥ u₁ ≠ 0 := fun h => hu₁ (dotProduct_self_eq_zero.mp h)

  set β : ℝ := (m₀ ⬝ᵥ m₂) / (m₂ ⬝ᵥ m₂) with hβ
  set γ : ℝ := (m₀ ⬝ᵥ u₁) / (u₁ ⬝ᵥ u₁) with hγ
  set u₀ : Fin 3 → ℝ := m₀ - β • m₂ - γ • u₁ with hu₀def
  have hu₀₂ : u₀ ⬝ᵥ m₂ = 0 := by
    rw [hu₀def, sub_dotProduct, sub_dotProduct, smul_dotProduct, smul_dotProduct, hu₁₂, hβ, smul_eq_mul,
      div_mul_cancel₀ _ hu₂sq]
    simp
  have hu₀₁ : u₀ ⬝ᵥ u₁ = 0 := by
    have h₂₁ : m₂ ⬝ᵥ u₁ = 0 := by rw [dotProduct_comm]; exact hu₁₂
    rw [hu₀def, sub_dotProduct, sub_dotProduct, smul_dotProduct, smul_dotProduct, h₂₁, hγ]
    simp only [smul_eq_mul]
    rw [div_mul_cancel₀ _ hu₁sq]
    simp
  have hdet₀ : (Matrix.of ![u₀, u₁, m₂]).det = m.det := by
    rw [← hdet₁]
    have h1 : Matrix.of ![m₀ - β • m₂, u₁, m₂] =
        (Matrix.of ![m₀, u₁, m₂]).updateRow 0 (Matrix.of ![m₀, u₁, m₂] 0 + (-β) • Matrix.of ![m₀, u₁, m₂] 2) := by
      ext i j; fin_cases i <;> simp [Matrix.updateRow_apply, sub_eq_add_neg]
    have h2 : Matrix.of ![u₀, u₁, m₂] =
        (Matrix.of ![m₀ - β • m₂, u₁, m₂]).updateRow 0
          (Matrix.of ![m₀ - β • m₂, u₁, m₂] 0 + (-γ) • Matrix.of ![m₀ - β • m₂, u₁, m₂] 1) := by
      ext i j; fin_cases i <;> simp [u₀, Matrix.updateRow_apply, sub_eq_add_neg]
    rw [h2, Matrix.det_updateRow_add_smul_self _ (by decide : (0 : Fin 3) ≠ 1), h1,
      Matrix.det_updateRow_add_smul_self _ (by decide : (0 : Fin 3) ≠ 2)]
  have hu₀ : u₀ ≠ 0 := by
    intro h; apply hm; rw [← hdet₀]
    exact Matrix.det_eq_zero_of_row_eq_zero 0 fun j => by simp [h]
  have hu₀sq : u₀ ⬝ᵥ u₀ ≠ 0 := fun h => hu₀ (dotProduct_self_eq_zero.mp h)

  have hnn : ∀ u : Fin 3 → ℝ, 0 ≤ u ⬝ᵥ u := fun u => Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
  have hpos : ∀ u : Fin 3 → ℝ, u ⬝ᵥ u ≠ 0 → 0 < u ⬝ᵥ u := fun u hu => lt_of_le_of_ne (hnn u) (Ne.symm hu)
  set d : Fin 3 → ℝ := ![Real.sqrt (u₀ ⬝ᵥ u₀), Real.sqrt (u₁ ⬝ᵥ u₁), Real.sqrt (m₂ ⬝ᵥ m₂)] with hd
  have hd0 : d 0 ≠ 0 := by simp [d]; exact (Real.sqrt_pos.mpr (hpos _ hu₀sq)).ne'
  have hd1 : d 1 ≠ 0 := by simp [d]; exact (Real.sqrt_pos.mpr (hpos _ hu₁sq)).ne'
  have hd2 : d 2 ≠ 0 := by simp [d]; exact (Real.sqrt_pos.mpr (hpos _ hu₂sq)).ne'
  set U : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![u₀, u₁, m₂] with hU
  set k : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => U i j / d i with hk
  refine ⟨γ, α, β, d, k, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> assumption
  ·
    have hsq : ∀ i, d i * d i = U i ⬝ᵥ U i := by
      intro i; fin_cases i <;> simp [d, U] <;> exact Real.mul_self_sqrt (hnn _)
    have horth : ∀ i j, i ≠ j → U i ⬝ᵥ U j = 0 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | (simp [U]; first
            | exact hu₀₁ | exact hu₀₂ | exact hu₁₂
            | (rw [dotProduct_comm]; first | exact hu₀₁ | exact hu₀₂ | exact hu₁₂))
    ext i j
    have hdi : d i ≠ 0 := by fin_cases i <;> assumption
    have hdj : d j ≠ 0 := by fin_cases j <;> assumption
    have hentry : (k * k.transpose) i j = (U i ⬝ᵥ U j) / (d i * d j) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hk, Matrix.of_apply, dotProduct, Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ => ?_
      field_simp
    rw [hentry]
    by_cases hij : i = j
    · subst hij; rw [← hsq i, div_self (mul_ne_zero hdi hdi), Matrix.one_apply_eq]
    · rw [horth i j hij, zero_div, Matrix.one_apply_ne hij]
  ·
    have hdk : Matrix.diagonal d * k = U := by
      ext i j
      have hdi : d i ≠ 0 := by fin_cases i <;> assumption
      rw [Matrix.diagonal_mul, hk, Matrix.of_apply, mul_div_cancel₀ _ hdi]
    rw [Matrix.mul_assoc, hdk]
    ext i j
    fin_cases i <;> simp [U, u₀, u₁, m₀, m₁, m₂, Matrix.mul_apply, Fin.sum_univ_three]

section
open Matrix

namespace RootSizeAlg

private def _root_.LanglandsTunnell.CubicInduction.RootSizeBound.RootSizeAlg.unip (x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, x, z; 0, 1, y; 0, 0, 1]

p2m_export "LanglandsTunnell.CubicInduction.RootSizeBound.RootSizeAlg" "unip"
private theorem det_unip (x y z : ℝ) : (unip x y z).det = 1 := by
  simp [unip, Matrix.det_fin_three]

private theorem line_dot (k : Matrix (Fin 3) (Fin 3) ℝ) (hk : k * k.transpose = 1) (i j : Fin 3) :
    k i 0 * k j 0 + k i 1 * k j 1 + k i 2 * k j 2 = if i = j then 1 else 0 := by
  have h := congrFun (congrFun hk i) j
  simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] using h

private theorem abs_det_orth (k : Matrix (Fin 3) (Fin 3) ℝ) (hk : k * k.transpose = 1) : |k.det| = 1 := by
  have h : k.det * k.det = 1 := by
    have := congrArg Matrix.det hk
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have h' : |k.det| * |k.det| = 1 := by rw [← abs_mul, h, abs_one]
  nlinarith [abs_nonneg k.det]

private theorem entry_line2 (x y z : ℝ) (d : Fin 3 → ℝ) (k : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) :
    (unip x y z * Matrix.diagonal d * k) 2 j = d 2 * k 2 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.mul_diagonal]
  simp [unip]

private theorem entry_line1 (x y z : ℝ) (d : Fin 3 → ℝ) (k : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) :
    (unip x y z * Matrix.diagonal d * k) 1 j = d 1 * k 1 j + y * (d 2 * k 2 j) := by
  rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.mul_diagonal]
  simp [unip]
  ring

private theorem abs_det_shape (x y z : ℝ) (d : Fin 3 → ℝ) (k : Matrix (Fin 3) (Fin 3) ℝ) (hk : k * k.transpose = 1) :
    |(unip x y z * Matrix.diagonal d * k).det| = |d 0 * d 1 * d 2| := by
  rw [Matrix.det_mul, Matrix.det_mul, det_unip, one_mul, Matrix.det_diagonal, Fin.prod_univ_three, abs_mul,
    abs_det_orth k hk, mul_one]

private theorem lastLine_sq_shape (x y z : ℝ) (d : Fin 3 → ℝ) (k : Matrix (Fin 3) (Fin 3) ℝ) (hk : k * k.transpose = 1) :
    (unip x y z * Matrix.diagonal d * k) 2 0 ^ 2 + (unip x y z * Matrix.diagonal d * k) 2 1 ^ 2 +
        (unip x y z * Matrix.diagonal d * k) 2 2 ^ 2 = d 2 ^ 2 := by
  simp only [entry_line2]
  have h22 := line_dot k hk 2 2
  simp only [if_true] at h22
  linear_combination (d 2) ^ 2 * h22

private theorem minors_sq_shape (x y z : ℝ) (d : Fin 3 → ℝ) (k : Matrix (Fin 3) (Fin 3) ℝ) (hk : k * k.transpose = 1) :
    let m := unip x y z * Matrix.diagonal d * k
    (m 1 0 * m 2 1 - m 1 1 * m 2 0) ^ 2 + (m 1 0 * m 2 2 - m 1 2 * m 2 0) ^ 2 +
        (m 1 1 * m 2 2 - m 1 2 * m 2 1) ^ 2 = (d 1 * d 2) ^ 2 := by
  intro m
  have e1 : ∀ j, m 1 j = d 1 * k 1 j + y * (d 2 * k 2 j) := entry_line1 x y z d k
  have e2 : ∀ j, m 2 j = d 2 * k 2 j := entry_line2 x y z d k
  simp only [e1, e2]
  have h11 := line_dot k hk 1 1
  have h22 := line_dot k hk 2 2
  have h12 := line_dot k hk 1 2
  simp only [if_true, show (1 : Fin 3) ≠ 2 by decide, if_false] at h11 h22 h12

  linear_combination (d 1 * d 2) ^ 2 * ((k 2 0 * k 2 0 + k 2 1 * k 2 1 + k 2 2 * k 2 2) * h11 + h22 -
    (k 1 0 * k 2 0 + k 1 1 * k 2 1 + k 1 2 * k 2 2) * h12)

end RootSizeAlg

end

private theorem norm_archEval_eq_abs_realCoord (t : InfiniteAdeleRing ℚ) :
    ‖AdelicLevel.archEval ℚ Rat.infinitePlace t‖ = |StandardKernel.realCoord t| := by
  rw [StandardKernel.realCoord_apply, ← Real.norm_eq_abs,
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
      (map_zero _)]
  rfl

private theorem archPlaceComponent3_coe (w : InfinitePlace ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((archPlaceComponent3 ℚ w g : GL (Fin 3) w.Completion) : Matrix (Fin 3) (Fin 3) w.Completion) =
      (AdelicLevel.archEval ℚ w).mapMatrix
        (archComponent3 (𝓞 ℚ) ℚ g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :=
  rfl

private theorem norm_archPlaceComponent3_apply (w : InfinitePlace ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    ‖((archPlaceComponent3 ℚ w g : GL (Fin 3) w.Completion) : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ =
      |StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g) i j| := by
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  rw [archPlaceComponent3_coe, RingHom.mapMatrix_apply, Matrix.map_apply, StandardKernel.realMat_eq, Matrix.map_apply,
    norm_archEval_eq_abs_realCoord]

private theorem archRoot_eq (w : InfinitePlace ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x y z : ℝ) (d : Fin 3 → ℝ) (hd : ∀ i, d i ≠ 0)
    (k : Matrix (Fin 3) (Fin 3) ℝ) (hk : k * k.transpose = 1)
    (hg : StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g) = !![1, x, z; 0, 1, y; 0, 0, 1] * Matrix.diagonal d * k) :
    archRoot₁ ℚ w g = |d 0| / |d 1| ∧ archRoot₂ ℚ w g = |d 1| / |d 2| := by
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _

  have hm : StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g) = RootSizeAlg.unip x y z * Matrix.diagonal d * k := hg
  set A := archPlaceComponent3 ℚ Rat.infinitePlace g with hA

  have hent : ∀ i j : Fin 3, ‖(A : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j‖ =
      |(RootSizeAlg.unip x y z * Matrix.diagonal d * k) i j| := fun i j => by
    rw [← hm]; exact norm_archPlaceComponent3_apply Rat.infinitePlace g i j
  have hminor : ∀ j j' : Fin 3, ‖bottomMinor A j j'‖ =
      |(RootSizeAlg.unip x y z * Matrix.diagonal d * k) 1 j *
            (RootSizeAlg.unip x y z * Matrix.diagonal d * k) 2 j' -
          (RootSizeAlg.unip x y z * Matrix.diagonal d * k) 1 j' *
            (RootSizeAlg.unip x y z * Matrix.diagonal d * k) 2 j| := by
    intro j j'
    rw [← hm, StandardKernel.realMat_eq]
    simp only [bottomMinor, hA, archPlaceComponent3_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [← map_mul, ← map_mul, ← map_sub, norm_archEval_eq_abs_realCoord, map_sub, map_mul, map_mul]
  have hdet : detSize A = |d 0 * d 1 * d 2| := by
    rw [← RootSizeAlg.abs_det_shape x y z d k hk, ← hm, StandardKernel.realMat_eq, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, detSize, hA, archPlaceComponent3_coe, ← RingHom.map_det, norm_archEval_eq_abs_realCoord]
  have hrow : lastRowEucl A = |d 2| := by
    rw [lastRowEucl, hent, hent, hent, sq_abs, sq_abs, sq_abs, RootSizeAlg.lastLine_sq_shape x y z d k hk,
      Real.sqrt_sq_eq_abs]
  have hmin : minorEucl A = |d 1 * d 2| := by
    rw [minorEucl, hminor, hminor, hminor, sq_abs, sq_abs, sq_abs, RootSizeAlg.minors_sq_shape x y z d k hk,
      Real.sqrt_sq_eq_abs]
  have h1 : |d 1| ≠ 0 := abs_ne_zero.mpr (hd 1)
  have h2 : |d 2| ≠ 0 := abs_ne_zero.mpr (hd 2)
  refine ⟨?_, ?_⟩
  · rw [archRoot₁, hdet, hrow, hmin, abs_mul, abs_mul, abs_mul]
    field_simp
  · rw [archRoot₂, hmin, hrow, abs_mul]
    field_simp

private theorem norm_psiArch (t : InfiniteAdeleRing ℚ) : ‖NumberField.StandardAddChar.psiArch t‖ = 1 := by
  rw [NumberField.StandardAddChar.psiArch_apply, finprod_eq_prod_of_fintype, norm_prod]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [NumberField.StandardAddChar.psiArchPlace_apply, Complex.norm_exp]
  simp [-InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]

private theorem norm_jacquetVector3_upperUnipotent3_mul {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (x y z : InfiniteAdeleRing ℚ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ‖jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S (upperUnipotent3 x y z * g)‖ =
      ‖jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S g‖ := by
  rw [isGL3PsiWhittakerFn_jacquetVector3 P D u₃ a₃ a psiInf hpsiInf S x y z g, norm_mul, hpsiInf, norm_psiArch,
    one_mul]

private theorem re_archExponent_eq_zero (K : Type) [Field K] [NumberField K] (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) :
    ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw)).re = 0 := by
  classical
  have hre : ∀ (w : InfinitePlace K) (hw : w.IsReal), (uR w hw).re = 0 := fun w hw =>
    re_eq_zero_of_isArchCompAt_of_isUnitaryChar K μ hμ.2.2 w _ _ (huR w hw)
  have hreC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), (uC w hw).re = 0 := fun w hw =>
    re_eq_zero_of_isArchCompAt_of_isUnitaryChar K μ hμ.2.2 w _ _ (huC w hw)
  have h1 : (∑ᶠ (w) (hw : w.IsReal), uR w hw).re = 0 := by
    rw [finsum_eq_sum_of_fintype, Complex.re_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [finsum_eq_dif]
    split_ifs with hw
    · exact hre w hw
    · rfl
  have h2 : (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw).re = 0 := by
    rw [finsum_eq_sum_of_fintype, Complex.re_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [finsum_eq_dif]
    split_ifs with hw
    · simp [Complex.mul_re, hreC w hw]
    · rfl
  rw [Complex.add_re, h1, h2, add_zero]

private theorem norm_apply_E_eq_one (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (t : ℂ) (ht : t.re = 0) (e : ℤ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ ω v t e)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (z : (InfiniteAdeleRing ℚ)ˣ) : ‖((ω (E z) : ℂˣ) : ℂ)‖ = 1 := by
  have hmul : (z : InfiniteAdeleRing ℚ) Rat.infinitePlace *
      ((z⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) Rat.infinitePlace = 1 :=
    congrFun (Units.mul_inv z) Rat.infinitePlace
  have hpos : 0 < ‖(z : InfiniteAdeleRing ℚ) Rat.infinitePlace‖ :=
    norm_pos_iff.mpr (left_ne_zero_of_mul_eq_one hmul)
  have hre : ((Rat.infinitePlace.mult : ℂ) * t).re = 0 := by simp [ht]
  rw [apply_of_infPart_eq_of_isArchCompAt ω E hE t e hω z Rat.infinitePlace Rat.isReal_infinitePlace, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos, hre, Real.rpow_zero, norm_zpow, norm_div,
    (InfinitePlace.Completion.isometry_extensionEmbedding Rat.infinitePlace).norm_map_of_map_zero (map_zero _),
    Complex.norm_real, norm_norm, div_self hpos.ne', one_zpow, mul_one]

end RootSizeBound

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse

open MeasureTheory

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam RealArchParam.discrete RealArchParam.principal"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gaussian3 polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq AdelicGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero archComponent3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂ archRootSum archPlaceComponent3 isGL3PsiWhittakerFn_jacquetVector3 jacquetVector3_scalar_mul apply_of_infPart_eq_of_isArchCompAt re_eq_zero_of_isArchCompAt_of_isUnitaryChar exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod upperUnipotent3_inv_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem exists_eq_unip_mul_smul_diagOne_mul_of_det_ne_zero (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) :
    ∃ (s z y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k ∧ 0 < z ∧
      z = Real.sqrt (x 1 0 ^ 2 + x 1 1 ^ 2) ∧ |y| = |x.det| / (x 1 0 ^ 2 + x 1 1 ^ 2) ∧
      x = ArchR.unip s * (z • (ArchR.diagOne y * k)) := by
  have hdet : x.det = x 0 0 * x 1 1 - x 0 1 * x 1 0 := Matrix.det_fin_two x
  have hq : 0 < x 1 0 ^ 2 + x 1 1 ^ 2 := by
    by_contra hcon
    have h10 : x 1 0 = 0 := by nlinarith [sq_nonneg (x 1 0), sq_nonneg (x 1 1)]
    have h11 : x 1 1 = 0 := by nlinarith [sq_nonneg (x 1 0), sq_nonneg (x 1 1)]
    exact hx (by rw [hdet, h10, h11]; ring)
  have hq' : x 1 0 ^ 2 + x 1 1 ^ 2 ≠ 0 := hq.ne'
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = Real.sqrt (x 1 0 ^ 2 + x 1 1 ^ 2) := ⟨_, rfl⟩
  have hz0 : 0 < z := by rw [hz]; exact Real.sqrt_pos.mpr hq
  have hz0' : z ≠ 0 := hz0.ne'
  have hz2 : z ^ 2 = x 1 0 ^ 2 + x 1 1 ^ 2 := by rw [hz]; exact Real.sq_sqrt hq.le
  refine ⟨(x 0 0 * x 1 0 + x 0 1 * x 1 1) / (x 1 0 ^ 2 + x 1 1 ^ 2), z, x.det / (x 1 0 ^ 2 + x 1 1 ^ 2),
    !![x 1 1 / z, -(x 1 0) / z; x 1 0 / z, x 1 1 / z], ?_, hz0, hz, ?_, ?_⟩
  · unfold ArchR.IsK
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> nlinarith [hz2]
  · rw [abs_div, abs_of_pos hq]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ArchR.unip, ArchR.diagOne, Matrix.mul_apply, Fin.sum_univ_two, hdet] <;> field_simp <;> ring

private theorem norm_psi_le_one (s : ℝ) : ‖ArchR.psi s‖ ≤ 1 := by
  unfold ArchR.psi
  simp [Complex.norm_exp]

private theorem norm_quasiChar_le (u : ℂ) (b : ZMod 2) {z : ℝ} (hz : z ≠ 0) :
    ‖ArchR.quasiChar u b z‖ ≤ |z| ^ u.re := by
  unfold ArchR.quasiChar
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hz)]
  refine mul_le_of_le_one_right (Real.rpow_nonneg (abs_nonneg z) _) ?_
  split_ifs
  · simp
  · rw [Complex.norm_real, Real.norm_eq_abs]
    rcases lt_or_gt_of_ne hz with h | h
    · simp [sign_neg h]
    · simp [sign_pos h]

private theorem norm_W_smul_le {P : RealArchParam} (D : ArchDatumR P) {z : ℝ} (hz : 0 < z)
    (g : Matrix (Fin 2) (Fin 2) ℝ) : ‖D.W (z • g)‖ ≤ z ^ (P.centralExponent.re + 1) * ‖D.W g‖ := by
  rw [D.central_law z g hz.ne', norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs, abs_of_pos hz,
    Real.rpow_add_one hz.ne']
  have h := norm_quasiChar_le P.centralExponent P.centralSign hz.ne'
  rw [abs_of_pos hz] at h
  unfold ArchR.centralChar
  gcongr

private theorem norm_W_unip_mul_le {P : RealArchParam} (D : ArchDatumR P) (s : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖D.W (ArchR.unip s * g)‖ ≤ ‖D.W g‖ := by
  rw [D.unip_law s g, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_psi_le_one s)

private theorem exists_forall_norm_W_diagOne_mul_le_of_le {P : RealArchParam} (D : ArchDatumR P) (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    (q : ℝ) (hq : c₀ - 1 ≤ q) :
    ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 →
      ‖D.W (ArchR.diagOne y * k)‖ ≤ C * |y| ^ (-q) := by
  obtain ⟨C₁, h₁⟩ := ArchDatumR.norm_iteratedFDerivWithin_diagOne_le P D c₀ hc₀ 0
  obtain ⟨C₂, h₂⟩ := D.decay_top 0 ⌈max q 0⌉₊
  refine ⟨max (max C₁ C₂) 0, ?_⟩
  intro y k hk hy
  have hW : ‖iteratedFDerivWithin ℝ 0 (ArchR.asPi D.W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖ =
      ‖D.W (ArchR.diagOne y * k)‖ := by
    rw [norm_iteratedFDerivWithin_zero]
    simp [ArchR.asPi, ArchR.diagOneMulCoords]
  have hy0 : 0 < |y| := abs_pos.mpr hy
  have hC0 : (0 : ℝ) ≤ max (max C₁ C₂) 0 := le_max_right _ _
  have hC₁ : C₁ ≤ max (max C₁ C₂) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC₂ : C₂ ≤ max (max C₁ C₂) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
  rcases le_or_gt |y| 1 with hle | hlt
  · have h := h₁ y k hk hy hle
    rw [hW] at h
    calc ‖D.W (ArchR.diagOne y * k)‖ ≤ C₁ * |y| ^ (1 - c₀ - ((0 : ℕ) : ℝ)) := h
      _ ≤ max (max C₁ C₂) 0 * |y| ^ (1 - c₀ - ((0 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hC₁ (Real.rpow_nonneg hy0.le _)
      _ ≤ max (max C₁ C₂) 0 * |y| ^ (-q) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy0 hle (by push_cast; linarith)) hC0
  · have h := h₂ y k hk hlt.le
    rw [hW] at h
    calc ‖D.W (ArchR.diagOne y * k)‖ ≤ C₂ * |y| ^ (-((⌈max q 0⌉₊ : ℕ) : ℝ)) := h
      _ ≤ max (max C₁ C₂) 0 * |y| ^ (-((⌈max q 0⌉₊ : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hC₂ (Real.rpow_nonneg hy0.le _)
      _ ≤ max (max C₁ C₂) 0 * |y| ^ (-q) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hlt.le (neg_le_neg ((le_max_left _ _).trans (Nat.le_ceil _)))) hC0

private theorem archDatumR_exists_forall_norm_W_le_rpow_mul_rpow_of_le {P : RealArchParam} (D : ArchDatumR P)
    (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    (q : ℝ) (hq : c₀ - 1 ≤ q) :
    ∃ C : ℝ, ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 →
      ‖D.W x‖ ≤ C * Real.sqrt (x 1 0 ^ 2 + x 1 1 ^ 2) ^ (P.centralExponent.re + 1) *
        (|x.det| / (x 1 0 ^ 2 + x 1 1 ^ 2)) ^ (-q) := by
  obtain ⟨C, hC⟩ := exists_forall_norm_W_diagOne_mul_le_of_le D c₀ hc₀ q hq
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨s, z, y, k, hk, hz, hzeq, hyabs, hxeq⟩ := exists_eq_unip_mul_smul_diagOne_mul_of_det_ne_zero x hx
  have hq : 0 < x 1 0 ^ 2 + x 1 1 ^ 2 := by
    have h := hz
    rw [hzeq] at h
    exact Real.sqrt_pos.mp h
  have hy : y ≠ 0 := by
    intro h
    rw [h, abs_zero, eq_comm, div_eq_zero_iff] at hyabs
    rcases hyabs with h0 | h0
    · exact hx (abs_eq_zero.mp h0)
    · exact hq.ne' h0
  calc ‖D.W x‖ = ‖D.W (ArchR.unip s * (z • (ArchR.diagOne y * k)))‖ := by rw [← hxeq]
    _ ≤ ‖D.W (z • (ArchR.diagOne y * k))‖ := norm_W_unip_mul_le D s _
    _ ≤ z ^ (P.centralExponent.re + 1) * ‖D.W (ArchR.diagOne y * k)‖ := norm_W_smul_le D hz _
    _ ≤ z ^ (P.centralExponent.re + 1) * (C * |y| ^ (-q)) :=
        mul_le_mul_of_nonneg_left (hC y k hk hy) (Real.rpow_nonneg hz.le _)
    _ = C * Real.sqrt (x 1 0 ^ 2 + x 1 1 ^ 2) ^ (P.centralExponent.re + 1) *
          (|x.det| / (x 1 0 ^ 2 + x 1 1 ^ 2)) ^ (-q) := by
        rw [← hzeq, ← hyabs]
        ring

private theorem psiArch_eq_psi_realCoord (w : InfiniteAdeleRing ℚ) :
    NumberField.StandardAddChar.psiArch w = ArchR.psi (StandardKernel.realCoord w) := by
  have h1 : NumberField.StandardAddChar.psiArch w =
      NumberField.StandardAddChar.psiArchPlace Rat.infinitePlace (w Rat.infinitePlace) := by
    rw [NumberField.StandardAddChar.psiArch_apply]
    exact finprod_eq_single _ Rat.infinitePlace fun v hv => absurd (Subsingleton.elim v Rat.infinitePlace) hv
  rw [h1, NumberField.StandardAddChar.psiArchPlace_apply, ArchR.psi, StandardKernel.realCoord_apply]

private theorem realCoord_ratCast (a : ℚ) :
    StandardKernel.realCoord (algebraMap ℚ (InfiniteAdeleRing ℚ) a) = (a : ℝ) := by
  rw [← RingHom.comp_apply]
  exact eq_ratCast (StandardKernel.realCoord.comp (algebraMap ℚ (InfiniteAdeleRing ℚ))) a

private theorem realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private theorem _root_.LanglandsTunnell.CubicInduction.psiInf_ofReal_neg (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x)) (t : ℝ) :
    psiInf (StandardKernel.ofReal (-t)) =
      Complex.exp (((-(2 * Real.pi * (a : ℝ) * t) : ℝ) : ℂ) * Complex.I) := by
  rw [hpsiInf, psiArch_eq_psi_realCoord, map_mul, realCoord_ratCast, realCoord_ofReal, ArchR.psi]
  congr 1
  push_cast
  ring

p2m_export "LanglandsTunnell.CubicInduction" "psiInf_ofReal_neg"
section SchwartzSlices

open scoped BigOperators SchwartzMap FourierTransform

private theorem exists_finset_forall_norm_integral_schwartzMap_mul_exp_neg_inner_le (ι : Type) [Fintype ι] (N : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (φ : 𝓢((ι → ℝ), ℂ)) (ξ : ι → ℝ),
      ‖∫ u : ι → ℝ, φ u * Complex.exp (((-(2 * Real.pi * ∑ i, ξ i * u i) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (s.sup (schwartzSeminormFamily ℝ (ι → ℝ) ℂ)) φ * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  classical

  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)
  let T : 𝓢((ι → ℝ), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ ι, ℂ) :=
    (SchwartzMap.fourierTransformCLM ℂ).comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e)

  have hcont : ∀ k : ℕ, Continuous
      ((schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ (k, 0)).comp (T : 𝓢((ι → ℝ), ℂ) →ₗ[ℂ] _)) := by
    intro k
    exact ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ ι) ℂ).continuous_seminorm (k, 0)).comp T.continuous
  obtain ⟨s₀, C₀, -, h₀⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (ι → ℝ) ℂ) _ (hcont 0)
  obtain ⟨s₁, C₁, -, h₁⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (ι → ℝ) ℂ) _ (hcont N)
  refine ⟨s₀ ∪ s₁, 2 ^ N * ((C₀ : ℝ) + C₁), by positivity, ?_⟩
  intro φ ξ
  set S : ℝ := ((s₀ ∪ s₁).sup (schwartzSeminormFamily ℝ (ι → ℝ) ℂ)) φ with hS
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hbridge : ((s₀ ∪ s₁).sup (schwartzSeminormFamily ℂ (ι → ℝ) ℂ)) φ = S := by
    rw [hS]
    simp only [Seminorm.finset_sup_apply]
    rfl

  have hb : ∀ (k : ℕ) (sk : Finset (ℕ × ℕ)) (Ck : NNReal),
      (schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ (k, 0)).comp (T : 𝓢((ι → ℝ), ℂ) →ₗ[ℂ] _) ≤
        Ck • sk.sup (schwartzSeminormFamily ℂ (ι → ℝ) ℂ) → sk ⊆ s₀ ∪ s₁ →
        SchwartzMap.seminorm ℂ k 0 (T φ) ≤ (Ck : ℝ) * S := by
    intro k sk Ck hk hsub
    have h1 := Seminorm.le_def.1 hk φ
    have h2 : (sk.sup (schwartzSeminormFamily ℂ (ι → ℝ) ℂ)) φ ≤ S := by
      rw [← hbridge]
      exact Seminorm.le_def.1 (Finset.sup_mono hsub) φ
    simp only [Seminorm.comp_apply, SchwartzMap.schwartzSeminormFamily_apply, Seminorm.smul_apply, NNReal.smul_def,
      smul_eq_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h2 Ck.coe_nonneg)
  have hq₀ := hb 0 s₀ C₀ h₀ Finset.subset_union_left
  have hqN := hb N s₁ C₁ h₁ Finset.subset_union_right

  set x : EuclideanSpace ℝ ι := WithLp.toLp 2 ξ with hx
  have hξx : ‖ξ‖ ≤ ‖x‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => ?_
    exact PiLp.norm_apply_le x i
  have hTx : T φ x = (𝓕 (⇑(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ)) : EuclideanSpace ℝ ι → ℂ) x := by
    simp only [T, ContinuousLinearMap.comp_apply]
    rfl
  have hmp : MeasureTheory.MeasurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ)) := by
    simpa using (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).symm _
  have hId : (∫ u : ι → ℝ, φ u * Complex.exp (((-(2 * Real.pi * ∑ i, ξ i * u i) : ℝ) : ℂ) * Complex.I)) =
      T φ x := by
    rw [hTx, Real.fourier_eq', ← hmp.integral_comp']
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hinner : @inner ℝ _ _ (WithLp.toLp 2 u : EuclideanSpace ℝ ι) x = ∑ i, ξ i * u i := by
      simp only [hx, PiLp.inner_apply]
      rfl
    simp only [smul_eq_mul, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, e,
      PiLp.coe_continuousLinearEquiv, MeasurableEquiv.coe_toLp, hinner]
    rw [mul_comm]
    congr 2
    push_cast
    ring

  have hpow : ∀ a : ℝ, 0 ≤ a → (1 + a) ^ N ≤ 2 ^ N * (1 + a ^ N) := by
    intro a ha
    calc (1 + a) ^ N ≤ (2 * max 1 a) ^ N :=
          pow_le_pow_left₀ (by positivity) (by linarith [le_max_left 1 a, le_max_right 1 a]) N
      _ = 2 ^ N * (max 1 a) ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + a ^ N) := by
          gcongr
          rcases max_cases 1 a with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
          · rw [one_pow]; linarith [pow_nonneg ha N]
          · linarith
  have hdecay : (1 + ‖x‖) ^ N * ‖T φ x‖ ≤
      2 ^ N * (SchwartzMap.seminorm ℂ 0 0 (T φ) + SchwartzMap.seminorm ℂ N 0 (T φ)) := by
    have hA := SchwartzMap.norm_le_seminorm ℂ (T φ) x
    have hB := SchwartzMap.norm_pow_mul_le_seminorm ℂ (T φ) N x
    calc (1 + ‖x‖) ^ N * ‖T φ x‖ ≤ 2 ^ N * (1 + ‖x‖ ^ N) * ‖T φ x‖ :=
          mul_le_mul_of_nonneg_right (hpow _ (norm_nonneg x)) (norm_nonneg _)
      _ = 2 ^ N * (‖T φ x‖ + ‖x‖ ^ N * ‖T φ x‖) := by ring
      _ ≤ 2 ^ N * (SchwartzMap.seminorm ℂ 0 0 (T φ) + SchwartzMap.seminorm ℂ N 0 (T φ)) := by gcongr

  have hbase : 0 < 1 + ‖ξ‖ := by positivity
  rw [hId, Real.rpow_neg hbase.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hmono : (1 + ‖ξ‖) ^ N ≤ (1 + ‖x‖) ^ N := pow_le_pow_left₀ hbase.le (by linarith) N
  calc ‖T φ x‖ * (1 + ‖ξ‖) ^ N ≤ ‖T φ x‖ * (1 + ‖x‖) ^ N :=
        mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
    _ = (1 + ‖x‖) ^ N * ‖T φ x‖ := mul_comm _ _
    _ ≤ 2 ^ N * (SchwartzMap.seminorm ℂ 0 0 (T φ) + SchwartzMap.seminorm ℂ N 0 (T φ)) := hdecay
    _ ≤ 2 ^ N * ((C₀ : ℝ) * S + (C₁ : ℝ) * S) := by gcongr
    _ = 2 ^ N * ((C₀ : ℝ) + C₁) * S := by ring

namespace G0

private theorem iteratedDeriv_real_exp (n : ℕ) : iteratedDeriv n Real.exp = Real.exp := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ, ih, Real.deriv_exp]

private theorem norm_iteratedFDeriv_real_exp_le (n : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ n Real.exp y‖ ≤ Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_real_exp, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos y)]

private theorem exists_forall_pow_mul_exp_neg_pi_sq_le (m : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → t ^ m * Real.exp (-(Real.pi * t ^ 2)) ≤ C := by
  refine ⟨1 + m.factorial / Real.pi ^ m, fun t ht => ?_⟩
  have hπ : 0 < Real.pi := Real.pi_pos
  have hexp : (Real.pi * t ^ 2) ^ m / m.factorial ≤ Real.exp (Real.pi * t ^ 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) m
  have hpos : 0 < Real.exp (Real.pi * t ^ 2) := Real.exp_pos _
  rw [Real.exp_neg]
  rcases le_or_gt t 1 with h1 | h1
  · calc t ^ m * (Real.exp (Real.pi * t ^ 2))⁻¹ ≤ 1 * 1 := by
          gcongr
          · exact pow_le_one₀ ht h1
          · exact inv_le_one_of_one_le₀ (Real.one_le_exp (by positivity))
      _ ≤ 1 + m.factorial / Real.pi ^ m := by
          have : (0 : ℝ) ≤ m.factorial / Real.pi ^ m := by positivity
          linarith
  ·
    have htm : t ^ m ≤ (t ^ 2) ^ m := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ h1.le (by omega)
    have key : (t ^ 2) ^ m * (Real.exp (Real.pi * t ^ 2))⁻¹ ≤ m.factorial / Real.pi ^ m := by
      rw [mul_inv_le_iff₀ hpos, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have := hexp
      rw [div_le_iff₀ (by positivity), mul_pow] at this
      nlinarith [this, pow_pos hπ m, pow_nonneg (sq_nonneg t) m]
    calc t ^ m * (Real.exp (Real.pi * t ^ 2))⁻¹ ≤ (t ^ 2) ^ m * (Real.exp (Real.pi * t ^ 2))⁻¹ := by
          gcongr
      _ ≤ m.factorial / Real.pi ^ m := key
      _ ≤ 1 + m.factorial / Real.pi ^ m := by linarith

private theorem norm_sq_le_sum_sq {ι : Type} [Fintype ι] (x : ι → ℝ) : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Subsingleton.elim x 0]
  · obtain ⟨i, hi⟩ := Finite.exists_max fun i => ‖x i‖
    have hnorm : ‖x‖ = ‖x i‖ := by
      apply le_antisymm
      · exact pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 hi
      · exact norm_le_pi_norm x i
    rw [hnorm, Real.norm_eq_abs, sq_abs]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

variable {ι : Type} [Fintype ι]

private def quad (x : ι → ℝ) : ℝ := -(Real.pi * ∑ i, x i ^ 2)

private theorem contDiff_quad : ContDiff ℝ (⊤ : ℕ∞) (quad (ι := ι)) := by
  unfold quad
  apply ContDiff.neg
  apply ContDiff.mul contDiff_const
  exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).pow 2

private theorem norm_proj_le_one (i : ι) : ‖(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using norm_le_pi_norm x i

private theorem norm_iteratedFDeriv_proj_le (i : ι) (j : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ j (⇑(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x‖ ≤ max ‖x‖ 1 := by
  rcases j with _ | j
  · rw [norm_iteratedFDeriv_zero]
    exact (norm_le_pi_norm x i).trans (le_max_left _ _)
  · rw [← norm_iteratedFDeriv_fderiv]
    have hfd : fderiv ℝ (⇑(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) =
        fun _ => (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) := funext fun _ => ContinuousLinearMap.fderiv _
    rw [hfd]
    rcases j with _ | j
    · rw [norm_iteratedFDeriv_zero]
      exact (norm_proj_le_one i).trans (le_max_right _ _)
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
      simp

private theorem contDiff_proj (i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (⇑(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) := by
  exact ContinuousLinearMap.contDiff _

private theorem norm_iteratedFDeriv_coord_sq_le (i : ι) (j : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ j (fun y : ι → ℝ => y i ^ 2) x‖ ≤ 2 ^ j * max ‖x‖ 1 ^ 2 := by
  have hfun : (fun y : ι → ℝ => y i ^ 2) = fun y => (ContinuousLinearMap.mul ℝ ℝ)
      ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) y) ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) y) := by
    funext y; simp [sq]
  rw [hfun]
  refine ((ContinuousLinearMap.mul ℝ ℝ).norm_iteratedFDeriv_le_of_bilinear (contDiff_proj i) (contDiff_proj i) x
    (n := j) (by exact_mod_cast le_top)).trans ?_
  have hm : (0 : ℝ) ≤ max ‖x‖ 1 := le_max_of_le_right zero_le_one
  calc ‖ContinuousLinearMap.mul ℝ ℝ‖ * ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
          ‖iteratedFDeriv ℝ k (⇑(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x‖ *
            ‖iteratedFDeriv ℝ (j - k) (⇑(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x‖
        ≤ 1 * ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * max ‖x‖ 1 * max ‖x‖ 1 := by
          gcongr with k _ <;>
            first
              | exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
              | exact norm_iteratedFDeriv_proj_le i _ x
              | exact Finset.sum_nonneg fun k _ => by positivity
              | positivity
      _ = 2 ^ j * max ‖x‖ 1 ^ 2 := by
          rw [one_mul, ← Finset.sum_mul, ← Finset.sum_mul]
          have h2 : ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) = 2 ^ j := by
            exact_mod_cast Nat.sum_range_choose j
          rw [h2]; ring

private theorem norm_iteratedFDeriv_quad_le (j : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ j (quad (ι := ι)) x‖ ≤ Real.pi * Fintype.card ι * (2 ^ j * max ‖x‖ 1 ^ 2) := by
  have hq : quad (ι := ι) = fun y => (-Real.pi) • ∑ i, (fun z : ι → ℝ => z i ^ 2) y := by
    funext y; simp [quad]
  rw [hq]
  have hcd : ∀ i : ι, ContDiff ℝ (⊤ : ℕ∞) (fun z : ι → ℝ => z i ^ 2) := fun i => (contDiff_apply ℝ ℝ i).pow 2
  have hcdj : ∀ i : ι, ContDiff ℝ (j : ℕ) (fun z : ι → ℝ => z i ^ 2) := fun i => (hcd i).of_le (by exact_mod_cast le_top)
  have hS : ContDiff ℝ (j : ℕ) (fun y : ι → ℝ => ∑ i, (fun z : ι → ℝ => z i ^ 2) y) :=
    ContDiff.sum fun i _ => hcdj i
  have hsplit := congrFun (iteratedFDeriv_sum (𝕜 := ℝ) (f := fun i : ι => fun z : ι → ℝ => z i ^ 2) (u := Finset.univ)
    (i := j) (fun i _ => hcdj i)) x
  simp only [Finset.sum_apply] at hsplit
  calc ‖iteratedFDeriv ℝ j (fun y => (-Real.pi) • ∑ i, (fun z : ι → ℝ => z i ^ 2) y) x‖
      = ‖(-Real.pi) • iteratedFDeriv ℝ j (fun y => ∑ i, (fun z : ι → ℝ => z i ^ 2) y) x‖ := by
        rw [iteratedFDeriv_const_smul_apply' hS.contDiffAt]
    _ = Real.pi * ‖iteratedFDeriv ℝ j (fun y => ∑ i, (fun z : ι → ℝ => z i ^ 2) y) x‖ := by
        rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    _ ≤ Real.pi * ∑ i : ι, ‖iteratedFDeriv ℝ j (fun z : ι → ℝ => z i ^ 2) x‖ := by
        gcongr
        rw [hsplit]
        exact norm_sum_le _ _
    _ ≤ Real.pi * ∑ _i : ι, 2 ^ j * max ‖x‖ 1 ^ 2 := by
        gcongr with i _
        exact norm_iteratedFDeriv_coord_sq_le i j x
    _ = Real.pi * Fintype.card ι * (2 ^ j * max ‖x‖ 1 ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

private def gauss (x : ι → ℝ) : ℝ := Real.exp (quad x)

private theorem contDiff_gauss : ContDiff ℝ (⊤ : ℕ∞) (gauss (ι := ι)) :=
  Real.contDiff_exp.comp contDiff_quad

private theorem norm_iteratedFDeriv_quad_le_pow (j : ℕ) (hj : 1 ≤ j) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ j (quad (ι := ι)) x‖ ≤ (2 * Real.pi * Fintype.card ι * max ‖x‖ 1 ^ 2 + 2) ^ j := by
  set A : ℝ := Real.pi * Fintype.card ι * max ‖x‖ 1 ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hD2 : (2 : ℝ) ≤ 2 * A + 2 := by linarith
  refine (norm_iteratedFDeriv_quad_le j x).trans ?_
  have hre : Real.pi * Fintype.card ι * (2 ^ j * max ‖x‖ 1 ^ 2) = 2 ^ j * A := by rw [hA]; ring
  have hD : 2 * Real.pi * Fintype.card ι * max ‖x‖ 1 ^ 2 + 2 = 2 * A + 2 := by rw [hA]; ring
  rw [hre, hD]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  calc (2 : ℝ) ^ (k + 1) * A = 2 ^ k * (2 * A) := by ring
    _ ≤ (2 * A + 2) ^ k * (2 * A + 2) := by
        gcongr
        linarith
    _ = (2 * A + 2) ^ (k + 1) := by ring

private theorem norm_iteratedFDeriv_gauss_le (n : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ n (gauss (ι := ι)) x‖ ≤
      n.factorial * Real.exp (quad x) * (2 * Real.pi * Fintype.card ι * max ‖x‖ 1 ^ 2 + 2) ^ n := by
  have h : gauss (ι := ι) = Real.exp ∘ quad := rfl
  rw [h]
  exact norm_iteratedFDeriv_comp_le Real.contDiff_exp contDiff_quad (by exact_mod_cast le_top) x
    (fun i _ => norm_iteratedFDeriv_real_exp_le i (quad x))
    (fun i hi _ => norm_iteratedFDeriv_quad_le_pow i hi x)

private theorem exp_quad_le (x : ι → ℝ) : Real.exp (quad x) ≤ Real.exp (-(Real.pi * ‖x‖ ^ 2)) := by
  apply Real.exp_le_exp.2
  unfold quad
  have := norm_sq_le_sum_sq x
  nlinarith [Real.pi_pos]

private theorem gauss_decay (k n : ℕ) : ∃ C : ℝ, ∀ x : ι → ℝ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (gauss (ι := ι)) x‖ ≤ C := by

  set c₁ : ℝ := 2 * Real.pi * Fintype.card ι + 2 with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  obtain ⟨C₀, hC₀⟩ := exists_forall_pow_mul_exp_neg_pi_sq_le (k + 2 * n)
  refine ⟨n.factorial * c₁ ^ n * (2 ^ (k + 2 * n) * (1 + C₀)), fun x => ?_⟩
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  set t : ℝ := ‖x‖ with ht
  have hmax : max t 1 ≤ 1 + t := max_le (by linarith) (by linarith)
  have hD : 2 * Real.pi * Fintype.card ι * max t 1 ^ 2 + 2 ≤ c₁ * (1 + t) ^ 2 := by
    have h1 : max t 1 ^ 2 ≤ (1 + t) ^ 2 := pow_le_pow_left₀ (le_max_of_le_right zero_le_one) hmax 2
    have h2 : (1 : ℝ) ≤ (1 + t) ^ 2 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * Real.pi * Fintype.card ι)
    rw [hc₁]; nlinarith [h3, h2]
  have hgauss : Real.exp (quad x) ≤ Real.exp (-(Real.pi * t ^ 2)) := exp_quad_le x
  have hexp0 : 0 < Real.exp (-(Real.pi * t ^ 2)) := Real.exp_pos _
  have hpow : t ^ k * (1 + t) ^ (2 * n) ≤ (1 + t) ^ (k + 2 * n) := by
    rw [pow_add]; gcongr; linarith
  have hkey : (1 + t) ^ (k + 2 * n) * Real.exp (-(Real.pi * t ^ 2)) ≤ 2 ^ (k + 2 * n) * (1 + C₀) := by
    have hC₀' := hC₀ t hx0
    have hexp1 : Real.exp (-(Real.pi * t ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    have hbin : (1 + t) ^ (k + 2 * n) ≤ 2 ^ (k + 2 * n) * (1 + t ^ (k + 2 * n)) := by
      have hm : (1 + t) ≤ 2 * max 1 t := by linarith [le_max_left (1 : ℝ) t, le_max_right (1 : ℝ) t]
      calc (1 + t) ^ (k + 2 * n) ≤ (2 * max 1 t) ^ (k + 2 * n) := by gcongr
        _ = 2 ^ (k + 2 * n) * max 1 t ^ (k + 2 * n) := mul_pow _ _ _
        _ ≤ 2 ^ (k + 2 * n) * (1 + t ^ (k + 2 * n)) := by
            gcongr
            rcases le_total t 1 with h | h
            · rw [max_eq_left h, one_pow]; linarith [pow_nonneg hx0 (k + 2 * n)]
            · rw [max_eq_right h]; linarith
    calc (1 + t) ^ (k + 2 * n) * Real.exp (-(Real.pi * t ^ 2))
        ≤ 2 ^ (k + 2 * n) * (1 + t ^ (k + 2 * n)) * Real.exp (-(Real.pi * t ^ 2)) := by gcongr
      _ = 2 ^ (k + 2 * n) * (Real.exp (-(Real.pi * t ^ 2)) + t ^ (k + 2 * n) * Real.exp (-(Real.pi * t ^ 2))) := by
          ring
      _ ≤ 2 ^ (k + 2 * n) * (1 + C₀) := by gcongr
  calc t ^ k * ‖iteratedFDeriv ℝ n (gauss (ι := ι)) x‖
      ≤ t ^ k * (n.factorial * Real.exp (quad x) * (2 * Real.pi * Fintype.card ι * max t 1 ^ 2 + 2) ^ n) := by
        gcongr; exact norm_iteratedFDeriv_gauss_le n x
    _ ≤ t ^ k * (n.factorial * Real.exp (-(Real.pi * t ^ 2)) * (c₁ * (1 + t) ^ 2) ^ n) := by
        gcongr
    _ = n.factorial * c₁ ^ n * ((t ^ k * (1 + t) ^ (2 * n)) * Real.exp (-(Real.pi * t ^ 2))) := by
        rw [mul_pow, ← pow_mul]; ring
    _ ≤ n.factorial * c₁ ^ n * ((1 + t) ^ (k + 2 * n) * Real.exp (-(Real.pi * t ^ 2))) := by gcongr
    _ ≤ n.factorial * c₁ ^ n * (2 ^ (k + 2 * n) * (1 + C₀)) := by gcongr

private theorem exists_schwartzMap_eq_exp_neg_pi_sum_sq' :
    ∃ Φ : SchwartzMap (ι → ℝ) ℝ, ∀ x : ι → ℝ, Φ x = Real.exp (-(Real.pi * ∑ i, x i ^ 2)) :=
  ⟨⟨gauss, contDiff_gauss, gauss_decay⟩, fun _ => rfl⟩

private abbrev Arr : Type := Fin 2 → Fin 3 → ℝ

private abbrev Pl : Type := Fin 2 → ℝ

private def blk (h : Fin 2 → Fin 2 → ℝ) (w : Pl) : Arr := fun i => ![h i 0, h i 1, w i]

private def rmul (T : Matrix (Fin 3) (Fin 3) ℝ) (X : Arr) : Arr := fun i b => (Matrix.of X * T) i b

private theorem rmul_apply (T : Matrix (Fin 3) (Fin 3) ℝ) (X : Arr) (i : Fin 2) (b : Fin 3) :
    rmul T X i b = ∑ k : Fin 3, X i k * T k b := by
  simp [rmul, Matrix.mul_apply]

private theorem rmul_add (T : Matrix (Fin 3) (Fin 3) ℝ) (X Y : Arr) : rmul T (X + Y) = rmul T X + rmul T Y := by
  funext i b; simp [rmul_apply, add_mul, Finset.sum_add_distrib]

private theorem rmul_smul (T : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) (X : Arr) : rmul T (c • X) = c • rmul T X := by
  funext i b; simp [rmul_apply, Finset.mul_sum, mul_assoc]

private theorem rmul_rmul (T S : Matrix (Fin 3) (Fin 3) ℝ) (X : Arr) : rmul S (rmul T X) = rmul (T * S) X := by
  funext i b
  simp only [rmul_apply, Matrix.mul_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

private theorem rmul_inv_rmul (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (X : Arr) : rmul T⁻¹ (rmul T X) = X := by
  rw [rmul_rmul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hT)]
  funext i b; simp [rmul_apply, Matrix.one_apply]

private theorem blk_add (h : Fin 2 → Fin 2 → ℝ) (w : Pl) : blk h w = blk h 0 + blk 0 w := by
  funext i b; fin_cases b <;> simp [blk]

private theorem blk_zero_add_smul (w w' : Pl) : blk 0 (w + w') = blk 0 w + blk 0 w' := by
  funext i b; fin_cases b <;> simp [blk]

private theorem blk_zero_smul (c : ℝ) (w : Pl) : blk 0 (c • w) = c • blk 0 w := by
  funext i b; fin_cases b <;> simp [blk]

private def mnorm (T : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ‖(fun i j => T i j : Fin 3 → Fin 3 → ℝ)‖

private theorem mnorm_nonneg (T : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ mnorm T := norm_nonneg _

private theorem abs_entry_le_mnorm (T : Matrix (Fin 3) (Fin 3) ℝ) (k b : Fin 3) : |T k b| ≤ mnorm T := by
  have h1 := norm_le_pi_norm (fun i j => T i j : Fin 3 → Fin 3 → ℝ) k
  have h2 := norm_le_pi_norm (fun j => T k j : Fin 3 → ℝ) b
  simp only [Real.norm_eq_abs] at h2
  exact h2.trans h1

private theorem abs_entry_le_norm (X : Arr) (i : Fin 2) (b : Fin 3) : |X i b| ≤ ‖X‖ := by
  have h1 := norm_le_pi_norm X i
  have h2 := norm_le_pi_norm (X i) b
  simp only [Real.norm_eq_abs] at h2
  exact h2.trans h1

private theorem norm_rmul_le (T : Matrix (Fin 3) (Fin 3) ℝ) (X : Arr) : ‖rmul T X‖ ≤ 3 * ‖X‖ * mnorm T := by
  have hnn : (0 : ℝ) ≤ 3 * ‖X‖ * mnorm T := mul_nonneg (by positivity) (mnorm_nonneg T)
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun i => (pi_norm_le_iff_of_nonneg hnn).2 fun b => ?_
  rw [Real.norm_eq_abs, rmul_apply]
  calc |∑ k : Fin 3, X i k * T k b| ≤ ∑ k : Fin 3, |X i k * T k b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin 3, ‖X‖ * mnorm T := by
        gcongr with k _
        rw [abs_mul]
        exact mul_le_mul (abs_entry_le_norm X i k) (abs_entry_le_mnorm T k b) (abs_nonneg _) (norm_nonneg _)
    _ = 3 * ‖X‖ * mnorm T := by simp [Finset.sum_const]; ring

private theorem norm_le_norm_blk_left (h : Fin 2 → Fin 2 → ℝ) (w : Pl) : ‖h‖ ≤ ‖blk h w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have h1 := norm_le_pi_norm (blk h w) i
  fin_cases j
  · have h2 := norm_le_pi_norm (blk h w i) 0
    simp only [blk, Matrix.cons_val_zero] at h2
    exact h2.trans h1
  · have h2 := norm_le_pi_norm (blk h w i) 1
    simp only [blk, Matrix.cons_val_one] at h2
    exact h2.trans h1

private theorem norm_le_norm_blk_right (h : Fin 2 → Fin 2 → ℝ) (w : Pl) : ‖w‖ ≤ ‖blk h w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have h1 := norm_le_pi_norm (blk h w) i
  have h2 := norm_le_pi_norm (blk h w i) 2
  simp only [blk] at h2
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
  exact h2.trans h1

private def sliceLin (T : Matrix (Fin 3) (Fin 3) ℝ) : Pl →L[ℝ] Arr :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => rmul T (blk 0 w)
      map_add' := fun w w' => by rw [blk_zero_add_smul, rmul_add]
      map_smul' := fun c w => by rw [blk_zero_smul, rmul_smul]; rfl }

private theorem sliceLin_apply (T : Matrix (Fin 3) (Fin 3) ℝ) (w : Pl) : sliceLin T w = rmul T (blk 0 w) := rfl

private theorem rmul_blk_eq (T : Matrix (Fin 3) (Fin 3) ℝ) (h : Fin 2 → Fin 2 → ℝ) (w : Pl) :
    rmul T (blk h w) = sliceLin T w + rmul T (blk h 0) := by
  rw [blk_add, rmul_add, sliceLin_apply, add_comm]

private theorem norm_blk_zero_le (w : Pl) : ‖blk (0 : Fin 2 → Fin 2 → ℝ) w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun b => ?_
  fin_cases b <;> simp [blk]
  exact norm_le_pi_norm w i

private theorem norm_sliceLin_le (T : Matrix (Fin 3) (Fin 3) ℝ) : ‖sliceLin T‖ ≤ 3 * mnorm T := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (mnorm_nonneg T)) fun w => ?_
  rw [sliceLin_apply]
  calc ‖rmul T (blk 0 w)‖ ≤ 3 * ‖blk (0 : Fin 2 → Fin 2 → ℝ) w‖ * mnorm T := norm_rmul_le T _
    _ ≤ 3 * ‖w‖ * mnorm T :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_blk_zero_le w) (by norm_num)) (mnorm_nonneg T)
    _ = 3 * mnorm T * ‖w‖ := by ring

private theorem norm_iteratedFDeriv_slice_le {F : Arr → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (T : Matrix (Fin 3) (Fin 3) ℝ)
    (h : Fin 2 → Fin 2 → ℝ) (n : ℕ) (w : Pl) :
    ‖iteratedFDeriv ℝ n (fun w' : Pl => F (rmul T (blk h w'))) w‖ ≤
      ‖sliceLin T‖ ^ n * ‖iteratedFDeriv ℝ n F (rmul T (blk h w))‖ := by
  have hfun : (fun w' : Pl => F (rmul T (blk h w'))) = (fun X => F (X + rmul T (blk h 0))) ∘ (sliceLin T) := by
    funext w'; simp only [Function.comp]; rw [rmul_blk_eq T h w']
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun X : Arr => F (X + rmul T (blk h 0))) :=
    hF.comp (contDiff_id.add contDiff_const)
  rw [hfun, (sliceLin T).iteratedFDeriv_comp_right hG w (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_comm]
  gcongr
  rw [iteratedFDeriv_comp_add_right, rmul_blk_eq T h w]

open scoped SchwartzMap

private theorem norm_blk_le_norm_rmul (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (h : Fin 2 → Fin 2 → ℝ) (w : Pl) :
    ‖blk h w‖ ≤ 3 * mnorm T⁻¹ * ‖rmul T (blk h w)‖ := by
  calc ‖blk h w‖ = ‖rmul T⁻¹ (rmul T (blk h w))‖ := by rw [rmul_inv_rmul T hT]
    _ ≤ 3 * ‖rmul T (blk h w)‖ * mnorm T⁻¹ := norm_rmul_le _ _
    _ = 3 * mnorm T⁻¹ * ‖rmul T (blk h w)‖ := by ring

private theorem exists_bound_mnorm_of_isCompact (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K)
    (hKdet : ∀ T ∈ K, T.det ≠ 0) : ∃ R : ℝ, 1 ≤ R ∧ ∀ T ∈ K, mnorm T ≤ R ∧ mnorm T⁻¹ ≤ R := by
  have hc1 : Continuous (fun T : Matrix (Fin 3) (Fin 3) ℝ => (fun i j => T i j : Fin 3 → Fin 3 → ℝ)) :=
    continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i j
  have hinv : ContinuousOn (fun T : Matrix (Fin 3) (Fin 3) ℝ => T⁻¹) K := fun T hT =>
    (continuousAt_matrix_inv T (by
      have hdet : T.det ≠ 0 := hKdet T hT
      simpa [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet))).continuousWithinAt
  have hc2 : ContinuousOn (fun T : Matrix (Fin 3) (Fin 3) ℝ => (fun i j => T⁻¹ i j : Fin 3 → Fin 3 → ℝ)) K :=
    hc1.comp_continuousOn hinv
  obtain ⟨R₁, hR₁⟩ := hK.exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨R₂, hR₂⟩ := hK.exists_bound_of_continuousOn hc2
  refine ⟨max 1 (max R₁ R₂), le_max_left _ _, fun T hT => ⟨?_, ?_⟩⟩
  · exact (hR₁ T hT).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hR₂ T hT).trans ((le_max_right _ _).trans (le_max_right _ _))

private theorem exists_forall_norm_pow_mul_norm_iteratedFDeriv_slice_le (Ψ : 𝓢(Arr, ℂ)) (K : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (hK : IsCompact K) (hKdet : ∀ T ∈ K, T.det ≠ 0) (k n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ K, ∀ (h : Fin 2 → Fin 2 → ℝ) (w : Pl),
      ‖w‖ ^ k * ‖iteratedFDeriv ℝ n (fun w' : Pl => Ψ (rmul T (blk h w'))) w‖ ≤ C * ((1 + ‖h‖) ^ N)⁻¹ := by
  obtain ⟨R, hR1, hR⟩ := exists_bound_mnorm_of_isCompact K hK hKdet
  set m : ℕ := k + N with hm

  set B : ℝ := 2 ^ m * (Finset.Iic (m, n)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℝ p.1 p.2) Ψ with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact mul_nonneg (by positivity) (apply_nonneg _ _)
  have hΨ : ∀ P : Arr, (1 + ‖P‖) ^ m * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖ ≤ B := fun P =>
    SchwartzMap.one_add_le_sup_seminorm_apply (m := (m, n)) le_rfl le_rfl Ψ P
  have h3R : (1 : ℝ) ≤ 3 * R := by linarith
  refine ⟨(3 * R) ^ n * (3 * R) ^ m * B, by positivity, fun T hT h w => ?_⟩
  obtain ⟨hTn, hTi⟩ := hR T hT
  set P : Arr := rmul T (blk h w) with hP
  have hpos : (0 : ℝ) < (1 + ‖h‖) ^ N := by positivity
  rw [le_mul_inv_iff₀ hpos]

  have hblk : 1 + ‖blk h w‖ ≤ 3 * R * (1 + ‖P‖) := by
    have h1 := norm_blk_le_norm_rmul T (hKdet T hT) h w
    have h2 : 3 * mnorm T⁻¹ * ‖P‖ ≤ 3 * R * ‖P‖ := by
      gcongr
    nlinarith [norm_nonneg P]
  have hsl : ‖sliceLin T‖ ≤ 3 * R := (norm_sliceLin_le T).trans (by gcongr)
  have hD := norm_iteratedFDeriv_slice_le (F := ⇑Ψ) (Ψ.smooth (⊤ : ℕ∞)) T h n w
  have hw : ‖w‖ ≤ ‖blk h w‖ := norm_le_norm_blk_right h w
  have hh : ‖h‖ ≤ ‖blk h w‖ := norm_le_norm_blk_left h w
  have hD0 : 0 ≤ ‖iteratedFDeriv ℝ n (⇑Ψ) P‖ := norm_nonneg _
  calc ‖w‖ ^ k * ‖iteratedFDeriv ℝ n (fun w' : Pl => Ψ (rmul T (blk h w'))) w‖ * (1 + ‖h‖) ^ N
      ≤ (1 + ‖blk h w‖) ^ k * (‖sliceLin T‖ ^ n * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) * (1 + ‖blk h w‖) ^ N := by
        gcongr
        linarith
    _ ≤ (1 + ‖blk h w‖) ^ k * ((3 * R) ^ n * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) * (1 + ‖blk h w‖) ^ N := by
        gcongr
    _ = (3 * R) ^ n * ((1 + ‖blk h w‖) ^ m * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) := by
        rw [hm, pow_add]; ring
    _ ≤ (3 * R) ^ n * ((3 * R * (1 + ‖P‖)) ^ m * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) := by
        gcongr
    _ = (3 * R) ^ n * (3 * R) ^ m * ((1 + ‖P‖) ^ m * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) := by
        rw [mul_pow (3 * R) (1 + ‖P‖) m]; ring
    _ ≤ (3 * R) ^ n * (3 * R) ^ m * B := by
        gcongr
        exact hΨ P

private def sliceSchwartz (Ψ : 𝓢(Arr, ℂ)) (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (h : Fin 2 → Fin 2 → ℝ) :
    𝓢(Pl, ℂ) where
  toFun := fun w => Ψ (rmul T (blk h w))
  smooth' := by
    have hfun : (fun w : Pl => rmul T (blk h w)) = fun w => sliceLin T w + rmul T (blk h 0) :=
      funext fun w => rmul_blk_eq T h w
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun w : Pl => rmul T (blk h w)) := by
      rw [hfun]; exact (sliceLin T).contDiff.add contDiff_const
    exact (Ψ.smooth (⊤ : ℕ∞)).comp hc
  decay' := by
    intro k n
    obtain ⟨C, -, hC⟩ := exists_forall_norm_pow_mul_norm_iteratedFDeriv_slice_le Ψ {T} isCompact_singleton
      (by simpa using hT) k n 0
    refine ⟨C, fun w => ?_⟩
    simpa using hC T (Set.mem_singleton T) h w

private theorem sliceSchwartz_apply (Ψ : 𝓢(Arr, ℂ)) (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (h : Fin 2 → Fin 2 → ℝ)
    (w : Pl) : sliceSchwartz Ψ T hT h w = Ψ (rmul T (blk h w)) := rfl

private theorem exists_forall_seminorm_sliceSchwartz_le (Ψ : 𝓢(Arr, ℂ)) (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K)
    (hKdet : ∀ T ∈ K, T.det ≠ 0) (k n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T ∈ K) (h : Fin 2 → Fin 2 → ℝ),
      SchwartzMap.seminorm ℝ k n (sliceSchwartz Ψ T (hKdet T hT) h) ≤ C * ((1 + ‖h‖) ^ N)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := exists_forall_norm_pow_mul_norm_iteratedFDeriv_slice_le Ψ K hK hKdet k n N
  refine ⟨C, hC0, fun T hT h => ?_⟩
  refine SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity) fun w => ?_
  exact hC T hT h w

private theorem character_eq (c : ℝ) (h : Fin 2 → Fin 2 → ℝ) (hdet : (Matrix.of h).det ≠ 0) (v : Pl) :
    c * v 1 = ∑ i, (c • ((Matrix.of h)⁻¹ 1)) i * ((Matrix.of h).mulVec v) i := by
  have hv : (Matrix.of h)⁻¹.mulVec ((Matrix.of h).mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  have h1 : v 1 = ∑ i, (Matrix.of h)⁻¹ 1 i * ((Matrix.of h).mulVec v) i := by
    conv_lhs => rw [← hv]
    simp [Matrix.mulVec, dotProduct]
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem integral_comp_mulVec_eq {G : Pl → ℂ} (hG : Continuous G) (h : Fin 2 → Fin 2 → ℝ) (hdet : (Matrix.of h).det ≠ 0) :
    ∫ v : Pl, G ((Matrix.of h).mulVec v) = ((|(Matrix.of h).det|⁻¹ : ℝ) : ℂ) * ∫ u : Pl, G u := by
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (ι := Fin 2) hdet
  have hmeas : Measurable (Matrix.toLin' (Matrix.of h)) := (Matrix.toLin' (Matrix.of h)).continuous_of_finiteDimensional.measurable
  have hfun : (fun v : Pl => G ((Matrix.of h).mulVec v)) = fun v => G (Matrix.toLin' (Matrix.of h) v) := by
    funext v; simp [Matrix.toLin'_apply]
  rw [hfun, ← MeasureTheory.integral_map hmeas.aemeasurable (hG.aestronglyMeasurable), hmap,
    MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (by positivity), abs_inv]
  exact Complex.real_smul

private theorem inv_pow_mul_inv_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (N : ℕ) :
    ((1 + a) ^ N)⁻¹ * ((1 + b) ^ N)⁻¹ ≤ ((1 + a + b) ^ N)⁻¹ := by
  rw [← mul_inv, ← mul_pow]
  apply inv_anti₀ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [mul_nonneg ha hb]

private theorem norm_integral_schwartzMap_cols_mulVec_mul_right_mul_exp_le' (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (N : ℕ)
    (c : ℝ) (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K) (hKdet : ∀ T ∈ K, T.det ≠ 0) :
    ∃ C : ℝ, ∀ T ∈ K, ∀ h : Fin 2 → Fin 2 → ℝ, (Matrix.of h).det ≠ 0 →
      ‖∫ v : Fin 2 → ℝ,
          Ψ (fun i b => (Matrix.of (fun i' => ![h i' 0, h i' 1, (Matrix.of h).mulVec v i']) * T) i b) *
            Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * |(Matrix.of h).det|⁻¹ * (1 + ‖h‖ + |c| * ‖(Matrix.of h)⁻¹ 1‖) ^ (-(N : ℝ)) := by
  obtain ⟨s, C₂, hC₂0, hB2⟩ :=
    LanglandsTunnell.CubicInduction.exists_finset_forall_norm_integral_schwartzMap_mul_exp_neg_inner_le (Fin 2) N

  choose C₁ hC₁0 hC₁ using fun p : ℕ × ℕ => exists_forall_seminorm_sliceSchwartz_le Ψ K hK hKdet p.1 p.2 N
  set C₁s : ℝ := ∑ p ∈ s, C₁ p with hC₁s
  have hC₁s0 : 0 ≤ C₁s := Finset.sum_nonneg fun p _ => hC₁0 p
  refine ⟨C₂ * C₁s, fun T hT h hdet => ?_⟩
  set φ : 𝓢(Pl, ℂ) := sliceSchwartz Ψ T (hKdet T hT) h with hφ
  set ξ : Pl := c • ((Matrix.of h)⁻¹ 1) with hξ

  set G : Pl → ℂ := fun u => φ u * Complex.exp (((-(2 * Real.pi * ∑ i, ξ i * u i) : ℝ) : ℂ) * Complex.I) with hG
  have hGc : Continuous G := by
    rw [hG]
    refine φ.continuous.mul (Complex.continuous_exp.comp ?_)
    refine Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_const
    exact (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))).neg
  have hint : (fun v : Pl =>
      Ψ (fun i b => (Matrix.of (fun i' => ![h i' 0, h i' 1, (Matrix.of h).mulVec v i']) * T) i b) *
        Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)) = fun v => G ((Matrix.of h).mulVec v) := by
    funext v
    rw [hG]
    simp only []
    rw [hφ, sliceSchwartz_apply]
    congr 2
    rw [mul_assoc (2 * Real.pi) c (v 1), character_eq c h hdet v]
  rw [hint, integral_comp_mulVec_eq hGc h hdet, norm_mul, Complex.norm_of_nonneg (by positivity)]

  have hsup : (s.sup (schwartzSeminormFamily ℝ Pl ℂ)) φ ≤ C₁s * ((1 + ‖h‖) ^ N)⁻¹ := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun p hp => ?_
    obtain ⟨a, b⟩ := p
    rw [SchwartzMap.schwartzSeminormFamily_apply]
    exact (hC₁ (a, b) T hT h).trans (by gcongr; exact Finset.single_le_sum (fun q _ => hC₁0 q) hp)
  have hξn : ‖ξ‖ = |c| * ‖(Matrix.of h)⁻¹ 1‖ := by rw [hξ, norm_smul, Real.norm_eq_abs]
  have hrpow : ∀ x : ℝ, 0 ≤ x → x ^ (-(N : ℝ)) = (x ^ N)⁻¹ := fun x hx => by
    rw [Real.rpow_neg hx, Real.rpow_natCast]
  have hdetpos : 0 < |(Matrix.of h).det|⁻¹ := by positivity
  calc |(Matrix.of h).det|⁻¹ * ‖∫ u : Pl, G u‖
      ≤ |(Matrix.of h).det|⁻¹ * (C₂ * (s.sup (schwartzSeminormFamily ℝ Pl ℂ)) φ * (1 + ‖ξ‖) ^ (-(N : ℝ))) := by
        gcongr
        exact hB2 φ ξ
    _ ≤ |(Matrix.of h).det|⁻¹ * (C₂ * (C₁s * ((1 + ‖h‖) ^ N)⁻¹) * ((1 + ‖ξ‖) ^ N)⁻¹) := by
        rw [hrpow _ (by positivity)]
        gcongr
    _ = C₂ * C₁s * |(Matrix.of h).det|⁻¹ * (((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖ξ‖) ^ N)⁻¹) := by ring
    _ ≤ C₂ * C₁s * |(Matrix.of h).det|⁻¹ * ((1 + ‖h‖ + ‖ξ‖) ^ N)⁻¹ := by
        gcongr
        exact inv_pow_mul_inv_pow_le _ _ (norm_nonneg _) (norm_nonneg _) N
    _ = C₂ * C₁s * |(Matrix.of h).det|⁻¹ * (1 + ‖h‖ + |c| * ‖(Matrix.of h)⁻¹ 1‖) ^ (-(N : ℝ)) := by
        rw [hrpow _ (by positivity), hξn]

end G0

private theorem exists_schwartzMap_eq_exp_neg_pi_sum_sq (ι : Type) [Fintype ι] :
    ∃ Φ : 𝓢((ι → ℝ), ℝ), ∀ x : ι → ℝ, Φ x = Real.exp (-(Real.pi * ∑ i, x i ^ 2)) := by
  exact G0.exists_schwartzMap_eq_exp_neg_pi_sum_sq' (ι := ι)

private theorem norm_integral_schwartzMap_cols_mulVec_mul_right_mul_exp_le (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (N : ℕ)
    (c : ℝ) (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (_hK : IsCompact K) (_hKdet : ∀ T ∈ K, T.det ≠ 0) :
    ∃ C : ℝ, ∀ T ∈ K, ∀ h : Fin 2 → Fin 2 → ℝ, (Matrix.of h).det ≠ 0 →
      ‖∫ v : Fin 2 → ℝ,
          Ψ (fun i b => (Matrix.of (fun i' => ![h i' 0, h i' 1, (Matrix.of h).mulVec v i']) * T) i b) *
            Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * |(Matrix.of h).det|⁻¹ * (1 + ‖h‖ + |c| * ‖(Matrix.of h)⁻¹ 1‖) ^ (-(N : ℝ)) := by
  exact G0.norm_integral_schwartzMap_cols_mulVec_mul_right_mul_exp_le' Ψ N c K _hK _hKdet

namespace G0

private def entryL (v : Fin 2 × Fin 3) : (Fin 2 → Fin 3 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj v.2 : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj v.1 : (Fin 2 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))

private theorem entryL_apply (v : Fin 2 × Fin 3) (M : Fin 2 → Fin 3 → ℝ) : entryL v M = M v.1 v.2 := rfl

private def uncurryL : (Fin 2 → Fin 3 → ℝ) →L[ℝ] (Fin 2 × Fin 3 → ℝ) :=
  ContinuousLinearMap.pi entryL

private theorem uncurryL_apply (M : Fin 2 → Fin 3 → ℝ) (v : Fin 2 × Fin 3) : uncurryL M v = M v.1 v.2 := rfl

private def coordL (v : Fin 2 × Fin 3) : (Fin 2 → Fin 3 → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (entryL v)

private theorem norm_le_norm_uncurryL (M : Fin 2 → Fin 3 → ℝ) : ‖M‖ ≤ ‖uncurryL M‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun b => ?_
  have := norm_le_pi_norm (uncurryL M) (i, b)
  simpa [uncurryL_apply] using this

private theorem hasTemperateGrowth_eval (p : MvPolynomial (Fin 2 × Fin 3) ℂ) :
    Function.HasTemperateGrowth fun M : Fin 2 → Fin 3 → ℝ =>
      MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact Function.HasTemperateGrowth.const a
  | add p q hp hq => simpa [MvPolynomial.eval_add, Pi.add_def] using hp.add hq
  | mul_X p v hp =>
    have hX : Function.HasTemperateGrowth fun M : Fin 2 → Fin 3 → ℝ => ((M v.1 v.2 : ℝ) : ℂ) := by
      have h := (coordL v).hasTemperateGrowth
      convert h using 1 <;> first | with_reducible_and_instances rfl | rfl | exact funext fun _ => rfl
    simpa [MvPolynomial.eval_mul, Pi.mul_def] using hp.mul hX

private theorem exists_schwartzMap_eq_gaussian3 :
    ∃ Φ : 𝓢((Fin 2 → Fin 3 → ℝ), ℝ), ∀ M : Matrix (Fin 2) (Fin 3) ℝ,
      Φ (fun i b => M i b) = Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, M i b ^ 2)) := by
  obtain ⟨Φ₀, hΦ₀⟩ := LanglandsTunnell.CubicInduction.exists_schwartzMap_eq_exp_neg_pi_sum_sq (Fin 2 × Fin 3)
  refine ⟨SchwartzMap.compCLM ℝ uncurryL.hasTemperateGrowth ⟨1, 1, fun M => ?_⟩ Φ₀, fun M => ?_⟩
  · have := norm_le_norm_uncurryL M
    nlinarith [norm_nonneg (uncurryL M)]
  · rw [SchwartzMap.compCLM_apply, Function.comp_apply, hΦ₀]
    simp only [uncurryL_apply, Fintype.sum_prod_type]

private theorem exists_schwartzMap_eq_of_mem_polyGauss3' {S : Matrix (Fin 2) (Fin 3) ℝ → ℂ} (hS : S ∈ polyGauss3) :
    ∃ Φ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ), ∀ M : Matrix (Fin 2) (Fin 3) ℝ, Φ (fun i b => M i b) = S M := by
  obtain ⟨p, rfl⟩ := hS
  obtain ⟨Φg, hΦg⟩ := exists_schwartzMap_eq_gaussian3
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun M : Fin 2 → Fin 3 → ℝ =>
      MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p) (Φg.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM), fun M => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_eval p), SchwartzMap.postcompCLM_apply, hΦg M, smul_eq_mul]
  rfl

end G0

end SchwartzSlices

private theorem godementInner3_eq_integral (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (Φ : SchwartzMap (Fin 2 → Fin 3 → ℝ) ℂ)
    (hΦ : ∀ M : Matrix (Fin 2) (Fin 3) ℝ, Φ (fun i b => M i b) = S M)
    (h : Fin 2 → Fin 2 → ℝ) (T : Matrix (Fin 3) (Fin 3) ℝ) :
    godementInner3 psiInf S (Matrix.of h) T =
      ∫ v : Fin 2 → ℝ, Φ (G0.rmul T (G0.blk h ((Matrix.of h).mulVec v))) *
        Complex.exp (((-(2 * Real.pi * (a : ℝ) * v 1) : ℝ) : ℂ) * Complex.I) := by
  unfold godementInner3
  congr 1
  funext v
  rw [psiInf_ofReal_neg a psiInf hpsiInf (v 1)]
  show _ = Φ (fun i b => (Matrix.of (fun i' => ![h i' 0, h i' 1, (Matrix.of h).mulVec v i']) * T) i b) * _
  rw [hΦ]
  congr 2
  ext i b
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.mulVec, dotProduct]
  ring

open scoped SchwartzMap

open G0 in

private theorem norm_integral_schwartzMap_cols_mulVec_mul_right_mul_exp_le_uniform (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (N : ℕ)
    (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K) (hKdet : ∀ T ∈ K, T.det ≠ 0) :
    ∃ C : ℝ, ∀ (c : ℝ), ∀ T ∈ K, ∀ h : Fin 2 → Fin 2 → ℝ, (Matrix.of h).det ≠ 0 →
      ‖∫ v : Fin 2 → ℝ,
          Ψ (fun i b => (Matrix.of (fun i' => ![h i' 0, h i' 1, (Matrix.of h).mulVec v i']) * T) i b) *
            Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * |(Matrix.of h).det|⁻¹ * (1 + ‖h‖ + |c| * ‖(Matrix.of h)⁻¹ 1‖) ^ (-(N : ℝ)) := by
  obtain ⟨s, C₂, hC₂0, hB2⟩ :=
    LanglandsTunnell.CubicInduction.exists_finset_forall_norm_integral_schwartzMap_mul_exp_neg_inner_le (Fin 2) N
  choose C₁ hC₁0 hC₁ using fun p : ℕ × ℕ => exists_forall_seminorm_sliceSchwartz_le Ψ K hK hKdet p.1 p.2 N
  set C₁s : ℝ := ∑ p ∈ s, C₁ p with hC₁s
  have hC₁s0 : 0 ≤ C₁s := Finset.sum_nonneg fun p _ => hC₁0 p
  refine ⟨C₂ * C₁s, fun c T hT h hdet => ?_⟩
  set φ : 𝓢(Pl, ℂ) := sliceSchwartz Ψ T (hKdet T hT) h with hφ
  set ξ : Pl := c • ((Matrix.of h)⁻¹ 1) with hξ
  set G : Pl → ℂ := fun u => φ u * Complex.exp (((-(2 * Real.pi * ∑ i, ξ i * u i) : ℝ) : ℂ) * Complex.I) with hG
  have hGc : Continuous G := by
    rw [hG]
    refine φ.continuous.mul (Complex.continuous_exp.comp ?_)
    refine Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_const
    exact (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))).neg
  have hint : (fun v : Pl =>
      Ψ (fun i b => (Matrix.of (fun i' => ![h i' 0, h i' 1, (Matrix.of h).mulVec v i']) * T) i b) *
        Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)) = fun v => G ((Matrix.of h).mulVec v) := by
    funext v
    rw [hG]
    simp only []
    rw [hφ, sliceSchwartz_apply]
    congr 2
    rw [mul_assoc (2 * Real.pi) c (v 1), character_eq c h hdet v]
  rw [hint, integral_comp_mulVec_eq hGc h hdet, norm_mul, Complex.norm_of_nonneg (by positivity)]
  have hsup : (s.sup (schwartzSeminormFamily ℝ Pl ℂ)) φ ≤ C₁s * ((1 + ‖h‖) ^ N)⁻¹ := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun p hp => ?_
    obtain ⟨a, b⟩ := p
    rw [SchwartzMap.schwartzSeminormFamily_apply]
    exact (hC₁ (a, b) T hT h).trans (by gcongr; exact Finset.single_le_sum (fun q _ => hC₁0 q) hp)
  have hξn : ‖ξ‖ = |c| * ‖(Matrix.of h)⁻¹ 1‖ := by rw [hξ, norm_smul, Real.norm_eq_abs]
  have hrpow : ∀ x : ℝ, 0 ≤ x → x ^ (-(N : ℝ)) = (x ^ N)⁻¹ := fun x hx => by
    rw [Real.rpow_neg hx, Real.rpow_natCast]
  have hdetpos : 0 < |(Matrix.of h).det|⁻¹ := by positivity
  calc |(Matrix.of h).det|⁻¹ * ‖∫ u : Pl, G u‖
      ≤ |(Matrix.of h).det|⁻¹ * (C₂ * (s.sup (schwartzSeminormFamily ℝ Pl ℂ)) φ * (1 + ‖ξ‖) ^ (-(N : ℝ))) := by
        gcongr
        exact hB2 φ ξ
    _ ≤ |(Matrix.of h).det|⁻¹ * (C₂ * (C₁s * ((1 + ‖h‖) ^ N)⁻¹) * ((1 + ‖ξ‖) ^ N)⁻¹) := by
        rw [hrpow _ (by positivity)]
        gcongr
    _ = C₂ * C₁s * |(Matrix.of h).det|⁻¹ * (((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖ξ‖) ^ N)⁻¹) := by ring
    _ ≤ C₂ * C₁s * |(Matrix.of h).det|⁻¹ * ((1 + ‖h‖ + ‖ξ‖) ^ N)⁻¹ := by
        gcongr
        exact inv_pow_mul_inv_pow_le _ _ (norm_nonneg _) (norm_nonneg _) N
    _ = C₂ * C₁s * |(Matrix.of h).det|⁻¹ * (1 + ‖h‖ + |c| * ‖(Matrix.of h)⁻¹ 1‖) ^ (-(N : ℝ)) := by
        rw [hrpow _ (by positivity), hξn]

namespace RootSizeBound

open G0

private def orthSet : Set (Matrix (Fin 3) (Fin 3) ℝ) := {k | k * k.transpose = 1}

private theorem abs_det_eq_one_of_mul_transpose_eq_one (k : Matrix (Fin 3) (Fin 3) ℝ) (hk : k * k.transpose = 1) :
    |k.det| = 1 := by
  have h : k.det * k.det = 1 := by
    have h1 := congrArg Matrix.det hk
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
  have h2 : |k.det| * |k.det| = 1 := by rw [← abs_mul, h, abs_one]
  rcases mul_self_eq_one_iff.1 h2 with h3 | h3
  · exact h3
  · linarith [abs_nonneg k.det]

private theorem det_ne_zero_of_mem_orthSet (k : Matrix (Fin 3) (Fin 3) ℝ) (hk : k ∈ orthSet) : k.det ≠ 0 := by
  intro h0
  have h1 := abs_det_eq_one_of_mul_transpose_eq_one k hk
  rw [h0, abs_zero] at h1
  exact zero_ne_one h1

private theorem isCompact_orthSet : IsCompact orthSet := by
  have hψ : Continuous (fun M : Fin 3 → Fin 3 → ℝ => Matrix.of M) :=
    continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i)
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine (hbox.image hψ).of_isClosed_subset ?_ ?_
  · have hc : Continuous fun k : Matrix (Fin 3) (Fin 3) ℝ => k * k.transpose :=
      continuous_id.matrix_mul continuous_id.matrix_transpose
    exact isClosed_eq hc continuous_const
  · intro k hk
    refine ⟨fun i j => k i j, ?_, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i j
    have h1 : ∑ l, k i l * k i l = 1 := by
      have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i i) hk
      simpa [Matrix.mul_apply, Matrix.transpose_apply] using h
    have h2 : k i j * k i j ≤ 1 := by
      rw [← h1]
      exact Finset.single_le_sum (f := fun l => k i l * k i l) (fun l _ => mul_self_nonneg (k i l))
        (Finset.mem_univ j)
    constructor <;> nlinarith [h2]

private def colScale (d₀ d₁ : ℝ) (e : Fin 2 → Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j => e i j * ![d₀, d₁] j

private theorem of_colScale (d₀ d₁ : ℝ) (e : Fin 2 → Fin 2 → ℝ) :
    Matrix.of (colScale d₀ d₁ e) = Matrix.of e * Matrix.diagonal ![d₀, d₁] := by
  ext i j
  simp [colScale, Matrix.mul_diagonal]

private theorem det_diagonal_two (d₀ d₁ : ℝ) : (Matrix.diagonal ![d₀, d₁]).det = d₀ * d₁ := by
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem det_of_colScale (d₀ d₁ : ℝ) (e : Fin 2 → Fin 2 → ℝ) :
    (Matrix.of (colScale d₀ d₁ e)).det = (Matrix.of e).det * (d₀ * d₁) := by
  rw [of_colScale, Matrix.det_mul, det_diagonal_two]

private theorem min_mul_norm_le_norm_colScale (d₀ d₁ : ℝ) (e : Fin 2 → Fin 2 → ℝ) :
    min |d₀| |d₁| * ‖e‖ ≤ ‖colScale d₀ d₁ e‖ := by
  have hm : 0 ≤ min |d₀| |d₁| := le_min (abs_nonneg _) (abs_nonneg _)
  have hsmul : min |d₀| |d₁| * ‖e‖ = ‖(min |d₀| |d₁|) • e‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hm]
  rw [hsmul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have h1 : ‖colScale d₀ d₁ e i j‖ ≤ ‖colScale d₀ d₁ e‖ :=
    (norm_le_pi_norm (colScale d₀ d₁ e i) j).trans (norm_le_pi_norm (colScale d₀ d₁ e) i)
  refine le_trans ?_ h1
  have hj : min |d₀| |d₁| ≤ |![d₀, d₁] j| := by
    fin_cases j
    · exact min_le_left _ _
    · exact min_le_right _ _
  simp only [Pi.smul_apply, smul_eq_mul, colScale, Real.norm_eq_abs, abs_mul, abs_of_nonneg hm]
  calc min |d₀| |d₁| * |e i j| ≤ |![d₀, d₁] j| * |e i j| := by gcongr
    _ = |e i j| * |![d₀, d₁] j| := mul_comm _ _

private theorem inv_colScale_apply_one (d₀ d₁ : ℝ) (hd₀ : d₀ ≠ 0) (hd₁ : d₁ ≠ 0) (e : Fin 2 → Fin 2 → ℝ)
    (he : (Matrix.of e).det ≠ 0) :
    (Matrix.of (colScale d₀ d₁ e))⁻¹ 1 = d₁⁻¹ • (Matrix.of e)⁻¹ 1 := by
  have hinv : (Matrix.of (colScale d₀ d₁ e))⁻¹ = Matrix.diagonal ![d₀⁻¹, d₁⁻¹] * (Matrix.of e)⁻¹ := by
    rw [of_colScale]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.of e)⁻¹, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 he),
      Matrix.one_mul, Matrix.diagonal_mul_diagonal]
    have hfun : (fun i => ![d₀⁻¹, d₁⁻¹] i * ![d₀, d₁] i) = fun _ : Fin 2 => (1 : ℝ) := by
      funext i
      fin_cases i
      · simp [inv_mul_cancel₀ hd₀]
      · simp [inv_mul_cancel₀ hd₁]
    rw [hfun, Matrix.diagonal_one]
  rw [hinv]
  funext j
  simp [Matrix.diagonal_mul]

private theorem rpow_neg_bracket_le (m x y : ℝ) (hm : 0 < m) (hx : 0 ≤ x) (hy : 0 ≤ y) (N : ℕ) :
    (1 + m * x + y) ^ (-(N : ℝ)) ≤ (1 + m⁻¹) ^ N * (1 + x + y) ^ (-(N : ℝ)) := by
  have hA : 0 < 1 + m * x + y := by positivity
  have hB : 0 < 1 + x + y := by positivity
  have hkey : 1 + x + y ≤ (1 + m⁻¹) * (1 + m * x + y) := by
    have hexp : (1 + m⁻¹) * (1 + m * x + y) = 1 + m * x + y + m⁻¹ + x + m⁻¹ * y := by
      field_simp
      ring
    rw [hexp]
    have h1 : 0 ≤ m * x := mul_nonneg hm.le hx
    have h2 : 0 ≤ m⁻¹ := inv_nonneg.2 hm.le
    have h3 : 0 ≤ m⁻¹ * y := mul_nonneg h2 hy
    linarith
  have hpow : (1 + x + y) ^ N ≤ (1 + m⁻¹) ^ N * (1 + m * x + y) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hB.le hkey N
  have hP : (1 + m * x + y) ^ N ≠ 0 := by positivity
  have hQ : (1 + x + y) ^ N ≠ 0 := by positivity
  rw [Real.rpow_neg hA.le, Real.rpow_neg hB.le, Real.rpow_natCast, Real.rpow_natCast]
  calc ((1 + m * x + y) ^ N)⁻¹
      = ((1 + m * x + y) ^ N)⁻¹ * (1 + x + y) ^ N * ((1 + x + y) ^ N)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hQ, mul_one]
    _ ≤ ((1 + m * x + y) ^ N)⁻¹ * ((1 + m⁻¹) ^ N * (1 + m * x + y) ^ N) * ((1 + x + y) ^ N)⁻¹ := by
        gcongr
    _ = (1 + m⁻¹) ^ N * ((1 + x + y) ^ N)⁻¹ := by
        rw [mul_comm ((1 + m⁻¹) ^ N), ← mul_assoc, inv_mul_cancel₀ hP, one_mul]

private theorem rmul_diagonal_mul_blk (d₀ d₁ : ℝ) (k : Matrix (Fin 3) (Fin 3) ℝ) (h : Fin 2 → Fin 2 → ℝ) (w : Pl) :
    rmul (Matrix.diagonal ![d₀, d₁, 1] * k) (blk h w) = rmul k (blk (colScale d₀ d₁ h) w) := by
  have hmat : Matrix.of (blk h w) * Matrix.diagonal ![d₀, d₁, 1] = Matrix.of (blk (colScale d₀ d₁ h) w) := by
    ext i c
    rw [Matrix.mul_diagonal]
    fin_cases c <;> simp [blk, colScale]
  funext i b
  simp only [rmul]
  rw [← Matrix.mul_assoc, hmat]

private theorem continuous_torus_integrand (Φ : 𝓢(Arr, ℂ)) (k : Matrix (Fin 3) (Fin 3) ℝ) (h' e : Fin 2 → Fin 2 → ℝ)
    (c : ℝ) :
    Continuous (fun v : Pl => Φ (rmul k (blk h' ((Matrix.of e).mulVec v))) *
      Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)) := by
  have h1 : Continuous (fun v : Pl => rmul k (blk h' ((Matrix.of e).mulVec v))) := by
    have hfun : (fun v : Pl => rmul k (blk h' ((Matrix.of e).mulVec v))) =
        fun v => sliceLin k ((Matrix.of e).mulVec v) + rmul k (blk h' 0) :=
      funext fun v => rmul_blk_eq k h' _
    rw [hfun]
    exact ((sliceLin k).continuous.comp (continuous_const.matrix_mulVec continuous_id)).add continuous_const
  have h2 : Continuous (fun v : Pl => Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)) := by
    refine Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp ?_).mul continuous_const)
    exact (continuous_const.mul (continuous_apply 1)).neg
  exact (Φ.continuous.comp h1).mul h2

private theorem exists_forall_norm_integral_diagonal_mul_le (Φ : 𝓢(Arr, ℂ)) (c : ℝ) (N : ℕ) :
    ∃ C : ℝ, ∀ (d₀ d₁ : ℝ), d₀ ≠ 0 → d₁ ≠ 0 → ∀ k : Matrix (Fin 3) (Fin 3) ℝ, k * k.transpose = 1 →
      ∀ e : Fin 2 → Fin 2 → ℝ, (Matrix.of e).det ≠ 0 →
        ‖∫ v : Pl, Φ (rmul (Matrix.diagonal ![d₀, d₁, 1] * k) (blk e ((Matrix.of e).mulVec v))) *
            Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)‖ ≤
          C * |(Matrix.of e).det|⁻¹ * (1 + min |d₀| |d₁| * ‖e‖ + |c| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-(N : ℝ)) := by
  obtain ⟨C, hC⟩ := norm_integral_schwartzMap_cols_mulVec_mul_right_mul_exp_le_uniform Φ N orthSet
    isCompact_orthSet det_ne_zero_of_mem_orthSet
  refine ⟨max C 0, fun d₀ d₁ hd₀ hd₁ k hk e he => ?_⟩
  set h' : Fin 2 → Fin 2 → ℝ := colScale d₀ d₁ e with hh'
  have hdet' : (Matrix.of h').det = (Matrix.of e).det * (d₀ * d₁) := det_of_colScale d₀ d₁ e
  have hd : d₀ * d₁ ≠ 0 := mul_ne_zero hd₀ hd₁
  have hdet'0 : (Matrix.of h').det ≠ 0 := by rw [hdet']; exact mul_ne_zero he hd

  set hD : Fin 2 → Fin 2 → ℝ := fun i j => Matrix.diagonal ![d₀, d₁] i j with hhD
  have hDof : Matrix.of hD = Matrix.diagonal ![d₀, d₁] := rfl
  have hDdet : (Matrix.of hD).det ≠ 0 := by rw [hDof, det_diagonal_two]; exact hd
  set G : Pl → ℂ := fun u => Φ (rmul k (blk h' ((Matrix.of e).mulVec u))) *
    Complex.exp (((-(2 * Real.pi * c * u 1) : ℝ) : ℂ) * Complex.I) with hG
  have hGc : Continuous G := continuous_torus_integrand Φ k h' e c

  have hint : (fun v : Pl => Φ (rmul (Matrix.diagonal ![d₀, d₁, 1] * k) (blk e ((Matrix.of e).mulVec v))) *
      Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)) = G := by
    funext v
    simp only [hG]
    rw [rmul_diagonal_mul_blk]

  have hcomp : (fun v : Pl => G ((Matrix.of hD).mulVec v)) = fun v : Pl =>
      Φ (rmul k (blk h' ((Matrix.of h').mulVec v))) *
        Complex.exp (((-(2 * Real.pi * (c * d₁) * v 1) : ℝ) : ℂ) * Complex.I) := by
    funext v
    simp only [hG]
    have h1 : (Matrix.diagonal ![d₀, d₁]).mulVec v 1 = d₁ * v 1 := by simp [Matrix.mulVec_diagonal]
    have hr : 2 * Real.pi * c * (d₁ * v 1) = 2 * Real.pi * (c * d₁) * v 1 := by ring
    rw [hDof, Matrix.mulVec_mulVec, ← of_colScale, h1, hr, hh']
  have hsubst := integral_comp_mulVec_eq hGc hD hDdet
  rw [hcomp, hDof, det_diagonal_two] at hsubst

  have hb := hC (c * d₁) k hk h' hdet'0
  have hrow : ‖(Matrix.of h')⁻¹ 1‖ = |d₁|⁻¹ * ‖(Matrix.of e)⁻¹ 1‖ := by
    rw [hh', inv_colScale_apply_one d₀ d₁ hd₀ hd₁ e he, norm_smul, Real.norm_eq_abs, abs_inv]

  have hG_int : ‖∫ u : Pl, G u‖ = |d₀ * d₁| * ‖∫ v : Pl, Φ (rmul k (blk h' ((Matrix.of h').mulVec v))) *
      Complex.exp (((-(2 * Real.pi * (c * d₁) * v 1) : ℝ) : ℂ) * Complex.I)‖ := by
    rw [hsubst, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_abs, ← mul_assoc,
      mul_inv_cancel₀ (abs_ne_zero.2 hd), one_mul]
  rw [hint, hG_int]
  have hbr : (1 + min |d₀| |d₁| * ‖e‖ + |c| * ‖(Matrix.of e)⁻¹ 1‖) ≤ 1 + ‖h'‖ + |c * d₁| * ‖(Matrix.of h')⁻¹ 1‖ := by
    rw [hrow, abs_mul, mul_assoc, ← mul_assoc |d₁|, mul_inv_cancel₀ (abs_ne_zero.2 hd₁), one_mul]
    have := min_mul_norm_le_norm_colScale d₀ d₁ e
    linarith
  have hpos : 0 < 1 + min |d₀| |d₁| * ‖e‖ + |c| * ‖(Matrix.of e)⁻¹ 1‖ := by positivity
  have hrp : (1 + ‖h'‖ + |c * d₁| * ‖(Matrix.of h')⁻¹ 1‖) ^ (-(N : ℝ)) ≤
      (1 + min |d₀| |d₁| * ‖e‖ + |c| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-(N : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hpos hbr (by simp)
  have hdetinv : |(Matrix.of h').det|⁻¹ = |(Matrix.of e).det|⁻¹ * |d₀ * d₁|⁻¹ := by
    rw [hdet', abs_mul, mul_inv]
  have hb' : ‖∫ v : Pl, Φ (rmul k (blk h' ((Matrix.of h').mulVec v))) *
      Complex.exp (((-(2 * Real.pi * (c * d₁) * v 1) : ℝ) : ℂ) * Complex.I)‖ ≤
        max C 0 * |(Matrix.of h').det|⁻¹ *
          (1 + min |d₀| |d₁| * ‖e‖ + |c| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-(N : ℝ)) := by
    calc ‖∫ v : Pl, Φ (rmul k (blk h' ((Matrix.of h').mulVec v))) *
          Complex.exp (((-(2 * Real.pi * (c * d₁) * v 1) : ℝ) : ℂ) * Complex.I)‖
        ≤ C * |(Matrix.of h').det|⁻¹ * (1 + ‖h'‖ + |c * d₁| * ‖(Matrix.of h')⁻¹ 1‖) ^ (-(N : ℝ)) := hb
      _ ≤ max C 0 * |(Matrix.of h').det|⁻¹ * (1 + ‖h'‖ + |c * d₁| * ‖(Matrix.of h')⁻¹ 1‖) ^ (-(N : ℝ)) := by
          gcongr
          exact le_max_left _ _
      _ ≤ max C 0 * |(Matrix.of h').det|⁻¹ *
            (1 + min |d₀| |d₁| * ‖e‖ + |c| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-(N : ℝ)) :=
          mul_le_mul_of_nonneg_left hrp (by positivity)
  calc |d₀ * d₁| * ‖∫ v : Pl, Φ (rmul k (blk h' ((Matrix.of h').mulVec v))) *
          Complex.exp (((-(2 * Real.pi * (c * d₁) * v 1) : ℝ) : ℂ) * Complex.I)‖
      ≤ |d₀ * d₁| * (max C 0 * |(Matrix.of h').det|⁻¹ *
          (1 + min |d₀| |d₁| * ‖e‖ + |c| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-(N : ℝ))) := by gcongr
    _ = max C 0 * |(Matrix.of e).det|⁻¹ *
          (1 + min |d₀| |d₁| * ‖e‖ + |c| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-(N : ℝ)) := by
        rw [hdetinv]
        field_simp

end RootSizeBound

section ColumnIntegrability

open Real

namespace ColumnBracket

private theorem integrable_abs_rpow_mul_bracket {q m : ℝ} (hq : -1 < q) (hm : q + 1 < m) :
    Integrable fun t : ℝ => |t| ^ q * (1 + |t|) ^ (-m) := by
  have hmeas : Measurable fun t : ℝ => |t| ^ q * (1 + |t|) ^ (-m) :=
    (measurable_norm.pow_const q).mul ((measurable_const.add measurable_norm).pow_const (-m))
  have hIoi : IntegrableOn (fun t : ℝ => |t| ^ q * (1 + |t|) ^ (-m)) (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun t : ℝ => t ^ q) (Set.Ioc (0 : ℝ) 1) := by
      have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) hq
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
    have h2 : IntegrableOn (fun t : ℝ => t ^ (q - m)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro h
        by_cases h1 : t ≤ 1
        · exact Or.inl ⟨h, h1⟩
        · exact Or.inr (lt_of_not_ge h1)
      · rintro (⟨h, _⟩ | h)
        · exact h
        · linarith
    rw [hsplit]
    refine IntegrableOn.union ?_ ?_
    · refine h1.mono' hmeas.aestronglyMeasurable.restrict ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos ht0]
      have hb : (1 + t) ^ (-m) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      calc t ^ q * (1 + t) ^ (-m) ≤ t ^ q * 1 := by gcongr
        _ = t ^ q := mul_one _
    · refine h2.mono' hmeas.aestronglyMeasurable.restrict ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : (1 : ℝ) < t := ht
      have ht0 : 0 < t := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos ht0]
      have hb : (1 + t) ^ (-m) ≤ t ^ (-m) :=
        Real.rpow_le_rpow_of_nonpos ht0 (by linarith) (by linarith)
      calc t ^ q * (1 + t) ^ (-m) ≤ t ^ q * t ^ (-m) := by gcongr
        _ = t ^ (q - m) := by rw [← Real.rpow_add ht0, sub_eq_add_neg]
  have hIci : IntegrableOn (fun t : ℝ => |t| ^ q * (1 + |t|) ^ (-m)) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hIoi
  have hIic : IntegrableOn (fun t : ℝ => |t| ^ q * (1 + |t|) ^ (-m)) (Set.Iic 0) := by
    have h := (show IntegrableOn (fun t : ℝ => |t| ^ q * (1 + |t|) ^ (-m)) (Set.Ici (-(0 : ℝ))) by
      simpa using hIci).comp_neg_Iic
    simpa [abs_neg] using h
  have hunion := hIic.union hIci
  rwa [Set.Iic_union_Ici, integrableOn_univ] at hunion

private theorem integrable_entrywise_prod (q : Fin 2 → Fin 2 → ℝ) (m : ℝ) (hq : ∀ i j, -1 < q i j)
    (hm : ∀ i j, q i j + 1 < m) :
    Integrable fun e : Fin 2 → Fin 2 → ℝ => ∏ i, ∏ j, |e i j| ^ (q i j) * (1 + |e i j|) ^ (-m) := by
  have hrow : ∀ i : Fin 2,
      Integrable fun r : Fin 2 → ℝ => ∏ j, |r j| ^ (q i j) * (1 + |r j|) ^ (-m) := by
    intro i
    have h := Integrable.fintype_prod (μ := fun _ : Fin 2 => (volume : Measure ℝ))
      (f := fun j (t : ℝ) => |t| ^ (q i j) * (1 + |t|) ^ (-m))
      (fun j => integrable_abs_rpow_mul_bracket (hq i j) (hm i j))
    rwa [← volume_pi] at h
  have h := Integrable.fintype_prod (μ := fun _ : Fin 2 => (volume : Measure (Fin 2 → ℝ)))
    (f := fun i (r : Fin 2 → ℝ) => ∏ j, |r j| ^ (q i j) * (1 + |r j|) ^ (-m)) hrow
  rwa [← volume_pi] at h

private theorem measurable_column_rpow_mul_bracket (p : ℝ) :
    Measurable fun e : Fin 2 → Fin 2 → ℝ =>
      Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ p * (1 + ‖e‖) ^ (-(4 * max p 0 + 8)) := by
  have h00 : Measurable fun e : Fin 2 → Fin 2 → ℝ => e 0 0 := (measurable_pi_apply 0).comp (measurable_pi_apply 0)
  have h10 : Measurable fun e : Fin 2 → Fin 2 → ℝ => e 1 0 := (measurable_pi_apply 0).comp (measurable_pi_apply 1)
  refine Measurable.mul ?_ ?_
  · exact (Real.continuous_sqrt.measurable.comp ((h00.pow_const 2).add (h10.pow_const 2))).pow_const p
  · exact (measurable_const.add measurable_norm).pow_const _

private theorem abs_entry_le_norm (e : Fin 2 → Fin 2 → ℝ) (i j : Fin 2) : |e i j| ≤ ‖e‖ := by
  calc |e i j| = ‖e i j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖e i‖ := norm_le_pi_norm (e i) j
    _ ≤ ‖e‖ := norm_le_pi_norm e i

private theorem bracket_le_prod (e : Fin 2 → Fin 2 → ℝ) {m : ℝ} (hm : 0 ≤ m) :
    (1 + ‖e‖) ^ (-(4 * m)) ≤ ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-m) := by
  have hpos : (0 : ℝ) < 1 + ‖e‖ := by positivity
  have hfac : ∀ i j : Fin 2, (1 + ‖e‖) ^ (-m) ≤ (1 + |e i j|) ^ (-m) := fun i j =>
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [abs_entry_le_norm e i j]) (by linarith)
  have hsplit : (1 + ‖e‖) ^ (-(4 * m)) = ∏ i : Fin 2, ∏ j : Fin 2, (1 + ‖e‖) ^ (-m) := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
    ring_nf
  rw [hsplit]
  refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => by positivity) fun i _ => ?_
  exact Finset.prod_le_prod (fun j _ => by positivity) fun j _ => hfac i j

private theorem column_rpow_le_of_nonpos {p : ℝ} (hp : p ≤ 0) {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.sqrt (x ^ 2 + y ^ 2) ^ p ≤ (2 : ℝ) ^ (p / 2) * (|x| ^ (p / 2) * |y| ^ (p / 2)) := by
  have hxy : 0 < 2 * (|x| * |y|) := by positivity
  have hle : 2 * (|x| * |y|) ≤ x ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
  have hsq : Real.sqrt (x ^ 2 + y ^ 2) ^ p = (x ^ 2 + y ^ 2) ^ (p / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    ring_nf
  rw [hsq, ← Real.mul_rpow (abs_nonneg x) (abs_nonneg y), ← Real.mul_rpow (by norm_num) (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos hxy hle (by linarith)

private theorem column_rpow_le_of_pos {p : ℝ} (hp : 0 < p) (x y : ℝ) :
    Real.sqrt (x ^ 2 + y ^ 2) ^ p ≤ (2 : ℝ) ^ p * (|x| ^ p + |y| ^ p) := by
  have hs : Real.sqrt (x ^ 2 + y ^ 2) ≤ 2 * max |x| |y| := by
    have hx : |x| ≤ max |x| |y| := le_max_left _ _
    have hy : |y| ≤ max |x| |y| := le_max_right _ _
    have hm : 0 ≤ max |x| |y| := le_trans (abs_nonneg x) hx
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_abs x, sq_abs y, abs_nonneg x, abs_nonneg y]
  calc Real.sqrt (x ^ 2 + y ^ 2) ^ p ≤ (2 * max |x| |y|) ^ p :=
        Real.rpow_le_rpow (Real.sqrt_nonneg _) hs hp.le
    _ = (2 : ℝ) ^ p * max |x| |y| ^ p := Real.mul_rpow (by norm_num) (le_max_of_le_left (abs_nonneg x))
    _ ≤ (2 : ℝ) ^ p * (|x| ^ p + |y| ^ p) := by
        gcongr
        rcases le_total |x| |y| with h | h
        · rw [max_eq_right h]
          linarith [Real.rpow_nonneg (abs_nonneg x) p]
        · rw [max_eq_left h]
          linarith [Real.rpow_nonneg (abs_nonneg y) p]

private theorem ae_column_entries_ne_zero :
    ∀ᵐ e : Fin 2 → Fin 2 → ℝ, e 0 0 ≠ 0 ∧ e 1 0 ≠ 0 := by
  have hrow : ∀ᵐ r : Fin 2 → ℝ, r 0 ≠ 0 := by
    rw [volume_pi]
    exact Measure.ae_eval_ne (fun _ => volume) 0 0
  have h0 : ∀ᵐ e : Fin 2 → Fin 2 → ℝ, e 0 0 ≠ 0 := by
    rw [volume_pi]
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin 2 => (volume : Measure (Fin 2 → ℝ))) (i := 0)).eventually hrow
  have h1 : ∀ᵐ e : Fin 2 → Fin 2 → ℝ, e 1 0 ≠ 0 := by
    rw [volume_pi]
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin 2 => (volume : Measure (Fin 2 → ℝ))) (i := 1)).eventually hrow
  exact h0.and h1

private theorem integrable_column_rpow_mul_bracket {p : ℝ} (hp : -2 < p) :
    Integrable fun e : Fin 2 → Fin 2 → ℝ =>
      Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ p * (1 + ‖e‖) ^ (-(4 * max p 0 + 8)) := by
  have hmeas : AEStronglyMeasurable (fun e : Fin 2 → Fin 2 → ℝ =>
      Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ p * (1 + ‖e‖) ^ (-(4 * max p 0 + 8))) volume :=
    (measurable_column_rpow_mul_bracket p).aestronglyMeasurable
  rcases le_or_gt p 0 with hp0 | hp0
  ·
    rw [max_eq_right hp0] at hmeas ⊢
    set q : Fin 2 → Fin 2 → ℝ := fun _ j => if j = 0 then p / 2 else 0 with hq_def
    have hdom := (integrable_entrywise_prod q 2 (fun i j => by
        simp only [hq_def]; split_ifs <;> linarith) (fun i j => by
        simp only [hq_def]; split_ifs <;> linarith)).const_mul ((2 : ℝ) ^ (p / 2))
    refine hdom.mono' hmeas ?_
    filter_upwards [ae_column_entries_ne_zero] with e he
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hcol := column_rpow_le_of_nonpos hp0 he.1 he.2
    have hbr : (1 + ‖e‖) ^ (-(4 * 0 + 8 : ℝ)) ≤ ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(2 : ℝ)) := by
      have := bracket_le_prod e (m := 2) (by norm_num)
      norm_num at this ⊢
      exact this
    have hprod : ∏ i : Fin 2, ∏ j : Fin 2, |e i j| ^ (q i j) * (1 + |e i j|) ^ (-(2 : ℝ)) =
        (|e 0 0| ^ (p / 2) * |e 1 0| ^ (p / 2)) * ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(2 : ℝ)) := by
      simp only [hq_def, Fin.prod_univ_two, Fin.isValue, if_true, one_ne_zero, if_false, Real.rpow_zero, one_mul]
      ring
    rw [hprod]
    calc Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ p * (1 + ‖e‖) ^ (-(4 * 0 + 8 : ℝ))
        ≤ ((2 : ℝ) ^ (p / 2) * (|e 0 0| ^ (p / 2) * |e 1 0| ^ (p / 2))) *
            ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(2 : ℝ)) := by
          gcongr
      _ = (2 : ℝ) ^ (p / 2) * ((|e 0 0| ^ (p / 2) * |e 1 0| ^ (p / 2)) *
            ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(2 : ℝ))) := by ring
  ·
    rw [max_eq_left hp0.le] at hmeas ⊢
    set q0 : Fin 2 → Fin 2 → ℝ := fun i j => if i = 0 ∧ j = 0 then p else 0 with hq0_def
    set q1 : Fin 2 → Fin 2 → ℝ := fun i j => if i = 1 ∧ j = 0 then p else 0 with hq1_def
    have hi0 := integrable_entrywise_prod q0 (p + 2) (fun i j => by
        simp only [hq0_def]; split_ifs <;> linarith) (fun i j => by simp only [hq0_def]; split_ifs <;> linarith)
    have hi1 := integrable_entrywise_prod q1 (p + 2) (fun i j => by
        simp only [hq1_def]; split_ifs <;> linarith) (fun i j => by simp only [hq1_def]; split_ifs <;> linarith)
    have hdom := (hi0.add hi1).const_mul ((2 : ℝ) ^ p)
    refine hdom.mono' hmeas (Filter.Eventually.of_forall fun e => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hcol := column_rpow_le_of_pos hp0 (e 0 0) (e 1 0)
    have hbr : (1 + ‖e‖) ^ (-(4 * p + 8)) ≤ ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(p + 2)) := by
      have := bracket_le_prod e (m := p + 2) (by linarith)
      rwa [show -(4 * (p + 2)) = -(4 * p + 8) by ring] at this
    have h0 : ∏ i : Fin 2, ∏ j : Fin 2, |e i j| ^ (q0 i j) * (1 + |e i j|) ^ (-(p + 2)) =
        |e 0 0| ^ p * ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(p + 2)) := by
      simp only [hq0_def, Fin.prod_univ_two, Fin.isValue]
      simp
      ring
    have h1 : ∏ i : Fin 2, ∏ j : Fin 2, |e i j| ^ (q1 i j) * (1 + |e i j|) ^ (-(p + 2)) =
        |e 1 0| ^ p * ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(p + 2)) := by
      simp only [hq1_def, Fin.prod_univ_two, Fin.isValue]
      simp
      ring
    simp only [Pi.add_apply]
    rw [h0, h1]
    calc Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ p * (1 + ‖e‖) ^ (-(4 * p + 8))
        ≤ ((2 : ℝ) ^ p * (|e 0 0| ^ p + |e 1 0| ^ p)) * ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(p + 2)) := by
          gcongr
      _ = (2 : ℝ) ^ p * (|e 0 0| ^ p * ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(p + 2)) +
            |e 1 0| ^ p * ∏ i : Fin 2, ∏ j : Fin 2, (1 + |e i j|) ^ (-(p + 2))) := by ring

end ColumnBracket

end ColumnIntegrability

private theorem integrable_sqrt_col_rpow_mul_one_add_norm_rpow_neg (p : ℝ) (hp : -2 < p) :
    Integrable
      (fun e : Fin 2 → Fin 2 → ℝ =>
        Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ p * (1 + ‖e‖) ^ (-(4 * max p 0 + 8)))
      volume := by
  exact ColumnBracket.integrable_column_rpow_mul_bracket hp

private def integrandT {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (A : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (T : Matrix (Fin 3) (Fin 3) ℝ) (e : Fin 2 → Fin 2 → ℝ) : ℂ :=
  godementInner3 ψ S (Matrix.of e) T *
    ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
      D.W (ArchR.diagOne A * (Matrix.of e)⁻¹)

private theorem jacquetIntegrand3_eq_integrandT {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2)
    (A : ℝ) (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    jacquetIntegrand3 D u₃ a₃ A ψ S g = integrandT D u₃ a₃ A ψ S (StandardKernel.realMat g) :=
  rfl

private theorem of_inv_lower_line (e : Fin 2 → Fin 2 → ℝ) :
    (Matrix.of e)⁻¹ 1 0 = (Matrix.of e).det⁻¹ * -(e 1 0) ∧ (Matrix.of e)⁻¹ 1 1 = (Matrix.of e).det⁻¹ * e 0 0 := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  simp

private theorem sqrt_col_pos (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0) :
    0 < Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) := by
  refine Real.sqrt_pos.2 ?_
  by_contra hcon
  have h00 : e 0 0 = 0 := by nlinarith [sq_nonneg (e 0 0), sq_nonneg (e 1 0)]
  have h10 : e 1 0 = 0 := by nlinarith [sq_nonneg (e 0 0), sq_nonneg (e 1 0)]
  apply he
  rw [Matrix.det_fin_two]
  simp [h00, h10]

private theorem sqrt_col_div_le_norm_inv_lower (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0) :
    Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) / (2 * |(Matrix.of e).det|) ≤ ‖(Matrix.of e)⁻¹ 1‖ := by
  obtain ⟨h10, h11⟩ := of_inv_lower_line e
  have hd : 0 < |(Matrix.of e).det| := abs_pos.2 he
  have hr0 : |(Matrix.of e).det|⁻¹ * |e 1 0| ≤ ‖(Matrix.of e)⁻¹ 1‖ := by
    have h := norm_le_pi_norm ((Matrix.of e)⁻¹ 1) 0
    rwa [Real.norm_eq_abs, h10, abs_mul, abs_inv, abs_neg] at h
  have hr1 : |(Matrix.of e).det|⁻¹ * |e 0 0| ≤ ‖(Matrix.of e)⁻¹ 1‖ := by
    have h := norm_le_pi_norm ((Matrix.of e)⁻¹ 1) 1
    rwa [Real.norm_eq_abs, h11, abs_mul, abs_inv] at h
  have hsqrt : Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ≤ |e 0 0| + |e 1 0| := by
    rw [show e 0 0 ^ 2 + e 1 0 ^ 2 = |e 0 0| ^ 2 + |e 1 0| ^ 2 by simp [sq_abs]]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith [abs_nonneg (e 0 0), abs_nonneg (e 1 0)]
  have h0' : |e 1 0| ≤ |(Matrix.of e).det| * ‖(Matrix.of e)⁻¹ 1‖ := by
    have := mul_le_mul_of_nonneg_left hr0 hd.le
    rwa [← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul] at this
  have h1' : |e 0 0| ≤ |(Matrix.of e).det| * ‖(Matrix.of e)⁻¹ 1‖ := by
    have := mul_le_mul_of_nonneg_left hr1 hd.le
    rwa [← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul] at this
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hsqrt, h0', h1']

private theorem abs_det_le_sqrt_col_mul (e : Fin 2 → Fin 2 → ℝ) :
    |(Matrix.of e).det| ≤ 2 * Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) * (1 + ‖e‖) := by
  have hdet : (Matrix.of e).det = e 0 0 * e 1 1 - e 0 1 * e 1 0 := by
    rw [Matrix.det_fin_two]
    rfl
  have hρ0 : 0 ≤ Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) := Real.sqrt_nonneg _
  have h00 : |e 0 0| ≤ Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg (e 1 0)])
  have h10 : |e 1 0| ≤ Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg (e 0 0)])
  have h11 : |e 1 1| ≤ ‖e‖ := by
    have h1 := norm_le_pi_norm (e 1) 1
    have h2 := norm_le_pi_norm e 1
    rw [Real.norm_eq_abs] at h1
    linarith
  have h01 : |e 0 1| ≤ ‖e‖ := by
    have h1 := norm_le_pi_norm (e 0) 1
    have h2 := norm_le_pi_norm e 0
    rw [Real.norm_eq_abs] at h1
    linarith
  rw [hdet]
  calc |e 0 0 * e 1 1 - e 0 1 * e 1 0| ≤ |e 0 0 * e 1 1| + |e 0 1 * e 1 0| := abs_sub _ _
    _ = |e 0 0| * |e 1 1| + |e 0 1| * |e 1 0| := by rw [abs_mul, abs_mul]
    _ ≤ Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) * ‖e‖ + ‖e‖ * Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) := by
        gcongr
    _ ≤ 2 * Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) * (1 + ‖e‖) := by nlinarith [norm_nonneg e]

private theorem gauge_coords {A : ℝ} (hA : A ≠ 0) (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0) :
    Real.sqrt ((ArchR.diagOne A * (Matrix.of e)⁻¹) 1 0 ^ 2 + (ArchR.diagOne A * (Matrix.of e)⁻¹) 1 1 ^ 2) =
        Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) / |(Matrix.of e).det| ∧
      |(ArchR.diagOne A * (Matrix.of e)⁻¹).det| /
          ((ArchR.diagOne A * (Matrix.of e)⁻¹) 1 0 ^ 2 + (ArchR.diagOne A * (Matrix.of e)⁻¹) 1 1 ^ 2) =
        |A| * |(Matrix.of e).det| / Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ 2 ∧
      (ArchR.diagOne A * (Matrix.of e)⁻¹).det ≠ 0 := by
  obtain ⟨h10, h11⟩ := of_inv_lower_line e
  have hx10 : (ArchR.diagOne A * (Matrix.of e)⁻¹) 1 0 = (Matrix.of e)⁻¹ 1 0 := by
    simp [ArchR.diagOne, Matrix.mul_apply, Fin.sum_univ_two]
  have hx11 : (ArchR.diagOne A * (Matrix.of e)⁻¹) 1 1 = (Matrix.of e)⁻¹ 1 1 := by
    simp [ArchR.diagOne, Matrix.mul_apply, Fin.sum_univ_two]
  have hxdet : (ArchR.diagOne A * (Matrix.of e)⁻¹).det = A * (Matrix.of e).det⁻¹ := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    congr 1
    rw [Matrix.det_fin_two]
    simp [ArchR.diagOne]
  have hsum : (ArchR.diagOne A * (Matrix.of e)⁻¹) 1 0 ^ 2 + (ArchR.diagOne A * (Matrix.of e)⁻¹) 1 1 ^ 2 =
      (e 0 0 ^ 2 + e 1 0 ^ 2) / (Matrix.of e).det ^ 2 := by
    rw [hx10, hx11, h10, h11]
    field_simp
    ring
  have hcol : 0 ≤ e 0 0 ^ 2 + e 1 0 ^ 2 := by positivity
  have hcolpos : 0 < e 0 0 ^ 2 + e 1 0 ^ 2 := by
    have := sqrt_col_pos e he
    exact Real.sqrt_pos.1 this
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum, Real.sqrt_div hcol, Real.sqrt_sq_eq_abs]
  · rw [hsum, hxdet, abs_mul, abs_inv, Real.sq_sqrt hcol]
    have hd : |(Matrix.of e).det| ≠ 0 := abs_ne_zero.2 he
    rw [show (Matrix.of e).det ^ 2 = |(Matrix.of e).det| ^ 2 by rw [sq_abs]]
    field_simp
  · rw [hxdet]
    exact mul_ne_zero hA (inv_ne_zero he)

private theorem majorant_core (u γ' q' : ℝ) (N₂ N₃ : ℕ) (hm : 0 ≤ (N₂ : ℝ) + u - γ' - q' - 3)
    (hN₃ : (N₂ : ℝ) + u - γ' - q' - 3 + (4 * max (u + q' - 3) 0 + 8) ≤ N₃)
    {a₀ d ρ x r A : ℝ} (ha₀ : 0 < a₀) (hd : 0 < d) (hρ : 0 < ρ) (hx : 0 ≤ x) (hA : 0 < A)
    (hr : ρ / (2 * d) ≤ r) (hdn : d ≤ 2 * ρ * (1 + x)) :
    d⁻¹ * (1 + x + a₀ * r) ^ (-((N₂ + N₃ : ℕ) : ℝ)) * d ^ u * (d ^ 2)⁻¹ *
        ((ρ / d) ^ γ' * (A * d / ρ ^ 2) ^ (-q')) ≤
      (2 / a₀) ^ N₂ * 2 ^ ((N₂ : ℝ) + u - γ' - q' - 3) *
        (A ^ (-q') * ρ ^ (u + q' - 3) * (1 + x) ^ (-(4 * max (u + q' - 3) 0 + 8))) := by
  have hn0 : 0 < 1 + x := by linarith
  have hn : (1 : ℝ) ≤ 1 + x := by linarith
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hρr : 0 < a₀ * r := mul_pos ha₀ hr0
  have hX : 0 < 1 + x + a₀ * r := by positivity
  have ha₀' : a₀ ≠ 0 := ha₀.ne'
  have hd' : d ≠ 0 := hd.ne'
  have hρ' : ρ ≠ 0 := hρ.ne'

  have h1 : (1 + x + a₀ * r) ^ (-((N₂ + N₃ : ℕ) : ℝ)) ≤ (a₀ * r) ^ (-(N₂ : ℝ)) * (1 + x) ^ (-(N₃ : ℝ)) := by
    have hXn : 1 + x ≤ 1 + x + a₀ * r := by linarith
    have hXr : a₀ * r ≤ 1 + x + a₀ * r := by linarith
    rw [Nat.cast_add, neg_add, Real.rpow_add hX]
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hρr hXr (by simp)) (Real.rpow_le_rpow_of_nonpos hn0 hXn (by simp))
      (by positivity) (by positivity)

  have hlow : a₀ * (ρ / (2 * d)) ≤ a₀ * r := mul_le_mul_of_nonneg_left hr ha₀.le
  have hpos : 0 < a₀ * (ρ / (2 * d)) := by positivity
  have h2 : (a₀ * r) ^ (-(N₂ : ℝ)) ≤ (2 / a₀) ^ N₂ * (d ^ (N₂ : ℝ) * ρ ^ (-(N₂ : ℝ))) := by
    calc (a₀ * r) ^ (-(N₂ : ℝ)) ≤ (a₀ * (ρ / (2 * d))) ^ (-(N₂ : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hpos hlow (by simp)
      _ = (2 / a₀) ^ N₂ * (d ^ (N₂ : ℝ) * ρ ^ (-(N₂ : ℝ))) := by
          rw [Real.rpow_neg hpos.le, Real.rpow_neg hρ.le, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast,
            ← inv_pow, ← inv_pow, ← mul_pow, ← mul_pow]
          congr 1
          rw [div_eq_mul_inv, div_eq_mul_inv]
          simp only [mul_inv, inv_inv]
          ring
  have hB : (1 + x + a₀ * r) ^ (-((N₂ + N₃ : ℕ) : ℝ)) ≤
      (2 / a₀) ^ N₂ * (d ^ (N₂ : ℝ) * ρ ^ (-(N₂ : ℝ))) * (1 + x) ^ (-(N₃ : ℝ)) :=
    h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))

  have e1 : (ρ / d) ^ γ' = ρ ^ γ' * d ^ (-γ') := by
    rw [Real.div_rpow hρ.le hd.le, Real.rpow_neg hd.le, div_eq_mul_inv]
  have hAd : 0 ≤ A * d := by positivity
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  have e2 : (A * d / ρ ^ 2) ^ (-q') = A ^ (-q') * d ^ (-q') * ρ ^ (2 * q') := by
    rw [Real.div_rpow hAd hρ2, Real.mul_rpow hA.le hd.le, Real.rpow_mul hρ.le, Real.rpow_two, Real.rpow_neg hρ2,
      div_inv_eq_mul]

  have hdm : d⁻¹ * d ^ (N₂ : ℝ) * d ^ u * (d ^ 2)⁻¹ * d ^ (-γ') * d ^ (-q') = d ^ ((N₂ : ℝ) + u - γ' - q' - 3) := by
    rw [← Real.rpow_neg_one d, ← Real.rpow_natCast d 2, ← Real.rpow_neg hd.le, ← Real.rpow_add hd, ← Real.rpow_add hd,
      ← Real.rpow_add hd, ← Real.rpow_add hd, ← Real.rpow_add hd]
    congr 1
    push_cast
    ring
  have hρm : ρ ^ (-(N₂ : ℝ)) * ρ ^ γ' * ρ ^ (2 * q') = ρ ^ (γ' + 2 * q' - N₂) := by
    rw [← Real.rpow_add hρ, ← Real.rpow_add hρ]
    congr 1
    ring
  have hdet : d ^ ((N₂ : ℝ) + u - γ' - q' - 3) ≤
      2 ^ ((N₂ : ℝ) + u - γ' - q' - 3) * ρ ^ ((N₂ : ℝ) + u - γ' - q' - 3) *
        (1 + x) ^ ((N₂ : ℝ) + u - γ' - q' - 3) := by
    have h2ρ : (0 : ℝ) ≤ 2 * ρ := by positivity
    rw [← Real.mul_rpow (by norm_num) hρ.le, ← Real.mul_rpow h2ρ hn0.le]
    exact Real.rpow_le_rpow hd.le hdn hm
  have hρ2m : ρ ^ ((N₂ : ℝ) + u - γ' - q' - 3) * ρ ^ (γ' + 2 * q' - N₂) = ρ ^ (u + q' - 3) := by
    rw [← Real.rpow_add hρ]
    congr 1
    ring
  have hxm : (1 + x) ^ ((N₂ : ℝ) + u - γ' - q' - 3) * (1 + x) ^ (-(N₃ : ℝ)) ≤
      (1 + x) ^ (-(4 * max (u + q' - 3) 0 + 8)) := by
    rw [← Real.rpow_add hn0]
    exact Real.rpow_le_rpow_of_exponent_le hn (by linarith)

  have hG : 0 ≤ ρ ^ γ' * d ^ (-γ') * (A ^ (-q') * d ^ (-q') * ρ ^ (2 * q')) := by positivity
  calc d⁻¹ * (1 + x + a₀ * r) ^ (-((N₂ + N₃ : ℕ) : ℝ)) * d ^ u * (d ^ 2)⁻¹ * ((ρ / d) ^ γ' * (A * d / ρ ^ 2) ^ (-q'))
        = d⁻¹ * (1 + x + a₀ * r) ^ (-((N₂ + N₃ : ℕ) : ℝ)) * d ^ u * (d ^ 2)⁻¹ *
          (ρ ^ γ' * d ^ (-γ') * (A ^ (-q') * d ^ (-q') * ρ ^ (2 * q'))) := by rw [e1, e2]
    _ ≤ d⁻¹ * ((2 / a₀) ^ N₂ * (d ^ (N₂ : ℝ) * ρ ^ (-(N₂ : ℝ))) * (1 + x) ^ (-(N₃ : ℝ))) * d ^ u * (d ^ 2)⁻¹ *
          (ρ ^ γ' * d ^ (-γ') * (A ^ (-q') * d ^ (-q') * ρ ^ (2 * q'))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hB (by positivity)) (by positivity)) (by positivity)) hG
    _ = (2 / a₀) ^ N₂ * (d⁻¹ * d ^ (N₂ : ℝ) * d ^ u * (d ^ 2)⁻¹ * d ^ (-γ') * d ^ (-q')) *
          (ρ ^ (-(N₂ : ℝ)) * ρ ^ γ' * ρ ^ (2 * q')) * A ^ (-q') * (1 + x) ^ (-(N₃ : ℝ)) := by ring
    _ = (2 / a₀) ^ N₂ * d ^ ((N₂ : ℝ) + u - γ' - q' - 3) * ρ ^ (γ' + 2 * q' - N₂) * A ^ (-q') *
          (1 + x) ^ (-(N₃ : ℝ)) := by rw [hdm, hρm]
    _ ≤ (2 / a₀) ^ N₂ *
          (2 ^ ((N₂ : ℝ) + u - γ' - q' - 3) * ρ ^ ((N₂ : ℝ) + u - γ' - q' - 3) *
            (1 + x) ^ ((N₂ : ℝ) + u - γ' - q' - 3)) * ρ ^ (γ' + 2 * q' - N₂) * A ^ (-q') * (1 + x) ^ (-(N₃ : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdet (by positivity)) (by positivity)) (by positivity)) (by positivity)
    _ = (2 / a₀) ^ N₂ * 2 ^ ((N₂ : ℝ) + u - γ' - q' - 3) *
          (A ^ (-q') * (ρ ^ ((N₂ : ℝ) + u - γ' - q' - 3) * ρ ^ (γ' + 2 * q' - N₂)) *
            ((1 + x) ^ ((N₂ : ℝ) + u - γ' - q' - 3) * (1 + x) ^ (-(N₃ : ℝ)))) := by ring
    _ = (2 / a₀) ^ N₂ * 2 ^ ((N₂ : ℝ) + u - γ' - q' - 3) *
          (A ^ (-q') * ρ ^ (u + q' - 3) * ((1 + x) ^ ((N₂ : ℝ) + u - γ' - q' - 3) * (1 + x) ^ (-(N₃ : ℝ)))) := by
        rw [hρ2m]
    _ ≤ (2 / a₀) ^ N₂ * 2 ^ ((N₂ : ℝ) + u - γ' - q' - 3) *
          (A ^ (-q') * ρ ^ (u + q' - 3) * (1 + x) ^ (-(4 * max (u + q' - 3) 0 + 8))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxm (by positivity)) (by positivity)

namespace RootSizeBound

private theorem exists_forall_norm_godementInner3_diagonal_mul_le (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) (N : ℕ) :
    ∃ C : ℝ, ∀ (d₀ d₁ : ℝ), d₀ ≠ 0 → d₁ ≠ 0 → ∀ k : Matrix (Fin 3) (Fin 3) ℝ, k * k.transpose = 1 →
      ∀ e : Fin 2 → Fin 2 → ℝ, (Matrix.of e).det ≠ 0 →
        ‖godementInner3 psiInf S (Matrix.of e) (Matrix.diagonal ![d₀, d₁, 1] * k)‖ ≤
          C * |(Matrix.of e).det|⁻¹ *
            (1 + min |d₀| |d₁| * ‖e‖ + |(a : ℝ)| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-(N : ℝ)) := by
  obtain ⟨Φ, hΦ⟩ := G0.exists_schwartzMap_eq_of_mem_polyGauss3' hS
  obtain ⟨C, hC⟩ := exists_forall_norm_integral_diagonal_mul_le Φ (a : ℝ) N
  refine ⟨C, fun d₀ d₁ hd₀ hd₁ k hk e he => ?_⟩
  rw [godementInner3_eq_integral a psiInf hpsiInf S Φ hΦ e (Matrix.diagonal ![d₀, d₁, 1] * k)]
  exact hC d₀ d₁ hd₀ hd₁ k hk e he

private theorem one_add_inv_min_pow_le (d₀ d₁ : ℝ) (hd₀ : d₀ ≠ 0) (hd₁ : d₁ ≠ 0) (n : ℕ) :
    (1 + (min |d₀| |d₁|)⁻¹) ^ n ≤ (1 + |d₀|⁻¹ + |d₁|⁻¹) ^ n := by
  have h0 : 0 ≤ |d₀|⁻¹ := inv_nonneg.2 (abs_nonneg _)
  have h1 : 0 ≤ |d₁|⁻¹ := inv_nonneg.2 (abs_nonneg _)
  refine pow_le_pow_left₀ (by positivity) ?_ n
  rcases min_choice |d₀| |d₁| with h | h <;> rw [h] <;> linarith

private theorem exists_nat_forall_exists_integrable_forall_norm_jacquetIntegrand3_diagonal_mul_le
    {P : RealArchParam} (D : ArchDatumR P)
    (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (c₀ : ℝ)
    (hc₀ : ∀ b : ZMod 2,
      (∀ μ ∈ (P.twist 0 b).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 b).gammaC, -ν.re < c₀)) :
    ∃ n : ℕ, ∀ S ∈ polyGauss3, ∃ G : (Fin 2 → Fin 2 → ℝ) → ℝ, Integrable G volume ∧
      ∀ (d₀ d₁ : ℝ), d₀ ≠ 0 → d₁ ≠ 0 → ∀ k : Matrix (Fin 3) (Fin 3) ℝ, k * k.transpose = 1 →
        ∀ g : GL (Fin 3) (InfiniteAdeleRing ℚ), StandardKernel.realMat g = Matrix.diagonal ![d₀, d₁, 1] * k →
          ∀ e : Fin 2 → Fin 2 → ℝ,
            ‖jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf S g e‖ ≤ (1 + |d₀|⁻¹ + |d₁|⁻¹) ^ n * G e := by

  set q : ℝ := max c₀ (-u₃.re) + 1 with hq_def
  set u : ℝ := (u₃ + 2).re with hu_def
  set γ' : ℝ := P.centralExponent.re + 1 with hγ'_def
  set q' : ℝ := q - 1 with hq'_def
  have hq'c₀ : c₀ - 1 ≤ q' := by
    have := le_max_left c₀ (-u₃.re)
    linarith
  have hure : u = u₃.re + 2 := by simp [hu_def]
  have hp : -2 < u + q' - 3 := by
    have := le_max_right c₀ (-u₃.re)
    linarith
  set N₂ : ℕ := ⌈γ' + q' + 3 - u⌉₊ with hN₂_def
  have hm : 0 ≤ (N₂ : ℝ) + u - γ' - q' - 3 := by
    have := Nat.le_ceil (γ' + q' + 3 - u)
    linarith
  set N₃ : ℕ := ⌈(N₂ : ℝ) + u - γ' - q' - 3 + (4 * max (u + q' - 3) 0 + 8)⌉₊ with hN₃_def
  have hN₃ : (N₂ : ℝ) + u - γ' - q' - 3 + (4 * max (u + q' - 3) 0 + 8) ≤ N₃ := Nat.le_ceil _
  refine ⟨N₂ + N₃, fun S hS => ?_⟩
  obtain ⟨C₁, hC₁⟩ := exists_forall_norm_godementInner3_diagonal_mul_le a psiInf hpsiInf S hS (N₂ + N₃)
  obtain ⟨C₂, hC₂⟩ := archDatumR_exists_forall_norm_W_le_rpow_mul_rpow_of_le D c₀ hc₀ q' hq'c₀
  have ha' : (0 : ℝ) < |(a : ℝ)| := abs_pos.2 (by exact_mod_cast ha)
  set cst : ℝ := max C₁ 0 * max C₂ 0 * ((2 / |(a : ℝ)|) ^ N₂ * 2 ^ ((N₂ : ℝ) + u - γ' - q' - 3)) with hcst_def
  have hcst : 0 ≤ cst := by positivity
  refine ⟨fun e => cst * |(a : ℝ)| ^ (-q') *
      (Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ (u + q' - 3) * (1 + ‖e‖) ^ (-(4 * max (u + q' - 3) 0 + 8))),
    (integrable_sqrt_col_rpow_mul_one_add_norm_rpow_neg (u + q' - 3) hp).const_mul (cst * |(a : ℝ)| ^ (-q')), ?_⟩
  intro d₀ d₁ hd₀ hd₁ k hk g hg e
  rw [jacquetIntegrand3_eq_integrandT, hg]
  have hTn : (0 : ℝ) ≤ (1 + |d₀|⁻¹ + |d₁|⁻¹) ^ (N₂ + N₃) := by positivity
  have hGnn : 0 ≤ cst * |(a : ℝ)| ^ (-q') *
      (Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ (u + q' - 3) * (1 + ‖e‖) ^ (-(4 * max (u + q' - 3) 0 + 8))) :=
    mul_nonneg (mul_nonneg hcst (Real.rpow_nonneg (abs_nonneg _) _))
      (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (Real.rpow_nonneg (by positivity) _))
  by_cases he : (Matrix.of e).det = 0
  ·
    have h0 : integrandT D u₃ a₃ (a : ℝ) psiInf S (Matrix.diagonal ![d₀, d₁, 1] * k) e = 0 := by
      simp [integrandT, he]
    rw [h0, norm_zero]
    exact mul_nonneg hTn hGnn

  have hd : 0 < |(Matrix.of e).det| := abs_pos.2 he
  have hρ : 0 < Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) := sqrt_col_pos e he
  have hamin : 0 < min |d₀| |d₁| := lt_min (abs_pos.2 hd₀) (abs_pos.2 hd₁)
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  obtain ⟨hρx, hτx, hxdet⟩ := gauge_coords haR e he
  have hI : ‖godementInner3 psiInf S (Matrix.of e) (Matrix.diagonal ![d₀, d₁, 1] * k)‖ ≤
      (1 + |d₀|⁻¹ + |d₁|⁻¹) ^ (N₂ + N₃) * (max C₁ 0 * (|(Matrix.of e).det|⁻¹ *
        (1 + ‖e‖ + |(a : ℝ)| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-((N₂ + N₃ : ℕ) : ℝ)))) := by
    have h := hC₁ d₀ d₁ hd₀ hd₁ k hk e he
    have hbr := rpow_neg_bracket_le (min |d₀| |d₁|) ‖e‖ (|(a : ℝ)| * ‖(Matrix.of e)⁻¹ 1‖) hamin (norm_nonneg _)
      (by positivity) (N₂ + N₃)
    have hpow := one_add_inv_min_pow_le d₀ d₁ hd₀ hd₁ (N₂ + N₃)
    calc ‖godementInner3 psiInf S (Matrix.of e) (Matrix.diagonal ![d₀, d₁, 1] * k)‖
        ≤ C₁ * |(Matrix.of e).det|⁻¹ *
          (1 + min |d₀| |d₁| * ‖e‖ + |(a : ℝ)| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-((N₂ + N₃ : ℕ) : ℝ)) := h
      _ ≤ max C₁ 0 * |(Matrix.of e).det|⁻¹ *
          (1 + min |d₀| |d₁| * ‖e‖ + |(a : ℝ)| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-((N₂ + N₃ : ℕ) : ℝ)) := by
          gcongr
          exact le_max_left _ _
      _ ≤ max C₁ 0 * |(Matrix.of e).det|⁻¹ *
          ((1 + (min |d₀| |d₁|)⁻¹) ^ (N₂ + N₃) *
            (1 + ‖e‖ + |(a : ℝ)| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-((N₂ + N₃ : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hbr (by positivity)
      _ ≤ max C₁ 0 * |(Matrix.of e).det|⁻¹ *
          ((1 + |d₀|⁻¹ + |d₁|⁻¹) ^ (N₂ + N₃) *
            (1 + ‖e‖ + |(a : ℝ)| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-((N₂ + N₃ : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by positivity) _))
            (by positivity)
      _ = _ := by ring
  have hQ : ‖ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det‖ ≤ |(Matrix.of e).det| ^ u := norm_quasiChar_le _ _ he
  have hJ : ‖(((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)‖ = (|(Matrix.of e).det| ^ 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hW : ‖D.W (ArchR.diagOne (a : ℝ) * (Matrix.of e)⁻¹)‖ ≤ max C₂ 0 *
      ((Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) / |(Matrix.of e).det|) ^ γ' *
        (|(a : ℝ)| * |(Matrix.of e).det| / Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ 2) ^ (-q')) := by
    have h := hC₂ _ hxdet
    rw [hρx, hτx] at h
    calc ‖D.W (ArchR.diagOne (a : ℝ) * (Matrix.of e)⁻¹)‖
        ≤ C₂ * (Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) / |(Matrix.of e).det|) ^ γ' *
          (|(a : ℝ)| * |(Matrix.of e).det| / Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ 2) ^ (-q') := h
      _ ≤ max C₂ 0 * (Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) / |(Matrix.of e).det|) ^ γ' *
          (|(a : ℝ)| * |(Matrix.of e).det| / Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ 2) ^ (-q') := by
          gcongr
          exact le_max_left _ _
      _ = _ := by ring
  have hcore := majorant_core u γ' q' N₂ N₃ hm hN₃ ha' hd hρ (norm_nonneg e) ha'
    (sqrt_col_div_le_norm_inv_lower e he) (abs_det_le_sqrt_col_mul e)
  have hnorm : ‖integrandT D u₃ a₃ (a : ℝ) psiInf S (Matrix.diagonal ![d₀, d₁, 1] * k) e‖ =
      ‖godementInner3 psiInf S (Matrix.of e) (Matrix.diagonal ![d₀, d₁, 1] * k)‖ *
        ‖ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det‖ * ‖(((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)‖ *
          ‖D.W (ArchR.diagOne (a : ℝ) * (Matrix.of e)⁻¹)‖ := by
    simp only [integrandT, norm_mul]
  rw [hnorm, hJ]
  calc ‖godementInner3 psiInf S (Matrix.of e) (Matrix.diagonal ![d₀, d₁, 1] * k)‖ *
        ‖ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det‖ * (|(Matrix.of e).det| ^ 2)⁻¹ *
          ‖D.W (ArchR.diagOne (a : ℝ) * (Matrix.of e)⁻¹)‖
      ≤ ((1 + |d₀|⁻¹ + |d₁|⁻¹) ^ (N₂ + N₃) * (max C₁ 0 * (|(Matrix.of e).det|⁻¹ *
            (1 + ‖e‖ + |(a : ℝ)| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-((N₂ + N₃ : ℕ) : ℝ))))) *
          |(Matrix.of e).det| ^ u * (|(Matrix.of e).det| ^ 2)⁻¹ *
            (max C₂ 0 * ((Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) / |(Matrix.of e).det|) ^ γ' *
              (|(a : ℝ)| * |(Matrix.of e).det| / Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ 2) ^ (-q'))) := by
        gcongr
    _ = (1 + |d₀|⁻¹ + |d₁|⁻¹) ^ (N₂ + N₃) * (max C₁ 0 * max C₂ 0 *
          (|(Matrix.of e).det|⁻¹ * (1 + ‖e‖ + |(a : ℝ)| * ‖(Matrix.of e)⁻¹ 1‖) ^ (-((N₂ + N₃ : ℕ) : ℝ)) *
            |(Matrix.of e).det| ^ u * (|(Matrix.of e).det| ^ 2)⁻¹ *
              ((Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) / |(Matrix.of e).det|) ^ γ' *
                (|(a : ℝ)| * |(Matrix.of e).det| / Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ 2) ^ (-q')))) := by ring
    _ ≤ (1 + |d₀|⁻¹ + |d₁|⁻¹) ^ (N₂ + N₃) * (max C₁ 0 * max C₂ 0 *
          ((2 / |(a : ℝ)|) ^ N₂ * 2 ^ ((N₂ : ℝ) + u - γ' - q' - 3) *
            (|(a : ℝ)| ^ (-q') * Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ (u + q' - 3) *
              (1 + ‖e‖) ^ (-(4 * max (u + q' - 3) 0 + 8))))) := by
        gcongr
    _ = (1 + |d₀|⁻¹ + |d₁|⁻¹) ^ (N₂ + N₃) * (cst * |(a : ℝ)| ^ (-q') *
          (Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) ^ (u + q' - 3) * (1 + ‖e‖) ^ (-(4 * max (u + q' - 3) 0 + 8)))) := by
        rw [hcst_def]
        ring

end RootSizeBound

namespace RootSizeBound

private theorem exists_nat_forall_exists_forall_norm_jacquetVector3_diagonal_mul_le
    {P : RealArchParam} (D : ArchDatumR P)
    (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (c₀ : ℝ)
    (hc₀ : ∀ b : ZMod 2,
      (∀ μ ∈ (P.twist 0 b).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 b).gammaC, -ν.re < c₀)) :
    ∃ n : ℕ, ∀ S ∈ polyGauss3, ∃ C : ℝ, ∀ (d₀ d₁ : ℝ), d₀ ≠ 0 → d₁ ≠ 0 →
      ∀ k : Matrix (Fin 3) (Fin 3) ℝ, k * k.transpose = 1 →
        ∀ g : GL (Fin 3) (InfiniteAdeleRing ℚ), StandardKernel.realMat g = Matrix.diagonal ![d₀, d₁, 1] * k →
          ‖jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S g‖ ≤
            C * |d₀ * d₁| ^ (u₃.re + 1) * (1 + |d₀|⁻¹ + |d₁|⁻¹) ^ n := by
  obtain ⟨n, hn⟩ := exists_nat_forall_exists_integrable_forall_norm_jacquetIntegrand3_diagonal_mul_le D u₃ a₃ a ha
    psiInf hpsiInf c₀ hc₀
  refine ⟨n, fun S hS => ?_⟩
  obtain ⟨G, hGi, hG⟩ := hn S hS
  refine ⟨∫ e : Fin 2 → Fin 2 → ℝ, G e, fun d₀ d₁ hd₀ hd₁ k hk g hg => ?_⟩
  have hdd : (Matrix.diagonal ![d₀, d₁, 1]).det = d₀ * d₁ := by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp
  have habs : |(Matrix.diagonal ![d₀, d₁, 1] * k).det| = |d₀ * d₁| := by
    rw [Matrix.det_mul, hdd, abs_mul, abs_det_eq_one_of_mul_transpose_eq_one k hk, mul_one]
  have hne : (Matrix.diagonal ![d₀, d₁, 1] * k).det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at habs
    exact mul_ne_zero hd₀ hd₁ (abs_eq_zero.1 habs.symm)
  have hpre : ‖ArchR.quasiChar (u₃ + 1) a₃ (Matrix.diagonal ![d₀, d₁, 1] * k).det‖ ≤ |d₀ * d₁| ^ (u₃.re + 1) := by
    have h := norm_quasiChar_le (u₃ + 1) a₃ hne
    rwa [habs, Complex.add_re, Complex.one_re] at h
  have hTn : (0 : ℝ) ≤ (1 + |d₀|⁻¹ + |d₁|⁻¹) ^ n := by positivity
  have hint : ‖∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf S g e‖ ≤
      (1 + |d₀|⁻¹ + |d₁|⁻¹) ^ n * ∫ e : Fin 2 → Fin 2 → ℝ, G e := by
    rw [← integral_const_mul]
    exact norm_integral_le_of_norm_le (hGi.const_mul _)
      (Filter.Eventually.of_forall fun e => hG d₀ d₁ hd₀ hd₁ k hk g hg e)
  unfold jacquetVector3
  rw [hg, norm_mul]
  calc ‖ArchR.quasiChar (u₃ + 1) a₃ (Matrix.diagonal ![d₀, d₁, 1] * k).det‖ *
        ‖∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf S g e‖
      ≤ |d₀ * d₁| ^ (u₃.re + 1) * ((1 + |d₀|⁻¹ + |d₁|⁻¹) ^ n * ∫ e : Fin 2 → Fin 2 → ℝ, G e) :=
        mul_le_mul hpre hint (norm_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _)
    _ = (∫ e : Fin 2 → Fin 2 → ℝ, G e) * |d₀ * d₁| ^ (u₃.re + 1) * (1 + |d₀|⁻¹ + |d₁|⁻¹) ^ n := by ring

end RootSizeBound

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse

noncomputable section

section LineCalculus
open MvPolynomial Finset MeasureTheory Filter Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam RealArchParam.discrete RealArchParam.principal"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gaussian3 polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq AdelicGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero archComponent3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂ archRootSum archPlaceComponent3 isGL3PsiWhittakerFn_jacquetVector3 jacquetVector3_scalar_mul apply_of_infPart_eq_of_isArchCompAt re_eq_zero_of_isArchCompAt_of_isUnitaryChar exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod upperUnipotent3_inv_eq"
namespace PolyGaussLine
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private abbrev Mat := Matrix (Fin 2) (Fin 3) ℝ

private def qf (M : Mat) : ℝ := ∑ i : Fin 2, ∑ b : Fin 3, M i b ^ 2

private theorem qf_nonneg (M : Mat) : 0 ≤ qf M :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

private theorem sq_entry_le_qf (M : Mat) (i : Fin 2) (b : Fin 3) : M i b ^ 2 ≤ qf M := by
  refine (single_le_sum (f := fun b' => M i b' ^ 2) (fun _ _ => sq_nonneg _) (mem_univ b)).trans ?_
  exact single_le_sum (f := fun i' => ∑ b', M i' b' ^ 2) (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)
    (mem_univ i)

private theorem abs_entry_le (M : Mat) (i : Fin 2) (b : Fin 3) : |M i b| ≤ 1 + qf M := by
  have h := sq_entry_le_qf M i b
  nlinarith [abs_nonneg (M i b), sq_abs (M i b)]

private theorem norm_gaussian3 (M : Mat) : ‖gaussian3 M‖ = Real.exp (-(Real.pi * qf M)) := by
  rw [gaussian3, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rfl

private def ent (M : Mat) : Fin 2 × Fin 3 → ℂ := fun v => ((M v.1 v.2 : ℝ) : ℂ)

private def pg (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (M : Mat) : ℂ := eval (ent M) p * gaussian3 M

private theorem hasDerivAt_eval_line {σ : Type*} [Fintype σ] [DecidableEq σ] (p : MvPolynomial σ ℂ) (Z V : σ → ℂ)
    (ε₀ : ℝ) :
    HasDerivAt (fun ε : ℝ => eval (fun v => Z v + (ε : ℂ) * V v) p)
      (∑ v, eval (fun w => Z w + (ε₀ : ℂ) * V w) (pderiv v p) * V v) ε₀ := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero, zero_mul, sum_const_zero]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    simp only [map_add, add_mul, sum_add_distrib]
    exact hp.add hq
  | mul_X p i hp =>
    have hγ : HasDerivAt (fun ε : ℝ => Z i + (ε : ℂ) * V i) (1 * V i) ε₀ :=
      ((hasDerivAt_id ε₀).ofReal_comp.mul_const (V i)).const_add (Z i)
    have h := hp.mul hγ
    have hfun : (fun ε : ℝ => eval (fun v => Z v + (ε : ℂ) * V v) (p * X i)) =
        fun ε : ℝ => eval (fun v => Z v + (ε : ℂ) * V v) p * (Z i + (ε : ℂ) * V i) := by
      funext ε
      rw [map_mul, eval_X]
    rw [hfun]
    convert h using 1 <;> try with_reducible_and_instances rfl
    simp only [pderiv_mul, pderiv_X, map_add, map_mul, eval_X, add_mul, sum_add_distrib]
    congr 1
    · rw [sum_mul]
      exact sum_congr rfl fun v _ => by ring
    · rw [sum_eq_single i]
      · simp
      · intro v _ hv
        simp [hv]
      · intro hi
        exact absurd (mem_univ i) hi

private theorem hasDerivAt_gaussian3_line (A D : Mat) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => gaussian3 (A + t • D))
      (gaussian3 (A + t₀ • D) *
        (-(2 * Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, (A + t₀ • D) i b * D i b) : ℝ)) t₀ := by
  have key : ∀ (i : Fin 2) (b : Fin 3),
      HasDerivAt (fun t : ℝ => (A + t • D) i b ^ 2) (2 * ((A + t₀ • D) i b * D i b)) t₀ := by
    intro i b
    have h1 : HasDerivAt (fun t : ℝ => (A + t • D) i b) (D i b) t₀ := by
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      simpa using ((hasDerivAt_id t₀).mul_const (D i b)).const_add (A i b)
    have h2 := h1.fun_mul h1
    simp only [← pow_two] at h2
    exact h2.congr_deriv (by ring)
  have hq : HasDerivAt (fun t : ℝ => ∑ i : Fin 2, ∑ b : Fin 3, (A + t • D) i b ^ 2)
      (2 * ∑ i : Fin 2, ∑ b : Fin 3, (A + t₀ • D) i b * D i b) t₀ := by
    have hs := HasDerivAt.fun_sum (u := univ) fun i _ => HasDerivAt.fun_sum (u := univ) fun b _ => key i b
    refine hs.congr_deriv ?_
    simp only [mul_sum]
  unfold gaussian3
  have h := ((hq.const_mul Real.pi).neg.exp).ofReal_comp
  convert h using 1 <;> try with_reducible_and_instances rfl
  simp only [Pi.neg_apply]
  push_cast
  ring

private def rPoly (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (w : Fin 2 × Fin 3) : MvPolynomial (Fin 2 × Fin 3) ℂ :=
  pderiv w p - C (2 * Real.pi : ℂ) * p * X w

private def pgDir (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (M D : Mat) : ℂ :=
  (∑ w, ent D w * eval (ent M) (rPoly p w)) * gaussian3 M

private theorem hasDerivAt_pg_line (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (A D : Mat) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => pg p (A + t • D)) (pgDir p (A + t₀ • D) D) t₀ := by
  have hent : ∀ t : ℝ, ent (A + t • D) = fun w => ent A w + (t : ℂ) * ent D w := by
    intro t
    funext w
    simp only [ent, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]
  have hP := hasDerivAt_eval_line p (ent A) (ent D) t₀
  have hfun : (fun t : ℝ => eval (ent (A + t • D)) p) =
      fun t : ℝ => eval (fun v => ent A v + (t : ℂ) * ent D v) p := by
    funext t
    rw [hent t]
  rw [← hent t₀, ← hfun] at hP
  have h : HasDerivAt (fun t : ℝ => pg p (A + t • D)) _ t₀ := hP.mul (hasDerivAt_gaussian3_line A D t₀)
  refine h.congr_deriv ?_

  set M : Mat := A + t₀ • D with hM
  set G : ℂ := gaussian3 M
  set S₁ : ℂ := ∑ w, eval (ent M) (pderiv w p) * ent D w with hS₁
  set S₂ : ℂ := ∑ w, ent M w * ent D w with hS₂
  have e1 : ∑ w, ent D w * eval (ent M) (rPoly p w) = S₁ - 2 * Real.pi * eval (ent M) p * S₂ := by
    simp only [rPoly, map_sub, map_mul, eval_C, eval_X, mul_sub, Finset.sum_sub_distrib, hS₁, hS₂,
      Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun w _ => by ring
    · exact Finset.sum_congr rfl fun w _ => by ring
  have e2 : (((∑ i : Fin 2, ∑ b : Fin 3, M i b * D i b : ℝ)) : ℂ) = S₂ := by
    rw [hS₂, Fintype.sum_prod_type]
    push_cast
    rfl
  rw [pgDir, e1, ← e2]
  push_cast
  ring

private theorem exists_eval_le (q : MvPolynomial (Fin 2 × Fin 3) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ M : Mat, ‖eval (ent M) q‖ ≤ C * (1 + qf M) ^ d := by
  induction q using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, norm_nonneg _, 0, fun M => by simp⟩
  | add p q hp hq =>
    obtain ⟨C₁, hC₁, d₁, h₁⟩ := hp
    obtain ⟨C₂, hC₂, d₂, h₂⟩ := hq
    refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, max d₁ d₂, fun M => ?_⟩
    have h1 : (1 : ℝ) ≤ 1 + qf M := le_add_of_nonneg_right (qf_nonneg M)
    rw [map_add]
    refine (norm_add_le _ _).trans ?_
    have e₁ := pow_le_pow_right₀ h1 (le_max_left d₁ d₂)
    have e₂ := pow_le_pow_right₀ h1 (le_max_right d₁ d₂)
    nlinarith [h₁ M, h₂ M, mul_le_mul_of_nonneg_left e₁ hC₁, mul_le_mul_of_nonneg_left e₂ hC₂]
  | mul_X p w hp =>
    obtain ⟨C, hC, d, h⟩ := hp
    refine ⟨C, hC, d + 1, fun M => ?_⟩
    rw [map_mul, eval_X, norm_mul, pow_succ, ← mul_assoc]
    refine mul_le_mul (h M) ?_ (norm_nonneg _) (mul_nonneg hC (pow_nonneg (by linarith [qf_nonneg M]) _))
    simp only [ent, Complex.norm_real, Real.norm_eq_abs]
    exact abs_entry_le M w.1 w.2

private theorem exists_pow_mul_exp_le (d : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ d * Real.exp (-(c * x)) ≤ K := by
  refine ⟨d.factorial * c⁻¹ ^ d * Real.exp c, by positivity, fun x hx => ?_⟩
  have h := Real.pow_div_factorial_le_exp (c * (1 + x)) (by positivity) d
  have h1 : (c * (1 + x)) ^ d ≤ Real.exp (c * (1 + x)) * d.factorial := (div_le_iff₀ (by positivity)).1 h
  have h2 : (1 + x) ^ d = (c * (1 + x)) ^ d * c⁻¹ ^ d := by
    rw [mul_pow, mul_assoc, mul_comm ((1 + x) ^ d), ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hc.ne', one_pow,
      one_mul]
  calc (1 + x) ^ d * Real.exp (-(c * x))
      = (c * (1 + x)) ^ d * c⁻¹ ^ d * Real.exp (-(c * x)) := by rw [← h2]
    _ ≤ Real.exp (c * (1 + x)) * d.factorial * c⁻¹ ^ d * Real.exp (-(c * x)) := by gcongr
    _ = d.factorial * c⁻¹ ^ d * (Real.exp (c * (1 + x)) * Real.exp (-(c * x))) := by ring
    _ = d.factorial * c⁻¹ ^ d * Real.exp c := by rw [← Real.exp_add]; ring_nf

private theorem integrable_exp_neg_mul_norm_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun v : Fin 2 → ℝ => Real.exp (-(a * ‖v‖ ^ 2))) := by
  have hprod : Integrable (fun v : Fin 2 → ℝ => ∏ i, Real.exp (-(a / 2) * v i ^ 2)) :=
    Integrable.fintype_prod (f := fun (_ : Fin 2) (x : ℝ) => Real.exp (-(a / 2) * x ^ 2))
      fun _ => integrable_exp_neg_mul_sq (by positivity)
  refine hprod.mono' (by fun_prop) (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Fin.prod_univ_two, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h0 : ‖v 0‖ ≤ ‖v‖ := norm_le_pi_norm v 0
  have h1 : ‖v 1‖ ≤ ‖v‖ := norm_le_pi_norm v 1
  rw [Real.norm_eq_abs] at h0 h1
  have e0 : v 0 ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have e1 : v 1 ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith

private theorem continuous_ent : Continuous (ent : Mat → Fin 2 × Fin 3 → ℂ) :=
  continuous_pi fun w => Complex.continuous_ofReal.comp (continuous_id.matrix_elem w.1 w.2)

private theorem continuous_qf : Continuous qf := by
  unfold qf
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun b _ =>
    (continuous_id.matrix_elem i b).pow 2

private theorem continuous_gaussian3 : Continuous gaussian3 := by
  change Continuous fun M : Mat => ((Real.exp (-(Real.pi * qf M)) : ℝ) : ℂ)
  exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_qf).neg)

private theorem continuous_pg (p : MvPolynomial (Fin 2 × Fin 3) ℂ) : Continuous (pg p) :=
  ((MvPolynomial.continuous_eval p).comp continuous_ent).mul continuous_gaussian3

private theorem continuous_pgDir (p : MvPolynomial (Fin 2 × Fin 3) ℂ) :
    Continuous fun MD : Mat × Mat => pgDir p MD.1 MD.2 := by
  unfold pgDir
  refine Continuous.mul (continuous_finsetSum _ fun w _ => ?_) (continuous_gaussian3.comp continuous_fst)
  exact ((continuous_apply w).comp (continuous_ent.comp continuous_snd)).mul
    ((MvPolynomial.continuous_eval _).comp (continuous_ent.comp continuous_fst))

private theorem norm_pgDir_le (p : MvPolynomial (Fin 2 × Fin 3) ℂ) {Cr : ℝ} {dr : ℕ}
    (hrb : ∀ w M, ‖eval (ent M) (rPoly p w)‖ ≤ Cr * (1 + qf M) ^ dr) {B : ℝ} (M D : Mat)
    (hD : ∀ w, ‖ent D w‖ ≤ B) :
    ‖pgDir p M D‖ ≤ 6 * B * Cr * (1 + qf M) ^ dr * Real.exp (-(Real.pi * qf M)) := by
  rw [pgDir, norm_mul, norm_gaussian3]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  have hB : 0 ≤ B := (norm_nonneg _).trans (hD ((0 : Fin 2), (0 : Fin 3)))
  calc ∑ w, ‖ent D w * eval (ent M) (rPoly p w)‖ ≤ ∑ _w : Fin 2 × Fin 3, B * (Cr * (1 + qf M) ^ dr) :=
        sum_le_sum fun w _ => by
          rw [norm_mul]
          exact mul_le_mul (hD w) (hrb w M) (norm_nonneg _) hB
    _ = 6 * B * Cr * (1 + qf M) ^ dr := by
        rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

private theorem hasDerivAt_integral_pg_line (p : MvPolynomial (Fin 2 × Fin 3) ℂ) {χ : (Fin 2 → ℝ) → ℂ}
    (hχ : Continuous χ) (hχ1 : ∀ v, ‖χ v‖ ≤ 1) {Z₀ Z₁ : (Fin 2 → ℝ) → Mat} (hZ₀ : Continuous Z₀)
    (hZ₁ : Continuous Z₁) {C₁ : ℝ} (hC₁ : ∀ v w, ‖ent (Z₁ v) w‖ ≤ C₁ * (1 + ‖v‖ ^ 2)) {t₀ δ c C : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hgrow : ∀ t ∈ Metric.ball t₀ δ, ∀ v, c * ‖v‖ ^ 2 - C ≤ qf (Z₀ v + t • Z₁ v)) :
    HasDerivAt (fun t : ℝ => ∫ v, pg p (Z₀ v + t • Z₁ v) * χ v)
      (∫ v, pgDir p (Z₀ v + t₀ • Z₁ v) (Z₁ v) * χ v) t₀ := by

  obtain ⟨Cp, hCp, dp, hpb⟩ := exists_eval_le p
  have hr : ∃ Cr : ℝ, 0 ≤ Cr ∧ ∃ dr : ℕ, ∀ w M, ‖eval (ent M) (rPoly p w)‖ ≤ Cr * (1 + qf M) ^ dr := by
    choose Cw hCw dw hw using fun w => exists_eval_le (rPoly p w)
    refine ⟨∑ w, Cw w, sum_nonneg fun w _ => hCw w, ∑ w, dw w, fun w M => (hw w M).trans ?_⟩
    have h1 : (1 : ℝ) ≤ 1 + qf M := le_add_of_nonneg_right (qf_nonneg M)
    exact mul_le_mul (single_le_sum (fun w _ => hCw w) (mem_univ w))
      (pow_le_pow_right₀ h1 (single_le_sum (fun w _ => Nat.zero_le (dw w)) (mem_univ w)))
      (by positivity) (sum_nonneg fun w _ => hCw w)
  obtain ⟨Cr, hCr, dr, hrb⟩ := hr
  obtain ⟨Kp, hKp, hKpb⟩ := exists_pow_mul_exp_le dp (c := Real.pi / 2) (by positivity)
  obtain ⟨Kr, hKr, hKrb⟩ := exists_pow_mul_exp_le dr (c := Real.pi / 2) (by positivity)
  obtain ⟨Kv, hKv, hKvb⟩ := exists_pow_mul_exp_le 1 (c := Real.pi * c / 4) (by positivity)

  have core : ∀ {d : ℕ} {K : ℝ}, 0 ≤ K → (∀ x : ℝ, 0 ≤ x → (1 + x) ^ d * Real.exp (-(Real.pi / 2 * x)) ≤ K) →
      ∀ t ∈ Metric.ball t₀ δ, ∀ v,
        (1 + qf (Z₀ v + t • Z₁ v)) ^ d * Real.exp (-(Real.pi * qf (Z₀ v + t • Z₁ v))) ≤
          K * (Real.exp (Real.pi / 2 * C) * Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2))) := by
    intro d K hK0 hK t ht v
    set q := qf (Z₀ v + t • Z₁ v)
    have hq0 : 0 ≤ q := qf_nonneg _
    have hq : c * ‖v‖ ^ 2 - C ≤ q := hgrow t ht v
    have hsplit : Real.exp (-(Real.pi * q)) =
        Real.exp (-(Real.pi / 2 * q)) * Real.exp (-(Real.pi / 2 * q)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit, ← mul_assoc]
    refine mul_le_mul (hK q hq0) ?_ (Real.exp_nonneg _) hK0
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hq (le_of_lt (half_pos Real.pi_pos))
    linarith
  have hv : ∀ v : Fin 2 → ℝ, (1 + ‖v‖ ^ 2) * Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2)) ≤
      Kv * Real.exp (-(Real.pi * c / 4 * ‖v‖ ^ 2)) := by
    intro v
    have hsplit : Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2)) =
        Real.exp (-(Real.pi * c / 4 * ‖v‖ ^ 2)) * Real.exp (-(Real.pi * c / 4 * ‖v‖ ^ 2)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
    simpa using hKvb (‖v‖ ^ 2) (by positivity)

  set bound : (Fin 2 → ℝ) → ℝ := fun v =>
    6 * C₁ * Cr * Kr * Real.exp (Real.pi / 2 * C) * Kv * Real.exp (-(Real.pi * c / 4 * ‖v‖ ^ 2)) with hbound
  have hbound_int : Integrable bound := (integrable_exp_neg_mul_norm_sq (by positivity)).const_mul _

  have hFc : ∀ t : ℝ, Continuous fun v => pg p (Z₀ v + t • Z₁ v) * χ v := fun t =>
    ((continuous_pg p).comp (hZ₀.add (hZ₁.const_smul t))).mul hχ
  have hF'c : Continuous fun v => pgDir p (Z₀ v + t₀ • Z₁ v) (Z₁ v) * χ v :=
    ((continuous_pgDir p).comp ((hZ₀.add (hZ₁.const_smul t₀)).prodMk hZ₁)).mul hχ

  have ht₀ : t₀ ∈ Metric.ball t₀ δ := Metric.mem_ball_self hδ
  have hF_int : Integrable fun v => pg p (Z₀ v + t₀ • Z₁ v) * χ v := by
    refine Integrable.mono' ((integrable_exp_neg_mul_norm_sq (by positivity : (0 : ℝ) < Real.pi / 2 * c)).const_mul
      (Cp * Kp * Real.exp (Real.pi / 2 * C))) (hFc t₀).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
    rw [norm_mul, pg, norm_mul, norm_gaussian3]
    have hq0 := qf_nonneg (Z₀ v + t₀ • Z₁ v)
    calc ‖eval (ent (Z₀ v + t₀ • Z₁ v)) p‖ * Real.exp (-(Real.pi * qf (Z₀ v + t₀ • Z₁ v))) * ‖χ v‖
        ≤ Cp * (1 + qf (Z₀ v + t₀ • Z₁ v)) ^ dp * Real.exp (-(Real.pi * qf (Z₀ v + t₀ • Z₁ v))) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hpb _) (Real.exp_nonneg _)) (hχ1 v) (norm_nonneg _)
            (mul_nonneg (mul_nonneg hCp (pow_nonneg (by linarith) _)) (Real.exp_nonneg _))
      _ ≤ Cp * (Kp * (Real.exp (Real.pi / 2 * C) * Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2)))) := by
          rw [mul_one, mul_assoc]
          exact mul_le_mul_of_nonneg_left (core hKp hKpb t₀ ht₀ v) hCp
      _ = Cp * Kp * Real.exp (Real.pi / 2 * C) * Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2)) := by ring

  have h_bound : ∀ᵐ v ∂volume, ∀ t ∈ Metric.ball t₀ δ, ‖pgDir p (Z₀ v + t • Z₁ v) (Z₁ v) * χ v‖ ≤ bound v := by
    refine Eventually.of_forall fun v t ht => ?_
    rw [norm_mul]
    have h1 := norm_pgDir_le p hrb (Z₀ v + t • Z₁ v) (Z₁ v) (hC₁ v)
    have hC₁0 : 0 ≤ C₁ * (1 + ‖v‖ ^ 2) := (norm_nonneg _).trans (hC₁ v ((0 : Fin 2), (0 : Fin 3)))
    have hv0 : (0 : ℝ) ≤ 1 + ‖v‖ ^ 2 := by positivity
    have hC₁' : 0 ≤ C₁ := nonneg_of_mul_nonneg_left hC₁0 (by positivity)
    have hq0 := qf_nonneg (Z₀ v + t • Z₁ v)
    have hA : (0 : ℝ) ≤ 6 * C₁ * Cr := by positivity
    have hB : (0 : ℝ) ≤ 6 * C₁ * Cr * Kr * Real.exp (Real.pi / 2 * C) := by positivity
    calc ‖pgDir p (Z₀ v + t • Z₁ v) (Z₁ v)‖ * ‖χ v‖
        ≤ 6 * (C₁ * (1 + ‖v‖ ^ 2)) * Cr * (1 + qf (Z₀ v + t • Z₁ v)) ^ dr *
            Real.exp (-(Real.pi * qf (Z₀ v + t • Z₁ v))) * 1 :=
          mul_le_mul h1 (hχ1 v) (norm_nonneg _)
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₁0) hCr)
              (pow_nonneg (by linarith) _)) (Real.exp_nonneg _))
      _ = 6 * C₁ * Cr * ((1 + qf (Z₀ v + t • Z₁ v)) ^ dr * Real.exp (-(Real.pi * qf (Z₀ v + t • Z₁ v)))) *
            (1 + ‖v‖ ^ 2) := by ring
      _ ≤ 6 * C₁ * Cr * (Kr * (Real.exp (Real.pi / 2 * C) * Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2)))) *
            (1 + ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (core hKr hKrb t ht v) hA) hv0
      _ = 6 * C₁ * Cr * Kr * Real.exp (Real.pi / 2 * C) *
            ((1 + ‖v‖ ^ 2) * Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2))) := by ring
      _ ≤ 6 * C₁ * Cr * Kr * Real.exp (Real.pi / 2 * C) * (Kv * Real.exp (-(Real.pi * c / 4 * ‖v‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left (hv v) hB
      _ = bound v := by rw [hbound]; ring

  have h_diff : ∀ᵐ v ∂volume, ∀ t ∈ Metric.ball t₀ δ,
      HasDerivAt (fun t : ℝ => pg p (Z₀ v + t • Z₁ v) * χ v) (pgDir p (Z₀ v + t • Z₁ v) (Z₁ v) * χ v) t :=
    Eventually.of_forall fun v t _ => (hasDerivAt_pg_line p (Z₀ v) (Z₁ v) t).mul_const (χ v)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t₀ hδ)
    (Eventually.of_forall fun t => (hFc t).aestronglyMeasurable) hF_int hF'c.aestronglyMeasurable h_bound
    hbound_int h_diff).2

private theorem pgDir_smul (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (M D : Mat) (t : ℝ) :
    pgDir p M (t • D) = (t : ℂ) * pgDir p M D := by
  simp only [pgDir, ent, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc]
  rw [← mul_sum, mul_assoc]

private def entryMulPoly (Y : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 × Fin 3) : MvPolynomial (Fin 2 × Fin 3) ℂ :=
  ∑ k : Fin 3, X (v.1, k) * C ((Y k v.2 : ℝ) : ℂ)

private theorem eval_entryMulPoly (M : Mat) (Y : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 × Fin 3) :
    eval (ent M) (entryMulPoly Y v) = ent (M * Y) v := by
  simp only [entryMulPoly, map_sum, map_mul, eval_X, eval_C, ent, Matrix.mul_apply, Complex.ofReal_sum,
    Complex.ofReal_mul]

private def derivedPoly (Y : Matrix (Fin 3) (Fin 3) ℝ) (p : MvPolynomial (Fin 2 × Fin 3) ℂ) :
    MvPolynomial (Fin 2 × Fin 3) ℂ :=
  ∑ w, rPoly p w * entryMulPoly Y w

private theorem pg_derivedPoly (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (Y : Matrix (Fin 3) (Fin 3) ℝ) (M : Mat) :
    pg (derivedPoly Y p) M = pgDir p M (M * Y) := by
  simp only [pg, pgDir, derivedPoly, map_sum, map_mul, eval_entryMulPoly]
  congr 1
  exact sum_congr rfl fun w _ => by ring

private theorem smul_pgDir_eq_pg_derivedPoly (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (Y : Matrix (Fin 3) (Fin 3) ℝ)
    (Z₀ Z₁ : Mat) (t : ℝ) (h : t • Z₁ = (Z₀ + t • Z₁) * Y) :
    (t : ℂ) * pgDir p (Z₀ + t • Z₁) Z₁ = pg (derivedPoly Y p) (Z₀ + t • Z₁) := by
  rw [← pgDir_smul, pg_derivedPoly, ← h]

end LanglandsTunnell.CubicInduction.PolyGaussLine

end LineCalculus

section SliceGrowthAndOuterDerivative
open MvPolynomial Finset MeasureTheory Filter Topology

namespace DualStripDecay

open LanglandsTunnell.CubicInduction.PolyGaussLine Metric

private def rs (r : Fin 3 → ℝ) : ℝ := ∑ b : Fin 3, r b ^ 2

private def qf2 (h : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := ∑ i : Fin 2, ∑ k : Fin 2, h i k ^ 2

private def slice0 (m : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 → ℝ) : Mat :=
  Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b]

private def sliceMat (h : Matrix (Fin 2) (Fin 2) ℝ) (m : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 → ℝ) : Mat :=
  h * slice0 m v

private theorem slice0_apply (m : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 → ℝ) (i : Fin 2) (b : Fin 3) :
    slice0 m v i b = m (Fin.castSucc i) b + v i * m 2 b := by
  fin_cases i <;> rfl

private theorem slice0_add_smul (m₀ m₁ : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) (v : Fin 2 → ℝ) :
    slice0 (m₀ + t • m₁) v = slice0 m₀ v + t • slice0 m₁ v := by
  ext i b
  simp only [slice0_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem sliceMat_add_smul (h : Matrix (Fin 2) (Fin 2) ℝ) (m₀ m₁ : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ)
    (v : Fin 2 → ℝ) : sliceMat h (m₀ + t • m₁) v = sliceMat h m₀ v + t • sliceMat h m₁ v := by
  simp only [sliceMat, slice0_add_smul, Matrix.mul_add, Matrix.mul_smul]

private theorem slice0_smul (M : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) (v : Fin 2 → ℝ) :
    slice0 (t • M) v = t • slice0 M v := by
  ext i b
  simp only [slice0_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem sliceMat_smul (h : Matrix (Fin 2) (Fin 2) ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) (v : Fin 2 → ℝ) :
    sliceMat h (t • M) v = t • sliceMat h M v := by
  simp only [sliceMat, slice0_smul, Matrix.mul_smul]

private theorem slice0_mul (m Y : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 → ℝ) :
    slice0 (m * Y) v = slice0 m v * Y := by
  ext i b
  simp only [slice0_apply, Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> simp <;> ring

private theorem sliceMat_mul (h : Matrix (Fin 2) (Fin 2) ℝ) (m Y : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 → ℝ) :
    sliceMat h (m * Y) v = sliceMat h m v * Y := by
  rw [sliceMat, sliceMat, slice0_mul, Matrix.mul_assoc]

private theorem continuous_slice0 (m : Matrix (Fin 3) (Fin 3) ℝ) : Continuous fun v : Fin 2 → ℝ => slice0 m v := by
  refine continuous_pi fun i => continuous_pi fun b => ?_
  simp only [slice0_apply]
  fun_prop

private theorem continuous_sliceMat (h : Matrix (Fin 2) (Fin 2) ℝ) (m : Matrix (Fin 3) (Fin 3) ℝ) :
    Continuous fun v : Fin 2 → ℝ => sliceMat h m v :=
  continuous_const.matrix_mul (continuous_slice0 m)

private theorem abs_apply_le_norm (v : Fin 2 → ℝ) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have := norm_le_pi_norm v i
  rwa [Real.norm_eq_abs] at this

private theorem norm_le_one_add_sq (v : Fin 2 → ℝ) : ‖v‖ ≤ 1 + ‖v‖ ^ 2 := by
  nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - 1)]

private theorem exists_abs_sliceMat_le (h : Matrix (Fin 2) (Fin 2) ℝ) (m : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ C₁ : ℝ, ∀ (v : Fin 2 → ℝ) (i : Fin 2) (b : Fin 3), |sliceMat h m v i b| ≤ C₁ * (1 + ‖v‖ ^ 2) := by

  refine ⟨∑ i : Fin 2, ∑ b : Fin 3, ∑ k : Fin 2, (|h i k| * |m (Fin.castSucc k) b| + |h i k| * |m 2 b|), ?_⟩
  intro v i b
  have hv1 : (1 : ℝ) ≤ 1 + ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  have hvn : ‖v‖ ≤ 1 + ‖v‖ ^ 2 := norm_le_one_add_sq v
  have hentry : sliceMat h m v i b = ∑ k : Fin 2, h i k * (m (Fin.castSucc k) b + v k * m 2 b) := by
    simp only [sliceMat, Matrix.mul_apply, slice0_apply]
  rw [hentry]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k : Fin 2, |h i k * (m (Fin.castSucc k) b + v k * m 2 b)| ≤
      (|h i k| * |m (Fin.castSucc k) b| + |h i k| * |m 2 b|) * (1 + ‖v‖ ^ 2) := by
    intro k
    rw [abs_mul]
    have hk : |v k| ≤ 1 + ‖v‖ ^ 2 := (abs_apply_le_norm v k).trans hvn
    have h1 : |m (Fin.castSucc k) b + v k * m 2 b| ≤
        |m (Fin.castSucc k) b| * (1 + ‖v‖ ^ 2) + |m 2 b| * (1 + ‖v‖ ^ 2) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      have hm0 : |m (Fin.castSucc k) b| ≤ |m (Fin.castSucc k) b| * (1 + ‖v‖ ^ 2) :=
        le_mul_of_one_le_right (abs_nonneg _) hv1
      have hm2 : |v k| * |m 2 b| ≤ |m 2 b| * (1 + ‖v‖ ^ 2) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hk (abs_nonneg _)
      linarith
    calc |h i k| * |m (Fin.castSucc k) b + v k * m 2 b|
        ≤ |h i k| * (|m (Fin.castSucc k) b| * (1 + ‖v‖ ^ 2) + |m 2 b| * (1 + ‖v‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = (|h i k| * |m (Fin.castSucc k) b| + |h i k| * |m 2 b|) * (1 + ‖v‖ ^ 2) := by ring
  refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)

  have hib : (∑ k : Fin 2, (|h i k| * |m (Fin.castSucc k) b| + |h i k| * |m 2 b|)) ≤
      ∑ b' : Fin 3, ∑ k : Fin 2, (|h i k| * |m (Fin.castSucc k) b'| + |h i k| * |m 2 b'|) :=
    Finset.single_le_sum (f := fun b' => ∑ k : Fin 2, (|h i k| * |m (Fin.castSucc k) b'| + |h i k| * |m 2 b'|))
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ b)
  refine hib.trans ?_
  exact Finset.single_le_sum
    (f := fun i' => ∑ b' : Fin 3, ∑ k : Fin 2, (|h i' k| * |m (Fin.castSucc k) b'| + |h i' k| * |m 2 b'|))
    (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

private theorem qf_mul_le (A : Matrix (Fin 2) (Fin 2) ℝ) (X : Mat) : qf (A * X) ≤ qf2 A * qf X := by
  simp only [qf, qf2, Matrix.mul_apply]

  have hentry : ∀ (i : Fin 2) (b : Fin 3),
      (∑ k : Fin 2, A i k * X k b) ^ 2 ≤ (∑ k : Fin 2, A i k ^ 2) * ∑ k : Fin 2, X k b ^ 2 := fun i b =>
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => A i k) (fun k => X k b)
  calc ∑ i : Fin 2, ∑ b : Fin 3, (∑ k : Fin 2, A i k * X k b) ^ 2
      ≤ ∑ i : Fin 2, ∑ b : Fin 3, (∑ k : Fin 2, A i k ^ 2) * ∑ k : Fin 2, X k b ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => hentry i b
    _ = (∑ i : Fin 2, ∑ k : Fin 2, A i k ^ 2) * ∑ k : Fin 2, ∑ b : Fin 3, X k b ^ 2 := by
        simp only [Fin.sum_univ_two, Fin.sum_univ_three]
        ring

private theorem qf_le_of_det_ne_zero (h : Matrix (Fin 2) (Fin 2) ℝ) (hdet : h.det ≠ 0) (X : Mat) :
    qf X ≤ (qf2 h⁻¹ + 1) * qf (h * X) := by
  have hX : X = h⁻¹ * (h * X) := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul h (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mul]
  have hq : 0 ≤ qf (h * X) := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc qf X = qf (h⁻¹ * (h * X)) := by rw [← hX]
    _ ≤ qf2 h⁻¹ * qf (h * X) := qf_mul_le _ _
    _ ≤ (qf2 h⁻¹ + 1) * qf (h * X) := by nlinarith

private theorem qf_slice0_ge (m : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 → ℝ) :
    rs (m 2) / 2 * (v 0 ^ 2 + v 1 ^ 2) - (rs (m 0) + rs (m 1)) ≤ qf (slice0 m v) := by
  simp only [qf, rs, slice0_apply, Fin.sum_univ_two, Fin.sum_univ_three, Fin.castSucc_zero, Fin.castSucc_one]
  nlinarith [sq_nonneg (2 * m 0 0 + v 0 * m 2 0), sq_nonneg (2 * m 0 1 + v 0 * m 2 1),
    sq_nonneg (2 * m 0 2 + v 0 * m 2 2), sq_nonneg (2 * m 1 0 + v 1 * m 2 0), sq_nonneg (2 * m 1 1 + v 1 * m 2 1),
    sq_nonneg (2 * m 1 2 + v 1 * m 2 2)]

private theorem rs_pos_of_ne_zero {r : Fin 3 → ℝ} (hr : r ≠ 0) : 0 < rs r := by
  rcases (Finset.sum_nonneg fun b _ => sq_nonneg (r b) : (0 : ℝ) ≤ rs r).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hr
    have h0 : ∑ b : Fin 3, r b ^ 2 = 0 := h.symm
    funext b
    have hb := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => sq_nonneg (r b)).mp h0 b (Finset.mem_univ b)
    exact (pow_eq_zero_iff two_ne_zero).mp hb

private theorem sq_norm_le (v : Fin 2 → ℝ) : ‖v‖ ^ 2 ≤ v 0 ^ 2 + v 1 ^ 2 := by
  have h0 : ‖v‖ ≤ Real.sqrt (v 0 ^ 2 + v 1 ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    fin_cases i <;> (try simp) <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  calc ‖v‖ ^ 2 ≤ Real.sqrt (v 0 ^ 2 + v 1 ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h0 2
    _ = v 0 ^ 2 + v 1 ^ 2 := Real.sq_sqrt (by positivity)

private theorem continuous_rs_apply (m₀ m₁ : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    Continuous fun t : ℝ => rs ((m₀ + t • m₁) i) := by
  simp only [rs, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

private theorem exists_growth (h : Matrix (Fin 2) (Fin 2) ℝ) (hdet : h.det ≠ 0) (M₀ M₁ : Matrix (Fin 3) (Fin 3) ℝ)
    (t₀ δ : ℝ) (hδ : 0 < δ) (hrow : ∀ t ∈ closedBall t₀ δ, (M₀ + t • M₁) 2 ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ t ∈ ball t₀ δ, ∀ v : Fin 2 → ℝ,
      c * ‖v‖ ^ 2 - C ≤ qf (sliceMat h M₀ v + t • sliceMat h M₁ v) := by

  obtain ⟨tm, htm, hmin⟩ := (isCompact_closedBall t₀ δ).exists_isMinOn (nonempty_closedBall.mpr hδ.le)
    (continuous_rs_apply M₀ M₁ 2).continuousOn
  set ρ : ℝ := rs ((M₀ + tm • M₁) 2) with hρ
  have hρpos : 0 < ρ := rs_pos_of_ne_zero (hrow tm htm)

  obtain ⟨B, hB⟩ := (isCompact_closedBall t₀ δ).exists_bound_of_continuousOn
    ((continuous_rs_apply M₀ M₁ 0).add (continuous_rs_apply M₀ M₁ 1)).continuousOn
  set κ : ℝ := qf2 h⁻¹ + 1 with hκ
  have hκpos : 0 < κ := by
    have : 0 ≤ qf2 h⁻¹ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  refine ⟨ρ / 2 / κ, by positivity, B / κ, fun t ht v => ?_⟩
  have ht' : t ∈ closedBall t₀ δ := ball_subset_closedBall ht
  rw [← sliceMat_add_smul, sliceMat]
  have h1 := qf_le_of_det_ne_zero h hdet (slice0 (M₀ + t • M₁) v)
  have h2 := qf_slice0_ge (M₀ + t • M₁) v
  have h3 : ρ ≤ rs ((M₀ + t • M₁) 2) := hmin ht'
  have h4 : rs ((M₀ + t • M₁) 0) + rs ((M₀ + t • M₁) 1) ≤ B := by
    have hBt := hB t ht'
    rw [Real.norm_eq_abs] at hBt
    exact (abs_le.mp hBt).2
  have h5 := sq_norm_le v
  have hvv : 0 ≤ v 0 ^ 2 + v 1 ^ 2 := by positivity

  have h6 : ρ / 2 * ‖v‖ ^ 2 - B ≤ κ * qf (h * slice0 (M₀ + t • M₁) v) := by
    have h7 : ρ / 2 * ‖v‖ ^ 2 ≤ rs ((M₀ + t • M₁) 2) / 2 * (v 0 ^ 2 + v 1 ^ 2) := by
      have := mul_le_mul h3 h5 (sq_nonneg _) (by linarith)
      linarith
    linarith
  rw [div_mul_eq_mul_div, div_sub_div_same]
  exact (div_le_iff₀ hκpos).mpr (by linarith)

end DualStripDecay

namespace DualStripDecay

p2m_open "MeasureTheory Metric Filter Topology AutomorphicForm.StandardKernel LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_norm_archComponent3_le.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_norm_archComponent3_le.LanglandsTunnell.CubicInduction LanglandsTunnell.Converse.ArchR P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_norm_archComponent3_le.LanglandsTunnell.CubicInduction.PolyGaussLine"

section Bridge

private def wFactor {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (e : Fin 2 → Fin 2 → ℝ) : ℂ :=
  quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) * D.W (diagOne a * (Matrix.of e)⁻¹)

private theorem jacquetIntegrand3_eq {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ))
    (e : Fin 2 → Fin 2 → ℝ) :
    jacquetIntegrand3 D u₃ a₃ a ψ S g e = godementInner3 ψ S (Matrix.of e) (realMat g) * wFactor D u₃ a₃ a e := by
  simp only [jacquetIntegrand3, wFactor, mul_assoc]

private theorem godementInner3_pg_eq (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (p : MvPolynomial (Fin 2 × Fin 3) ℂ)
    (h : Matrix (Fin 2) (Fin 2) ℝ) (m : Matrix (Fin 3) (Fin 3) ℝ) :
    godementInner3 ψ (pg p) h m = ∫ v : Fin 2 → ℝ, pg p (sliceMat h m v) * ψ (ofReal (-(v 1))) :=
  rfl

end Bridge

section Inner

variable (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ)

private theorem hasDerivAt_inner (hχ : Continuous fun v : Fin 2 → ℝ => ψ (ofReal (-(v 1))))
    (hχ1 : ∀ v : Fin 2 → ℝ, ‖ψ (ofReal (-(v 1)))‖ ≤ 1) (p : MvPolynomial (Fin 2 × Fin 3) ℂ)
    {h : Matrix (Fin 2) (Fin 2) ℝ} (hdet : h.det ≠ 0) (M₀ M₁ : Matrix (Fin 3) (Fin 3) ℝ) {t₀ δ : ℝ} (hδ : 0 < δ)
    (hrow : ∀ t ∈ closedBall t₀ δ, (M₀ + t • M₁) 2 ≠ 0) :
    HasDerivAt (fun t : ℝ => godementInner3 ψ (pg p) h (M₀ + t • M₁))
      (∫ v : Fin 2 → ℝ, pgDir p (sliceMat h M₀ v + t₀ • sliceMat h M₁ v) (sliceMat h M₁ v) * ψ (ofReal (-(v 1))))
      t₀ := by
  obtain ⟨c, hc, C, hgrow⟩ := exists_growth h hdet M₀ M₁ t₀ δ hδ hrow
  obtain ⟨C₁, hC₁⟩ := exists_abs_sliceMat_le h M₁
  have hfun : (fun t : ℝ => godementInner3 ψ (pg p) h (M₀ + t • M₁)) =
      fun t : ℝ => ∫ v : Fin 2 → ℝ, pg p (sliceMat h M₀ v + t • sliceMat h M₁ v) * ψ (ofReal (-(v 1))) := by
    funext t
    rw [godementInner3_pg_eq]
    simp only [sliceMat_add_smul]
  rw [hfun]
  refine hasDerivAt_integral_pg_line p hχ hχ1 (continuous_sliceMat h M₀) (continuous_sliceMat h M₁) (C₁ := C₁)
    (fun v w => ?_) hδ hc hgrow
  simp only [ent, Complex.norm_real, Real.norm_eq_abs]
  exact hC₁ v w.1 w.2

private theorem mul_inner_deriv_eq (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (h : Matrix (Fin 2) (Fin 2) ℝ)
    (M₀ M₁ Y : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) (hY : (M₀ + t • M₁) * Y = t • M₁) :
    t * (∫ v : Fin 2 → ℝ, pgDir p (sliceMat h M₀ v + t • sliceMat h M₁ v) (sliceMat h M₁ v) * ψ (ofReal (-(v 1)))) =
      godementInner3 ψ (pg (derivedPoly Y p)) h (M₀ + t • M₁) := by
  rw [godementInner3_pg_eq]
  refine (integral_const_mul (t : ℂ) _).symm.trans (integral_congr_ae (Eventually.of_forall fun v => ?_))
  have hv : t • sliceMat h M₁ v = (sliceMat h M₀ v + t • sliceMat h M₁ v) * Y := by
    rw [← sliceMat_add_smul, ← sliceMat_mul, hY, sliceMat_smul]
  show t * (pgDir p (sliceMat h M₀ v + t • sliceMat h M₁ v) (sliceMat h M₁ v) * ψ (ofReal (-(v 1)))) =
    pg (derivedPoly Y p) (sliceMat h (M₀ + t • M₁) v) * ψ (ofReal (-(v 1)))
  rw [← mul_assoc, smul_pgDir_eq_pg_derivedPoly p Y _ _ t hv, sliceMat_add_smul]

end Inner

section OuterAffine

private theorem realMat_apply_ne_zero (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (i : Fin 3) : realMat g i ≠ 0 := by
  intro h0
  have hdet : (realMat g).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (realGL g).isUnit).ne_zero
  exact hdet (Matrix.det_eq_zero_of_row_eq_zero i fun j => congrFun h0 j)

private theorem integrable_pg_slice (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hχ : Continuous fun v : Fin 2 → ℝ => ψ (ofReal (-(v 1)))) (hχ1 : ∀ v : Fin 2 → ℝ, ‖ψ (ofReal (-(v 1)))‖ ≤ 1)
    (q : MvPolynomial (Fin 2 × Fin 3) ℂ) {h : Matrix (Fin 2) (Fin 2) ℝ} (hdet : h.det ≠ 0)
    {m : Matrix (Fin 3) (Fin 3) ℝ} (hm : m 2 ≠ 0) :
    Integrable fun v : Fin 2 → ℝ => pg q (sliceMat h m v) * ψ (ofReal (-(v 1))) := by
  have hrow₀ : ∀ t ∈ closedBall (0 : ℝ) 1, (m + t • (0 : Matrix (Fin 3) (Fin 3) ℝ)) 2 ≠ 0 := fun t _ => by
    rw [smul_zero, add_zero]
    exact hm
  obtain ⟨c, hc, C, hgrow⟩ := exists_growth h hdet m 0 0 1 one_pos hrow₀
  have hg : ∀ v : Fin 2 → ℝ, c * ‖v‖ ^ 2 - C ≤ qf (sliceMat h m v) := fun v => by
    have := hgrow 0 (mem_ball_self one_pos) v
    rwa [zero_smul, add_zero] at this
  obtain ⟨Cp, hCp, dp, hpb⟩ := exists_eval_le q
  obtain ⟨Kp, hKp, hKpb⟩ := exists_pow_mul_exp_le dp (c := Real.pi / 2) (by positivity)
  have hcont : Continuous fun v : Fin 2 → ℝ => pg q (sliceMat h m v) * ψ (ofReal (-(v 1))) :=
    ((continuous_pg q).comp (continuous_sliceMat h m)).mul hχ
  refine Integrable.mono' ((integrable_exp_neg_mul_norm_sq (by positivity : (0 : ℝ) < Real.pi / 2 * c)).const_mul
    (Cp * Kp * Real.exp (Real.pi / 2 * C))) hcont.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [norm_mul, pg, norm_mul, norm_gaussian3]
  have hq0 : 0 ≤ qf (sliceMat h m v) := qf_nonneg _
  have hsplit : Real.exp (-(Real.pi * qf (sliceMat h m v))) =
      Real.exp (-(Real.pi / 2 * qf (sliceMat h m v))) * Real.exp (-(Real.pi / 2 * qf (sliceMat h m v))) := by
    rw [← Real.exp_add]
    ring_nf
  have h2 : Real.exp (-(Real.pi / 2 * qf (sliceMat h m v))) ≤
      Real.exp (Real.pi / 2 * C) * Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left (hg v) (le_of_lt (half_pos Real.pi_pos))
    linarith
  calc ‖eval (ent (sliceMat h m v)) q‖ * Real.exp (-(Real.pi * qf (sliceMat h m v))) * ‖ψ (ofReal (-(v 1)))‖
      ≤ Cp * (1 + qf (sliceMat h m v)) ^ dp * Real.exp (-(Real.pi * qf (sliceMat h m v))) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hpb _) (Real.exp_nonneg _)) (hχ1 v) (norm_nonneg _)
          (mul_nonneg (mul_nonneg hCp (pow_nonneg (by linarith) _)) (Real.exp_nonneg _))
    _ = Cp * ((1 + qf (sliceMat h m v)) ^ dp * Real.exp (-(Real.pi / 2 * qf (sliceMat h m v)))) *
          Real.exp (-(Real.pi / 2 * qf (sliceMat h m v))) := by
        rw [hsplit]
        ring
    _ ≤ Cp * Kp * (Real.exp (Real.pi / 2 * C) * Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hKpb _ hq0) hCp) h2 (Real.exp_nonneg _) (by positivity)
    _ = Cp * Kp * Real.exp (Real.pi / 2 * C) * Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2)) := by ring

private theorem inner_deriv_eq_affine (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (p : MvPolynomial (Fin 2 × Fin 3) ℂ)
    (h : Matrix (Fin 2) (Fin 2) ℝ) (M₀ M₁ Y : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) (hY : (M₀ + t • M₁) * Y = M₁) :
    (∫ v : Fin 2 → ℝ, pgDir p (sliceMat h M₀ v + t • sliceMat h M₁ v) (sliceMat h M₁ v) * ψ (ofReal (-(v 1)))) =
      godementInner3 ψ (pg (derivedPoly Y p)) h (M₀ + t • M₁) := by
  rw [godementInner3_pg_eq]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  have hv : (sliceMat h M₀ v + t • sliceMat h M₁ v) * Y = sliceMat h M₁ v := by
    rw [← sliceMat_add_smul, ← sliceMat_mul, hY]
  show pgDir p (sliceMat h M₀ v + t • sliceMat h M₁ v) (sliceMat h M₁ v) * ψ (ofReal (-(v 1))) =
    pg (derivedPoly Y p) (sliceMat h (M₀ + t • M₁) v) * ψ (ofReal (-(v 1)))
  rw [sliceMat_add_smul, pg_derivedPoly, hv]

private theorem hasDerivAt_integral_jacquetIntegrand3_affine_core {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ)
    (a₃ : ZMod 2) (a : ℝ) (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hχ : Continuous fun v : Fin 2 → ℝ => ψ (ofReal (-(v 1)))) (hχ1 : ∀ v : Fin 2 → ℝ, ‖ψ (ofReal (-(v 1)))‖ ≤ 1)
    (hnull : (volume : Measure (Fin 2 → Fin 2 → ℝ)) {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} = 0)
    (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (M₀ M₁ Y : Matrix (Fin 3) (Fin 3) ℝ)
    (hY : ∀ t : ℝ, (M₀ + t • M₁) * Y = M₁)
    (γ : ℝ → GL (Fin 3) (InfiniteAdeleRing ℚ)) (hγ : ∀ t : ℝ, realMat (γ t) = M₀ + t • M₁) (hγc : Continuous γ)
    (hmeas : ∀ g : GL (Fin 3) (InfiniteAdeleRing ℚ),
      AEStronglyMeasurable (jacquetIntegrand3 D u₃ a₃ a ψ (pg p) g) volume)
    (hmeas' : ∀ g : GL (Fin 3) (InfiniteAdeleRing ℚ),
      AEStronglyMeasurable (jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly Y p)) g) volume)
    (hmaj : ∀ g₀ : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ U ∈ nhds g₀, ∃ F : (Fin 2 → Fin 2 → ℝ) → ℝ,
      Integrable F volume ∧ ∀ g ∈ U, ∀ e : Fin 2 → Fin 2 → ℝ, ‖jacquetIntegrand3 D u₃ a₃ a ψ (pg p) g e‖ ≤ F e)
    (hmaj' : ∀ g₀ : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ U ∈ nhds g₀, ∃ F : (Fin 2 → Fin 2 → ℝ) → ℝ,
      Integrable F volume ∧
        ∀ g ∈ U, ∀ e : Fin 2 → Fin 2 → ℝ, ‖jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly Y p)) g e‖ ≤ F e)
    (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg p) (γ t) e)
      (∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly Y p)) (γ t₀) e) t₀ := by
  obtain ⟨U, hU, Fm, hFm, hbound⟩ := hmaj' (γ t₀)
  obtain ⟨U₀, hU₀, Fm₀, hFm₀, hbound₀⟩ := hmaj (γ t₀)
  have hs : γ ⁻¹' U ∈ 𝓝 t₀ := hγc.continuousAt.preimage_mem_nhds hU
  have hrow : ∀ t : ℝ, (M₀ + t • M₁) 2 ≠ 0 := fun t => by
    rw [← hγ t]
    exact realMat_apply_ne_zero (γ t) 2
  set F' : ℝ → (Fin 2 → Fin 2 → ℝ) → ℂ :=
    fun t e => jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly Y p)) (γ t) e with hF'_def
  have h_bound : ∀ᵐ e : Fin 2 → Fin 2 → ℝ, ∀ t ∈ γ ⁻¹' U, ‖F' t e‖ ≤ Fm e :=
    Eventually.of_forall fun e t ht => hbound (γ t) ht e
  have hF_int : Integrable (jacquetIntegrand3 D u₃ a₃ a ψ (pg p) (γ t₀)) volume :=
    hFm₀.mono' (hmeas (γ t₀)) (Eventually.of_forall fun e => hbound₀ (γ t₀) (mem_of_mem_nhds hU₀) e)
  have hF'_meas : AEStronglyMeasurable (F' t₀) volume := hmeas' (γ t₀)
  have hae : ∀ᵐ e : Fin 2 → Fin 2 → ℝ, (Matrix.of e).det ≠ 0 := by
    rw [ae_iff]
    simpa using hnull
  have h_diff : ∀ᵐ e : Fin 2 → Fin 2 → ℝ, ∀ t ∈ γ ⁻¹' U,
      HasDerivAt (fun t' : ℝ => jacquetIntegrand3 D u₃ a₃ a ψ (pg p) (γ t') e) (F' t e) t := by
    refine hae.mono fun e hdet t _ => ?_
    have hrow' : ∀ t' ∈ closedBall t 1, (M₀ + t' • M₁) 2 ≠ 0 := fun t' _ => hrow t'
    have hin := (hasDerivAt_inner ψ hχ hχ1 p hdet M₀ M₁ one_pos hrow').mul_const (wFactor D u₃ a₃ a e)
    have hfun : (fun t' : ℝ => jacquetIntegrand3 D u₃ a₃ a ψ (pg p) (γ t') e) =
        fun t' : ℝ => godementInner3 ψ (pg p) (Matrix.of e) (M₀ + t' • M₁) * wFactor D u₃ a₃ a e := by
      funext t'
      rw [jacquetIntegrand3_eq, hγ t']
    rw [hfun]
    refine hin.congr_deriv ?_
    simp only [hF'_def]
    rw [jacquetIntegrand3_eq, hγ t, inner_deriv_eq_affine ψ p (Matrix.of e) M₀ M₁ Y t (hY t)]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs (Eventually.of_forall fun t => hmeas (γ t)) hF_int
    hF'_meas h_bound hFm h_diff
  refine key.2.congr_deriv ?_
  simp only [hF'_def]

private theorem integral_jacquetIntegrand3_pg_sum_core {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ)
    (a₃ : ZMod 2) (a : ℝ) (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hχ : Continuous fun v : Fin 2 → ℝ => ψ (ofReal (-(v 1)))) (hχ1 : ∀ v : Fin 2 → ℝ, ‖ψ (ofReal (-(v 1)))‖ ≤ 1)
    (hnull : (volume : Measure (Fin 2 → Fin 2 → ℝ)) {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} = 0)
    (hmeas : ∀ (q : MvPolynomial (Fin 2 × Fin 3) ℂ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
      AEStronglyMeasurable (jacquetIntegrand3 D u₃ a₃ a ψ (pg q) g) volume)
    (hmaj : ∀ (q : MvPolynomial (Fin 2 × Fin 3) ℂ) (g₀ : GL (Fin 3) (InfiniteAdeleRing ℚ)),
      ∃ U ∈ nhds g₀, ∃ F : (Fin 2 → Fin 2 → ℝ) → ℝ, Integrable F volume ∧
        ∀ g ∈ U, ∀ e : Fin 2 → Fin 2 → ℝ, ‖jacquetIntegrand3 D u₃ a₃ a ψ (pg q) g e‖ ≤ F e)
    (c : Fin 9 → ℂ) (q : Fin 9 → MvPolynomial (Fin 2 × Fin 3) ℂ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg (∑ j, C (c j) * q j)) g e =
      ∑ j, c j * ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg (q j)) g e := by
  have hae : ∀ᵐ e : Fin 2 → Fin 2 → ℝ, (Matrix.of e).det ≠ 0 := by
    rw [ae_iff]
    simpa using hnull
  have hrow : realMat g 2 ≠ 0 := realMat_apply_ne_zero g 2
  have hpt : jacquetIntegrand3 D u₃ a₃ a ψ (pg (∑ j, C (c j) * q j)) g =ᵐ[volume]
      fun e : Fin 2 → Fin 2 → ℝ => ∑ j, c j * jacquetIntegrand3 D u₃ a₃ a ψ (pg (q j)) g e := by
    refine hae.mono fun e hdet => ?_
    have hlin : ∀ v : Fin 2 → ℝ,
        pg (∑ j, C (c j) * q j) (sliceMat (Matrix.of e) (realMat g) v) * ψ (ofReal (-(v 1))) =
          ∑ j, c j * (pg (q j) (sliceMat (Matrix.of e) (realMat g) v) * ψ (ofReal (-(v 1)))) := by
      intro v
      simp only [pg, map_sum, map_mul, eval_C, sum_mul, mul_assoc]
    show jacquetIntegrand3 D u₃ a₃ a ψ (pg (∑ j, C (c j) * q j)) g e =
      ∑ j, c j * jacquetIntegrand3 D u₃ a₃ a ψ (pg (q j)) g e
    simp only [jacquetIntegrand3_eq, godementInner3_pg_eq, hlin]
    rw [integral_finsetSum _ fun j _ => (integrable_pg_slice ψ hχ hχ1 (q j) hdet hrow).const_mul (c j), sum_mul]
    simp only [integral_const_mul, mul_assoc]
  rw [integral_congr_ae hpt]
  have hint : ∀ j : Fin 9, Integrable (jacquetIntegrand3 D u₃ a₃ a ψ (pg (q j)) g) volume := fun j => by
    obtain ⟨U, hU, F, hF, hb⟩ := hmaj (q j) g
    exact hF.mono' (hmeas (q j) g) (Eventually.of_forall fun e => hb g (mem_of_mem_nhds hU) e)
  rw [integral_finsetSum _ fun j _ => (hint j).const_mul (c j)]
  simp only [integral_const_mul]

end OuterAffine

end DualStripDecay

end SliceGrowthAndOuterDerivative

section Singular
open MeasureTheory Set

namespace SingularArrays

private theorem volume_setOf_line_eq_zero (r₀ r₁ : ℝ) (h : r₀ ≠ 0) :
    (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} = 0 := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} :=
    measurableSet_eq_fun (measurable_const.mul measurable_snd) (measurable_const.mul measurable_fst)
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hmeas]
  refine Filter.Eventually.of_forall fun u => ?_
  have hsub : Prod.mk u ⁻¹' {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} ⊆ {r₁ * u / r₀} := by
    intro v hv
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hv
    simp only [Set.mem_singleton_iff]
    field_simp
    linarith [hv]
  exact measure_mono_null hsub (Real.volume_singleton)

private theorem volume_setOf_vector_on_line_eq_zero (r₀ r₁ : ℝ) (h : r₀ ≠ 0) :
    (volume : Measure (Fin 2 → ℝ)) {q : Fin 2 → ℝ | r₀ * q 1 = r₁ * q 0} = 0 := by
  have hpre : {q : Fin 2 → ℝ | r₀ * q 1 = r₁ * q 0} =
      MeasurableEquiv.piFinTwo (fun _ => ℝ) ⁻¹' {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} := by
    ext q; rfl
  rw [hpre, ← (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).measurableEmbedding.map_apply,
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).map_eq]
  exact volume_setOf_line_eq_zero r₀ r₁ h

private theorem volume_setOf_det_eq_zero :
    (volume : Measure (Fin 2 → Fin 2 → ℝ)) {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} = 0 := by
  have hdet : ∀ x : Fin 2 → Fin 2 → ℝ, (Matrix.of x).det = x 0 0 * x 1 1 - x 0 1 * x 1 0 := fun x => by
    rw [Matrix.det_fin_two]; rfl
  set S : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ)) := {p | p.1 0 * p.2 1 - p.1 1 * p.2 0 = 0} with hS
  have hpre : {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} =
      MeasurableEquiv.piFinTwo (fun _ => Fin 2 → ℝ) ⁻¹' S := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hdet, hS]
    rfl
  rw [hpre, ← (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Fin 2 → ℝ)).measurableEmbedding.map_apply,
    (volume_preserving_piFinTwo (fun _ : Fin 2 => Fin 2 → ℝ)).map_eq]
  have hmeas : MeasurableSet S := by
    refine measurableSet_eq_fun ?_ measurable_const
    exact ((measurable_pi_apply 0).comp measurable_fst).mul ((measurable_pi_apply 1).comp measurable_snd) |>.sub
      (((measurable_pi_apply 1).comp measurable_fst).mul ((measurable_pi_apply 0).comp measurable_snd))
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hmeas]
  have hae : ∀ᵐ r : Fin 2 → ℝ ∂(volume : Measure (Fin 2 → ℝ)), r 0 ≠ 0 :=
    Measure.ae_eval_ne (fun _ : Fin 2 => (volume : Measure ℝ)) 0 (0 : ℝ)
  filter_upwards [hae] with r hr
  have hfib : Prod.mk r ⁻¹' S ⊆ {q : Fin 2 → ℝ | r 0 * q 1 = r 1 * q 0} := by
    intro q hq
    simp only [Set.mem_preimage, hS, Set.mem_setOf_eq] at hq
    simp only [Set.mem_setOf_eq]
    linarith [hq]
  exact measure_mono_null hfib (volume_setOf_vector_on_line_eq_zero (r 0) (r 1) hr)

end SingularArrays

end Singular

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam RealArchParam.discrete RealArchParam.principal"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gaussian3 polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq AdelicGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero archComponent3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂ archRootSum archPlaceComponent3 isGL3PsiWhittakerFn_jacquetVector3 jacquetVector3_scalar_mul apply_of_infPart_eq_of_isArchCompAt re_eq_zero_of_isArchCompAt_of_isUnitaryChar exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod upperUnipotent3_inv_eq"
namespace DirectStripDecay
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open Filter Topology NumberField AutomorphicForm AutomorphicForm.StandardKernel LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchR LanglandsTunnell.CubicInduction.PolyGaussLine

private theorem psiArch_eq_psi_realCoord (w : InfiniteAdeleRing ℚ) :
    NumberField.StandardAddChar.psiArch w = ArchR.psi (StandardKernel.realCoord w) := by
  have h1 : NumberField.StandardAddChar.psiArch w =
      NumberField.StandardAddChar.psiArchPlace Rat.infinitePlace (w Rat.infinitePlace) := by
    rw [NumberField.StandardAddChar.psiArch_apply]
    exact finprod_eq_single _ Rat.infinitePlace fun v hv => absurd (Subsingleton.elim v Rat.infinitePlace) hv
  rw [h1, NumberField.StandardAddChar.psiArchPlace_apply, ArchR.psi, StandardKernel.realCoord_apply]

private theorem realCoord_ratCast (a : ℚ) :
    StandardKernel.realCoord (algebraMap ℚ (InfiniteAdeleRing ℚ) a) = (a : ℝ) := by
  rw [← RingHom.comp_apply]
  exact eq_ratCast (StandardKernel.realCoord.comp (algebraMap ℚ (InfiniteAdeleRing ℚ))) a

private theorem realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private theorem psiInf_ofReal_neg (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x)) (t : ℝ) :
    psiInf (StandardKernel.ofReal (-t)) =
      Complex.exp (((-(2 * Real.pi * (a : ℝ) * t) : ℝ) : ℂ) * Complex.I) := by
  rw [hpsiInf, psiArch_eq_psi_realCoord, map_mul, realCoord_ratCast, realCoord_ofReal, ArchR.psi]
  congr 1
  push_cast
  ring

end LanglandsTunnell.CubicInduction.DirectStripDecay

section Heads
open MvPolynomial Finset MeasureTheory Filter Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam RealArchParam.discrete RealArchParam.principal"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gaussian3 polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq AdelicGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero archComponent3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂ archRootSum archPlaceComponent3 isGL3PsiWhittakerFn_jacquetVector3 jacquetVector3_scalar_mul apply_of_infPart_eq_of_isArchCompAt re_eq_zero_of_isArchCompAt_of_isUnitaryChar exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod upperUnipotent3_inv_eq"
namespace PolyGaussLine
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem inputs {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x)) :
    (∀ (q : MvPolynomial (Fin 2 × Fin 3) ℂ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
      AEStronglyMeasurable (jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf (pg q) g) volume) ∧
    (∀ (q : MvPolynomial (Fin 2 × Fin 3) ℂ) (g₀ : GL (Fin 3) (InfiniteAdeleRing ℚ)),
      ∃ U ∈ nhds g₀, ∃ F : (Fin 2 → Fin 2 → ℝ) → ℝ, Integrable F volume ∧
        ∀ g ∈ U, ∀ e : Fin 2 → Fin 2 → ℝ, ‖jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf (pg q) g e‖ ≤ F e) := by
  obtain ⟨c₀, hc₀⟩ := exists_forall_twist_neg_re_lt P
  have ha' : (a : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr ha
  refine ⟨fun q g => ?_, fun q g₀ => ?_⟩
  · exact (exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod u₃ a₃ a psiInf hpsiInf ha D
      (pg q) ⟨q, rfl⟩ c₀ hc₀).2.2.2 g
  · obtain ⟨h1, -, -, -⟩ :=
      exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod u₃ a₃ a psiInf hpsiInf ha D (pg q)
        ⟨q, rfl⟩ c₀ hc₀
    obtain ⟨U, hU, F, hF, hb⟩ := h1 g₀ (max c₀ (-u₃.re) + 1) (lt_add_one _)
    exact ⟨U, hU, fun e => |(a : ℝ)| ^ (1 - (max c₀ (-u₃.re) + 1)) * F e, hF.const_mul _,
      fun g hg e => hb g hg (a : ℝ) ha' e⟩

private theorem character_inputs (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x)) :
    (Continuous fun v : Fin 2 → ℝ => psiInf (StandardKernel.ofReal (-(v 1)))) ∧
      ∀ v : Fin 2 → ℝ, ‖psiInf (StandardKernel.ofReal (-(v 1)))‖ ≤ 1 := by
  refine ⟨?_, fun v => ?_⟩
  · simp only [DirectStripDecay.psiInf_ofReal_neg a psiInf hpsiInf]
    fun_prop
  · exact le_of_eq (by rw [DirectStripDecay.psiInf_ofReal_neg a psiInf hpsiInf, Complex.norm_exp_ofReal_mul_I])

private theorem hasDerivAt_integral_jacquetIntegrand3_affine {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ)
    (a₃ : ZMod 2) (a : ℚ) (ha : a ≠ 0) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (M₀ M₁ Y : Matrix (Fin 3) (Fin 3) ℝ)
    (hY : ∀ t : ℝ, (M₀ + t • M₁) * Y = M₁)
    (γ : ℝ → GL (Fin 3) (InfiniteAdeleRing ℚ))
    (hγ : ∀ t : ℝ, AutomorphicForm.StandardKernel.realMat (γ t) = M₀ + t • M₁) (hγc : Continuous γ)
    (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf (pg p) (γ t) e)
      (∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf (pg (derivedPoly Y p)) (γ t₀) e) t₀ := by
  obtain ⟨hmeas, hmaj⟩ := inputs D u₃ a₃ a ha psiInf hpsiInf
  obtain ⟨hχ, hχ1⟩ := character_inputs a psiInf hpsiInf
  exact DualStripDecay.hasDerivAt_integral_jacquetIntegrand3_affine_core D u₃ a₃ (a : ℝ) psiInf hχ hχ1
    SingularArrays.volume_setOf_det_eq_zero p M₀ M₁ Y hY γ hγ hγc (hmeas p) (hmeas _) (hmaj p) (hmaj _) t₀

private theorem integral_jacquetIntegrand3_pg_sum {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2)
    (a : ℚ) (ha : a ≠ 0) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (c : Fin 9 → ℂ) (q : Fin 9 → MvPolynomial (Fin 2 × Fin 3) ℂ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf (pg (∑ j, C (c j) * q j)) g e =
      ∑ j, c j * ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf (pg (q j)) g e := by
  obtain ⟨hmeas, hmaj⟩ := inputs D u₃ a₃ a ha psiInf hpsiInf
  obtain ⟨hχ, hχ1⟩ := character_inputs a psiInf hpsiInf
  exact DualStripDecay.integral_jacquetIntegrand3_pg_sum_core D u₃ a₃ (a : ℝ) psiInf hχ hχ1
    SingularArrays.volume_setOf_det_eq_zero hmeas hmaj c q g

end LanglandsTunnell.CubicInduction.PolyGaussLine

end Heads

end

noncomputable section

section RootAlgebra
open Matrix Finset

namespace RootDerivative

private theorem mul_single_mul_apply (X Z : Matrix (Fin 3) (Fin 3) ℝ) (i j m n : Fin 3) (c : ℝ) :
    (X * single i j c * Z) m n = X m i * c * Z j n := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem abs_entry_le_one_of_orth (k : Matrix (Fin 3) (Fin 3) ℝ) (hk : k * k.transpose = 1) (i m : Fin 3) :
    |k i m| ≤ 1 := by
  have h1 : (k * k.transpose) i i = 1 := by rw [hk, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h1
  simp only [Matrix.transpose_apply] at h1
  have hle : k i m * k i m ≤ 1 := by
    rw [← h1]
    exact Finset.single_le_sum (f := fun l => k i l * k i l) (fun l _ => mul_self_nonneg (k i l))
      (Finset.mem_univ m)
  exact abs_le_one_iff_mul_self_le_one.mpr hle

private def conjRoot (d : Fin 3 → ℝ) (k : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  k.transpose * single i j (d j / d i) * k

private theorem abs_conjRoot_apply_le (d : Fin 3 → ℝ) (k : Matrix (Fin 3) (Fin 3) ℝ) (hk : k * k.transpose = 1)
    (i j m n : Fin 3) : |conjRoot d k i j m n| ≤ |d j| / |d i| := by
  rw [conjRoot, mul_single_mul_apply, Matrix.transpose_apply, abs_mul, abs_mul, abs_div]
  have h1 := abs_entry_le_one_of_orth k hk i m
  have h2 := abs_entry_le_one_of_orth k hk j n
  have h3 : 0 ≤ |d j| / |d i| := div_nonneg (abs_nonneg _) (abs_nonneg _)
  calc |k i m| * (|d j| / |d i|) * |k j n| ≤ 1 * (|d j| / |d i|) * 1 :=
        mul_le_mul (mul_le_mul h1 le_rfl h3 zero_le_one) h2 (abs_nonneg _) (by positivity)
    _ = |d j| / |d i| := by ring

private theorem single_one_mul_diagonal (d : Fin 3 → ℝ) (i j : Fin 3) :
    single i j (1 : ℝ) * diagonal d = single i j (d j) := by
  ext m n
  rw [Matrix.mul_diagonal]
  by_cases h : i = m ∧ j = n
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [Matrix.single, h]

private theorem diagonal_mul_single (d : Fin 3 → ℝ) (i j : Fin 3) (c : ℝ) :
    diagonal d * single i j c = single i j (d i * c) := by
  ext m n
  rw [Matrix.diagonal_mul]
  by_cases h : i = m ∧ j = n
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [Matrix.single, h]

private theorem line_mul_conjRoot (d : Fin 3 → ℝ) (hd : ∀ l, d l ≠ 0) (k : Matrix (Fin 3) (Fin 3) ℝ)
    (hk : k * k.transpose = 1) (i j : Fin 3) (hij : i ≠ j) (t : ℝ) :
    (diagonal d * k + t • (single i j (1 : ℝ) * (diagonal d * k))) * conjRoot d k i j =
      single i j (1 : ℝ) * (diagonal d * k) := by
  have hE : single i j (1 : ℝ) * (diagonal d * k) = single i j (d j) * k := by
    rw [← Matrix.mul_assoc, single_one_mul_diagonal]
  have hcancel : d i * (d j / d i) = d j := by field_simp [hd i]
  have hkk : ∀ Z : Matrix (Fin 3) (Fin 3) ℝ, k * (k.transpose * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hk, Matrix.one_mul]
  have hbase : diagonal d * k * conjRoot d k i j = single i j (d j) * k := by
    rw [conjRoot, Matrix.mul_assoc (diagonal d), Matrix.mul_assoc k.transpose, hkk, ← Matrix.mul_assoc,
      diagonal_mul_single, hcancel]
  have h0 : single i j (d j) * single i j (d j / d i) = (0 : Matrix (Fin 3) (Fin 3) ℝ) := by
    simp [Ne.symm hij]
  have htan : single i j (d j) * k * conjRoot d k i j = 0 := by
    rw [conjRoot, Matrix.mul_assoc (single i j (d j)), Matrix.mul_assoc k.transpose, hkk, ← Matrix.mul_assoc, h0,
      Matrix.zero_mul]
  rw [hE, Matrix.add_mul, hbase, Matrix.smul_mul, htan, smul_zero, add_zero]

private theorem unip_first_eq (x : ℝ) : (!![1, x, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ) =
    1 + x • single 0 1 (1 : ℝ) := by
  ext m n
  fin_cases m <;> fin_cases n <;> simp [Matrix.single]

private theorem unip_second_eq (y : ℝ) : (!![1, 0, 0; 0, 1, y; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ) =
    1 + y • single 1 2 (1 : ℝ) := by
  ext m n
  fin_cases m <;> fin_cases n <;> simp [Matrix.single]

private theorem one_add_smul_mul (E H : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) : (1 + t • E) * H = H + t • (E * H) := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]

private theorem ne_zero_of_det_diagonal_mul (d : Fin 3 → ℝ) (k : Matrix (Fin 3) (Fin 3) ℝ)
    (h : (diagonal d * k).det ≠ 0) (l : Fin 3) : d l ≠ 0 := by
  intro hl
  apply h
  rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_eq_zero (Finset.mem_univ l) hl, zero_mul]

end RootDerivative

end RootAlgebra

section RootPolynomials
open Matrix MvPolynomial Finset

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam RealArchParam.discrete RealArchParam.principal"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gaussian3 polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq AdelicGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero archComponent3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂ archRootSum archPlaceComponent3 isGL3PsiWhittakerFn_jacquetVector3 jacquetVector3_scalar_mul apply_of_infPart_eq_of_isArchCompAt re_eq_zero_of_isArchCompAt_of_isUnitaryChar exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod upperUnipotent3_inv_eq"
namespace PolyGaussLine
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem entryMulPoly_single (i j : Fin 3) (v : Fin 2 × Fin 3) :
    entryMulPoly (single i j (1 : ℝ)) v = if j = v.2 then X (v.1, i) else 0 := by
  unfold entryMulPoly
  by_cases hj : j = v.2
  · subst hj
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Matrix.single, Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [if_neg hj]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hne : ¬(i = b ∧ j = v.2) := fun h => hj h.2
    simp [Matrix.single, hne]

private theorem entryMulPoly_eq_sum (Y : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 × Fin 3) :
    entryMulPoly Y v = ∑ i : Fin 3, ∑ j : Fin 3, C ((Y i j : ℝ) : ℂ) * entryMulPoly (single i j 1) v := by
  simp only [entryMulPoly_single]
  unfold entryMulPoly
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single v.2]
  · simp [mul_comm]
  · intro b _ hb
    rw [if_neg hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ v.2) h

private theorem derivedPoly_eq_sum (Y : Matrix (Fin 3) (Fin 3) ℝ) (p : MvPolynomial (Fin 2 × Fin 3) ℂ) :
    derivedPoly Y p = ∑ i : Fin 3, ∑ j : Fin 3, C ((Y i j : ℝ) : ℂ) * derivedPoly (single i j 1) p := by
  unfold derivedPoly
  rw [Finset.sum_congr rfl fun w _ => by rw [entryMulPoly_eq_sum Y w]]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

private def idx : Fin 9 ≃ Fin 3 × Fin 3 := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin (3 * 3)).symm

private def elementary (n : Fin 9) : Matrix (Fin 3) (Fin 3) ℝ :=
  single (idx n).1 (idx n).2 (1 : ℝ)

private def coeffAt (Y : Matrix (Fin 3) (Fin 3) ℝ) (n : Fin 9) : ℝ :=
  Y (idx n).1 (idx n).2

private theorem derivedPoly_eq_sum_fin9 (Y : Matrix (Fin 3) (Fin 3) ℝ) (p : MvPolynomial (Fin 2 × Fin 3) ℂ) :
    derivedPoly Y p = ∑ n : Fin 9, C ((coeffAt Y n : ℝ) : ℂ) * derivedPoly (elementary n) p := by
  rw [derivedPoly_eq_sum, ← Fintype.sum_prod_type']
  simp only [coeffAt, elementary]
  exact (idx.sum_comp fun y : Fin 3 × Fin 3 => C ((Y y.1 y.2 : ℝ) : ℂ) * derivedPoly (single y.1 y.2 1) p).symm

end LanglandsTunnell.CubicInduction.PolyGaussLine

end RootPolynomials

section RootEstimateVector

open MeasureTheory MvPolynomial Finset
open AutomorphicForm.StandardKernel
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_norm_archComponent3_le.LanglandsTunnell.CubicInduction"
open LanglandsTunnell.CubicInduction.PolyGaussLine
open RootDerivative

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam RealArchParam.discrete RealArchParam.principal"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gaussian3 polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq AdelicGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero archComponent3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂ archRootSum archPlaceComponent3 isGL3PsiWhittakerFn_jacquetVector3 jacquetVector3_scalar_mul apply_of_infPart_eq_of_isArchCompAt re_eq_zero_of_isArchCompAt_of_isUnitaryChar exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod upperUnipotent3_inv_eq"
namespace RootSizeBound
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem realCoord_ofReal'' (r : ℝ) : realCoord (ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private theorem realCoord_injective' : Function.Injective realCoord := fun x y h => by
  rw [← ofReal_realCoord x, h, ofReal_realCoord]

private theorem ofReal_zero' : ofReal (0 : ℝ) = 0 :=
  realCoord_injective' (by rw [realCoord_ofReal'', map_zero])

private theorem psiArch_eq_exp (t : InfiniteAdeleRing ℚ) :
    NumberField.StandardAddChar.psiArch t = Complex.exp (2 * Real.pi * Complex.I * (realCoord t : ℂ)) := by
  have key : ∀ w : InfinitePlace ℚ, NumberField.StandardAddChar.psiArchPlace w (t w) =
      Complex.exp (2 * Real.pi * Complex.I * (realCoord t : ℂ)) := by
    intro w
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    rw [NumberField.StandardAddChar.psiArchPlace_apply, realCoord_apply]
  rw [NumberField.StandardAddChar.psiArch_apply, finprod_unique]
  exact key default

private theorem realCoord_algebraMap (q : ℚ) : realCoord (algebraMap ℚ (InfiniteAdeleRing ℚ) q) = (q : ℝ) := by
  have h := eq_ratCast (realCoord.comp (algebraMap ℚ (InfiniteAdeleRing ℚ))) q
  rwa [RingHom.comp_apply] at h

private theorem psiInf_ofReal_add (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (x y : ℝ) :
    psiInf (ofReal x + ofReal y) = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * ((x + y : ℝ) : ℂ)) := by
  rw [hpsiInf, psiArch_eq_exp, map_mul, map_add, realCoord_ofReal'', realCoord_ofReal'', realCoord_algebraMap]
  push_cast
  ring_nf

private theorem hasDerivAt_exp_char (a : ℚ) :
    HasDerivAt (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (t : ℂ)))
      (2 * Real.pi * Complex.I * (a : ℂ)) 0 := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * z))
      (Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * ((0 : ℝ) : ℂ)) * (2 * Real.pi * Complex.I * (a : ℂ)))
      ((0 : ℝ) : ℂ) := by
    have h1 : HasDerivAt (fun z : ℂ => 2 * Real.pi * Complex.I * (a : ℂ) * z) (2 * Real.pi * Complex.I * (a : ℂ))
        ((0 : ℝ) : ℂ) := by
      simpa using (hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul (2 * Real.pi * Complex.I * (a : ℂ))
    exact (Complex.hasDerivAt_exp _).comp _ h1
  have h2 := h.comp_ofReal
  simpa using h2

private theorem norm_two_pi_I_mul (a : ℚ) : ‖(2 * Real.pi * Complex.I * (a : ℂ) : ℂ)‖ = 2 * Real.pi * |(a : ℝ)| := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
  simp [abs_of_pos Real.pi_pos]

private def rootCurve₁ (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (t : ℝ) : GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  upperUnipotent3 (ofReal t) (ofReal 0) (ofReal 0) * g

private def rootCurve₂ (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (t : ℝ) : GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  upperUnipotent3 (ofReal 0) (ofReal t) (ofReal 0) * g

private theorem realMat_upperUnipotent3_ofReal' (x y z : ℝ) :
    realMat (upperUnipotent3 (ofReal x) (ofReal y) (ofReal z)) = !![1, x, z; 0, 1, y; 0, 0, 1] := by
  rw [realMat_eq, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realCoord_ofReal'']

private theorem realMat_rootCurve₁ (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (t : ℝ) :
    realMat (rootCurve₁ g t) = realMat g + t • (Matrix.single 0 1 (1 : ℝ) * realMat g) := by
  rw [rootCurve₁, realMat_mul, realMat_upperUnipotent3_ofReal', unip_first_eq, one_add_smul_mul]

private theorem realMat_rootCurve₂ (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (t : ℝ) :
    realMat (rootCurve₂ g t) = realMat g + t • (Matrix.single 1 2 (1 : ℝ) * realMat g) := by
  rw [rootCurve₂, realMat_mul, realMat_upperUnipotent3_ofReal', unip_second_eq, one_add_smul_mul]

private theorem rootCurve₁_zero (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : rootCurve₁ g 0 = g := by
  rw [rootCurve₁, ofReal_zero', upperUnipotent3_zero, one_mul]

private theorem rootCurve₂_zero (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : rootCurve₂ g 0 = g := by
  rw [rootCurve₂, ofReal_zero', upperUnipotent3_zero, one_mul]

private theorem continuous_upperUnipotent3_ofReal {x y z : ℝ → ℝ} (hx : Continuous x) (hy : Continuous y)
    (hz : Continuous z) :
    Continuous fun t : ℝ => upperUnipotent3 (ofReal (x t)) (ofReal (y t)) (ofReal (z t)) := by
  have hc : ∀ {u : ℝ → ℝ}, Continuous u → Continuous fun t => ofReal (u t) := fun hu =>
    continuous_ofReal.comp hu
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_def, upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp <;>
      first
      | exact hc hx
      | exact hc hy
      | exact hc hz
      | exact continuous_const
  · simp only [upperUnipotent3_inv_eq, upperUnipotent3_coe]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;>
      first
      | exact (hc hx).neg
      | exact (hc hy).neg
      | exact ((hc hx).mul (hc hy)).sub (hc hz)
      | exact continuous_const

private theorem continuous_rootCurve₁ (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Continuous (rootCurve₁ g) :=
  (continuous_upperUnipotent3_ofReal continuous_id continuous_const continuous_const).mul continuous_const

private theorem continuous_rootCurve₂ (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Continuous (rootCurve₂ g) :=
  (continuous_upperUnipotent3_ofReal continuous_const continuous_id continuous_const).mul continuous_const

private theorem jacquetVector3_rootCurve₁ {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (t : ℝ) :
    jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S (rootCurve₁ g t) =
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (t : ℂ)) * jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S g := by
  rw [rootCurve₁, isGL3PsiWhittakerFn_jacquetVector3 P D u₃ a₃ a psiInf hpsiInf S, psiInf_ofReal_add a psiInf hpsiInf,
    add_zero]

private theorem jacquetVector3_rootCurve₂ {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (t : ℝ) :
    jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S (rootCurve₂ g t) =
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (t : ℂ)) * jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S g := by
  rw [rootCurve₂, isGL3PsiWhittakerFn_jacquetVector3 P D u₃ a₃ a psiInf hpsiInf S, psiInf_ofReal_add a psiInf hpsiInf,
    zero_add]

private theorem det_rootCurve₁ (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (t : ℝ) :
    (realMat (rootCurve₁ g t)).det = (realMat g).det := by
  rw [rootCurve₁, realMat_mul, realMat_upperUnipotent3_ofReal', Matrix.det_mul, Matrix.det_fin_three]
  simp

private theorem det_rootCurve₂ (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (t : ℝ) :
    (realMat (rootCurve₂ g t)).det = (realMat g).det := by
  rw [rootCurve₂, realMat_mul, realMat_upperUnipotent3_ofReal', Matrix.det_mul, Matrix.det_fin_three]
  simp

private theorem det_realMat_ne_zero (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : (realMat g).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (realGL g).isUnit).ne_zero

private theorem rearrange {A x y z w : ℝ} (hA : 0 < A) (hy : 0 < y) (hz : 0 < z) (h : A * x ≤ y / z * w) :
    z / y * x ≤ A⁻¹ * w := by
  have hzA : 0 ≤ z / (y * A) := by positivity
  have h2 := mul_le_mul_of_nonneg_left h hzA
  have e1 : z / (y * A) * (A * x) = z / y * x := by field_simp
  have e2 : z / (y * A) * (y / z * w) = A⁻¹ * w := by field_simp
  rwa [e1, e2] at h2

private theorem core {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (E Y : Matrix (Fin 3) (Fin 3) ℝ)
    (hY : ∀ t : ℝ, (realMat g + t • (E * realMat g)) * Y = E * realMat g)
    (γ : ℝ → GL (Fin 3) (InfiniteAdeleRing ℚ)) (hγ : ∀ t, realMat (γ t) = realMat g + t • (E * realMat g))
    (hγc : Continuous γ) (hγ0 : γ 0 = g) (hdet : ∀ t, (realMat (γ t)).det = (realMat g).det)
    (hW : ∀ t : ℝ, jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg p) (γ t) =
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (t : ℂ)) * jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg p) g) :
    2 * Real.pi * |(a : ℝ)| * ‖jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg p) g‖ ≤
      ∑ n : Fin 9, |coeffAt Y n| * ‖jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg (derivedPoly (elementary n) p)) g‖ := by

  have hder := hasDerivAt_integral_jacquetIntegrand3_affine D u₃ a₃ a ha psiInf hpsiInf p (realMat g) (E * realMat g)
    Y hY γ hγ hγc 0
  rw [hγ0] at hder

  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ArchR.quasiChar (u₃ + 1) a₃ (realMat g).det := ⟨_, rfl⟩
  have hvec : ∀ (q : MvPolynomial (Fin 2 × Fin 3) ℂ) (t : ℝ), jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg q) (γ t) =
      c * ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf (pg q) (γ t) e := fun q t => by
    rw [jacquetVector3_eq, hdet, hc]
  have hvec0 : ∀ q : MvPolynomial (Fin 2 × Fin 3) ℂ, jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg q) g =
      c * ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf (pg q) g e := fun q => by
    rw [jacquetVector3_eq, hc]

  have h1 : HasDerivAt (fun t : ℝ => jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg p) (γ t))
      (c * ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf (pg (derivedPoly Y p)) g e) 0 := by
    have := hder.const_mul c
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    exact hvec p t
  have h2 : HasDerivAt (fun t : ℝ => jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg p) (γ t))
      (2 * Real.pi * Complex.I * (a : ℂ) * jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg p) g) 0 := by
    have := (hasDerivAt_exp_char a).mul_const (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg p) g)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    exact hW t
  have hident := h1.unique h2

  have hsplit : c * ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf (pg (derivedPoly Y p)) g e =
      ∑ n : Fin 9, ((coeffAt Y n : ℝ) : ℂ) *
        jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg (derivedPoly (elementary n) p)) g := by
    rw [derivedPoly_eq_sum_fin9, integral_jacquetIntegrand3_pg_sum D u₃ a₃ a ha psiInf hpsiInf, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hvec0]
    ring
  rw [hsplit] at hident

  have hnorm : ‖2 * Real.pi * Complex.I * (a : ℂ) * jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg p) g‖ =
      2 * Real.pi * |(a : ℝ)| * ‖jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg p) g‖ := by
    rw [norm_mul, norm_two_pi_I_mul]
  rw [← hnorm, ← hident]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

private theorem root_bound {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (d : Fin 3 → ℝ) (k : Matrix (Fin 3) (Fin 3) ℝ) (hk : k * k.transpose = 1)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (hg : realMat g = Matrix.diagonal d * k) (i j : Fin 3) (hij : i ≠ j)
    (γ : ℝ → GL (Fin 3) (InfiniteAdeleRing ℚ))
    (hγ : ∀ t, realMat (γ t) = realMat g + t • (Matrix.single i j (1 : ℝ) * realMat g)) (hγc : Continuous γ)
    (hγ0 : γ 0 = g) (hdet : ∀ t, (realMat (γ t)).det = (realMat g).det)
    (hW : ∀ t : ℝ, jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg p) (γ t) =
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (t : ℂ)) * jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg p) g) :
    |d i| / |d j| * ‖jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg p) g‖ ≤
      (2 * Real.pi * |(a : ℝ)|)⁻¹ *
        ∑ n : Fin 9, ‖jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg (derivedPoly (elementary n) p)) g‖ := by
  have hd : ∀ l, d l ≠ 0 := ne_zero_of_det_diagonal_mul d k (hg ▸ det_realMat_ne_zero g)
  have hY : ∀ t : ℝ, (realMat g + t • (Matrix.single i j (1 : ℝ) * realMat g)) * conjRoot d k i j =
      Matrix.single i j (1 : ℝ) * realMat g := fun t => by
    rw [hg]
    exact line_mul_conjRoot d hd k hk i j hij t
  have hcore := core D u₃ a₃ a ha psiInf hpsiInf p g (Matrix.single i j 1) (conjRoot d k i j) hY γ hγ hγc hγ0 hdet hW
  have hcoeff : ∀ n : Fin 9, |coeffAt (conjRoot d k i j) n| ≤ |d j| / |d i| := fun n =>
    abs_conjRoot_apply_le d k hk i j _ _
  have hsum : ∑ n : Fin 9, |coeffAt (conjRoot d k i j) n| *
        ‖jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg (derivedPoly (elementary n) p)) g‖ ≤
      |d j| / |d i| *
        ∑ n : Fin 9, ‖jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg (derivedPoly (elementary n) p)) g‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right (hcoeff n) (norm_nonneg _)
  have hapos : 0 < |(a : ℝ)| := abs_pos.mpr (by exact_mod_cast ha)
  exact rearrange (by positivity) (abs_pos.mpr (hd j)) (abs_pos.mpr (hd i)) (hcore.trans hsum)

private theorem exists_family_archRoot₁_mul_norm_jacquetVector3_le
    {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) :
    ∃ T : Fin 9 → Matrix (Fin 2) (Fin 3) ℝ → ℂ, (∀ j, T j ∈ polyGauss3) ∧
      ∀ (d : Fin 3 → ℝ) (k : Matrix (Fin 3) (Fin 3) ℝ), k * k.transpose = 1 →
        ∀ g : GL (Fin 3) (InfiniteAdeleRing ℚ), StandardKernel.realMat g = Matrix.diagonal d * k →
          |d 0| / |d 1| * ‖jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S g‖ ≤
            (2 * Real.pi * |(a : ℝ)|)⁻¹ * ∑ j, ‖jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (T j) g‖ := by
  obtain ⟨p, rfl⟩ := hS
  refine ⟨fun n => pg (derivedPoly (elementary n) p), fun n => ⟨derivedPoly (elementary n) p, rfl⟩, ?_⟩
  intro d k hk g hg
  exact root_bound D u₃ a₃ a ha psiInf hpsiInf p d k hk g hg 0 1 (by decide) (rootCurve₁ g) (realMat_rootCurve₁ g)
    (continuous_rootCurve₁ g) (rootCurve₁_zero g) (det_rootCurve₁ g)
    (jacquetVector3_rootCurve₁ D u₃ a₃ a psiInf hpsiInf (pg p) g)

private theorem exists_family_archRoot₂_mul_norm_jacquetVector3_le
    {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) :
    ∃ T : Fin 9 → Matrix (Fin 2) (Fin 3) ℝ → ℂ, (∀ j, T j ∈ polyGauss3) ∧
      ∀ (d : Fin 3 → ℝ) (k : Matrix (Fin 3) (Fin 3) ℝ), k * k.transpose = 1 →
        ∀ g : GL (Fin 3) (InfiniteAdeleRing ℚ), StandardKernel.realMat g = Matrix.diagonal d * k →
          |d 1| / |d 2| * ‖jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S g‖ ≤
            (2 * Real.pi * |(a : ℝ)|)⁻¹ * ∑ j, ‖jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (T j) g‖ := by
  obtain ⟨p, rfl⟩ := hS
  refine ⟨fun n => pg (derivedPoly (elementary n) p), fun n => ⟨derivedPoly (elementary n) p, rfl⟩, ?_⟩
  intro d k hk g hg
  exact root_bound D u₃ a₃ a ha psiInf hpsiInf p d k hk g hg 1 2 (by decide) (rootCurve₂ g) (realMat_rootCurve₂ g)
    (continuous_rootCurve₂ g) (rootCurve₂_zero g) (det_rootCurve₂ g)
    (jacquetVector3_rootCurve₂ D u₃ a₃ a psiInf hpsiInf (pg p) g)

end LanglandsTunnell.CubicInduction.RootSizeBound

end RootEstimateVector

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam RealArchParam.discrete RealArchParam.principal"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gaussian3 polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq AdelicGL upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero archComponent3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂ archRootSum archPlaceComponent3 isGL3PsiWhittakerFn_jacquetVector3 jacquetVector3_scalar_mul apply_of_infPart_eq_of_isArchCompAt re_eq_zero_of_isArchCompAt_of_isUnitaryChar exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod upperUnipotent3_inv_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section
open Finset

namespace RootSizeAssembly

private theorem weight_le {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    1 + (r₁ * r₂)⁻¹ + r₂⁻¹ ≤ (1 + (r₁ + r₂)) ^ 2 / (r₁ * r₂) := by
  have hp : 0 < r₁ * r₂ := mul_pos h₁ h₂
  rw [le_div_iff₀ hp]
  have e : (1 + (r₁ * r₂)⁻¹ + r₂⁻¹) * (r₁ * r₂) = r₁ * r₂ + 1 + r₁ := by
    field_simp
  rw [e]
  nlinarith [h₁.le, h₂.le, mul_nonneg h₁.le h₂.le, sq_nonneg r₁, sq_nonneg r₂]

private theorem weight_pow_mul_le {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) (n : ℕ) :
    (1 + (r₁ * r₂)⁻¹ + r₂⁻¹) ^ n * (r₁ * r₂) ^ n ≤ (1 + (r₁ + r₂)) ^ (2 * n) := by
  have hp : 0 < r₁ * r₂ := mul_pos h₁ h₂
  have hw : 0 ≤ 1 + (r₁ * r₂)⁻¹ + r₂⁻¹ := by positivity
  calc (1 + (r₁ * r₂)⁻¹ + r₂⁻¹) ^ n * (r₁ * r₂) ^ n
      ≤ ((1 + (r₁ + r₂)) ^ 2 / (r₁ * r₂)) ^ n * (r₁ * r₂) ^ n := by
        gcongr
        exact weight_le h₁ h₂
    _ = (1 + (r₁ + r₂)) ^ (2 * n) := by
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n hp.ne'), ← pow_mul]

private theorem region {r₁ r₂ φ c : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) (n N t₁ t₂ : ℕ)
    (H : r₁ ^ t₁ * r₂ ^ t₂ * φ ≤ c * (r₁ * r₂ ^ 2) * (1 + (r₁ * r₂)⁻¹ + r₂⁻¹) ^ n)
    (hreg : (1 + (r₁ + r₂)) ^ (N + 2 * n) * (r₁ * r₂ ^ 2) ≤ 3 ^ (N + 2 * n) * (r₁ ^ t₁ * r₂ ^ t₂)) :
    φ * ((r₁ * r₂) ^ n * (1 + (r₁ + r₂)) ^ N) ≤ max c 0 * 3 ^ (N + 2 * n) := by
  have hp : 0 < r₁ * r₂ := mul_pos h₁ h₂
  have hT : 0 < r₁ ^ t₁ * r₂ ^ t₂ := by positivity
  have hw : 0 ≤ (r₁ * r₂ ^ 2) * (1 + (r₁ * r₂)⁻¹ + r₂⁻¹) ^ n := by positivity
  have H' : r₁ ^ t₁ * r₂ ^ t₂ * φ ≤ max c 0 * ((r₁ * r₂ ^ 2) * (1 + (r₁ * r₂)⁻¹ + r₂⁻¹) ^ n) := by
    calc r₁ ^ t₁ * r₂ ^ t₂ * φ ≤ c * (r₁ * r₂ ^ 2) * (1 + (r₁ * r₂)⁻¹ + r₂⁻¹) ^ n := H
      _ = c * ((r₁ * r₂ ^ 2) * (1 + (r₁ * r₂)⁻¹ + r₂⁻¹) ^ n) := by ring
      _ ≤ max c 0 * ((r₁ * r₂ ^ 2) * (1 + (r₁ * r₂)⁻¹ + r₂⁻¹) ^ n) :=
        mul_le_mul_of_nonneg_right (le_max_left c 0) hw

  have hfac : 0 < (r₁ * r₂) ^ n * (1 + (r₁ + r₂)) ^ N / (r₁ ^ t₁ * r₂ ^ t₂) := by positivity
  have key := mul_le_mul_of_nonneg_right H' hfac.le
  have lhs : r₁ ^ t₁ * r₂ ^ t₂ * φ * ((r₁ * r₂) ^ n * (1 + (r₁ + r₂)) ^ N / (r₁ ^ t₁ * r₂ ^ t₂)) =
      φ * ((r₁ * r₂) ^ n * (1 + (r₁ + r₂)) ^ N) := by
    field_simp
  rw [lhs] at key
  refine key.trans ?_

  have hc : 0 ≤ max c 0 := le_max_right c 0
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [mul_div_assoc', div_le_iff₀ hT]
  calc (r₁ * r₂ ^ 2) * (1 + (r₁ * r₂)⁻¹ + r₂⁻¹) ^ n * ((r₁ * r₂) ^ n * (1 + (r₁ + r₂)) ^ N)
      = (r₁ * r₂ ^ 2) * (1 + (r₁ + r₂)) ^ N * ((1 + (r₁ * r₂)⁻¹ + r₂⁻¹) ^ n * (r₁ * r₂) ^ n) := by ring
    _ ≤ (r₁ * r₂ ^ 2) * (1 + (r₁ + r₂)) ^ N * (1 + (r₁ + r₂)) ^ (2 * n) := by
        gcongr
        exact weight_pow_mul_le h₁ h₂ n
    _ = (1 + (r₁ + r₂)) ^ (N + 2 * n) * (r₁ * r₂ ^ 2) := by ring
    _ ≤ 3 ^ (N + 2 * n) * (r₁ ^ t₁ * r₂ ^ t₂) := hreg

private theorem hreg_big_big {r₁ r₂ : ℝ} (h₁ : 1 ≤ r₁) (h₂ : 1 ≤ r₂) (m : ℕ) :
    (1 + (r₁ + r₂)) ^ m * (r₁ * r₂ ^ 2) ≤ 3 ^ m * (r₁ ^ (m + 1) * r₂ ^ (m + 2)) := by
  have h3 : 1 + (r₁ + r₂) ≤ 3 * (r₁ * r₂) := by nlinarith
  have h0 : 0 ≤ 1 + (r₁ + r₂) := by linarith
  calc (1 + (r₁ + r₂)) ^ m * (r₁ * r₂ ^ 2) ≤ (3 * (r₁ * r₂)) ^ m * (r₁ * r₂ ^ 2) := by
        gcongr
    _ = 3 ^ m * (r₁ ^ (m + 1) * r₂ ^ (m + 2)) := by ring

private theorem hreg_big_small {r₁ r₂ : ℝ} (h₁ : 1 ≤ r₁) (h₂₀ : 0 < r₂) (h₂ : r₂ ≤ 1) (m : ℕ) :
    (1 + (r₁ + r₂)) ^ m * (r₁ * r₂ ^ 2) ≤ 3 ^ m * (r₁ ^ (m + 1) * r₂ ^ 0) := by
  have h3 : 1 + (r₁ + r₂) ≤ 3 * r₁ := by nlinarith
  have h0 : 0 ≤ 1 + (r₁ + r₂) := by linarith
  have hr2 : r₂ ^ 2 ≤ 1 := pow_le_one₀ h₂₀.le h₂
  calc (1 + (r₁ + r₂)) ^ m * (r₁ * r₂ ^ 2) ≤ (3 * r₁) ^ m * (r₁ * 1) := by
        gcongr
    _ = 3 ^ m * (r₁ ^ (m + 1) * r₂ ^ 0) := by ring

private theorem hreg_small_big {r₁ r₂ : ℝ} (h₁₀ : 0 < r₁) (h₁ : r₁ ≤ 1) (h₂ : 1 ≤ r₂) (m : ℕ) :
    (1 + (r₁ + r₂)) ^ m * (r₁ * r₂ ^ 2) ≤ 3 ^ m * (r₁ ^ 0 * r₂ ^ (m + 2)) := by
  have h3 : 1 + (r₁ + r₂) ≤ 3 * r₂ := by nlinarith
  have h0 : 0 ≤ 1 + (r₁ + r₂) := by linarith
  calc (1 + (r₁ + r₂)) ^ m * (r₁ * r₂ ^ 2) ≤ (3 * r₂) ^ m * (1 * r₂ ^ 2) := by
        gcongr
    _ = 3 ^ m * (r₁ ^ 0 * r₂ ^ (m + 2)) := by ring

private theorem hreg_small_small {r₁ r₂ : ℝ} (h₁₀ : 0 < r₁) (h₁ : r₁ ≤ 1) (h₂₀ : 0 < r₂) (h₂ : r₂ ≤ 1) (m : ℕ) :
    (1 + (r₁ + r₂)) ^ m * (r₁ * r₂ ^ 2) ≤ 3 ^ m * (r₁ ^ 0 * r₂ ^ 0) := by
  have h3 : 1 + (r₁ + r₂) ≤ 3 := by linarith
  have h0 : 0 ≤ 1 + (r₁ + r₂) := by linarith
  have hr2 : r₂ ^ 2 ≤ 1 := pow_le_one₀ h₂₀.le h₂
  calc (1 + (r₁ + r₂)) ^ m * (r₁ * r₂ ^ 2) ≤ 3 ^ m * (1 * 1) := by
        gcongr
    _ = 3 ^ m * (r₁ ^ 0 * r₂ ^ 0) := by ring

private theorem assembly_bound (X : Type) (n : ℕ) (φ r₁ r₂ : X → ℝ) (hr₁ : ∀ x, 0 < r₁ x) (hr₂ : ∀ x, 0 < r₂ x)
    (H : ∀ t₁ t₂ : ℕ, ∃ c : ℝ, ∀ x,
      r₁ x ^ t₁ * r₂ x ^ t₂ * φ x ≤ c * (r₁ x * r₂ x ^ 2) * (1 + (r₁ x * r₂ x)⁻¹ + (r₂ x)⁻¹) ^ n) :
    ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ x, φ x ≤ C / ((r₁ x * r₂ x) ^ t * (1 + (r₁ x + r₂ x)) ^ N) := by
  refine ⟨n, fun N => ?_⟩
  set m : ℕ := N + 2 * n with hm
  obtain ⟨c₁₁, h₁₁⟩ := H (m + 1) (m + 2)
  obtain ⟨c₁₀, h₁₀⟩ := H (m + 1) 0
  obtain ⟨c₀₁, h₀₁⟩ := H 0 (m + 2)
  obtain ⟨c₀₀, h₀₀⟩ := H 0 0
  refine ⟨max (max (max c₁₁ 0) (max c₁₀ 0)) (max (max c₀₁ 0) (max c₀₀ 0)) * 3 ^ m, fun x => ?_⟩
  have hd : 0 < (r₁ x * r₂ x) ^ n * (1 + (r₁ x + r₂ x)) ^ N := by
    have := hr₁ x; have := hr₂ x; positivity
  rw [le_div_iff₀ hd]
  have h3 : (0 : ℝ) ≤ 3 ^ m := by positivity

  have bound : ∀ c' : ℝ, φ x * ((r₁ x * r₂ x) ^ n * (1 + (r₁ x + r₂ x)) ^ N) ≤ max c' 0 * 3 ^ m →
      c' = c₁₁ ∨ c' = c₁₀ ∨ c' = c₀₁ ∨ c' = c₀₀ →
      φ x * ((r₁ x * r₂ x) ^ n * (1 + (r₁ x + r₂ x)) ^ N) ≤
        max (max (max c₁₁ 0) (max c₁₀ 0)) (max (max c₀₁ 0) (max c₀₀ 0)) * 3 ^ m := by
    intro c' hc' hmem
    refine hc'.trans (mul_le_mul_of_nonneg_right ?_ h3)
    rcases hmem with rfl | rfl | rfl | rfl
    · exact le_sup_of_le_left (le_sup_left)
    · exact le_sup_of_le_left (le_sup_right)
    · exact le_sup_of_le_right (le_sup_left)
    · exact le_sup_of_le_right (le_sup_right)
  rcases le_total 1 (r₁ x) with hb₁ | hs₁ <;> rcases le_total 1 (r₂ x) with hb₂ | hs₂
  · exact bound c₁₁ (region (hr₁ x) (hr₂ x) n N (m + 1) (m + 2) (h₁₁ x) (hreg_big_big hb₁ hb₂ m))
      (Or.inl rfl)
  · exact bound c₁₀ (region (hr₁ x) (hr₂ x) n N (m + 1) 0 (h₁₀ x) (hreg_big_small hb₁ (hr₂ x) hs₂ m))
      (Or.inr (Or.inl rfl))
  · exact bound c₀₁ (region (hr₁ x) (hr₂ x) n N 0 (m + 2) (h₀₁ x) (hreg_small_big (hr₁ x) hs₁ hb₂ m))
      (Or.inr (Or.inr (Or.inl rfl)))
  · exact bound c₀₀ (region (hr₁ x) (hr₂ x) n N 0 0 (h₀₀ x) (hreg_small_small (hr₁ x) hs₁ (hr₂ x) hs₂ m))
      (Or.inr (Or.inr (Or.inr rfl)))

end RootSizeAssembly

namespace RootSizeIterate

variable {σ X : Type} (P : Set σ) (v : σ → X → ℝ)

private theorem apply_once {ρ : X → ℝ} {κ : ℝ} (hρ : ∀ x, 0 ≤ ρ x)
    (step : ∀ S ∈ P, ∃ T : Fin 9 → σ, (∀ j, T j ∈ P) ∧ ∀ x, ρ x * v S x ≤ κ * ∑ j, v (T j) x)
    {S : σ} {w : X → ℝ} {c : ℝ} (hc : 0 ≤ c) {m : ℕ} {T : Fin m → σ} (hT : ∀ j, T j ∈ P)
    (hb : ∀ x, w x * v S x ≤ c * ∑ j, v (T j) x) :
    ∃ T' : Fin (m * 9) → σ, (∀ j, T' j ∈ P) ∧ ∀ x, (w x * ρ x) * v S x ≤ (c * κ) * ∑ j, v (T' j) x := by
  choose fam hfamP hfam using step
  refine ⟨fun j => fam (T (finProdFinEquiv.symm j).1) (hT _) (finProdFinEquiv.symm j).2, fun j => hfamP _ _ _,
    fun x => ?_⟩

  have hsum : ∑ j : Fin (m * 9), v (fam (T (finProdFinEquiv.symm j).1) (hT _) (finProdFinEquiv.symm j).2) x =
      ∑ p : Fin m × Fin 9, v (fam (T p.1) (hT p.1) p.2) x := by
    rw [← finProdFinEquiv.sum_comp]
    simp
  rw [hsum, Fintype.sum_prod_type]

  have h1 : (w x * ρ x) * v S x ≤ ρ x * (c * ∑ j, v (T j) x) := by
    calc (w x * ρ x) * v S x = ρ x * (w x * v S x) := by ring
      _ ≤ ρ x * (c * ∑ j, v (T j) x) := mul_le_mul_of_nonneg_left (hb x) (hρ x)
  refine h1.trans ?_
  calc ρ x * (c * ∑ j, v (T j) x) = c * ∑ j, ρ x * v (T j) x := by
        simp only [mul_sum]
        exact sum_congr rfl fun j _ => by ring
    _ ≤ c * ∑ j, κ * ∑ i, v (fam (T j) (hT j) i) x := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => hfam (T j) (hT j) x) hc
    _ = (c * κ) * ∑ j, ∑ i, v (fam (T j) (hT j) i) x := by
        simp only [mul_sum]
        exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring

private theorem iterate {ρ₁ ρ₂ : X → ℝ} {κ : ℝ} (hρ₁ : ∀ x, 0 ≤ ρ₁ x) (hρ₂ : ∀ x, 0 ≤ ρ₂ x) (hκ : 0 ≤ κ)
    (step₁ : ∀ S ∈ P, ∃ T : Fin 9 → σ, (∀ j, T j ∈ P) ∧ ∀ x, ρ₁ x * v S x ≤ κ * ∑ j, v (T j) x)
    (step₂ : ∀ S ∈ P, ∃ T : Fin 9 → σ, (∀ j, T j ∈ P) ∧ ∀ x, ρ₂ x * v S x ≤ κ * ∑ j, v (T j) x)
    {S : σ} (hS : S ∈ P) (t₁ t₂ : ℕ) :
    ∃ (m : ℕ) (T : Fin m → σ), (∀ j, T j ∈ P) ∧
      ∀ x, (ρ₁ x ^ t₁ * ρ₂ x ^ t₂) * v S x ≤ κ ^ (t₁ + t₂) * ∑ j, v (T j) x := by

  have base : ∃ (m : ℕ) (T : Fin m → σ), (∀ j, T j ∈ P) ∧
      ∀ x, (ρ₁ x ^ t₁) * v S x ≤ κ ^ t₁ * ∑ j, v (T j) x := by
    induction t₁ with
    | zero =>
      refine ⟨1, fun _ => S, fun _ => hS, fun x => ?_⟩
      simp
    | succ t ih =>
      obtain ⟨m, T, hT, hb⟩ := ih
      obtain ⟨T', hT', hb'⟩ := apply_once P v hρ₁ step₁ (w := fun x => ρ₁ x ^ t) (pow_nonneg hκ t) hT hb
      refine ⟨m * 9, T', hT', fun x => ?_⟩
      have := hb' x
      simpa only [pow_succ] using this
  obtain ⟨m₀, T₀, hT₀, hb₀⟩ := base
  have top : ∀ u : ℕ, ∃ (m : ℕ) (T : Fin m → σ), (∀ j, T j ∈ P) ∧
      ∀ x, (ρ₁ x ^ t₁ * ρ₂ x ^ u) * v S x ≤ (κ ^ t₁ * κ ^ u) * ∑ j, v (T j) x := by
    intro u
    induction u with
    | zero =>
      refine ⟨m₀, T₀, hT₀, fun x => ?_⟩
      simpa using hb₀ x
    | succ u ih =>
      obtain ⟨m, T, hT, hb⟩ := ih
      obtain ⟨T', hT', hb'⟩ := apply_once P v hρ₂ step₂ (w := fun x => ρ₁ x ^ t₁ * ρ₂ x ^ u)
        (mul_nonneg (pow_nonneg hκ t₁) (pow_nonneg hκ u)) hT hb
      refine ⟨m * 9, T', hT', fun x => ?_⟩
      have := hb' x
      simp only [pow_succ] at this ⊢
      calc ρ₁ x ^ t₁ * (ρ₂ x ^ u * ρ₂ x) * v S x = ρ₁ x ^ t₁ * ρ₂ x ^ u * ρ₂ x * v S x := by ring
        _ ≤ κ ^ t₁ * κ ^ u * κ * ∑ j, v (T' j) x := this
        _ = κ ^ t₁ * (κ ^ u * κ) * ∑ j, v (T' j) x := by ring
  obtain ⟨m, T, hT, hb⟩ := top t₂
  exact ⟨m, T, hT, fun x => by rw [pow_add]; exact hb x⟩

end RootSizeIterate

end

end LanglandsTunnell.CubicInduction

section

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_norm_archComponent3_le.LanglandsTunnell.CubicInduction"

private theorem realCoord_ofReal' (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private theorem realCoord_injective : Function.Injective StandardKernel.realCoord := fun x y h => by
  rw [← StandardKernel.ofReal_realCoord x, h, StandardKernel.ofReal_realCoord]

private theorem exists_units_realCoord_eq (r : ℝ) (hr : r ≠ 0) :
    ∃ z : (InfiniteAdeleRing ℚ)ˣ, StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) = r := by
  refine ⟨⟨StandardKernel.ofReal r, StandardKernel.ofReal r⁻¹, ?_, ?_⟩, realCoord_ofReal' r⟩ <;>
  · apply realCoord_injective
    simp [realCoord_ofReal', hr]

private theorem realMat_upperUnipotent3_ofReal (x y z : ℝ) :
    StandardKernel.realMat
        (upperUnipotent3 (StandardKernel.ofReal x) (StandardKernel.ofReal y) (StandardKernel.ofReal z)) =
      !![1, x, z; 0, 1, y; 0, 0, 1] := by
  rw [StandardKernel.realMat_eq, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realCoord_ofReal']

private theorem det_unip (x y z : ℝ) : IsUnit (!![1, x, z; 0, 1, y; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ).det := by
  rw [Matrix.det_fin_three]
  simp

private theorem realMat_scalar (z : (InfiniteAdeleRing ℚ)ˣ) :
    StandardKernel.realMat (Matrix.GeneralLinearGroup.scalar (Fin 3) z) =
      Matrix.diagonal fun _ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) := by
  rw [StandardKernel.realMat_eq]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply]
  · simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]

end

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_norm_archComponent3_le.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_norm_archComponent3_le.LanglandsTunnell.CubicInduction in
open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal →
      IsArchCompAt ℚ ω v
        ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
        ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (ha : a ≠ 0)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) :
    ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖(jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N) := by
  have _ := hdeg
  have _ := haInf
  have _ := mA
  have _ := mT
  have _ := hν_add
  classical

  set u₃ : ℂ := uR w₀ h₀ with hu₃
  have hre : u₃.re = 0 := re_eq_zero_of_isArchCompAt_of_isUnitaryChar K μ hμ.2.2 w₀ _ _ (huR w₀ h₀)
  obtain ⟨c₀, hc₀⟩ := LanglandsTunnell.CubicInduction.exists_forall_twist_neg_re_lt P₂
  obtain ⟨n, hbrick⟩ := RootSizeBound.exists_nat_forall_exists_forall_norm_jacquetVector3_diagonal_mul_le D u₃
    (aR w₀ h₀) a ha psiInf hpsiInf c₀ hc₀

  let X : Type := {p : ℝ × ℝ × GL (Fin 3) (InfiniteAdeleRing ℚ) // ∃ k : Matrix (Fin 3) (Fin 3) ℝ,
    p.1 ≠ 0 ∧ p.2.1 ≠ 0 ∧ k * k.transpose = 1 ∧ StandardKernel.realMat p.2.2 = Matrix.diagonal ![p.1, p.2.1, 1] * k}
  let φ : (Matrix (Fin 2) (Fin 3) ℝ → ℂ) → X → ℝ := fun S' x =>
    ‖jacquetVector3 D u₃ (aR w₀ h₀) (a : ℝ) psiInf S' x.1.2.2‖
  let r₁ : X → ℝ := fun x => |x.1.1| / |x.1.2.1|
  let r₂ : X → ℝ := fun x => |x.1.2.1|
  have hr₁ : ∀ x, 0 < r₁ x := fun x => by
    obtain ⟨k, h0, h1, -, -⟩ := x.2
    exact div_pos (abs_pos.mpr h0) (abs_pos.mpr h1)
  have hr₂ : ∀ x, 0 < r₂ x := fun x => by
    obtain ⟨k, -, h1, -, -⟩ := x.2
    exact abs_pos.mpr h1
  set κ : ℝ := (2 * Real.pi * |(a : ℝ)|)⁻¹ with hκdef
  have hκ : 0 ≤ κ := by positivity

  have step₁ : ∀ S' ∈ polyGauss3, ∃ T : Fin 9 → Matrix (Fin 2) (Fin 3) ℝ → ℂ, (∀ j, T j ∈ polyGauss3) ∧
      ∀ x, r₁ x * φ S' x ≤ κ * ∑ j, φ (T j) x := by
    intro S' hS'
    obtain ⟨T, hT, hstep⟩ := RootSizeBound.exists_family_archRoot₁_mul_norm_jacquetVector3_le D u₃ (aR w₀ h₀) a ha
      psiInf hpsiInf S' hS'
    refine ⟨T, hT, fun x => ?_⟩
    obtain ⟨k, -, -, hk, hx⟩ := x.2
    have := hstep ![x.1.1, x.1.2.1, 1] k hk x.1.2.2 hx
    rw [hκdef]
    simpa [r₁, φ] using this
  have step₂ : ∀ S' ∈ polyGauss3, ∃ T : Fin 9 → Matrix (Fin 2) (Fin 3) ℝ → ℂ, (∀ j, T j ∈ polyGauss3) ∧
      ∀ x, r₂ x * φ S' x ≤ κ * ∑ j, φ (T j) x := by
    intro S' hS'
    obtain ⟨T, hT, hstep⟩ := RootSizeBound.exists_family_archRoot₂_mul_norm_jacquetVector3_le D u₃ (aR w₀ h₀) a ha
      psiInf hpsiInf S' hS'
    refine ⟨T, hT, fun x => ?_⟩
    obtain ⟨k, -, -, hk, hx⟩ := x.2
    have := hstep ![x.1.1, x.1.2.1, 1] k hk x.1.2.2 hx
    rw [hκdef]
    simpa [r₂, φ] using this

  have H : ∀ t₁ t₂ : ℕ, ∃ c : ℝ, ∀ x, r₁ x ^ t₁ * r₂ x ^ t₂ * φ S x ≤
      c * (r₁ x * r₂ x ^ 2) * (1 + (r₁ x * r₂ x)⁻¹ + (r₂ x)⁻¹) ^ n := by
    intro t₁ t₂
    obtain ⟨m, T, hT, hiter⟩ := RootSizeIterate.iterate polyGauss3 φ (fun x => (hr₁ x).le) (fun x => (hr₂ x).le) hκ
      step₁ step₂ hS t₁ t₂
    choose Cf hCf using fun j => hbrick (T j) (hT j)
    refine ⟨κ ^ (t₁ + t₂) * ∑ j, Cf j, fun x => ?_⟩
    obtain ⟨k, h0, h1, hk, hx⟩ := x.2

    have e₁ : |x.1.1| = r₁ x * r₂ x := by
      simp only [r₁, r₂]
      rw [div_mul_cancel₀ _ (abs_ne_zero.mpr h1)]
    have e₀ : |x.1.1 * x.1.2.1| = r₁ x * r₂ x ^ 2 := by
      rw [abs_mul, e₁]
      simp only [r₂]
      ring
    have hmem : ∀ j, φ (T j) x ≤ Cf j * (r₁ x * r₂ x ^ 2) * (1 + (r₁ x * r₂ x)⁻¹ + (r₂ x)⁻¹) ^ n := fun j => by
      have := hCf j x.1.1 x.1.2.1 h0 h1 k hk x.1.2.2 hx
      rw [hre, zero_add, Real.rpow_one, e₀, e₁] at this
      simpa [φ, r₂] using this
    have hw : 0 ≤ (r₁ x * r₂ x ^ 2) * (1 + (r₁ x * r₂ x)⁻¹ + (r₂ x)⁻¹) ^ n := by
      have := hr₁ x; have := hr₂ x; positivity
    calc r₁ x ^ t₁ * r₂ x ^ t₂ * φ S x ≤ κ ^ (t₁ + t₂) * ∑ j, φ (T j) x := hiter x
      _ ≤ κ ^ (t₁ + t₂) * ∑ j, Cf j * (r₁ x * r₂ x ^ 2) * (1 + (r₁ x * r₂ x)⁻¹ + (r₂ x)⁻¹) ^ n :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hmem j) (pow_nonneg hκ _)
      _ = κ ^ (t₁ + t₂) * ∑ j, Cf j * ((r₁ x * r₂ x ^ 2) * (1 + (r₁ x * r₂ x)⁻¹ + (r₂ x)⁻¹) ^ n) := by
          simp only [mul_assoc]
      _ = (κ ^ (t₁ + t₂) * ∑ j, Cf j) * (r₁ x * r₂ x ^ 2) * (1 + (r₁ x * r₂ x)⁻¹ + (r₂ x)⁻¹) ^ n := by
          rw [← Finset.sum_mul]
          ring
  obtain ⟨t, ht⟩ := RootSizeAssembly.assembly_bound X n (φ S) r₁ r₂ hr₁ hr₂ H
  refine ⟨t, fun N => ?_⟩
  obtain ⟨C, hC⟩ := ht N
  refine ⟨C, fun g => ?_⟩

  set gInf : GL (Fin 3) (InfiniteAdeleRing ℚ) := archComponent3 (𝓞 ℚ) ℚ g with hgInf
  have hdet : (StandardKernel.realMat gInf).det ≠ 0 := by
    have : IsUnit (StandardKernel.realMat gInf).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (StandardKernel.realGL gInf).isUnit
    exact this.ne_zero
  obtain ⟨x, y, z, d, k, hd, hk, hm⟩ := RootSizeBound.exists_eq_unip_mul_diagonal_mul_orth _ hdet

  have hroots := RootSizeBound.archRoot_eq Rat.infinitePlace g x y z d hd k hk hm

  set uu : GL (Fin 3) (InfiniteAdeleRing ℚ) :=
    upperUnipotent3 (StandardKernel.ofReal x) (StandardKernel.ofReal y) (StandardKernel.ofReal z) with huu
  set g₁ : GL (Fin 3) (InfiniteAdeleRing ℚ) := uu⁻¹ * gInf with hg₁
  have hg₁mat : StandardKernel.realMat g₁ = Matrix.diagonal d * k := by
    rw [hg₁, StandardKernel.realMat_mul, StandardKernel.realMat_inv, huu, realMat_upperUnipotent3_ofReal, hm,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (det_unip x y z)]
  have hn₁ : ‖jacquetVector3 D u₃ (aR w₀ h₀) (a : ℝ) psiInf S gInf‖ =
      ‖jacquetVector3 D u₃ (aR w₀ h₀) (a : ℝ) psiInf S g₁‖ := by
    have h := RootSizeBound.norm_jacquetVector3_upperUnipotent3_mul D u₃ (aR w₀ h₀) a psiInf hpsiInf S
      (StandardKernel.ofReal x) (StandardKernel.ofReal y) (StandardKernel.ofReal z) g₁
    rwa [← huu, hg₁, mul_inv_cancel_left] at h

  obtain ⟨zc, hzc⟩ := exists_units_realCoord_eq (d 2)⁻¹ (inv_ne_zero (hd 2))
  set h₂ : GL (Fin 3) (InfiniteAdeleRing ℚ) := Matrix.GeneralLinearGroup.scalar (Fin 3) zc * g₁ with hh₂
  have hh₂mat : StandardKernel.realMat h₂ = Matrix.diagonal ![d 0 / d 2, d 1 / d 2, 1] * k := by
    rw [hh₂, StandardKernel.realMat_mul, realMat_scalar, hzc, hg₁mat, ← Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal]
    congr 2
    ext i
    fin_cases i <;> simp [div_eq_inv_mul, inv_mul_cancel₀ (hd 2)]
  have hn₂ : ‖jacquetVector3 D u₃ (aR w₀ h₀) (a : ℝ) psiInf S g₁‖ =
      ‖jacquetVector3 D u₃ (aR w₀ h₀) (a : ℝ) psiInf S h₂‖ := by
    rw [hh₂, jacquetVector3_scalar_mul K uR aR uC kC ω hω E hE a psiInf w₀ h₀ P₂ hP₂ D S zc g₁, norm_mul,
      RootSizeBound.norm_apply_E_eq_one ω _ (RootSizeBound.re_archExponent_eq_zero K μ hμ uR aR uC kC huR huC) _ hω E
        hE zc, one_mul]
  let xpt : X := ⟨(d 0 / d 2, d 1 / d 2, h₂), k, div_ne_zero (hd 0) (hd 2), div_ne_zero (hd 1) (hd 2), hk, hh₂mat⟩
  have hx := hC xpt

  have hR₁ : archRoot₁ ℚ Rat.infinitePlace g = r₁ xpt := by
    rw [hroots.1]
    simp only [r₁, xpt, abs_div]
    rw [div_div_div_cancel_right₀ (abs_ne_zero.mpr (hd 2))]
  have hR₂ : archRoot₂ ℚ Rat.infinitePlace g = r₂ xpt := by
    rw [hroots.2]
    simp only [r₂, xpt, abs_div]
  have hnorm : ‖jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S (archComponent3 (𝓞 ℚ) ℚ g)‖ = φ S xpt := by
    show ‖jacquetVector3 D u₃ (aR w₀ h₀) (a : ℝ) psiInf S gInf‖ = _
    rw [hn₁, hn₂]
  rw [hnorm, Fintype.prod_subsingleton _ Rat.infinitePlace, archRootSum, Fintype.sum_subsingleton _ Rat.infinitePlace,
    hR₁, hR₂]
  exact hx

end S_LanglandsTunnell_CubicInduction_jacquetVector3_norm_archComponent3_le
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_norm_archComponent3_le (solution)
