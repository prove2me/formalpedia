-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_norm_apply_diagZ_mul_le_of_stabilised_jacquetIntegral_of_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ebd66192-4219-581c-a420-37268a2ff9ad

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_norm_apply_diagZ_mul_le_of_stabilised_jacquetIntegral_of_norm_eq_one

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction AutomorphicForm Filter Topology Matrix

open scoped NNReal ENNReal Pointwise Topology

noncomputable section

namespace LTJacquetGrowth

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

def qR : ℝ := ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)

theorem one_lt_qR : (1 : ℝ) < qR p := by
  unfold qR
  exact_mod_cast HeightOneSpectrum.one_lt_absNorm p

theorem qR_pos : (0 : ℝ) < qR p := lt_trans one_pos (one_lt_qR p)

private theorem toAdd_unzero_exp (n : ℤ) (h : (WithZero.exp n : WithZero (Multiplicative ℤ)) ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero h) = n :=
  rfl

theorem norm_eq_zpow_of_valued {y : F} {k : ℤ} (h : Valued.v y = WithZero.exp k) : ‖y‖ = qR p ^ k := by
  rw [NumberField.FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    toAdd_unzero_exp]
  unfold qR
  push_cast
  rfl

def ball (k : ℤ) : Set F := {y | Valued.v y ≤ WithZero.exp k}

theorem mem_ball {k : ℤ} {y : F} : y ∈ ball p k ↔ Valued.v y ≤ WithZero.exp k := Iff.rfl

variable {p} in
theorem valued_zpow (ϖ : Fˣ) (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (((ϖ ^ k : Fˣ) : F)) = WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  ring

theorem ball_eq_setOf_le_valued {k : ℤ} {t : F} (hvt : Valued.v t = WithZero.exp k) :
    ball p k = {y : F | Valued.v y ≤ Valued.v t} := by
  rw [hvt]; rfl

theorem isClosed_ball' {k : ℤ} {t : F} (ht : t ≠ 0) (hvt : Valued.v t = WithZero.exp k) : IsClosed (ball p k) := by
  rw [ball_eq_setOf_le_valued p hvt]
  exact AdelicLevel.isClosed_setOf_valued_le p t ht

theorem isOpen_ball' {k : ℤ} {t : F} (ht : t ≠ 0) (hvt : Valued.v t = WithZero.exp k) : IsOpen (ball p k) := by
  rw [ball_eq_setOf_le_valued p hvt]
  exact AdelicLevel.isOpen_setOf_valued_le p t ht

theorem ball_eq_smul {k : ℤ} (t : Fˣ) (hvt : Valued.v (t : F) = WithZero.exp k) :
    ball p k = t • ((HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F)) := by
  ext y
  rw [mem_ball, Set.mem_smul_set]
  simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro hy
    refine ⟨(t⁻¹ : Fˣ) • y, ?_, by simp⟩
    rw [Units.smul_def, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvt]
    calc (WithZero.exp k)⁻¹ * Valued.v y ≤ (WithZero.exp k)⁻¹ * WithZero.exp k := mul_le_mul_right hy _
      _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
  · rintro ⟨z, hz, rfl⟩
    rw [Units.smul_def, smul_eq_mul, map_mul, hvt]
    calc WithZero.exp k * Valued.v z ≤ WithZero.exp k * 1 := mul_le_mul_right hz _
      _ = WithZero.exp k := mul_one _

theorem isCompact_ball {k : ℤ} (t : Fˣ) (hvt : Valued.v (t : F) = WithZero.exp k) : IsCompact (ball p k) := by
  rw [ball_eq_smul p t hvt, ← coe_integersPositiveCompacts ℚ p]
  exact (integersPositiveCompacts ℚ p).isCompact.smul _

theorem measurableSet_ball {k : ℤ} (t : Fˣ) (hvt : Valued.v (t : F) = WithZero.exp k) :
    MeasurableSet (ball p k) :=
  (isOpen_ball' p t.ne_zero hvt).measurableSet

theorem ball_mono {k l : ℤ} (h : k ≤ l) : ball p k ⊆ ball p l :=
  fun _ hy => hy.trans (WithZero.exp_le_exp.mpr h)

theorem one_le_qR_zpow {m : ℤ} (hm : 0 ≤ m) : (1 : ℝ) ≤ qR p ^ m :=
  one_le_zpow₀ (one_lt_qR p).le hm

def lowerUnip (y : F) : G where
  val := !![1, 0; y, 1]
  inv := !![1, 0; -y, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem lowerUnip_coe (y : F) : ((lowerUnip p y : G) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; y, 1] := rfl

theorem lowerUnip_zero : lowerUnip p 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem continuous_lowerUnip : Continuous (lowerUnip p) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [lowerUnip] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [lowerUnip] <;> fun_prop

theorem continuous_upperUnipotent2 : Continuous (upperUnipotent2 p) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent2] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent2] <;> fun_prop

theorem diagonal2_coe' (a : Fin 2 → Fˣ) :
    ((diagonal2 p a : G) : Matrix (Fin 2) (Fin 2) F) = !![(a 0 : F), 0; 0, (a 1 : F)] := by
  rw [diagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem unipotentGL2_eq (y : F) : (unipotentGL2 y : G) = upperUnipotent2 p y := by
  apply Units.ext
  rw [unipotentGL2_coe, upperUnipotent2_coe]

theorem eq_antidiagonal2 (w₀ : G) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) : w₀ = antidiagonal2 p := by
  apply Units.ext
  rw [hw₀, antidiagonal2_coe]

theorem coe_upper_diag (x : F) (a : Fin 2 → Fˣ) :
    ((upperUnipotent2 p x * diagonal2 p a : G) : Matrix (Fin 2) (Fin 2) F)
      = !![(a 0 : F), x * (a 1 : F); 0, (a 1 : F)] := by
  rw [Units.val_mul, upperUnipotent2_coe, diagonal2_coe', Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_weyl_upper (y : F) :
    ((antidiagonal2 p * upperUnipotent2 p y : G) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, y] := by
  rw [Units.val_mul, upperUnipotent2_coe, antidiagonal2_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem weyl_upper_eq (y : F) (hy : y ≠ 0) :
    antidiagonal2 p * upperUnipotent2 p y
      = upperUnipotent2 p y⁻¹ * diagonal2 p ![Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy)),
          Units.mk0 y hy] * lowerUnip p y⁻¹ := by
  apply Units.ext
  rw [coe_weyl_upper, Units.val_mul, coe_upper_diag, lowerUnip_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

theorem weyl_upper_diag (y : F) (t₁ t₂ : Fˣ) :
    antidiagonal2 p * upperUnipotent2 p y * diagonal2 p ![t₁, t₂] =
      diagonal2 p ![t₂, t₁] * (antidiagonal2 p * upperUnipotent2 p (((t₂ * t₁⁻¹ : Fˣ) : F) * y)) := by
  apply Units.ext
  simp only [Units.val_mul, upperUnipotent2_coe, antidiagonal2_coe, diagonal2_coe', Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem lowerUnip_mul_diag (t : F) (a : Fˣ) :
    lowerUnip p t * diagonal2 p ![a, 1] = diagonal2 p ![a, 1] * lowerUnip p ((a : F) * t) := by
  apply Units.ext
  simp only [Units.val_mul, lowerUnip_coe, diagonal2_coe']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem diagZ_eq_diagonal2 (π : F) (hπ : π ≠ 0) (m : ℤ) :
    (diagZ π hπ m : G) = diagonal2 p ![Units.mk0 π hπ ^ m, 1] := by
  apply Units.ext
  rw [diagonal2_coe']
  show !![π ^ m, 0; 0, 1] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_zpow_eq_zpow_val]

theorem antidiagonal2_mul_self : antidiagonal2 p * antidiagonal2 p = 1 := by
  apply Units.ext
  rw [Units.val_mul, antidiagonal2_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem antidiagonal2_inv : (antidiagonal2 p)⁻¹ = antidiagonal2 p :=
  inv_eq_of_mul_eq_one_right (antidiagonal2_mul_self p)

variable (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ))

theorem law {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (x : F) (a : Fin 2 → Fˣ) (g : G) :
    f (upperUnipotent2 p x * (diagonal2 p a * g)) = torusChar2 p χ a * halfModulus2 p a * f g := by
  obtain ⟨-, hn, ht⟩ := mem_principalSeries2_iff.mp hf
  rw [hn, ht]

theorem halfModulus2_boundary (y : F) (hy : y ≠ 0) :
    halfModulus2 p ![Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy)), Units.mk0 y hy] = ((‖y‖⁻¹ : ℝ) : ℂ) := by
  unfold halfModulus2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_mk0, norm_neg, norm_inv]
  congr 1
  rw [div_eq_mul_inv, Real.sqrt_mul_self (inv_nonneg.mpr (norm_nonneg _))]

theorem apply_weyl_upper {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (y : F) (hy : y ≠ 0) (g : G) :
    f (antidiagonal2 p * upperUnipotent2 p y * g) =
      ((χ 0 (Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy))) : ℂˣ) : ℂ) * ((χ 1 (Units.mk0 y hy) : ℂˣ) : ℂ) *
        ((‖y‖⁻¹ : ℝ) : ℂ) * f (lowerUnip p y⁻¹ * g) := by
  rw [weyl_upper_eq p y hy]
  simp only [mul_assoc]
  rw [law p χ hf, halfModulus2_boundary p y hy]
  simp only [torusChar2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem norm_torusChar2 (hθu : ∀ (i : Fin 2) (z : Fˣ), ‖((χ i z : ℂˣ) : ℂ)‖ = 1) (a : Fin 2 → Fˣ) :
    ‖torusChar2 p χ a‖ = 1 := by
  simp [torusChar2, Fin.prod_univ_two, hθu]

theorem halfModulus2_left (a : Fˣ) : halfModulus2 p ![a, 1] = ((Real.sqrt ‖(a : F)‖ : ℝ) : ℂ) := by
  simp [halfModulus2]

theorem halfModulus2_right (a : Fˣ) : halfModulus2 p ![1, a] = ((Real.sqrt (‖(a : F)‖⁻¹) : ℝ) : ℂ) := by
  simp [halfModulus2]

theorem norm_apply_diag_left {f : G → ℂ} (hf : f ∈ principalSeries2 p χ)
    (hθu : ∀ (i : Fin 2) (z : Fˣ), ‖((χ i z : ℂˣ) : ℂ)‖ = 1) (a : Fˣ) (g : G) :
    ‖f (diagonal2 p ![a, 1] * g)‖ = Real.sqrt ‖(a : F)‖ * ‖f g‖ := by
  obtain ⟨-, -, ht⟩ := mem_principalSeries2_iff.mp hf
  rw [ht, norm_mul, norm_mul, norm_torusChar2 p χ hθu, one_mul, halfModulus2_left, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

theorem norm_apply_diag_right {f : G → ℂ} (hf : f ∈ principalSeries2 p χ)
    (hθu : ∀ (i : Fin 2) (z : Fˣ), ‖((χ i z : ℂˣ) : ℂ)‖ = 1) (a : Fˣ) (g : G) :
    ‖f (diagonal2 p ![1, a] * g)‖ = Real.sqrt (‖(a : F)‖⁻¹) * ‖f g‖ := by
  obtain ⟨-, -, ht⟩ := mem_principalSeries2_iff.mp hf
  rw [ht, norm_mul, norm_mul, norm_torusChar2 p χ hθu, one_mul, halfModulus2_right, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

def K : Subgroup G := AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤

theorem isCompact_K : IsCompact (K p : Set G) :=
  (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ (by simp)).1

theorem isLocalLevelOne_top {M : Matrix (Fin 2) (Fin 2) F} (h : ∀ i j, Valued.v (M i j) ≤ 1) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ M where
  integral i j := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h i j)
  lowerLeft := by rw [AdelicLevel.idealBound_top]; exact h 1 0
  lowerRight := by
    rw [AdelicLevel.idealBound_top]
    exact (Valuation.map_sub _ _ _).trans (max_le (h 1 1) (by simp))

theorem mem_K_of_valued_le {g : G} (h : ∀ i j, Valued.v ((g : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1)
    (h' : ∀ i j, Valued.v (((g⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1) : g ∈ K p :=
  (AdelicDock.mem_localLevelOne_iff (R := 𝓞 ℚ) (K := ℚ) (v := p) g).mpr
    ⟨isLocalLevelOne_top p h, isLocalLevelOne_top p h'⟩

theorem antidiagonal2_mem_K : antidiagonal2 p ∈ K p := by
  refine mem_K_of_valued_le p (fun i j => ?_) (fun i j => ?_)
  · rw [antidiagonal2_coe]
    fin_cases i <;> fin_cases j <;> simp
  · rw [antidiagonal2_inv, antidiagonal2_coe]
    fin_cases i <;> fin_cases j <;> simp

theorem upperUnipotent2_mem_K {y : F} (hy : Valued.v y ≤ 1) : upperUnipotent2 p y ∈ K p := by
  refine mem_K_of_valued_le p (fun i j => ?_) (fun i j => ?_)
  · rw [upperUnipotent2_coe]
    fin_cases i <;> fin_cases j <;> simp [hy]
  · rw [show (((upperUnipotent2 p y)⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) = !![1, -y; 0, 1] from rfl]
    fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, hy]

theorem lowerUnip_mem_K {t : F} (ht : Valued.v t ≤ 1) : lowerUnip p t ∈ K p := by
  refine mem_K_of_valued_le p (fun i j => ?_) (fun i j => ?_)
  · rw [lowerUnip_coe]
    fin_cases i <;> fin_cases j <;> simp [ht]
  · rw [show (((lowerUnip p t)⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; -t, 1] from rfl]
    fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, ht]

theorem exists_bound_on_K {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ k ∈ K p, ‖f k‖ ≤ S := by
  obtain ⟨hlc, -, -⟩ := mem_principalSeries2_iff.mp hf
  obtain ⟨C, hC⟩ := (isCompact_K p).exists_bound_of_continuousOn hlc.continuous.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun k hk => (hC k hk).trans (le_max_left _ _)⟩

theorem inv_norm_le_one_of_one_lt_valued {y : F} (hy : 1 < Valued.v y) : ‖y‖⁻¹ ≤ 1 := by
  have hy0 : Valued.v y ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' hy)
  set L : ℤ := WithZero.log (Valued.v y) with hL
  have hlog : Valued.v y = WithZero.exp L := (WithZero.exp_log hy0).symm
  have hL0 : 0 ≤ L := by
    have : WithZero.exp 0 < WithZero.exp L := by rwa [← hlog, WithZero.exp_zero]
    exact (WithZero.exp_lt_exp.mp this).le
  rw [norm_eq_zpow_of_valued p hlog]
  exact inv_le_one_of_one_le₀ (one_le_zpow₀ (one_lt_qR p).le hL0)

theorem norm_apply_weyl_upper_le {f : G → ℂ} (hf : f ∈ principalSeries2 p χ)
    (hθu : ∀ (i : Fin 2) (z : Fˣ), ‖((χ i z : ℂˣ) : ℂ)‖ = 1)
    {S : ℝ} (hS : ∀ k ∈ K p, ‖f k‖ ≤ S) (y : F) {k : G} (hk : k ∈ K p) :
    ‖f (antidiagonal2 p * upperUnipotent2 p y * k)‖ ≤ S := by
  by_cases hy : Valued.v y ≤ 1
  · exact hS _ ((K p).mul_mem ((K p).mul_mem (antidiagonal2_mem_K p) (upperUnipotent2_mem_K p hy)) hk)
  · rw [not_le] at hy
    have hy0 : y ≠ 0 := by
      intro h; rw [h, map_zero] at hy; exact not_lt_zero hy
    have hyi : Valued.v y⁻¹ ≤ 1 := by
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ hy.le
    rw [apply_weyl_upper p χ hf y hy0 k, norm_mul, norm_mul, norm_mul, hθu, hθu, one_mul, one_mul,
      Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    calc ‖y‖⁻¹ * ‖f (lowerUnip p y⁻¹ * k)‖ ≤ 1 * S :=
          mul_le_mul (inv_norm_le_one_of_one_lt_valued p hy) (hS _ ((K p).mul_mem (lowerUnip_mem_K p hyi) hk))
            (norm_nonneg _) zero_le_one
      _ = S := one_mul S

theorem exists_uniform_radius (U : Subgroup G) (hU : IsOpen (U : Set G)) :
    ∃ n₁ : ℕ, ∀ k ∈ K p, ∀ t : F, Valued.v t ≤ WithZero.exp (-(n₁ : ℤ)) → k⁻¹ * lowerUnip p t * k ∈ U := by
  have hφc : Continuous (fun q : G × F => q.1⁻¹ * lowerUnip p q.2 * q.1) := by
    refine Continuous.mul (Continuous.mul ?_ ?_) continuous_fst
    · exact continuous_fst.inv
    · exact (continuous_lowerUnip p).comp continuous_snd
  have hn : IsOpen ((fun q : G × F => q.1⁻¹ * lowerUnip p q.2 * q.1) ⁻¹' (U : Set G)) := hU.preimage hφc
  have hsub : (K p : Set G) ×ˢ ({0} : Set F) ⊆ (fun q : G × F => q.1⁻¹ * lowerUnip p q.2 * q.1) ⁻¹' (U : Set G) := by
    rintro ⟨k, t⟩ ⟨-, ht⟩
    rw [Set.mem_singleton_iff] at ht
    subst ht
    show k⁻¹ * lowerUnip p 0 * k ∈ (U : Set G)
    rw [lowerUnip_zero, mul_one, inv_mul_cancel]
    exact U.one_mem
  obtain ⟨u, w, -, hw, hKu, h0w, huw⟩ := generalized_tube_lemma (isCompact_K p) isCompact_singleton hn hsub
  have hw0 : w ∈ 𝓝 (0 : F) := hw.mem_nhds (h0w (Set.mem_singleton 0))
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hw0
  obtain ⟨n₁, hn₁⟩ := WithZero.exists_exp_neg_natCast_lt (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  refine ⟨n₁, fun k hk t ht => ?_⟩
  have htw : t ∈ w := by
    refine hγ ?_
    show Valued.v.restrict t < _
    rw [Valuation.restrict_lt_iff_lt_embedding]
    exact lt_of_le_of_lt ht hn₁
  have hmem := huw (Set.mk_mem_prod (hKu hk) htw)
  exact hmem

theorem continuous_addChar (ψ : AddChar F ℂ)
    (hψk : ∃ k : ℤ, ∀ y : F, Valued.v y ≤ WithZero.exp k → ψ y = 1) : Continuous ψ := by
  obtain ⟨k, hk⟩ := hψk
  have hv : Valued.v (((AdelicLevel.uniformizerUnit ℚ p ^ (-k) : Fˣ) : F)) = WithZero.exp k := by
    rw [valued_zpow _ (AdelicLevel.valued_uniformizerUnit ℚ p), neg_neg]
  have hopen : IsOpen (ball p k) := isOpen_ball' p (Units.ne_zero _) hv
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hev : ∀ᶠ y in 𝓝 x, ψ y = ψ x := by
    have hmem : (fun y : F => y - x) ⁻¹' ball p k ∈ 𝓝 x :=
      (hopen.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp [mem_ball])
    filter_upwards [hmem] with y hy
    have : y = (y - x) + x := by ring
    rw [this, AddChar.map_add_eq_mul, hk _ hy, one_mul]
  exact continuousAt_const.congr (Filter.EventuallyEq.symm hev)

open Classical in

def kappa (ψ : AddChar F ℂ) (y : F) : ℂ :=
  if hy : y = 0 then 0 else
    ((χ 0 (Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy))) : ℂˣ) : ℂ) * ((χ 1 (Units.mk0 y hy) : ℂˣ) : ℂ) *
      ((‖y‖⁻¹ : ℝ) : ℂ) * ψ y

def nearPart (f : G → ℂ) (ψ : AddChar F ℂ) (ν : Measure F) (n : ℤ) (g : G) : ℂ :=
  ∫ y in ball p n, f (antidiagonal2 p * upperUnipotent2 p y * g) * ψ y ∂ν

def farPart (ψ : AddChar F ℂ) (ν : Measure F) (n M : ℤ) : ℂ :=
  ∫ y in ball p M \ ball p n, kappa p χ ψ y ∂ν

theorem main
    (hθu : ∀ (i : Fin 2) (z : Fˣ), ‖((χ i z : ℂˣ) : ℂ)‖ = 1)
    {f : G → ℂ} (hf : f ∈ principalSeries2 p χ)
    (hfsm : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, f (g * k) = f g)
    (ψ : AddChar F ℂ) (hψk : ∃ k : ℤ, ∀ y : F, Valued.v y ≤ WithZero.exp k → ψ y = 1)
    (u : Fˣ) (hu : Valued.v (u : F) = WithZero.exp (-1 : ℤ))
    (ν : Measure F) [ν.IsAddHaarMeasure] (W : G → ℂ)
    (hW : ∀ g : G, ∃ M₀ : ℤ, ∀ M : ℤ, M₀ ≤ M →
      IntegrableOn (fun y : F => f (antidiagonal2 p * upperUnipotent2 p y * g) * ψ y) (ball p M) ν ∧
      W g = ∫ y in ball p M, f (antidiagonal2 p * upperUnipotent2 p y * g) * ψ y ∂ν) :
    ∃ C : ℝ, ∀ m : ℤ, 0 ≤ m → ∀ k ∈ K p,
      ‖W (diagonal2 p ![u ^ m, 1] * k)‖ ≤ C * qR p ^ m := by
  obtain ⟨U, hUo, hfU⟩ := hfsm
  obtain ⟨n₁, hn₁⟩ := exists_uniform_radius p U hUo
  obtain ⟨S, hS0, hS⟩ := exists_bound_on_K p χ hf

  have hvu : ∀ k : ℤ, Valued.v (((u ^ (-k) : Fˣ) : F)) = WithZero.exp k := fun k => by
    rw [valued_zpow u hu, neg_neg]
  have hballc : ∀ k : ℤ, IsCompact (ball p k) := fun k => isCompact_ball p (u ^ (-k)) (hvu k)
  have hballm : ∀ k : ℤ, MeasurableSet (ball p k) := fun k => measurableSet_ball p (u ^ (-k)) (hvu k)

  have hsmooth : ∀ m : ℤ, 0 ≤ m → ∀ k ∈ K p, ∀ t : F, Valued.v t ≤ WithZero.exp (-(n₁ : ℤ)) →
      f (lowerUnip p t * (diagonal2 p ![u ^ m, 1] * k)) = f (diagonal2 p ![u ^ m, 1] * k) := by
    intro m hm k hk t ht
    have hmem : k⁻¹ * lowerUnip p (((u ^ m : Fˣ) : F) * t) * k ∈ U := by
      refine hn₁ k hk _ ?_
      rw [map_mul, valued_zpow u hu]
      calc WithZero.exp (-m) * Valued.v t ≤ 1 * Valued.v t := by
            refine mul_le_mul' ?_ le_rfl
            rw [← WithZero.exp_zero, WithZero.exp_le_exp]
            omega
        _ ≤ WithZero.exp (-(n₁ : ℤ)) := by rw [one_mul]; exact ht
    have heq : lowerUnip p t * (diagonal2 p ![u ^ m, 1] * k) =
        diagonal2 p ![u ^ m, 1] * k * (k⁻¹ * lowerUnip p (((u ^ m : Fˣ) : F) * t) * k) := by
      rw [← mul_assoc, lowerUnip_mul_diag]
      group
    rw [heq, hfU _ hmem]

  have hfar : ∀ m : ℤ, 0 ≤ m → ∀ k ∈ K p, ∀ y : F, WithZero.exp (n₁ : ℤ) < Valued.v y →
      f (antidiagonal2 p * upperUnipotent2 p y * (diagonal2 p ![u ^ m, 1] * k)) * ψ y =
        f (diagonal2 p ![u ^ m, 1] * k) * kappa p χ ψ y := by
    intro m hm k hk y hy
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, map_zero] at hy
      exact not_lt_zero hy
    have hvy0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
    have hlog : Valued.v y = WithZero.exp (WithZero.log (Valued.v y)) := (WithZero.exp_log hvy0).symm
    have hL : (n₁ : ℤ) < WithZero.log (Valued.v y) := by
      rw [hlog] at hy
      exact WithZero.exp_lt_exp.mp hy
    have hyi : Valued.v y⁻¹ ≤ WithZero.exp (-(n₁ : ℤ)) := by
      rw [map_inv₀, hlog, ← WithZero.exp_neg, WithZero.exp_le_exp]
      omega
    simp only [kappa, dif_neg hy0]
    rw [apply_weyl_upper p χ hf y hy0, hsmooth m hm k hk _ hyi]
    ring

  have hdecomp : ∀ m : ℤ, 0 ≤ m → ∀ k ∈ K p, ∃ M₁ : ℤ, ∀ M : ℤ, M₁ ≤ M →
      W (diagonal2 p ![u ^ m, 1] * k) =
        nearPart p f ψ ν n₁ (diagonal2 p ![u ^ m, 1] * k) + f (diagonal2 p ![u ^ m, 1] * k) * farPart p χ ψ ν n₁ M := by
    intro m hm k hk
    obtain ⟨M₀, hM₀⟩ := hW (diagonal2 p ![u ^ m, 1] * k)
    refine ⟨max M₀ n₁, fun M hM => ?_⟩
    obtain ⟨hint, hWg⟩ := hM₀ M ((le_max_left _ _).trans hM)
    have hn₁M : (n₁ : ℤ) ≤ M := (le_max_right _ _).trans hM
    have hsplit : ball p M = ball p n₁ ∪ (ball p M \ ball p n₁) :=
      (Set.union_diff_cancel (ball_mono p hn₁M)).symm
    have hdisj : Disjoint (ball p n₁) (ball p M \ ball p n₁) := Set.disjoint_sdiff_right
    have hAm : MeasurableSet (ball p M \ ball p n₁) := (hballm M).diff (hballm n₁)
    rw [hWg, hsplit, setIntegral_union hdisj hAm (hint.mono_set (ball_mono p hn₁M))
      (hint.mono_set Set.diff_subset)]
    have hcongr : ∫ y in ball p M \ ball p n₁,
        f (antidiagonal2 p * upperUnipotent2 p y * (diagonal2 p ![u ^ m, 1] * k)) * ψ y ∂ν =
        ∫ y in ball p M \ ball p n₁, f (diagonal2 p ![u ^ m, 1] * k) * kappa p χ ψ y ∂ν := by
      refine setIntegral_congr_fun hAm fun y hy => hfar m hm k hk y ?_
      have hy' : y ∉ ball p n₁ := hy.2
      rw [mem_ball, not_le] at hy'
      exact hy'
    rw [hcongr, integral_const_mul]
    rfl

  have hstab : ∃ Φ₀ : ℂ, ∀ m : ℤ, 0 ≤ m → ∀ k ∈ K p,
      W (diagonal2 p ![u ^ m, 1] * k) =
        nearPart p f ψ ν n₁ (diagonal2 p ![u ^ m, 1] * k) + f (diagonal2 p ![u ^ m, 1] * k) * Φ₀ := by
    by_cases hex : ∃ m : ℤ, 0 ≤ m ∧ ∃ k ∈ K p, f (diagonal2 p ![u ^ m, 1] * k) ≠ 0
    ·
      obtain ⟨m₀, hm₀, k₀, hk₀, hne⟩ := hex
      obtain ⟨M₁', hM₁'⟩ := hdecomp m₀ hm₀ k₀ hk₀
      refine ⟨farPart p χ ψ ν n₁ M₁', fun m hm k hk => ?_⟩
      obtain ⟨M₁, hM₁⟩ := hdecomp m hm k hk
      have h1 := hM₁ (max M₁ M₁') (le_max_left _ _)
      have h2 := hM₁' (max M₁ M₁') (le_max_right _ _)
      have h3 := hM₁' M₁' le_rfl
      have hΦeq : farPart p χ ψ ν n₁ (max M₁ M₁') = farPart p χ ψ ν n₁ M₁' :=
        mul_left_cancel₀ hne (add_left_cancel (h2.symm.trans h3))
      rw [h1, hΦeq]
    ·
      push Not at hex
      refine ⟨0, fun m hm k hk => ?_⟩
      obtain ⟨M₁, hM₁⟩ := hdecomp m hm k hk
      rw [hM₁ M₁ le_rfl, hex m hm k hk, zero_mul, zero_mul]
  obtain ⟨Φ₀, hΦ₀⟩ := hstab

  obtain ⟨Bψ, hBψ⟩ := (hballc n₁).exists_bound_of_continuousOn (continuous_addChar p ψ hψk).continuousOn
  have hBψ0 : 0 ≤ Bψ := (norm_nonneg _).trans (hBψ 0 (by simp [mem_ball]))
  set V : ℝ := ν.real (ball p n₁) with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  refine ⟨S * Bψ * V + S * ‖Φ₀‖, fun m hm k hk => ?_⟩
  have hq1 : 1 ≤ qR p ^ m := one_le_qR_zpow p hm
  have hq0 : 0 ≤ qR p ^ m := zero_le_one.trans hq1

  have hfDk : ‖f (diagonal2 p ![u ^ m, 1] * k)‖ ≤ S := by
    rw [norm_apply_diag_left p χ hf hθu]
    have hsq : Real.sqrt ‖(((u ^ m : Fˣ)) : F)‖ ≤ 1 := by
      rw [Real.sqrt_le_one, norm_eq_zpow_of_valued p (valued_zpow u hu m)]
      exact zpow_le_one_of_nonpos₀ (one_lt_qR p).le (neg_nonpos.mpr hm)
    calc Real.sqrt ‖(((u ^ m : Fˣ)) : F)‖ * ‖f k‖ ≤ 1 * S := mul_le_mul hsq (hS k hk) (norm_nonneg _) zero_le_one
      _ = S := one_mul S

  have hpt : ∀ y ∈ ball p n₁,
      ‖f (antidiagonal2 p * upperUnipotent2 p y * (diagonal2 p ![u ^ m, 1] * k)) * ψ y‖ ≤ qR p ^ m * S * Bψ := by
    intro y hy
    rw [norm_mul]
    refine mul_le_mul ?_ (hBψ y hy) (norm_nonneg _) (mul_nonneg hq0 hS0)
    have hresc : antidiagonal2 p * upperUnipotent2 p y * (diagonal2 p ![u ^ m, 1] * k) =
        diagonal2 p ![(1 : Fˣ), u ^ m] *
          (antidiagonal2 p * upperUnipotent2 p ((((1 : Fˣ) * (u ^ m)⁻¹ : Fˣ) : F) * y) * k) := by
      rw [← mul_assoc, weyl_upper_diag, mul_assoc]
    rw [hresc, norm_apply_diag_right p χ hf hθu]
    have hsq : Real.sqrt (‖(((u ^ m : Fˣ)) : F)‖⁻¹) ≤ qR p ^ m := by
      rw [norm_eq_zpow_of_valued p (valued_zpow u hu m), ← _root_.zpow_neg, neg_neg,
        Real.sqrt_le_left hq0]
      nlinarith [hq1]
    exact mul_le_mul hsq (norm_apply_weyl_upper_le p χ hf hθu hS _ hk) (norm_nonneg _) hq0
  have hnear : ‖nearPart p f ψ ν n₁ (diagonal2 p ![u ^ m, 1] * k)‖ ≤ qR p ^ m * S * Bψ * V := by
    have h := norm_setIntegral_le_of_norm_le_const ((hballc n₁).measure_lt_top (μ := ν)) hpt
    rw [← hV] at h
    exact h
  calc ‖W (diagonal2 p ![u ^ m, 1] * k)‖
      = ‖nearPart p f ψ ν n₁ (diagonal2 p ![u ^ m, 1] * k) + f (diagonal2 p ![u ^ m, 1] * k) * Φ₀‖ := by
        rw [hΦ₀ m hm k hk]
    _ ≤ ‖nearPart p f ψ ν n₁ (diagonal2 p ![u ^ m, 1] * k)‖ + ‖f (diagonal2 p ![u ^ m, 1] * k)‖ * ‖Φ₀‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ qR p ^ m * S * Bψ * V + S * ‖Φ₀‖ := add_le_add hnear (mul_le_mul_of_nonneg_right hfDk (norm_nonneg _))
    _ ≤ qR p ^ m * S * Bψ * V + qR p ^ m * (S * ‖Φ₀‖) := by
        exact add_le_add le_rfl (le_mul_of_one_le_left (mul_nonneg hS0 (norm_nonneg Φ₀)) hq1)
    _ = (S * Bψ * V + S * ‖Φ₀‖) * qR p ^ m := by ring

end LTJacquetGrowth
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_norm_apply_diagZ_mul_le_of_stabilised_jacquetIntegral_of_norm_eq_one.LTJacquetGrowth"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_norm_apply_diagZ_mul_le_of_stabilised_jacquetIntegral_of_norm_eq_one.LTJacquetGrowth"

open MeasureTheory IsDedekindDomain NumberField UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction AutomorphicForm LTJacquetGrowth

open scoped nonZeroDivisors NNReal ENNReal

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hθu : ∀ (i : Fin 2) (z : (p.adicCompletion ℚ)ˣ), ‖((θ i z : ℂˣ) : ℂ)‖ = 1)
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p θ)
    (hfsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), f (g * k) = f g)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (ψ : AddChar (p.adicCompletion ℚ) ℂ)
    (hψk : ∃ k : ℤ, ∀ y : p.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → ψ y = 1)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    letI := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure] (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ g : GL (Fin 2) (p.adicCompletion ℚ), ∃ M₀ : ℤ, ∀ M : ℤ, M₀ ≤ M →
          IntegrableOn (fun y : p.adicCompletion ℚ => f (w₀ * unipotentGL2 y * g) * ψ y)
            {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp M} ν ∧
          W g = ∫ y in {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp M},
            f (w₀ * unipotentGL2 y * g) * ψ y ∂ν) →
      ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        ‖W (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
          C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m) := by
  intro ν _ W hW
  have hw := eq_antidiagonal2 p w₀ hw₀
  subst hw
  simp_rw [unipotentGL2_eq p] at hW
  have hu : Valued.v ((Units.mk0 _ hπ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
    rw [Units.val_mk0]; exact hϖ
  obtain ⟨C, hC⟩ := main p θ hθu hf hfsm ψ hψk (Units.mk0 _ hπ) hu ν W hW
  refine ⟨C, 1, fun m hm k hk => ?_⟩
  rw [diagZ_eq_diagonal2 p _ hπ m, one_mul, Real.rpow_intCast]
  exact hC m hm k hk

end S_LanglandsTunnell_CubicInduction_exists_norm_apply_diagZ_mul_le_of_stabilised_jacquetIntegral_of_norm_eq_one
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_norm_apply_diagZ_mul_le_of_stabilised_jacquetIntegral_of_norm_eq_one (solution)
