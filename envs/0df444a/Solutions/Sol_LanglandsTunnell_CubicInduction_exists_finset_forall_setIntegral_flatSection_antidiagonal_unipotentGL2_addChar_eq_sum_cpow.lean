-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a9531057-d7c3-50a4-96ed-1d5b68dc1adf

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_LanglandsTunnell_CubicInduction_flatSection_mem_principalSeries2_and_iwasawaHeight_mul_eq
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction AutomorphicForm Filter Topology Matrix

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace LTJacquetStab

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

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

theorem exists_norm_eq_zpow {y : F} (hy : y ≠ 0) : ∃ k : ℤ, ‖y‖ = qR p ^ k :=
  ⟨WithZero.log (Valued.v y), norm_eq_zpow_of_valued p (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hy)).symm⟩

def ball (k : ℤ) : Set F := {y | Valued.v y ≤ WithZero.exp k}

theorem mem_ball {k : ℤ} {y : F} : y ∈ ball p k ↔ Valued.v y ≤ WithZero.exp k := Iff.rfl

variable {p} in
theorem valued_zpow (ϖ : Fˣ) (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (((ϖ ^ k : Fˣ) : F)) = WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  ring

def piU : Fˣ := AdelicLevel.uniformizerUnit ℚ p

theorem valued_piU : Valued.v ((piU p : Fˣ) : F) = WithZero.exp (-1 : ℤ) := AdelicLevel.valued_uniformizerUnit ℚ p

theorem ball_eq_setOf_le_valued {k : ℤ} {t : F} (hvt : Valued.v t = WithZero.exp k) :
    ball p k = {y : F | Valued.v y ≤ Valued.v t} := by
  rw [hvt]; rfl

theorem isOpen_ball (k : ℤ) : IsOpen (ball p k) := by
  have hv : Valued.v (((piU p ^ (-k) : Fˣ) : F)) = WithZero.exp k := by rw [valued_zpow _ (valued_piU p), neg_neg]
  rw [ball_eq_setOf_le_valued p hv]
  exact AdelicLevel.isOpen_setOf_valued_le p _ (Units.ne_zero _)

theorem measurableSet_ball (k : ℤ) : MeasurableSet (ball p k) := (isOpen_ball p k).measurableSet

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

theorem isCompact_ball (k : ℤ) : IsCompact (ball p k) := by
  have hv : Valued.v (((piU p ^ (-k) : Fˣ) : F)) = WithZero.exp k := by rw [valued_zpow _ (valued_piU p), neg_neg]
  rw [ball_eq_smul p _ hv, ← coe_integersPositiveCompacts ℚ p]
  exact (integersPositiveCompacts ℚ p).isCompact.smul _

def shell (m : ℤ) : Set F := {y | Valued.v y = WithZero.exp m}

theorem mem_shell {m : ℤ} {y : F} : y ∈ shell p m ↔ Valued.v y = WithZero.exp m := Iff.rfl

theorem shell_subset_ball (m : ℤ) : shell p m ⊆ ball p m := fun _ hy => le_of_eq hy

theorem isClosed_shell (m : ℤ) : IsClosed (shell p m) := by
  have : shell p m = {y : F | Valued.v.restrict y = Valued.v.restrict (((piU p ^ (-m) : Fˣ) : F))} := by
    ext y
    rw [mem_shell, Set.mem_setOf_eq, Valuation.restrict_inj, valued_zpow _ (valued_piU p), neg_neg]
  rw [this]
  exact Valued.isClosed_sphere F _

theorem measurableSet_shell (m : ℤ) : MeasurableSet (shell p m) := (isClosed_shell p m).measurableSet

theorem isCompact_shell (m : ℤ) : IsCompact (shell p m) :=
  (isCompact_ball p m).of_isClosed_subset (isClosed_shell p m) (shell_subset_ball p m)

theorem ball_succ (m : ℤ) : ball p (m + 1) = ball p m ∪ shell p (m + 1) := by
  ext y
  simp only [mem_ball, Set.mem_union, mem_shell]
  constructor
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · left
      by_cases hy : Valued.v y = 0
      · rw [hy]; exact zero_le'
      · rw [← WithZero.exp_log hy] at h ⊢
        rw [WithZero.exp_lt_exp] at h
        rw [WithZero.exp_le_exp]
        omega
    · exact Or.inr h
  · rintro (h | h)
    · exact h.trans (WithZero.exp_le_exp.mpr (by omega))
    · exact h.le

theorem disjoint_ball_shell_succ (m : ℤ) : Disjoint (ball p m) (shell p (m + 1)) := by
  rw [Set.disjoint_left]
  intro y hy hy'
  rw [mem_ball] at hy
  rw [mem_shell] at hy'
  rw [hy', WithZero.exp_le_exp] at hy
  omega

theorem ne_zero_of_mem_shell {m : ℤ} {y : F} (hy : y ∈ shell p m) : y ≠ 0 := by
  intro h; rw [mem_shell, h, map_zero] at hy; exact WithZero.exp_ne_zero hy.symm

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

theorem upperUnipotent2_add (x y : F) : upperUnipotent2 p (x + y) = upperUnipotent2 p x * upperUnipotent2 p y :=
  (upperUnipotent2_mul p x y).symm

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

def hgt (g : G) : ℝ := ‖(g : Mat).det‖ / max ‖(g : Mat) 1 0‖ ‖(g : Mat) 1 1‖ ^ 2

theorem hgt_laws :
    (∀ (x : F) (g : G), hgt p (upperUnipotent2 p x * g) = hgt p g) ∧
    (∀ (a : Fin 2 → Fˣ) (g : G), hgt p (diagonal2 p a * g) = ‖(a 0 : F)‖ / ‖(a 1 : F)‖ * hgt p g) ∧
    (∀ (g k : G), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ → hgt p (g * k) = hgt p g) ∧
    (∀ g : G, 0 < hgt p g) := by
  have h := LanglandsTunnell.CubicInduction.flatSection_mem_principalSeries2_and_iwasawaHeight_mul_eq p 1 1 0
    (fun a => by simp) (fun a => by simp) 0 (Submodule.zero_mem _)
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

theorem hgt_upper (x : F) (g : G) : hgt p (upperUnipotent2 p x * g) = hgt p g := (hgt_laws p).1 x g

theorem hgt_diag (a : Fin 2 → Fˣ) (g : G) : hgt p (diagonal2 p a * g) = ‖(a 0 : F)‖ / ‖(a 1 : F)‖ * hgt p g :=
  (hgt_laws p).2.1 a g

theorem hgt_pos (g : G) : 0 < hgt p g := (hgt_laws p).2.2.2 g

theorem isLocallyConstant_hgt : IsLocallyConstant (hgt p) := by
  have hU : IsOpen ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ (by simp)).2
  refine (IsLocallyConstant.iff_exists_open _).mpr fun x => ?_
  refine ⟨(fun h => x⁻¹ * h) ⁻¹' ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G),
    hU.preimage (continuous_const.mul continuous_id), by simp, fun y hy => ?_⟩
  have := (hgt_laws p).2.2.1 x (x⁻¹ * y) hy
  rwa [mul_inv_cancel_left] at this

theorem hgt_weyl_upper (y : F) (hy : y ≠ 0) (g : G) :
    hgt p (antidiagonal2 p * upperUnipotent2 p y * g) = ‖y‖⁻¹ * ‖y‖⁻¹ * hgt p (lowerUnip p y⁻¹ * g) := by
  rw [weyl_upper_eq p y hy, mul_assoc, mul_assoc, hgt_upper, hgt_diag]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_mk0, norm_neg, norm_inv]
  rw [div_eq_mul_inv]

theorem exists_hgt_eq_zpow (g : G) : ∃ j : ℤ, hgt p g = qR p ^ j := by
  have hdet : (g : Mat).det ≠ 0 := by
    have h := (Matrix.GeneralLinearGroup.det g).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at h
  obtain ⟨a, ha⟩ := exists_norm_eq_zpow p hdet
  have hrow : ∃ b : ℤ, max ‖(g : Mat) 1 0‖ ‖(g : Mat) 1 1‖ = qR p ^ b := by
    rcases le_total ‖(g : Mat) 1 1‖ ‖(g : Mat) 1 0‖ with h | h
    · rw [max_eq_left h]
      by_cases h0 : (g : Mat) 1 0 = 0
      · exfalso
        have h1 : (g : Mat) 1 1 = 0 := by
          rw [h0, norm_zero] at h; exact norm_le_zero_iff.mp h
        apply hdet
        rw [Matrix.det_fin_two, h0, h1]; ring
      · exact exists_norm_eq_zpow p h0
    · rw [max_eq_right h]
      by_cases h1 : (g : Mat) 1 1 = 0
      · exfalso
        have h0 : (g : Mat) 1 0 = 0 := by
          rw [h1, norm_zero] at h; exact norm_le_zero_iff.mp h
        apply hdet
        rw [Matrix.det_fin_two, h0, h1]; ring
      · exact exists_norm_eq_zpow p h1
  obtain ⟨b, hb⟩ := hrow
  refine ⟨a - 2 * b, ?_⟩
  rw [hgt, ha, hb, ← zpow_natCast, ← _root_.zpow_mul, div_eq_mul_inv, ← _root_.zpow_neg,
    ← zpow_add₀ (qR_pos p).ne']
  congr 1
  push_cast
  ring

def jOf (r : ℝ) : ℤ :=
  open Classical in
  if h : ∃ j : ℤ, r = qR p ^ j then h.choose else 0

theorem zpow_jOf {r : ℝ} (h : ∃ j : ℤ, r = qR p ^ j) : qR p ^ jOf p r = r := by
  unfold jOf
  rw [dif_pos h]
  exact h.choose_spec.symm

theorem zpow_jOf_hgt (g : G) : qR p ^ jOf p (hgt p g) = hgt p g :=
  zpow_jOf p (exists_hgt_eq_zpow p g)

theorem exists_radius_lowerUnip {α : Type*} {φ : G → α} (hφ : IsLocallyConstant φ) (g : G) :
    ∃ k₀ : ℕ, ∀ t : F, Valued.v t ≤ WithZero.exp (-(k₀ : ℤ)) → φ (lowerUnip p t * g) = φ g := by
  have hcont : Continuous fun t : F => lowerUnip p t * g := (continuous_lowerUnip p).mul continuous_const
  obtain ⟨U, hU, hgU, hfU⟩ := hφ.exists_open g
  have hU0 : (fun t : F => lowerUnip p t * g) ⁻¹' U ∈ 𝓝 (0 : F) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [lowerUnip_zero, one_mul]; exact hU.mem_nhds hgU)
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU0
  obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  refine ⟨k, fun t ht => hfU _ (hγ ?_)⟩
  show Valued.v.restrict t < _
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt ht hk

theorem isLocallyConstant_addChar (θ : AddChar F ℂ) (hθk : ∃ k : ℤ, ∀ y : F, Valued.v y ≤ WithZero.exp k → θ y = 1) :
    IsLocallyConstant θ := by
  obtain ⟨k, hk⟩ := hθk
  refine (IsLocallyConstant.iff_exists_open _).mpr fun x => ?_
  refine ⟨(fun y => y - x) ⁻¹' ball p k, (isOpen_ball p k).preimage (continuous_id.sub continuous_const), by
    simp [mem_ball], fun y hy => ?_⟩
  have h : θ (y - x) = 1 := hk _ hy
  calc θ y = θ ((y - x) + x) := by rw [sub_add_cancel]
    _ = θ (y - x) * θ x := AddChar.map_add_eq_mul _ _ _
    _ = θ x := by rw [h, one_mul]

section FarShell

variable {p}

theorem ratio_deep {m : ℤ} {c : ℕ} (hc : 1 ≤ c) {y t : F} (hy : Valued.v y = WithZero.exp m)
    (ht : Valued.v t ≤ WithZero.exp (m - c)) :
    ∃ (_ : y ≠ 0) (_ : y + t ≠ 0), Valued.v (y + t) = WithZero.exp m ∧
      Valued.v ((y + t) * y⁻¹) = 1 ∧ Valued.v ((y + t) * y⁻¹ - 1) ≤ WithZero.exp (-(c : ℤ)) := by
  have hy0 : y ≠ 0 := by intro h; rw [h, map_zero] at hy; exact WithZero.exp_ne_zero hy.symm
  have hlt : Valued.v t < Valued.v y := by
    rw [hy]
    exact lt_of_le_of_lt ht (WithZero.exp_lt_exp.mpr (by omega))
  have hyt : Valued.v (y + t) = Valued.v y := Valuation.map_add_eq_of_lt_left _ hlt
  have hyt0 : y + t ≠ 0 := by
    intro h; rw [h, map_zero] at hyt; rw [← hyt] at hy; exact WithZero.exp_ne_zero hy.symm
  refine ⟨hy0, hyt0, by rw [hyt, hy], ?_, ?_⟩
  · rw [map_mul, map_inv₀, hyt, mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr hy0)]
  · have : (y + t) * y⁻¹ - 1 = t * y⁻¹ := by field_simp; ring
    rw [this, map_mul, map_inv₀, hy, ← WithZero.exp_neg, mul_comm]
    calc WithZero.exp (-m) * Valued.v t ≤ WithZero.exp (-m) * WithZero.exp (m - c) := mul_le_mul_right ht _
      _ = WithZero.exp (-(c : ℤ)) := by rw [← WithZero.exp_add]; congr 1; ring

theorem ratio_mem_higherUnitsAt {c n : ℕ} (hn : n ≤ c) {w : Fˣ} (hw1 : Valued.v (w : F) = 1)
    (hw2 : Valued.v ((w : F) - 1) ≤ WithZero.exp (-(c : ℤ))) : w ∈ higherUnitsAt ℚ p n := by
  refine ⟨hw1, Or.inr (hw2.trans (WithZero.exp_le_exp.mpr (by omega)))⟩

theorem char_mk0_add_eq (η : Fˣ →* ℂˣ) {n c : ℕ} (hη : ∀ u ∈ higherUnitsAt ℚ p n, η u = 1) (hn : n ≤ c) (hc : 1 ≤ c)
    {m : ℤ} {y t : F} (hy : Valued.v y = WithZero.exp m) (ht : Valued.v t ≤ WithZero.exp (m - c))
    (hy0 : y ≠ 0) (hyt0 : y + t ≠ 0) :
    η (Units.mk0 (y + t) hyt0) = η (Units.mk0 y hy0) := by
  obtain ⟨_, _, -, hw1, hw2⟩ := ratio_deep hc hy ht
  set w : Fˣ := Units.mk0 ((y + t) * y⁻¹) (mul_ne_zero hyt0 (inv_ne_zero hy0)) with hw
  have hmem : w ∈ higherUnitsAt ℚ p n := ratio_mem_higherUnitsAt hn (by rw [hw, Units.val_mk0]; exact hw1)
    (by rw [hw, Units.val_mk0]; exact hw2)
  have hfac : Units.mk0 (y + t) hyt0 = w * Units.mk0 y hy0 := by
    refine Units.ext ?_
    rw [Units.val_mul, hw, Units.val_mk0, Units.val_mk0, Units.val_mk0, inv_mul_cancel_right₀ hy0]
  rw [hfac, map_mul, hη w hmem, one_mul]

theorem char_mk0_neg_inv_add_eq (η : Fˣ →* ℂˣ) {n c : ℕ} (hη : ∀ u ∈ higherUnitsAt ℚ p n, η u = 1) (hn : n ≤ c)
    (hc : 1 ≤ c) {m : ℤ} {y t : F} (hy : Valued.v y = WithZero.exp m) (ht : Valued.v t ≤ WithZero.exp (m - c))
    (hy0 : y ≠ 0) (hyt0 : y + t ≠ 0) :
    η (Units.mk0 (-(y + t)⁻¹) (neg_ne_zero.mpr (inv_ne_zero hyt0))) =
      η (Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy0))) := by
  obtain ⟨_, _, -, hw1, hw2⟩ := ratio_deep hc hy ht
  set w : Fˣ := Units.mk0 ((y + t) * y⁻¹) (mul_ne_zero hyt0 (inv_ne_zero hy0)) with hw
  have hmem : w ∈ higherUnitsAt ℚ p n := ratio_mem_higherUnitsAt hn (by rw [hw, Units.val_mk0]; exact hw1)
    (by rw [hw, Units.val_mk0]; exact hw2)
  have hfac : Units.mk0 (-(y + t)⁻¹) (neg_ne_zero.mpr (inv_ne_zero hyt0)) =
      Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy0)) * w⁻¹ := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hw, Units.val_mk0, Units.val_mk0, Units.val_mk0]
    field_simp
  rw [hfac, map_mul, map_inv, hη w hmem, inv_one, mul_one]

theorem norm_add_eq_of_far {c : ℕ} (hc : 1 ≤ c) {m : ℤ} {y t : F} (hy : Valued.v y = WithZero.exp m)
    (ht : Valued.v t ≤ WithZero.exp (m - c)) : ‖y + t‖ = ‖y‖ := by
  obtain ⟨_, _, hv, -, -⟩ := ratio_deep hc hy ht
  rw [norm_eq_zpow_of_valued p hv, norm_eq_zpow_of_valued p hy]

end FarShell

section FlatIntegrand

variable {p}

def path (g : G) (y : F) : G := antidiagonal2 p * upperUnipotent2 p y * g

theorem continuous_path (g : G) : Continuous (path (p := p) g) :=
  (continuous_const.mul (continuous_upperUnipotent2 p)).mul continuous_const

def flatVal (f : G → ℂ) (u : ℂ) (g : G) (y : F) : ℂ :=
  f (path g y) * ((hgt p (path g y) : ℝ) : ℂ) ^ u

theorem continuous_flatVal {f : G → ℂ} (hlc : IsLocallyConstant f) (u : ℂ) (g : G) :
    Continuous (flatVal (p := p) f u g) := by
  have h1 : IsLocallyConstant (fun y : F => f (path (p := p) g y)) := hlc.comp_continuous (continuous_path g)
  have h2 : IsLocallyConstant (fun y : F => ((hgt p (path (p := p) g y) : ℝ) : ℂ) ^ u) :=
    ((isLocallyConstant_hgt p).comp_continuous (continuous_path g)).comp fun r : ℝ => ((r : ℝ) : ℂ) ^ u
  exact (h1.mul h2).continuous

theorem exists_common_radius {f : G → ℂ} (hlc : IsLocallyConstant f) (g : G) :
    ∃ k₀ : ℕ, ∀ t : F, Valued.v t ≤ WithZero.exp (-(k₀ : ℤ)) →
      f (lowerUnip p t * g) = f g ∧ hgt p (lowerUnip p t * g) = hgt p g := by
  obtain ⟨k₁, hk₁⟩ := exists_radius_lowerUnip p hlc g
  obtain ⟨k₂, hk₂⟩ := exists_radius_lowerUnip p (isLocallyConstant_hgt p) g
  refine ⟨max k₁ k₂, fun t ht => ⟨hk₁ t (ht.trans (WithZero.exp_le_exp.mpr ?_)), hk₂ t (ht.trans (WithZero.exp_le_exp.mpr ?_))⟩⟩
  · simp only [neg_le_neg_iff, Nat.cast_le]; exact le_max_left _ _
  · simp only [neg_le_neg_iff, Nat.cast_le]; exact le_max_right _ _

theorem flatVal_far {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (u : ℂ) (g : G) {k₀ : ℕ}
    (hk₀ : ∀ t : F, Valued.v t ≤ WithZero.exp (-(k₀ : ℤ)) → f (lowerUnip p t * g) = f g ∧ hgt p (lowerUnip p t * g) = hgt p g)
    {m : ℤ} (hm : (k₀ : ℤ) ≤ m) {y : F} (hy : Valued.v y = WithZero.exp m) (hy0 : y ≠ 0) :
    flatVal (p := p) f u g y =
      ((χ 0 (Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy0))) : ℂˣ) : ℂ) * ((χ 1 (Units.mk0 y hy0) : ℂˣ) : ℂ) *
        ((‖y‖⁻¹ : ℝ) : ℂ) * f g * (((‖y‖⁻¹ * ‖y‖⁻¹ * hgt p g : ℝ)) : ℂ) ^ u := by
  have hyi : Valued.v y⁻¹ ≤ WithZero.exp (-(k₀ : ℤ)) := by
    rw [map_inv₀, hy, ← WithZero.exp_neg, WithZero.exp_le_exp]; omega
  obtain ⟨hf1, hh1⟩ := hk₀ _ hyi
  unfold flatVal path
  rw [apply_weyl_upper p χ hf y hy0 g, hf1, hgt_weyl_upper p y hy0 g, hh1]

theorem flatVal_add_eq {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ higherUnitsAt ℚ p (cχ i), χ i u = 1) (u : ℂ) (g : G) {k₀ : ℕ}
    (hk₀ : ∀ t : F, Valued.v t ≤ WithZero.exp (-(k₀ : ℤ)) → f (lowerUnip p t * g) = f g ∧ hgt p (lowerUnip p t * g) = hgt p g)
    {m : ℤ} (hm : (k₀ : ℤ) ≤ m) {y t : F} (hy : Valued.v y = WithZero.exp m)
    (ht : Valued.v t ≤ WithZero.exp (m - (cχ 0 + cχ 1 + 1 : ℕ))) :
    flatVal (p := p) f u g (y + t) = flatVal (p := p) f u g y := by
  have hc : 1 ≤ cχ 0 + cχ 1 + 1 := by omega
  obtain ⟨hy0, hyt0, hvyt, -, -⟩ := ratio_deep hc hy ht
  rw [flatVal_far χ hf u g hk₀ hm hvyt hyt0, flatVal_far χ hf u g hk₀ hm hy hy0,
    char_mk0_neg_inv_add_eq (χ 0) (hcχ 0) (by omega) hc hy ht hy0 hyt0,
    char_mk0_add_eq (χ 1) (hcχ 1) (by omega) hc hy ht hy0 hyt0, norm_add_eq_of_far hc hy ht]

theorem mem_shell_add_iff {c : ℕ} (hc : 1 ≤ c) {m : ℤ} {t : F} (ht : Valued.v t ≤ WithZero.exp (m - c)) (y : F) :
    y + t ∈ shell p m ↔ y ∈ shell p m := by
  constructor
  · intro h
    have ht' : Valued.v (-t) ≤ WithZero.exp (m - c) := by rwa [Valuation.map_neg]
    obtain ⟨_, _, hv, -, -⟩ := ratio_deep hc h ht'
    rw [mem_shell, ← hv]; congr 1; ring
  · intro h
    obtain ⟨_, _, hv, -, -⟩ := ratio_deep hc h ht
    exact hv

end FlatIntegrand

section ShellVanish

variable {p}

theorem setIntegral_shell_eq_zero {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ higherUnitsAt ℚ p (cχ i), χ i u = 1) (u : ℂ) (g : G) {k₀ : ℕ}
    (hk₀ : ∀ t : F, Valued.v t ≤ WithZero.exp (-(k₀ : ℤ)) → f (lowerUnip p t * g) = f g ∧ hgt p (lowerUnip p t * g) = hgt p g)
    (θ : AddChar F ℂ) {x₀ : F} (hx₀ : θ x₀ ≠ 1) {e₀ : ℤ} (he₀ : Valued.v x₀ = WithZero.exp e₀)
    {m : ℤ} (hm : (k₀ : ℤ) ≤ m) (hm' : ((cχ 0 + cχ 1 + 1 : ℕ) : ℤ) + e₀ ≤ m)
    (ν : Measure F) [ν.IsAddHaarMeasure] :
    ∫ y in shell p m, flatVal (p := p) f u g y * θ y ∂ν = 0 := by
  set c : ℕ := cχ 0 + cχ 1 + 1 with hcdef
  have hc : 1 ≤ c := by omega
  have ht : Valued.v x₀ ≤ WithZero.exp (m - c) := by rw [he₀, WithZero.exp_le_exp]; omega
  set Ψ : F → ℂ := fun y => flatVal (p := p) f u g y * θ y with hΨ
  have hS := measurableSet_shell p m

  have hpt : ∀ y : F, (shell p m).indicator Ψ (y + x₀) = θ x₀ * (shell p m).indicator Ψ y := by
    intro y
    by_cases hy : y ∈ shell p m
    · rw [Set.indicator_of_mem ((mem_shell_add_iff hc ht y).mpr hy), Set.indicator_of_mem hy, hΨ]
      simp only
      rw [flatVal_add_eq χ hf cχ hcχ u g hk₀ hm hy ht, AddChar.map_add_eq_mul]
      ring
    · rw [Set.indicator_of_notMem (fun h => hy ((mem_shell_add_iff hc ht y).mp h)), Set.indicator_of_notMem hy,
        mul_zero]
  have hI : ∫ y in shell p m, Ψ y ∂ν = θ x₀ * ∫ y in shell p m, Ψ y ∂ν := by
    calc ∫ y in shell p m, Ψ y ∂ν = ∫ y, (shell p m).indicator Ψ y ∂ν := (integral_indicator hS).symm
      _ = ∫ y, (shell p m).indicator Ψ (y + x₀) ∂ν := (integral_add_right_eq_self _ x₀).symm
      _ = ∫ y, θ x₀ * (shell p m).indicator Ψ y ∂ν := integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = θ x₀ * ∫ y in shell p m, Ψ y ∂ν := by rw [integral_const_mul, integral_indicator hS]
  have h1 : (1 - θ x₀) * ∫ y in shell p m, Ψ y ∂ν = 0 := by rw [sub_mul, one_mul, ← hI, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hx₀
  · exact h

end ShellVanish

section Stabilise

variable {p}

theorem integrableOn_of_continuous {Ψ : F → ℂ} (hΨ : Continuous Ψ) {K : Set F} (hK : IsCompact K)
    (ν : Measure F) [ν.IsAddHaarMeasure] : IntegrableOn Ψ K ν :=
  hΨ.continuousOn.integrableOn_compact hK

theorem setIntegral_ball_eq {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ higherUnitsAt ℚ p (cχ i), χ i u = 1) (u : ℂ) (g : G) {k₀ : ℕ}
    (hk₀ : ∀ t : F, Valued.v t ≤ WithZero.exp (-(k₀ : ℤ)) → f (lowerUnip p t * g) = f g ∧ hgt p (lowerUnip p t * g) = hgt p g)
    (θ : AddChar F ℂ) (hθc : Continuous θ) {x₀ : F} (hx₀ : θ x₀ ≠ 1) {e₀ : ℤ} (he₀ : Valued.v x₀ = WithZero.exp e₀)
    (ν : Measure F) [ν.IsAddHaarMeasure] {M : ℤ}
    (hM : max (k₀ : ℤ) (((cχ 0 + cχ 1 + 1 : ℕ) : ℤ) + e₀) ≤ M) :
    ∫ y in ball p M, flatVal (p := p) f u g y * θ y ∂ν =
      ∫ y in ball p (max (k₀ : ℤ) (((cχ 0 + cχ 1 + 1 : ℕ) : ℤ) + e₀)), flatVal (p := p) f u g y * θ y ∂ν := by
  obtain ⟨hlc, -, -⟩ := mem_principalSeries2_iff.mp hf
  have hΨc : Continuous fun y => flatVal (p := p) f u g y * θ y := (continuous_flatVal hlc u g).mul hθc
  refine Int.leInduction (motive := fun N _ => ∫ y in ball p N, flatVal (p := p) f u g y * θ y ∂ν =
      ∫ y in ball p (max (k₀ : ℤ) (((cχ 0 + cχ 1 + 1 : ℕ) : ℤ) + e₀)), flatVal (p := p) f u g y * θ y ∂ν)
    rfl (fun N hN ih => ?_) M hM
  rw [ball_succ, setIntegral_union (disjoint_ball_shell_succ p N) (measurableSet_shell p _)
    (integrableOn_of_continuous hΨc (isCompact_ball p N) ν) (integrableOn_of_continuous hΨc (isCompact_shell p _) ν),
    setIntegral_shell_eq_zero χ hf cχ hcχ u g hk₀ θ hx₀ he₀ (by omega) (by omega) ν, add_zero, ih]

end Stabilise

section Laurent

variable {p}

theorem natCast_absNorm_eq : ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) = ((qR p : ℝ) : ℂ) := by
  unfold qR; push_cast; rfl

theorem cpow_qR_zpow (j : ℤ) (u : ℂ) :
    (((qR p ^ j : ℝ)) : ℂ) ^ u = ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((j : ℂ) * u) := by
  have hq := qR_pos p
  have hqj : (0 : ℝ) < qR p ^ j := zpow_pos hq j
  rw [natCast_absNorm_eq, Complex.cpow_def_of_ne_zero (by exact_mod_cast hqj.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hq.ne'), ← Complex.ofReal_log hqj.le, ← Complex.ofReal_log hq.le,
    Real.log_zpow]
  push_cast
  ring_nf

theorem exists_finset_setIntegral_ball_eq_sum {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (g : G)
    (θ : AddChar F ℂ) (hθc : Continuous θ) (ν : Measure F) [ν.IsAddHaarMeasure] (M : ℤ) :
    ∃ (S : Finset ℤ) (c : ℤ → ℂ), ∀ u : ℂ,
      ∫ y in ball p M, flatVal (p := p) f u g y * θ y ∂ν =
        ∑ j ∈ S, c j * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((j : ℂ) * u) := by
  obtain ⟨hlc, -, -⟩ := mem_principalSeries2_iff.mp hf

  set J : F → ℤ := fun y => jOf p (hgt p (path (p := p) g y)) with hJdef
  have hJlc : IsLocallyConstant J := ((isLocallyConstant_hgt p).comp_continuous (continuous_path g)).comp (jOf p)
  have hJ : ∀ y : F, hgt p (path (p := p) g y) = qR p ^ J y := fun y => (zpow_jOf_hgt p _).symm

  have hfin : (J '' ball p M).Finite := ((isCompact_ball p M).image hJlc.continuous).finite_of_discrete
  set S : Finset ℤ := hfin.toFinset with hSdef
  have hmemS : ∀ y ∈ ball p M, J y ∈ S := fun y hy => hfin.mem_toFinset.mpr ⟨y, hy, rfl⟩

  set P₀ : F → ℂ := fun y => f (path (p := p) g y) * θ y with hP₀
  have hP₀c : Continuous P₀ := (hlc.comp_continuous (continuous_path g)).continuous.mul hθc
  set c : ℤ → ℂ := fun j => ∫ y in ball p M, {y | J y = j}.indicator P₀ y ∂ν with hcdef
  refine ⟨S, c, fun u => ?_⟩
  set E : ℤ → F → ℂ := fun j y => ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((j : ℂ) * u) * P₀ y with hE
  have hmeas : ∀ j : ℤ, MeasurableSet {y : F | J y = j} := fun j => (hJlc.isOpen_fiber j).measurableSet

  have hpt : ∀ y ∈ ball p M, flatVal (p := p) f u g y * θ y = ∑ j ∈ S, {y | J y = j}.indicator (E j) y := by
    intro y hy
    have hsum : ∑ j ∈ S, {y | J y = j}.indicator (E j) y = ∑ j ∈ S, (if J y = j then E j y else 0) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Set.indicator_apply]; rfl
    rw [hsum, Finset.sum_ite_eq, if_pos (hmemS y hy), hE, hP₀]
    simp only
    rw [flatVal, hJ y, cpow_qR_zpow]
    ring

  have hint : ∀ j ∈ S, Integrable ({y | J y = j}.indicator (E j)) (ν.restrict (ball p M)) := by
    intro j _
    refine Integrable.indicator ?_ (hmeas j)
    exact integrableOn_of_continuous (continuous_const.mul hP₀c) (isCompact_ball p M) ν
  rw [setIntegral_congr_fun (measurableSet_ball p M) hpt, integral_finsetSum S hint]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hind : {y : F | J y = j}.indicator (E j) = fun y => ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((j : ℂ) * u) *
      {y : F | J y = j}.indicator P₀ y := by
    funext y
    rw [hE]
    exact Set.indicator_mul_right _ (fun _ => ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((j : ℂ) * u)) P₀
  rw [hind, integral_const_mul, mul_comm]

end Laurent

section Main

variable {p}

theorem main (cχ : Fin 2 → ℕ) (hcχ : ∀ i, ∀ u ∈ higherUnitsAt ℚ p (cχ i), χ i u = 1)
    {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (θ : AddChar F ℂ)
    (hθk : ∃ k : ℤ, ∀ y : F, Valued.v y ≤ WithZero.exp k → θ y = 1) (hθ1 : θ ≠ 1) (g : G)
    (ν : Measure F) [ν.IsAddHaarMeasure] :
    ∃ (M₀ : ℤ) (S : Finset ℤ) (c : ℤ → ℂ), ∀ (u : ℂ) (M : ℤ), M₀ ≤ M →
      IntegrableOn (fun y => flatVal (p := p) f u g y * θ y) (ball p M) ν ∧
      ∫ y in ball p M, flatVal (p := p) f u g y * θ y ∂ν =
        ∑ j ∈ S, c j * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((j : ℂ) * u) := by
  obtain ⟨hlc, -, -⟩ := mem_principalSeries2_iff.mp hf
  have hθc : Continuous θ := (isLocallyConstant_addChar p θ hθk).continuous
  obtain ⟨x₀, hx₀⟩ := AddChar.ne_one_iff.mp hθ1
  have hx₀0 : x₀ ≠ 0 := by intro h; rw [h, AddChar.map_zero_eq_one] at hx₀; exact hx₀ rfl
  have he₀ : Valued.v x₀ = WithZero.exp (WithZero.log (Valued.v x₀)) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx₀0)).symm
  obtain ⟨k₀, hk₀⟩ := exists_common_radius (p := p) hlc g
  set M₁ : ℤ := max (k₀ : ℤ) (((cχ 0 + cχ 1 + 1 : ℕ) : ℤ) + WithZero.log (Valued.v x₀)) with hM₁
  obtain ⟨S, c, hSc⟩ := exists_finset_setIntegral_ball_eq_sum χ hf g θ hθc ν M₁
  refine ⟨M₁, S, c, fun u M hM => ⟨?_, ?_⟩⟩
  · exact integrableOn_of_continuous ((continuous_flatVal hlc u g).mul hθc) (isCompact_ball p M) ν
  · rw [setIntegral_ball_eq χ hf cχ hcχ u g hk₀ θ hθc hx₀ he₀ ν hM]
    exact hSc u

end Main

end LTJacquetStab
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow.LTJacquetStab"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow.LTJacquetStab"

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction AutomorphicForm LTJacquetStab

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (θ : AddChar (p.adicCompletion ℚ) ℂ)
    (hθk : ∃ k : ℤ, ∀ y : p.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → θ y = 1)
    (hθ1 : θ ≠ 1)
    (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    letI := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      ∃ (M₀ : ℤ) (S : Finset ℤ) (c : ℤ → ℂ), ∀ (u : ℂ) (M : ℤ), M₀ ≤ M →
        IntegrableOn (fun y : p.adicCompletion ℚ =>
            f (w₀ * unipotentGL2 y * g) *
              ((‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                    Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
                  max ‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
                    ‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 : ℝ) : ℂ) ^ u * θ y)
          {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp M} ν ∧
        ∫ y in {y : p.adicCompletion ℚ | Valued.v y ≤ WithZero.exp M},
            f (w₀ * unipotentGL2 y * g) *
              ((‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                    Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
                  max ‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
                    ‖((w₀ * unipotentGL2 y * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 : ℝ) : ℂ) ^ u * θ y ∂ν =
          ∑ j ∈ S, c j * (Ideal.absNorm p.asIdeal : ℂ) ^ ((j : ℂ) * u) := by
  intro ν _
  have hw := eq_antidiagonal2 p w₀ hw₀
  subst hw
  simp_rw [unipotentGL2_eq p]
  exact main χ cχ hcχ hf θ hθk hθ1 g ν

end S_LanglandsTunnell_CubicInduction_exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow (solution)
