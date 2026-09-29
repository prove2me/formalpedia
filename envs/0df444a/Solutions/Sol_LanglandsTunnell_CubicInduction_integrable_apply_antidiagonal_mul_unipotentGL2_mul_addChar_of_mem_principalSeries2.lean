-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/23bd78fc-bb86-55c1-b23d-93ca13fc539c

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction AutomorphicForm Filter Topology Matrix

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace LTJacquetConv

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

theorem exists_radius_lowerUnip {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (g : G) :
    ∃ k₀ : ℕ, ∀ t : F, Valued.v t ≤ WithZero.exp (-(k₀ : ℤ)) → f (lowerUnip p t * g) = f g := by
  obtain ⟨hlc, -, -⟩ := mem_principalSeries2_iff.mp hf
  have hcont : Continuous fun t : F => lowerUnip p t * g := (continuous_lowerUnip p).mul continuous_const
  obtain ⟨U, hU, hgU, hfU⟩ := hlc.exists_open g
  have hU0 : (fun t : F => lowerUnip p t * g) ⁻¹' U ∈ 𝓝 (0 : F) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [lowerUnip_zero, one_mul]; exact hU.mem_nhds hgU)
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU0
  obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  refine ⟨k, fun t ht => hfU _ (hγ ?_)⟩
  show Valued.v.restrict t < _
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt ht hk

section CharNorm

theorem continuous_char (η : Fˣ →* ℂˣ) {c : ℕ} (hη : ∀ u ∈ higherUnitsAt ℚ p c, η u = 1) :
    Continuous fun a : Fˣ => ((η a : ℂˣ) : ℂ) := by

  have hopen : ∃ V : Set Fˣ, IsOpen V ∧ (1 : Fˣ) ∈ V ∧ ∀ u ∈ V, η u = 1 := by
    obtain ⟨t, ht, hvt⟩ := AdelicLevel.exists_valued_eq_exp_neg (K := ℚ) p (c + 1)
    have hc1 : Continuous fun u : Fˣ => (u : F) - 1 := Units.continuous_val.sub continuous_const
    refine ⟨(fun u : Fˣ => (u : F) - 1) ⁻¹' {y | Valued.v y ≤ Valued.v t},
      (AdelicLevel.isOpen_setOf_valued_le p t ht).preimage hc1, ?_, ?_⟩
    · simp
    · intro u hu
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hvt] at hu
      have hlt : Valued.v ((u : F) - 1) < 1 := by
        refine lt_of_le_of_lt hu ?_
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        push_cast
        omega
      apply hη
      refine ⟨?_, Or.inr (hu.trans ?_)⟩
      · have := Valuation.map_add_eq_of_lt_left (Valued.v : Valuation F _) (x := (1 : F)) (y := (u : F) - 1)
          (by rwa [Valuation.map_one])
        rw [Valuation.map_one, add_sub_cancel] at this
        exact this
      · rw [WithZero.exp_le_exp]
        push_cast
        omega
  obtain ⟨V, hV, h1V, hVker⟩ := hopen
  refine continuous_iff_continuousAt.mpr fun a => ?_
  have hev : ∀ᶠ b in 𝓝 a, ((η b : ℂˣ) : ℂ) = ((η a : ℂˣ) : ℂ) := by
    have hmem : (fun u => a * u) '' V ∈ 𝓝 a :=
      ((Homeomorph.mulLeft a).isOpenMap _ hV).mem_nhds ⟨1, h1V, by simp⟩
    filter_upwards [hmem] with b hb
    obtain ⟨u, hu, rfl⟩ := hb
    rw [map_mul, hVker u hu, mul_one]
  exact continuousAt_const.congr (Filter.EventuallyEq.symm hev)

theorem norm_char_eq_one_of_valued_eq_one (η : Fˣ →* ℂˣ) {c : ℕ} (hη : ∀ u ∈ higherUnitsAt ℚ p c, η u = 1)
    (u : Fˣ) (hu : Valued.v (u : F) = 1) : ‖((η u : ℂˣ) : ℂ)‖ = 1 := by
  set S : Set Fˣ := {u | Valued.v (u : F) = 1} with hS

  have hSc : IsCompact S := by
    rw [Units.isEmbedding_val₀.isCompact_iff]
    have himg : ((↑) : Fˣ → F) '' S = {x : F | Valued.v x = 1} := by
      ext x
      simp only [Set.mem_image, Set.mem_setOf_eq, hS]
      constructor
      · rintro ⟨u, hu, rfl⟩; exact hu
      · intro hx
        have hx0 : x ≠ 0 := by intro h; rw [h, map_zero] at hx; exact zero_ne_one hx
        exact ⟨Units.mk0 x hx0, hx, rfl⟩
    rw [himg]
    refine (integersPositiveCompacts ℚ p).isCompact.of_isClosed_subset ?_ ?_
    · have : {x : F | Valued.v x = 1} = {x : F | Valued.v.restrict x = Valued.v.restrict (1 : F)} := by
        ext x; simp
      rw [this]
      exact Valued.isClosed_sphere F _
    · intro x hx
      rw [coe_integersPositiveCompacts, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
      exact le_of_eq hx
  obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn (continuous_char p η hη).continuousOn
  have hle : ∀ w ∈ S, ‖((η w : ℂˣ) : ℂ)‖ ≤ 1 := by
    intro w hw
    by_contra hlt
    rw [not_le] at hlt
    have hpow : ∀ j : ℕ, ‖((η w : ℂˣ) : ℂ)‖ ^ j ≤ C := by
      intro j
      have hwj : w ^ j ∈ S := by
        show Valued.v (((w ^ j : Fˣ) : F)) = 1
        rw [Units.val_pow_eq_pow_val, map_pow, hw, one_pow]
      have := hC _ hwj
      rwa [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
    have ht := tendsto_pow_atTop_atTop_of_one_lt hlt
    rw [Filter.tendsto_atTop_atTop] at ht
    obtain ⟨j, hj⟩ := ht (C + 1)
    linarith [hpow j, hj j le_rfl]
  have h1 := hle u hu
  have h2 := hle u⁻¹ (by show Valued.v (((u⁻¹ : Fˣ) : F)) = 1; rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((η u : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  exact le_antisymm h1 (by rwa [inv_le_one₀ hpos] at h2)

theorem norm_char_eq_zpow (η : Fˣ →* ℂˣ) {c : ℕ} (hη : ∀ u ∈ higherUnitsAt ℚ p c, η u = 1)
    (ϖ : Fˣ) (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ)) (a : Fˣ) (k : ℤ)
    (ha : Valued.v (a : F) = WithZero.exp (-k)) : ‖((η a : ℂˣ) : ℂ)‖ = ‖((η ϖ : ℂˣ) : ℂ)‖ ^ k := by
  have hu : Valued.v (((ϖ ^ (-k) * a : Fˣ) : F)) = 1 := by
    rw [Units.val_mul, map_mul, valued_zpow ϖ hϖ, ha, ← WithZero.exp_add]
    simp
  have h := norm_char_eq_one_of_valued_eq_one p η hη _ hu
  rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow] at h
  rw [eq_inv_of_mul_eq_one_right h, _root_.zpow_neg, inv_inv]

end CharNorm

theorem valued_natCast_le_one (j : ℕ) : Valued.v ((j : F)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    push_cast
    exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

theorem norm_addChar_le_one (ϖ : Fˣ) (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ))
    (θ : AddChar F ℂ) (hθ : Continuous θ) (w : F) : ‖θ w‖ ≤ 1 := by

  have hw0 : ∃ k : ℤ, w ∈ ball p k := by
    by_cases hw : w = 0
    · exact ⟨0, by simp [hw, mem_ball]⟩
    · exact ⟨WithZero.log (Valued.v w), by
        rw [mem_ball, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hw)]⟩
  obtain ⟨k, hk⟩ := hw0
  have hcpt : IsCompact (ball p k) := isCompact_ball p (ϖ ^ (-k)) (by rw [valued_zpow ϖ hϖ, neg_neg])
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hθ.continuousOn
  by_contra hlt
  rw [not_le] at hlt
  have hpow : ∀ j : ℕ, ‖θ w‖ ^ j ≤ C := by
    intro j
    have hju : (j : F) * w ∈ ball p k := by
      rw [mem_ball, map_mul]
      calc Valued.v (j : F) * Valued.v w ≤ 1 * Valued.v w := mul_le_mul_left (valued_natCast_le_one p j) _
        _ ≤ WithZero.exp k := by rw [one_mul]; exact hk
    have := hC _ hju
    rwa [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow] at this
  have ht := tendsto_pow_atTop_atTop_of_one_lt hlt
  rw [Filter.tendsto_atTop_atTop] at ht
  obtain ⟨j, hj⟩ := ht (C + 1)
  linarith [hpow j, hj j le_rfl]

def shell (m : ℤ) : Set F := {y | Valued.v y = WithZero.exp m}

theorem mem_shell {m : ℤ} {y : F} : y ∈ shell p m ↔ Valued.v y = WithZero.exp m := Iff.rfl

theorem shell_subset_ball (m : ℤ) : shell p m ⊆ ball p m := fun _ hy => le_of_eq hy

theorem isClosed_shell (ϖ : Fˣ) (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ)) (m : ℤ) : IsClosed (shell p m) := by
  have : shell p m = {y : F | Valued.v.restrict y = Valued.v.restrict (((ϖ ^ (-m) : Fˣ) : F))} := by
    ext y
    rw [mem_shell, Set.mem_setOf_eq, Valuation.restrict_inj, valued_zpow ϖ hϖ, neg_neg]
  rw [this]
  exact Valued.isClosed_sphere F _

theorem isCompact_shell (ϖ : Fˣ) (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ)) (m : ℤ) : IsCompact (shell p m) :=
  (isCompact_ball p (ϖ ^ (-m)) (by rw [valued_zpow ϖ hϖ, neg_neg])).of_isClosed_subset
    (isClosed_shell p ϖ hϖ m) (shell_subset_ball p m)

theorem measureReal_ball (ϖ : Fˣ) (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ))
    (ν : Measure F) [ν.IsAddHaarMeasure] (m : ℤ) :
    ν.real (ball p m) = qR p ^ m * ν.real (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F) := by
  have hv : Valued.v (((ϖ ^ (-m) : Fˣ) : F)) = WithZero.exp m := by rw [valued_zpow ϖ hϖ, neg_neg]
  rw [ball_eq_smul p (ϖ ^ (-m)) hv, Measure.real,
    ← MeasureTheory.distribHaarChar_mul ν (ϖ ^ (-m)) (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F),
    ← modulus_coe_units,
    LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, ENNReal.toReal_mul, Measure.real]
  congr 1
  rw [ENNReal.coe_toReal, coe_nnnorm, norm_eq_zpow_of_valued p hv]

theorem measureReal_shell_le (ϖ : Fˣ) (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ))
    (ν : Measure F) [ν.IsAddHaarMeasure] (m : ℤ) :
    ν.real (shell p m) ≤ qR p ^ m * ν.real (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F) := by
  rw [← measureReal_ball p ϖ hϖ ν m]
  exact measureReal_mono (shell_subset_ball p m)
    ((isCompact_ball p (ϖ ^ (-m)) (by rw [valued_zpow ϖ hϖ, neg_neg])).measure_lt_top.ne)

theorem norm_apply_weyl_upper_of_mem_shell (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (ϖ : Fˣ) (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ))
    {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (g : G) {k₀ : ℕ}
    (hk₀ : ∀ t : F, Valued.v t ≤ WithZero.exp (-(k₀ : ℤ)) → f (lowerUnip p t * g) = f g)
    {m : ℕ} (hm : k₀ ≤ m) {y : F} (hy : y ∈ shell p m) :
    ‖f (antidiagonal2 p * upperUnipotent2 p y * g)‖ =
      (‖((χ 0 ϖ : ℂˣ) : ℂ)‖ / ‖((χ 1 ϖ : ℂˣ) : ℂ)‖) ^ m * (qR p ^ m)⁻¹ * ‖f g‖ := by
  rw [mem_shell] at hy
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy; exact WithZero.exp_ne_zero hy.symm
  have hyi : Valued.v y⁻¹ = WithZero.exp (-(m : ℤ)) := by rw [map_inv₀, hy, WithZero.exp_neg]
  have hsmall : f (lowerUnip p y⁻¹ * g) = f g := hk₀ _ (by rw [hyi, WithZero.exp_le_exp]; omega)
  rw [apply_weyl_upper p χ hf y hy0 g, hsmall, norm_mul, norm_mul, norm_mul]
  have h0 : ‖((χ 0 (Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy0))) : ℂˣ) : ℂ)‖ =
      ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ ^ (m : ℤ) :=
    norm_char_eq_zpow p (χ 0) (hcχ 0) ϖ hϖ _ m (by rw [Units.val_mk0, Valuation.map_neg, hyi])
  have h1 : ‖(((χ 1) (Units.mk0 y hy0) : ℂˣ) : ℂ)‖ = ‖((χ 1 ϖ : ℂˣ) : ℂ)‖ ^ (-(m : ℤ)) :=
    norm_char_eq_zpow p (χ 1) (hcχ 1) ϖ hϖ _ (-(m : ℤ)) (by rw [Units.val_mk0, hy, neg_neg])
  have hq : ‖(((‖y‖⁻¹ : ℝ) : ℂ))‖ = (qR p ^ m)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      norm_eq_zpow_of_valued p hy, zpow_natCast]
  rw [h0, h1, hq, zpow_natCast, _root_.zpow_neg, zpow_natCast, div_pow]
  ring

theorem integrable_jacquet (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (ϖ : Fˣ) (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ))
    (hdom : ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ < ‖((χ 1 ϖ : ℂˣ) : ℂ)‖)
    {f : G → ℂ} (hf : f ∈ principalSeries2 p χ)
    (θ : AddChar F ℂ) (hθ : Continuous θ) (g : G)
    (ν : Measure F) [ν.IsAddHaarMeasure] :
    Integrable (fun y : F => f (antidiagonal2 p * upperUnipotent2 p y * g) * θ y) ν := by
  set Φ : F → ℂ := fun y => f (antidiagonal2 p * upperUnipotent2 p y * g) * θ y with hΦ
  obtain ⟨hlc, -, -⟩ := mem_principalSeries2_iff.mp hf
  have hΦc : Continuous Φ :=
    (hlc.continuous.comp ((continuous_const.mul (continuous_upperUnipotent2 p)).mul continuous_const)).mul hθ
  obtain ⟨k₀, hk₀⟩ := exists_radius_lowerUnip p χ hf g

  set r : ℝ := ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ / ‖((χ 1 ϖ : ℂˣ) : ℂ)‖ with hr
  have h1pos : 0 < ‖((χ 1 ϖ : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg _) h1pos.le
  have hr1 : r < 1 := (div_lt_one h1pos).mpr hdom
  set V : ℝ := ν.real (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F) with hV

  have hcover : (Set.univ : Set F) = ball p k₀ ∪ ⋃ j : ℕ, shell p ((k₀ + 1 + j : ℕ) : ℤ) := by
    refine (Set.eq_univ_of_forall fun y => ?_).symm
    by_cases hy : Valued.v y ≤ WithZero.exp (k₀ : ℤ)
    · exact Or.inl hy
    · right
      rw [not_le] at hy
      have hy0 : Valued.v y ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' hy)
      set L : ℤ := WithZero.log (Valued.v y) with hLdef
      have hlog : Valued.v y = WithZero.exp L := (WithZero.exp_log hy0).symm
      have hL : (k₀ : ℤ) < L := (WithZero.lt_log_iff_exp_lt hy0).mpr hy
      refine Set.mem_iUnion.mpr ⟨(L - k₀ - 1).toNat, ?_⟩
      rw [mem_shell, hlog]
      congr 1
      push_cast
      omega

  have hnear : IntegrableOn Φ (ball p k₀) ν :=
    hΦc.continuousOn.integrableOn_compact (isCompact_ball p (ϖ ^ (-(k₀ : ℤ))) (by rw [valued_zpow ϖ hϖ, neg_neg]))

  have hfar : IntegrableOn Φ (⋃ j : ℕ, shell p ((k₀ + 1 + j : ℕ) : ℤ)) ν := by
    refine integrableOn_iUnion_of_summable_integral_norm
      (fun j => hΦc.continuousOn.integrableOn_compact (isCompact_shell p ϖ hϖ _)) ?_
    have hbound : ∀ j : ℕ, ∫ y in shell p ((k₀ + 1 + j : ℕ) : ℤ), ‖Φ y‖ ∂ν ≤ (‖f g‖ * V * r ^ (k₀ + 1)) * r ^ j := by
      intro j
      set m : ℕ := k₀ + 1 + j with hm
      have hCm : 0 ≤ r ^ m * (qR p ^ m)⁻¹ * ‖f g‖ :=
        mul_nonneg (mul_nonneg (pow_nonneg hr0 m) (inv_nonneg.mpr (pow_nonneg (qR_pos p).le m))) (norm_nonneg _)
      have hpt : ∀ y ∈ shell p (m : ℤ), ‖(fun y => ‖Φ y‖) y‖ ≤ r ^ m * (qR p ^ m)⁻¹ * ‖f g‖ := by
        intro y hy
        rw [Real.norm_of_nonneg (norm_nonneg _), hΦ]
        simp only
        rw [norm_mul, norm_apply_weyl_upper_of_mem_shell p χ cχ hcχ ϖ hϖ hf g hk₀ (by omega) hy]
        calc _ ≤ r ^ m * (qR p ^ m)⁻¹ * ‖f g‖ * 1 :=
              mul_le_mul_of_nonneg_left (norm_addChar_le_one p ϖ hϖ θ hθ y) hCm
          _ = _ := mul_one _
      have hI := norm_setIntegral_le_of_norm_le_const ((isCompact_shell p ϖ hϖ (m : ℤ)).measure_lt_top (μ := ν)) hpt
      have hle : ∫ y in shell p (m : ℤ), ‖Φ y‖ ∂ν ≤ r ^ m * (qR p ^ m)⁻¹ * ‖f g‖ * ν.real (shell p (m : ℤ)) :=
        (Real.le_norm_self _).trans hI
      refine hle.trans ?_
      have hsh := measureReal_shell_le p ϖ hϖ ν (m : ℤ)
      rw [zpow_natCast] at hsh
      have hqm : 0 < qR p ^ m := pow_pos (qR_pos p) m
      calc r ^ m * (qR p ^ m)⁻¹ * ‖f g‖ * ν.real (shell p (m : ℤ))
          ≤ r ^ m * (qR p ^ m)⁻¹ * ‖f g‖ * (qR p ^ m * V) :=
            mul_le_mul_of_nonneg_left hsh hCm
        _ = ‖f g‖ * V * r ^ m := by field_simp
        _ = (‖f g‖ * V * r ^ (k₀ + 1)) * r ^ j := by rw [hm, pow_add]; ring
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun y => norm_nonneg _) hbound ?_
    exact (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have huniv : IntegrableOn Φ Set.univ ν := by
    rw [hcover]
    exact hnear.union hfar
  exact integrableOn_univ.mp huniv

end LTJacquetConv
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2.LTJacquetConv"

open LTJacquetConv in
theorem solution (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (ϖ : (p.adicCompletion ℚ)ˣ) (hϖ : Valued.v (ϖ : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hdom : ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ < ‖((χ 1 ϖ : ℂˣ) : ℂ)‖)
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (θ : AddChar (p.adicCompletion ℚ) ℂ) (hθ : Continuous θ)
    (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    letI := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      Integrable (fun y : p.adicCompletion ℚ => f (w₀ * unipotentGL2 y * g) * θ y) ν := by
  intro ν _
  have hw := eq_antidiagonal2 p w₀ hw₀
  subst hw
  simp_rw [unipotentGL2_eq p]
  exact integrable_jacquet p χ cχ hcχ ϖ hϖ hdom hf θ hθ g ν

end
end S_LanglandsTunnell_CubicInduction_integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2 (solution)
