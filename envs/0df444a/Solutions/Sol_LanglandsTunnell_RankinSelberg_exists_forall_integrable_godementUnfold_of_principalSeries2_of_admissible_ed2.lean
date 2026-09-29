-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_godementUnfold_of_principalSeries2_of_admissible_ed2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/98246298-eafc-5031-a813-73ac6f6bb359

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_lintegral_enorm_jacquetIntegral_mul_whittaker_mul_translate_mul_row_le_of_admissible_of_chamber
import Theorems.Thm_AutomorphicForm_lintegral_indicator_norm_le_mul_norm_det_rpow_lt_top
import Theorems.Thm_LanglandsTunnell_RankinSelberg_aestronglyMeasurable_godementUnfold_integrand
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_jacquetIntegral_mul_whittaker_mul_row_withDensity_of_admissible_of_chamber
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_godementUnfold_of_principalSeries2_of_admissible_ed2
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_godementUnfold_of_principalSeries2_of_admissible_ed2.LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction"

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts RankinSelberg.exists_forall_lintegral_enorm_jacquetIntegral_mul_whittaker_mul_translate_mul_row_le_of_admissible_of_chamber RankinSelberg.aestronglyMeasurable_godementUnfold_integrand RankinSelberg.exists_forall_integrable_jacquetIntegral_mul_whittaker_mul_row_withDensity_of_admissible_of_chamber TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "exists_forall_lintegral_enorm_jacquetIntegral_mul_whittaker_mul_translate_mul_row_le_of_admissible_of_chamber aestronglyMeasurable_godementUnfold_integrand exists_forall_integrable_jacquetIntegral_mul_whittaker_mul_row_withDensity_of_admissible_of_chamber"
namespace B4Asm
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

section Valuation
open scoped WithZero

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem exists_uniformizer :
    ∃ ϖ : v.adicCompletion K, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K v
  exact ⟨((WithVal.equiv (HeightOneSpectrum.valuation K v)).symm π : v.adicCompletion K),
    by rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ⟩

variable {K v}

theorem uniformizer_ne_zero {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    ϖ ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm

theorem v_uniformizer_zpow {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (j : ℤ) : Valued.v (ϖ ^ j) = WithZero.exp (-j) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem v_uniformizer_pow {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (n : ℕ) : Valued.v (ϖ ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [← zpow_natCast, v_uniformizer_zpow hϖ]

theorem v_add_le {x y : v.adicCompletion K} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x + y) ≤ γ :=
  (Valuation.map_add _ x y).trans (max_le hx hy)

theorem v_sub_le {x y : v.adicCompletion K} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x - y) ≤ γ := by
  rw [sub_eq_add_neg]; exact v_add_le hx (by rwa [Valuation.map_neg])

theorem v_mul_le {x y : v.adicCompletion K} {a b : ℤ} (hx : Valued.v x ≤ WithZero.exp a)
    (hy : Valued.v y ≤ WithZero.exp b) : Valued.v (x * y) ≤ WithZero.exp (a + b) := by
  rw [Valuation.map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

theorem exp_neg_succ_lt_one (n : ℕ) : WithZero.exp (-((n : ℤ) + 1)) < (1 : ℤᵐ⁰) := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

theorem exp_neg_succ_le_one (n : ℕ) : WithZero.exp (-((n : ℤ) + 1)) ≤ (1 : ℤᵐ⁰) :=
  (exp_neg_succ_lt_one n).le

theorem exp_antitone_succ (n : ℕ) :
    WithZero.exp (-(((n + 1 : ℕ) : ℤ) + 1)) ≤ WithZero.exp (-((n : ℤ) + 1)) := by
  rw [WithZero.exp_le_exp]; push_cast; omega

theorem v_lt_one_iff (x : v.adicCompletion K) :
    Valued.v x < 1 ↔ Valued.v x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hx : Valued.v x = 0
  · simp [hx]
  · rw [← WithZero.exp_log hx, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem eq_zero_of_forall_v_le (x : v.adicCompletion K)
    (h : ∀ n : ℕ, Valued.v x ≤ WithZero.exp (-((n : ℤ) + 1))) : x = 0 := by
  by_contra hx
  have hx' : Valued.v x ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
  set L := WithZero.log (Valued.v x) with hL
  have hxL : Valued.v x = WithZero.exp L := (WithZero.exp_log hx').symm
  have := h ((-L).toNat)
  rw [hxL, WithZero.exp_le_exp] at this
  omega

theorem v_eq_one_of_sub_one {x : v.adicCompletion K} {n : ℕ}
    (hx : Valued.v (x - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) : Valued.v x = 1 := by
  have : x = 1 + (x - 1) := by ring
  rw [this]
  exact Valuation.map_one_add_of_lt _ (hx.trans_lt (exp_neg_succ_lt_one n))

theorem ne_zero_of_v_eq_one {x : v.adicCompletion K} (hx : Valued.v x = 1) : x ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hx; exact zero_ne_one hx

theorem v_inv_sub_one {x : v.adicCompletion K} {n : ℕ}
    (hx : Valued.v (x - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) :
    Valued.v (x⁻¹ - 1) ≤ WithZero.exp (-((n : ℤ) + 1)) := by
  have h1 := v_eq_one_of_sub_one hx
  have hx0 := ne_zero_of_v_eq_one h1
  have : x⁻¹ - 1 = x⁻¹ * (-(x - 1)) := by field_simp; ring
  rw [this, Valuation.map_mul, Valuation.map_neg, map_inv₀, h1, inv_one, one_mul]
  exact hx

theorem isOpen_ball (m : ℤ) : IsOpen {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer K v
  have hϖ0 : ϖ ≠ 0 := uniformizer_ne_zero hϖ
  have hset : {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp m} =
      (fun x => ϖ ^ m * x) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, v_uniformizer_zpow hϖ,
      WithZero.exp_neg]
    constructor
    · intro h
      calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m :=
            mul_le_mul_right h _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · intro h
      calc Valued.v x = WithZero.exp m * ((WithZero.exp m)⁻¹ * Valued.v x) := by
            rw [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul]
        _ ≤ WithZero.exp m * 1 := mul_le_mul_right h _
        _ = WithZero.exp m := mul_one _
  rw [hset]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_const_mul _)

theorem exists_eq_zpow_mul (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (y : v.adicCompletion K) (hy : y ≠ 0) :
    ∃ (j : ℤ) (t : v.adicCompletion K), Valued.v t = 1 ∧ y = ϖ ^ j * t ∧
      Valued.v y = WithZero.exp (-j) := by
  have hϖ0 : ϖ ≠ 0 := uniformizer_ne_zero hϖ
  have hy' : Valued.v y ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
  set L := WithZero.log (Valued.v y) with hL
  have hyL : Valued.v y = WithZero.exp L := (WithZero.exp_log hy').symm
  refine ⟨-L, ϖ ^ L * y, ?_, ?_, ?_⟩
  · rw [Valuation.map_mul, v_uniformizer_zpow hϖ, hyL, ← WithZero.exp_add, neg_add_cancel,
      WithZero.exp_zero]
  · rw [zpow_neg, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hϖ0), one_mul]
  · rw [neg_neg, hyL]

end Valuation

section CharNorm

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ

theorem exists_eq_zpow_mul_unit (π : (F)ˣ) (hπ : Valued.v (π : F) = WithZero.exp (-1 : ℤ)) (y : (F)ˣ) :
    ∃ (m : ℤ) (u : (F)ˣ), Valued.v (u : F) = 1 ∧ y = π ^ m * u := by
  have hvy : Valued.v (y : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  set m : ℤ := -WithZero.log (Valued.v (y : F)) with hm
  have hvπm : Valued.v (((π ^ m : (F)ˣ)) : F) = Valued.v (y : F) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, hm, neg_neg,
      WithZero.exp_log hvy]
  refine ⟨m, (π ^ m)⁻¹ * y, ?_, (mul_inv_cancel_left (π ^ m) y).symm⟩
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvπm, inv_mul_cancel₀ hvy]

theorem v_zpow_mul_unit (π : (F)ˣ) (hπ : Valued.v (π : F) = WithZero.exp (-1 : ℤ)) (m : ℤ) (u : (F)ˣ)
    (hu : Valued.v (u : F) = 1) : Valued.v (((π ^ m * u : (F)ˣ)) : F) = WithZero.exp (-m) := by
  rw [Units.val_mul, map_mul, hu, mul_one, Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul,
    mul_neg, mul_one]

def qR : ℝ := ((Ideal.absNorm p.asIdeal : NNReal) : ℝ)

theorem one_lt_qR : 1 < qR p := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p
  unfold qR; exact_mod_cast this

theorem norm_eq_qR_zpow (y : F) (j : ℤ) (hy : Valued.v y = WithZero.exp (-j)) : ‖y‖ = qR p ^ (-j) := by
  rw [NumberField.FinitePlace.norm_def, hy, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, NNReal.coe_zpow]
  unfold qR
  congr 1

theorem norm_eq_one_of_v (u : F) (hu : Valued.v u = 1) : ‖u‖ = 1 := by
  have := norm_eq_qR_zpow p u 0 (by rw [hu, neg_zero, WithZero.exp_zero])
  rw [this, neg_zero, zpow_zero]

theorem isCompact_units_sphere : IsCompact {u : (F)ˣ | Valued.v (u : F) = 1} := by
  have hO : IsCompact ((p.adicCompletionIntegers ℚ : Set F)) := by
    rw [← LanglandsTunnell.TateLocal.coe_integersPositiveCompacts]
    exact (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ p).isCompact
  have hS : IsCompact {x : F | Valued.v x = 1} := by
    refine hO.of_isClosed_subset ?_ (fun x hx => by
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]; exact le_of_eq hx)
    have ho : IsOpen {x : F | Valued.v x = 1}ᶜ := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      rw [Set.mem_compl_iff, Set.mem_setOf_eq] at hx
      by_cases hx0 : (Valued.v x : WithZero (Multiplicative ℤ)) = 0
      · have h0 : x = 0 := (Valuation.zero_iff _).1 hx0
        subst h0
        have hball : {y : F | Valued.v y ≤ WithZero.exp (-1 : ℤ)} ∈ nhds (0 : F) :=
          (isOpen_ball (K := ℚ) (v := p) (-1)).mem_nhds (by simp)
        refine Filter.mem_of_superset hball fun y hy => ?_
        rw [Set.mem_compl_iff, Set.mem_setOf_eq]
        intro h1
        rw [Set.mem_setOf_eq, h1, ← WithZero.exp_zero, WithZero.exp_le_exp] at hy
        omega
      · have h := Valued.locally_const hx0
        refine Filter.mem_of_superset h fun y hy => ?_
        rw [Set.mem_compl_iff, Set.mem_setOf_eq]
        rw [Set.mem_setOf_eq] at hy
        rw [hy]; exact hx
    exact ⟨ho⟩
  have himage : (Units.val : (F)ˣ → F) '' {u : (F)ˣ | Valued.v (u : F) = 1} = {x : F | Valued.v x = 1} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hx
      have hx0 : x ≠ 0 := by intro h; rw [h, Valuation.map_zero] at hx; exact zero_ne_one hx
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [(Units.isEmbedding_val₀ (G₀ := F)).isCompact_iff, himage]
  exact hS

theorem norm_char_unit_eq_one (θ : (F)ˣ →* ℂˣ) (hcont : Continuous fun t : (F)ˣ => ((θ t : ℂˣ) : ℂ))
    (u : (F)ˣ) (hu : Valued.v (u : F) = 1) : ‖((θ u : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨M, hM⟩ := (isCompact_units_sphere p).exists_bound_of_continuousOn hcont.continuousOn
  have hpow : ∀ (w : (F)ˣ), Valued.v (w : F) = 1 → ∀ k : ℕ, ‖((θ w : ℂˣ) : ℂ)‖ ^ k ≤ M := by
    intro w hw k
    have hmem : w ^ k ∈ {u : (F)ˣ | Valued.v (u : F) = 1} := by
      show Valued.v (((w ^ k : (F)ˣ)) : F) = 1
      rw [Units.val_pow_eq_pow_val, map_pow, hw, one_pow]
    have := hM _ hmem
    rwa [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  have hle : ∀ (w : (F)ˣ), Valued.v (w : F) = 1 → ‖((θ w : ℂˣ) : ℂ)‖ ≤ 1 := by
    intro w hw
    by_contra h
    push Not at h
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M h
    exact absurd (hpow w hw k) (not_le.2 hk)
  have h1 := hle u hu
  have h2 := hle u⁻¹ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((θ u : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (θ u).ne_zero
  have h3 : 1 ≤ ‖((θ u : ℂˣ) : ℂ)‖ := by rwa [inv_le_one₀ hpos] at h2
  exact le_antisymm h1 h3

theorem norm_char_zpow_mul_unit (θ : (F)ˣ →* ℂˣ) (hcont : Continuous fun t : (F)ˣ => ((θ t : ℂˣ) : ℂ))
    (π : (F)ˣ) (m : ℤ) (u : (F)ˣ) (hu : Valued.v (u : F) = 1) :
    ‖((θ (π ^ m * u) : ℂˣ) : ℂ)‖ = ‖((θ π : ℂˣ) : ℂ)‖ ^ m := by
  rw [map_mul, map_zpow, Units.val_mul, norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow,
    norm_char_unit_eq_one p θ hcont u hu, mul_one]

theorem zpow_eq_rpow (c : ℝ) (hc : 0 < c) (m : ℤ) :
    c ^ m = (qR p ^ (-m)) ^ (-Real.log c / Real.log (qR p)) := by
  have hq : 1 < qR p := one_lt_qR p
  have hq0 : 0 < qR p := zero_lt_one.trans hq
  have hlogq : Real.log (qR p) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hq0 hq.ne'
  rw [← Real.rpow_intCast (qR p) (-m), ← Real.rpow_mul hq0.le, Real.rpow_def_of_pos hq0,
    ← Real.rpow_intCast c m, Real.rpow_def_of_pos hc]
  congr 1
  field_simp
  push_cast
  ring

theorem exists_norm_char_eq_rpow (χ : (F)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ σχ : ℝ, ∀ a : (F)ˣ, ‖((χ a : ℂˣ) : ℂ)‖ = ‖(a : F)‖ ^ σχ := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer ℚ p
  have hϖ0 : ϖ ≠ 0 := uniformizer_ne_zero hϖ
  set π : (F)ˣ := Units.mk0 ϖ hϖ0 with hπdef
  have hπ : Valued.v (π : F) = WithZero.exp (-1 : ℤ) := hϖ
  have hcont : Continuous fun t : (F)ˣ => ((χ t : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (continuous_def.2 fun s _ => hχ s)
  refine ⟨-Real.log ‖((χ π : ℂˣ) : ℂ)‖ / Real.log (qR p), fun a => ?_⟩
  obtain ⟨m, u, hu, rfl⟩ := exists_eq_zpow_mul_unit p π hπ a
  rw [norm_char_zpow_mul_unit p χ hcont π m u hu, norm_eq_qR_zpow p _ m (v_zpow_mul_unit p π hπ m u hu)]
  exact zpow_eq_rpow p _ (norm_pos_iff.2 (χ π).ne_zero) m

end CharNorm

section Span

variable {G : Type*} [Group G]

theorem comp_mul_mem_span (w : G → ℂ) {w' : G → ℂ}
    (hw' : w' ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))) (h : G) :
    (fun g => w' (g * h)) ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)) := by
  let R : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun f g => f (g * h), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hR : R w' ∈ (Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))).map R :=
    Submodule.mem_map_of_mem hw'
  rw [Submodule.map_span] at hR
  refine (Submodule.span_mono ?_) hR
  rintro _ ⟨_, ⟨h', rfl⟩, rfl⟩
  exact ⟨h * h', by funext g; simp [R, mul_assoc]⟩

theorem span_translates_le (w : G → ℂ) {w' : G → ℂ}
    (hw' : w' ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))) :
    Submodule.span ℂ (Set.range fun h : G => fun g : G => w' (g * h)) ≤
      Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)) :=
  Submodule.span_le.mpr (by rintro _ ⟨h, rfl⟩; exact comp_mul_mem_span w hw' h)

theorem law_of_mem_span (w : G → ℂ) (a : G) (c : ℂ) (hw : ∀ g : G, w (a * g) = c * w g) {w' : G → ℂ}
    (hw' : w' ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))) :
    ∀ g : G, w' (a * g) = c * w' g := by
  induction hw' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    intro g
    show w (a * g * h) = c * w (g * h)
    rw [mul_assoc, hw]
  | zero => intro g; simp
  | add x y _ _ hx hy => intro g; simp only [Pi.add_apply, hx, hy, mul_add]
  | smul r x _ hx => intro g; simp only [Pi.smul_apply, smul_eq_mul, hx]; ring

theorem smooth_of_mem_span [TopologicalSpace G] [ContinuousMul G] (w : G → ℂ)
    (hwsm : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, w (g * k) = w g) {w' : G → ℂ}
    (hw' : w' ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, w' (g * k) = w' g := by
  induction hw' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    obtain ⟨U, hUo, hU⟩ := hwsm
    refine ⟨U.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
    · have hc : Continuous fun k : G => h⁻¹ * k * h⁻¹⁻¹ := (continuous_const.mul continuous_id).mul continuous_const
      have : ((U.comap (MulAut.conj h⁻¹).toMonoidHom : Subgroup G) : Set G) = (fun k : G => h⁻¹ * k * h⁻¹⁻¹) ⁻¹' (U : Set G) := by
        ext k; simp [Subgroup.coe_comap, MulAut.conj_apply]
      rw [this]
      exact hUo.preimage hc
    · intro k hk g
      have hk' : h⁻¹ * k * h ∈ U := by simpa [Subgroup.mem_comap, MulAut.conj_apply] using hk
      show w (g * k * h) = w (g * h)
      have := hU _ hk' (g * h)
      rw [← this]
      congr 1
      group
  | zero => exact ⟨⊤, by simp, fun _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨U₁, h₁o, h₁⟩ := hx
    obtain ⟨U₂, h₂o, h₂⟩ := hy
    refine ⟨U₁ ⊓ U₂, ?_, fun k hk g => ?_⟩
    · rw [Subgroup.coe_inf]; exact h₁o.inter h₂o
    · simp only [Pi.add_apply, h₁ k (Subgroup.mem_inf.1 hk).1 g, h₂ k (Subgroup.mem_inf.1 hk).2 g]
  | smul r x _ hx =>
    obtain ⟨U, ho, hU⟩ := hx
    exact ⟨U, ho, fun k hk g => by simp only [Pi.smul_apply, hU k hk g]⟩

theorem adm_of_mem_span [TopologicalSpace G] (w : G → ℂ)
    (hwadm : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ B : Finset (G → ℂ),
      ∀ w' ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)),
        (∀ k ∈ U, ∀ g : G, w' (g * k) = w' g) → w' ∈ Submodule.span ℂ (B : Set (G → ℂ)))
    {w' : G → ℂ} (hw' : w' ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))) :
    ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ B : Finset (G → ℂ),
      ∀ w'' ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w' (g * h)),
        (∀ k ∈ U, ∀ g : G, w'' (g * k) = w'' g) → w'' ∈ Submodule.span ℂ (B : Set (G → ℂ)) := by
  intro U hU
  obtain ⟨B, hB⟩ := hwadm U hU
  exact ⟨B, fun w'' hw'' hinv => hB w'' (span_translates_le w hw' hw'') hinv⟩

end Span

section RealIneq

theorem rpow_le_of_mem {y q : ℝ} (hq : 1 ≤ q) (hy0 : 0 < y) (hy1 : y ≤ 1) (hyq : q⁻¹ ≤ y) (τ : ℝ) :
    y ^ τ ≤ q ^ |τ| := by
  rcases le_or_gt 0 τ with hτ | hτ
  · calc y ^ τ ≤ 1 := Real.rpow_le_one hy0.le hy1 hτ
      _ ≤ q ^ |τ| := Real.one_le_rpow hq (abs_nonneg τ)
  · have hq0 : 0 < q := by linarith
    calc y ^ τ ≤ (q⁻¹) ^ τ := Real.rpow_le_rpow_of_nonpos (inv_pos.2 hq0) hyq hτ.le
      _ = q ^ |τ| := by rw [Real.inv_rpow hq0.le, ← Real.rpow_neg hq0.le, abs_of_neg hτ]

theorem rpow_le_of_mem_Icc {x M q : ℝ} (hM : 1 ≤ M) (hq : 1 ≤ q) (hx0 : 0 < x) (hxM : x ≤ M) (hqx : M / q ≤ x)
    (τ : ℝ) : x ^ τ ≤ M ^ |τ| * q ^ |τ| := by
  have hM0 : 0 < M := by linarith
  have hq0 : 0 < q := by linarith
  have hx : x = M * (x / M) := by field_simp
  have h1 : (x / M) ^ τ ≤ q ^ |τ| := by
    refine rpow_le_of_mem hq (div_pos hx0 hM0) ((div_le_one hM0).2 hxM) ?_ τ
    rw [le_div_iff₀ hM0]
    calc q⁻¹ * M = M / q := by ring
      _ ≤ x := hqx
  have h2 : M ^ τ ≤ M ^ |τ| := Real.rpow_le_rpow_of_exponent_le hM (le_abs_self τ)
  rw [hx, Real.mul_rpow hM0.le (div_pos hx0 hM0).le]
  exact mul_le_mul h2 h1 (Real.rpow_nonneg (div_pos hx0 hM0).le τ) (Real.rpow_nonneg hM0.le _)

theorem loss_le (B τ : ℝ) (A : ℕ) {n d : ℝ} (hn : 0 < n) (hd : 0 < d) (hnB : n ≤ B) (hdn : d ≤ n ^ 2) :
    max (n ^ τ) ((d / n) ^ τ) * max 1 (((d / n ^ 2) ^ A)⁻¹) ≤
      (max 1 B) ^ (3 * |τ| + 2 * (A : ℝ)) * d ^ (-(|τ| + (A : ℝ))) := by
  set M : ℝ := max 1 B with hMdef
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := by linarith
  have hnM : n ≤ M := hnB.trans (le_max_right _ _)
  have hdM2 : d ≤ M ^ 2 := hdn.trans (by nlinarith)

  set q : ℝ := M ^ 2 / d with hqdef
  have hq : 1 ≤ q := by rw [hqdef, one_le_div hd]; exact hdM2
  have hq0 : 0 < q := by linarith
  have hMq : M / q = d / M := by rw [hqdef]; field_simp

  have hA1 : n ^ τ ≤ M ^ |τ| * q ^ |τ| := by
    refine rpow_le_of_mem_Icc hM hq hn hnM ?_ τ
    rw [hMq, div_le_iff₀ hM0]
    nlinarith
  have hA2 : (d / n) ^ τ ≤ M ^ |τ| * q ^ |τ| := by
    refine rpow_le_of_mem_Icc hM hq (div_pos hd hn) ?_ ?_ τ
    · rw [div_le_iff₀ hn]; nlinarith
    · rw [hMq]; exact div_le_div_of_nonneg_left hd.le hn hnM
  have hA : max (n ^ τ) ((d / n) ^ τ) ≤ M ^ |τ| * q ^ |τ| := max_le hA1 hA2

  have hB' : max 1 (((d / n ^ 2) ^ A)⁻¹) ≤ q ^ (A : ℝ) := by
    refine max_le (Real.one_le_rpow hq (Nat.cast_nonneg A)) ?_
    rw [← inv_pow, inv_div, Real.rpow_natCast]
    refine pow_le_pow_left₀ (div_pos (pow_pos hn 2) hd).le ?_ A
    rw [hqdef]
    exact div_le_div_of_nonneg_right (by nlinarith) hd.le

  have hprod : max (n ^ τ) ((d / n) ^ τ) * max 1 (((d / n ^ 2) ^ A)⁻¹) ≤ (M ^ |τ| * q ^ |τ|) * q ^ (A : ℝ) :=
    mul_le_mul hA hB' (le_trans zero_le_one (le_max_left _ _)) (by positivity)
  refine hprod.trans (le_of_eq ?_)

  rw [hqdef, Real.div_rpow (by positivity) hd.le, Real.div_rpow (by positivity) hd.le,
    show (M ^ 2 : ℝ) = M ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul hM0.le, ← Real.rpow_mul hM0.le,
    Real.rpow_neg hd.le, Real.rpow_add hd]
  have e1 : M ^ (3 * |τ| + 2 * (A : ℝ)) = M ^ |τ| * M ^ (2 * |τ|) * M ^ (2 * (A : ℝ)) := by
    rw [← Real.rpow_add hM0, ← Real.rpow_add hM0]; ring_nf
  rw [e1]
  field_simp

end RealIneq

section Main

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

theorem modulusR_eq_norm (x : (F)ˣ) : ((modulus (x : F) : ℝ)) = ‖(x : F)‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]; rfl

theorem norm_modulus_cpow (x : (F)ˣ) (s : ℂ) : ‖(((modulus (x : F) : ℝ)) : ℂ) ^ s‖ = ‖(x : F)‖ ^ s.re := by
  rw [modulusR_eq_norm, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.2 x.ne_zero)]

theorem enorm_modulus_cpow (x : (F)ˣ) (s : ℂ) :
    ‖(((modulus (x : F) : ℝ)) : ℂ) ^ s‖ₑ = ENNReal.ofReal (‖(x : F)‖ ^ s.re) := by
  rw [← ofReal_norm_eq_enorm, norm_modulus_cpow]

def entryMax (g : G2) : ℝ :=
  max (max ‖(g : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(g : Matrix (Fin 2) (Fin 2) F) 0 1‖)
    (max ‖(g : Matrix (Fin 2) (Fin 2) F) 1 0‖ ‖(g : Matrix (Fin 2) (Fin 2) F) 1 1‖)

def entryMaxM (m : Matrix (Fin 2) (Fin 2) F) : ℝ :=
  max (max ‖m 0 0‖ ‖m 0 1‖) (max ‖m 1 0‖ ‖m 1 1‖)

theorem entryMax_eq (g : G2) : entryMax p g = entryMaxM p (g : Matrix (Fin 2) (Fin 2) F) := rfl

theorem continuous_entryMaxM : Continuous (entryMaxM p) := by
  unfold entryMaxM
  fun_prop

theorem entryMax_nonneg (g : G2) : 0 ≤ entryMax p g :=
  le_trans (norm_nonneg _) (le_trans (le_max_left _ _) (le_max_left _ _))

theorem norm_det_le_entryMax_sq (g : G2) :
    ‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖ ≤ entryMax p g ^ 2 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have h0 := entryMax_nonneg p g
  have e00 : ‖(g : Matrix (Fin 2) (Fin 2) F) 0 0‖ ≤ entryMax p g := le_trans (le_max_left _ _) (le_max_left _ _)
  have e01 : ‖(g : Matrix (Fin 2) (Fin 2) F) 0 1‖ ≤ entryMax p g := le_trans (le_max_right _ _) (le_max_left _ _)
  have e10 : ‖(g : Matrix (Fin 2) (Fin 2) F) 1 0‖ ≤ entryMax p g := le_trans (le_max_left _ _) (le_max_right _ _)
  have e11 : ‖(g : Matrix (Fin 2) (Fin 2) F) 1 1‖ ≤ entryMax p g := le_trans (le_max_right _ _) (le_max_right _ _)
  calc ‖(g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 -
          (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0‖
      ≤ max ‖(g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1‖
          ‖(g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0‖ := by
        rw [sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
        rw [norm_neg]
    _ ≤ entryMax p g ^ 2 := by
        rw [norm_mul, norm_mul, sq]
        exact max_le (mul_le_mul e00 e11 (norm_nonneg _) h0) (mul_le_mul e01 e10 (norm_nonneg _) h0)

theorem partA [SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ))] [LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ))]
    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ₁ : IsLocallyConstant φ₁ ∧ HasCompactSupport φ₁)
    (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (hφ₂ : IsLocallyConstant φ₂ ∧ HasCompactSupport φ₂)
    (θ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (a : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent a * g) = NumberField.StandardAddChar.psiLocal ℚ p a * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hwadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) →
            w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (zc : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = ((θ zc : ℂˣ) : ℂ) * w g)
    (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
    (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure]
    (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [ν.IsHaarMeasure] :
    ∃ σ' : ℝ, ∀ s : ℂ, σ' < s.re →
        Integrable (fun gh : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
            (φ₁ (gh.2 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det gh.2) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det gh.2 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) *
              ((∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x * gh.1) ∂(selfDualHaarAt ℚ p)) *
                w (gh.1 * gh.2) *
                φ₂ ((gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                ((modulus ((Matrix.GeneralLinearGroup.det gh.1 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s))
          ((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)).prod ν) := by

  obtain ⟨σχ, hσχ⟩ := exists_norm_char_eq_rpow p χ hχ
  obtain ⟨σ₀', τ, A, h3⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_lintegral_enorm_jacquetIntegral_mul_whittaker_mul_translate_mul_row_le_of_admissible_of_chamber
      p μ hμ σ hσ h01 φ hφ θ w hwlaw hwsm hwadm hcentral φ₂ hφ₂
  obtain ⟨Mφ, hMφ⟩ : ∃ C : ℝ, ∀ m, ‖φ₁ m‖ ≤ C := hφ₁.2.exists_bound_of_continuous hφ₁.1.continuous
  have hMφ0 : 0 ≤ Mφ := le_trans (norm_nonneg _) (hMφ 0)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ m ∈ tsupport φ₁, ‖entryMaxM p m‖ ≤ B :=
    hφ₁.2.isCompact.exists_bound_of_continuousOn (continuous_entryMaxM p).continuousOn
  set K : ℝ := (max 1 B) ^ (3 * |τ| + 2 * (A : ℝ)) with hKdef
  have hK0 : 0 ≤ K := Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  refine ⟨max σ₀' (1 / 2 - σχ + |τ| + (A : ℝ)), fun s hs => ?_⟩
  have hs3 : σ₀' < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have ht : 1 < s.re + 1 / 2 + σχ - (|τ| + (A : ℝ)) := by
    have := lt_of_le_of_lt (le_max_right _ _) hs; linarith
  obtain ⟨I, hI0, hI⟩ := h3 μ₂ μN₂ s.re hs3
  have h4 := AutomorphicForm.lintegral_indicator_norm_le_mul_norm_det_rpow_lt_top p B
    (s.re + 1 / 2 + σχ - (|τ| + (A : ℝ))) ht ν
  have hmeas := LanglandsTunnell.RankinSelberg.aestronglyMeasurable_godementUnfold_integrand
    p μ hμ σ hσ h01 φ hφ χ hχ φ₁ hφ₁.1 φ₂ hφ₂.1 w hwsm μ₂ μN₂ ν s
  refine ⟨hmeas, ?_⟩

  show ∫⁻ gh, ‖(fun gh : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
              (φ₁ (gh.2 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det gh.2) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det gh.2 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) *
                ((∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                  φ (antidiagonal2 p * upperUnipotent2 p x * gh.1) ∂(selfDualHaarAt ℚ p)) *
                  w (gh.1 * gh.2) *
                  φ₂ ((gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                  ((modulus ((Matrix.GeneralLinearGroup.det gh.1 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s)) gh‖ₑ
      ∂((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)).prod ν) < ⊤
  rw [lintegral_prod_symm _ hmeas.enorm]

  set P2 : Measure G2 := μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂) with hP2
  set Ph : G2 → ℂ := fun h => φ₁ (h : Matrix (Fin 2) (Fin 2) F) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
      ((modulus ((Matrix.GeneralLinearGroup.det h : (F)ˣ) : F) : ℝ) : ℂ) ^ (s + 1 / 2) with hPh
  set Qn : G2 → G2 → ENNReal := fun h g =>
      ‖(∫ x : F, NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) *
          w (g * h) * φ₂ ((g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1)‖ₑ *
        ENNReal.ofReal (‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖ ^ s.re) with hQn
  set Lh : G2 → ℝ := fun h =>
      max (entryMax p h ^ τ) ((‖((Matrix.GeneralLinearGroup.det h : (F)ˣ) : F)‖ / entryMax p h) ^ τ) *
        max 1 (((‖((Matrix.GeneralLinearGroup.det h : (F)ˣ) : F)‖ / entryMax p h ^ 2) ^ A)⁻¹) with hLh
  set bnd : G2 → ENNReal := fun h =>
      Set.indicator {h : G2 | ∀ i j : Fin 2, ‖((h : G2) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ B} (fun _ => (1 : ENNReal)) h *
        ENNReal.ofReal (‖((Matrix.GeneralLinearGroup.det h : (F)ˣ) : F)‖ ^ (s.re + 1 / 2 + σχ - (|τ| + (A : ℝ)))) with hbnd

  have hpt : ∀ h g : G2,
      ‖(fun gh : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
              (φ₁ (gh.2 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det gh.2) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det gh.2 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) *
                ((∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                  φ (antidiagonal2 p * upperUnipotent2 p x * gh.1) ∂(selfDualHaarAt ℚ p)) *
                  w (gh.1 * gh.2) *
                  φ₂ ((gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                  ((modulus ((Matrix.GeneralLinearGroup.det gh.1 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s)) (g, h)‖ₑ = ‖Ph h‖ₑ * Qn h g := by
    intro h g
    simp only [hPh, hQn, enorm_mul, enorm_modulus_cpow]

  have hinner : ∀ h : G2, ∫⁻ g, ‖(fun gh : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
              (φ₁ (gh.2 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det gh.2) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det gh.2 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) *
                ((∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                  φ (antidiagonal2 p * upperUnipotent2 p x * gh.1) ∂(selfDualHaarAt ℚ p)) *
                  w (gh.1 * gh.2) *
                  φ₂ ((gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                  ((modulus ((Matrix.GeneralLinearGroup.det gh.1 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s)) (g, h)‖ₑ ∂P2 ≤ ‖Ph h‖ₑ * ENNReal.ofReal (I * Lh h) := by
    intro h
    calc ∫⁻ g, ‖(fun gh : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
                (φ₁ (gh.2 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det gh.2) : ℂˣ) : ℂ) *
                    ((modulus ((Matrix.GeneralLinearGroup.det gh.2 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) *
                  ((∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * gh.1) ∂(selfDualHaarAt ℚ p)) *
                    w (gh.1 * gh.2) *
                    φ₂ ((gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                    ((modulus ((Matrix.GeneralLinearGroup.det gh.1 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s)) (g, h)‖ₑ ∂P2
        = ∫⁻ g, ‖Ph h‖ₑ * Qn h g ∂P2 := lintegral_congr (fun g => hpt h g)
      _ = ‖Ph h‖ₑ * ∫⁻ g, Qn h g ∂P2 := lintegral_const_mul' _ _ enorm_ne_top
      _ ≤ ‖Ph h‖ₑ * ENNReal.ofReal (I * Lh h) := by
          refine mul_le_mul_right ?_ _
          simpa only [hQn, hLh, hP2, entryMax, enorm_eq_nnnorm, mul_assoc] using hI h

  have hbound : ∀ h : G2, ‖Ph h‖ₑ * ENNReal.ofReal (I * Lh h) ≤ ENNReal.ofReal (Mφ * I * K) * bnd h := by
    intro h
    by_cases hφh : φ₁ (h : Matrix (Fin 2) (Fin 2) F) = 0
    · have : Ph h = 0 := by simp only [hPh, hφh, zero_mul]
      rw [this, enorm_zero, zero_mul]
      exact zero_le

    have hsupp : (h : Matrix (Fin 2) (Fin 2) F) ∈ tsupport φ₁ := subset_tsupport _ hφh
    have hnB' : ‖entryMaxM p (h : Matrix (Fin 2) (Fin 2) F)‖ ≤ B := hB _ hsupp
    have hnB : entryMax p h ≤ B := by
      rw [entryMax_eq]; exact le_trans (Real.le_norm_self _) hnB'
    have hind : Set.indicator {h : G2 | ∀ i j : Fin 2, ‖((h : G2) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ B}
        (fun _ => (1 : ENNReal)) h = 1 := by
      refine Set.indicator_of_mem ?_ _
      intro i j
      refine le_trans ?_ hnB
      fin_cases i <;> fin_cases j
      · exact le_trans (le_max_left _ _) (le_max_left _ _)
      · exact le_trans (le_max_right _ _) (le_max_left _ _)
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
      · exact le_trans (le_max_right _ _) (le_max_right _ _)
    set d : ℝ := ‖((Matrix.GeneralLinearGroup.det h : (F)ˣ) : F)‖ with hd
    have hd0 : 0 < d := norm_pos_iff.2 (Matrix.GeneralLinearGroup.det h).ne_zero
    have hdn : d ≤ entryMax p h ^ 2 := norm_det_le_entryMax_sq p h
    have hn0 : 0 < entryMax p h := by
      rcases (entryMax_nonneg p h).eq_or_lt with h0 | h0
      · exfalso; rw [← h0] at hdn; linarith
      · exact h0
    have hL : Lh h ≤ K * d ^ (-(|τ| + (A : ℝ))) := by
      simp only [hLh, hKdef]
      exact loss_le B τ A hn0 hd0 hnB hdn
    have hLnn : 0 ≤ Lh h := by
      simp only [hLh]
      exact mul_nonneg (le_trans (Real.rpow_nonneg hn0.le τ) (le_max_left _ _)) (le_trans zero_le_one (le_max_left _ _))
    have hP : ‖Ph h‖ = ‖φ₁ (h : Matrix (Fin 2) (Fin 2) F)‖ * d ^ σχ * d ^ (s.re + 1 / 2) := by
      have hre : (s + 1 / 2 : ℂ).re = s.re + 1 / 2 := by simp
      simp only [hPh, norm_mul, hσχ, norm_modulus_cpow, hre, hd]
    simp only [hbnd]
    rw [hind, one_mul, ← hd, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hMφ0 hI0) hK0)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hP]
    calc ‖φ₁ (h : Matrix (Fin 2) (Fin 2) F)‖ * d ^ σχ * d ^ (s.re + 1 / 2) * (I * Lh h)
        ≤ Mφ * d ^ σχ * d ^ (s.re + 1 / 2) * (I * (K * d ^ (-(|τ| + (A : ℝ))))) := by
          gcongr
          exact hMφ _
      _ = Mφ * I * K * d ^ (s.re + 1 / 2 + σχ - (|τ| + (A : ℝ))) := by
          have e : d ^ (s.re + 1 / 2 + σχ - (|τ| + (A : ℝ))) = d ^ σχ * d ^ (s.re + 1 / 2) * d ^ (-(|τ| + (A : ℝ))) := by
            rw [← Real.rpow_add hd0, ← Real.rpow_add hd0]
            congr 1
            ring
          rw [e]
          ring

  calc ∫⁻ h, ∫⁻ g, ‖(fun gh : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
              (φ₁ (gh.2 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det gh.2) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det gh.2 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) *
                ((∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                  φ (antidiagonal2 p * upperUnipotent2 p x * gh.1) ∂(selfDualHaarAt ℚ p)) *
                  w (gh.1 * gh.2) *
                  φ₂ ((gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                  ((modulus ((Matrix.GeneralLinearGroup.det gh.1 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s)) (g, h)‖ₑ ∂P2 ∂ν
      ≤ ∫⁻ h, ENNReal.ofReal (Mφ * I * K) * bnd h ∂ν := lintegral_mono fun h => (hinner h).trans (hbound h)
    _ = ENNReal.ofReal (Mφ * I * K) * ∫⁻ h, bnd h ∂ν := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simpa only [hbnd] using h4)

theorem main
    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ₁ : IsLocallyConstant φ₁ ∧ HasCompactSupport φ₁)
    (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (hφ₂ : IsLocallyConstant φ₂ ∧ HasCompactSupport φ₂)
    (θ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (a : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent a * g) = NumberField.StandardAddChar.psiLocal ℚ p a * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hwadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) →
            w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (zc : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = ((θ zc : ℂˣ) : ℂ) * w g) :
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure]
      (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [ν.IsHaarMeasure],

    (∃ σ' : ℝ, ∀ s : ℂ, σ' < s.re →
        Integrable (fun gh : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
            (φ₁ (gh.2 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det gh.2) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det gh.2 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) *
              ((∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x * gh.1) ∂(selfDualHaarAt ℚ p)) *
                w (gh.1 * gh.2) *
                φ₂ ((gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                ((modulus ((Matrix.GeneralLinearGroup.det gh.1 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s))
          ((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)).prod ν)) ∧

    (∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
      ∃ σ' : ℝ, ∀ s : ℂ, σ' < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              ∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) g *
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              w' g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) g) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))) := by
  intro μ₂ _ μN₂ _ ν _
  obtain ⟨hsc, hlc, -, -⟩ :=
    AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom ℚ p
  haveI := hsc
  haveI := hlc
  refine ⟨partA p μ hμ σ hσ h01 φ hφ χ hχ φ₁ hφ₁ φ₂ hφ₂ θ w hwlaw hwsm hwadm hcentral μ₂ μN₂ ν, ?_⟩
  intro w' hw'
  have hwlaw' : ∀ (a : F) (g : G2), w' (unipotent a * g) = NumberField.StandardAddChar.psiLocal ℚ p a * w' g :=
    fun a => law_of_mem_span w (unipotent a) _ (hwlaw a) hw'
  have hwsm' := smooth_of_mem_span w hwsm hw'
  have hwadm' := adm_of_mem_span w hwadm hw'
  have hcentral' : ∀ (zc : (F)ˣ) (g : G2),
      w' (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = ((θ zc : ℂˣ) : ℂ) * w' g :=
    fun zc => law_of_mem_span w _ _ (hcentral zc) hw'
  obtain ⟨σb, hb⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_integrable_jacquetIntegral_mul_whittaker_mul_row_withDensity_of_admissible_of_chamber
      p μ hμ σ hσ h01 φ hφ θ w' hwlaw' hwsm' hwadm' hcentral' φ₂ hφ₂
  exact ⟨σb, fun s hs => hb μ₂ μN₂ s hs⟩

end Main

end LanglandsTunnell.RankinSelberg.B4Asm

end

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)

    (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ₁ : IsLocallyConstant φ₁ ∧ HasCompactSupport φ₁)
    (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (hφ₂ : IsLocallyConstant φ₂ ∧ HasCompactSupport φ₂)

    (θ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (a : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent a * g) = NumberField.StandardAddChar.psiLocal ℚ p a * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hwadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) →
            w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (zc : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = ((θ zc : ℂˣ) : ℂ) * w g)
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure]
      (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [ν.IsHaarMeasure],

    (∃ σ' : ℝ, ∀ s : ℂ, σ' < s.re →
        Integrable (fun gh : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
            (φ₁ (gh.2 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det gh.2) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det gh.2 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) *
              ((∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x * gh.1) ∂(selfDualHaarAt ℚ p)) *
                w (gh.1 * gh.2) *
                φ₂ ((gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                ((modulus ((Matrix.GeneralLinearGroup.det gh.1 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s))
          ((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)).prod ν)) ∧

    (∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
      ∃ σ' : ℝ, ∀ s : ℂ, σ' < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              ∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) g *
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              w' g * φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) g) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))) :=
  LanglandsTunnell.RankinSelberg.B4Asm.main p μ hμ σ hσ h01 φ hφ χ hχ φ₁ hφ₁ φ₂ hφ₂ θ w hwlaw hwsm hwadm hcentral

end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_godementUnfold_of_principalSeries2_of_admissible_ed2
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_godementUnfold_of_principalSeries2_of_admissible_ed2 (solution)
