-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_exists_integrable_godementZeta2_whittaker_shift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/56b84f99-f1b3-5477-bb84-effa10e8b7bc

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
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar
import Theorems.Thm_AutomorphicForm_WhittakerModel_norm_diagUnits2_mul_le_of_forall_mem_localLevelOne_norm_diagUnits2_mul_le
import Theorems.Thm_AutomorphicForm_lintegral_indicator_norm_le_mul_norm_det_rpow_lt_top
import Theorems.Thm_AutomorphicForm_WhittakerModel_span_translates_stable_and_law_and_smooth_and_central
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_whittaker_shift
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace GJC2

section Valuation

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

theorem v_lt_one_iff (x : v.adicCompletion K) :
    Valued.v x < 1 ↔ Valued.v x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hx : Valued.v x = 0
  · simp [hx]
  · rw [← WithZero.exp_log hx, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

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

end Valuation

section Generic

variable {G : Type*} [Group G]

theorem translate_mem_span (f : G → ℂ) (h : G) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    (fun g : G => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h')) := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      exact Submodule.subset_span ⟨h * h', funext fun g => by simp only [mul_assoc]⟩
  | zero => exact Submodule.zero_mem _
  | add W₁ W₂ _ _ h₁ h₂ =>
      have : (fun g : G => (W₁ + W₂) (g * h)) = (fun g : G => W₁ (g * h)) + fun g : G => W₂ (g * h) := rfl
      rw [this]; exact Submodule.add_mem _ h₁ h₂
  | smul a W _ h₁ =>
      have : (fun g : G => (a • W) (g * h)) = a • fun g : G => W (g * h) := rfl
      rw [this]; exact Submodule.smul_mem _ a h₁

theorem span_le_span_of_mem (f W₀ : G → ℂ)
    (h₀ : f ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => W₀ (g * h'))) :
    Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h')) ≤
      Submodule.span ℂ (Set.range fun h' : G => fun g : G => W₀ (g * h')) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h, rfl⟩
  exact translate_mem_span W₀ h h₀

variable [TopologicalSpace G] [ContinuousMul G]

theorem continuous_of_open_stabilizer (f : G → ℂ)
    (hF : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, f (g * k) = f g) :
    Continuous f := by
  obtain ⟨U, hU, hinv⟩ := hF
  refine continuous_def.2 fun s _ => ?_
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun k => g * k) '' (U : Set G), ?_, ?_, ⟨1, U.one_mem, mul_one g⟩⟩
  · rintro _ ⟨k, hk, rfl⟩
    show f (g * k) ∈ s
    rw [hinv k hk g]; exact hg
  · exact (Homeomorph.mulLeft g).isOpenMap _ hU

end Generic

section Local

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

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

theorem qR_pos : 0 < qR p := zero_lt_one.trans (one_lt_qR p)

theorem norm_eq_qR_zpow (y : F) (j : ℤ) (hy : Valued.v y = WithZero.exp (-j)) : ‖y‖ = qR p ^ (-j) := by
  rw [NumberField.FinitePlace.norm_def, hy, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, NNReal.coe_zpow]
  unfold qR
  congr 1

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

theorem modulus_coe_eq_norm (y : (F)ˣ) : ((modulus (y : F) : NNReal) : ℝ) = ‖(y : F)‖ := by
  obtain ⟨_, h2, _, h4, _⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  obtain ⟨n, hn, -⟩ := h2 y
  rw [h4 n y hn, norm_eq_qR_zpow p (y : F) n hn]
  unfold qR
  push_cast
  rfl

theorem norm_psiLocal (x : F) : ‖(NumberField.StandardAddChar.psiLocal ℚ p x : ℂ)‖ = 1 := by
  set q : ℕ := Ideal.absNorm p.asIdeal with hq
  have hq0 : q ≠ 0 := by
    intro h
    exact p.ne_bot (Ideal.absNorm_eq_zero_iff.mp (by rw [← hq]; exact h))

  have hvq : Valued.v ((q : ℕ) : F) ≤ WithZero.exp (-1 : ℤ) := by
    have hmem : ((q : ℕ) : 𝓞 ℚ) ∈ p.asIdeal := by rw [hq]; exact Ideal.absNorm_mem _
    have h := NumberField.AdelicLevel.valued_algebraMap (K := ℚ) p ((q : ℕ) : 𝓞 ℚ)
    rw [map_natCast, map_natCast] at h
    rw [← v_lt_one_iff, h]
    exact (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).mpr hmem

  obtain ⟨n, hn⟩ : ∃ n : ℕ, Valued.v ((((q ^ n : ℕ)) : F) * x) ≤ 1 := by
    by_cases hx : Valued.v x = 0
    · exact ⟨0, by rw [Valuation.map_mul, hx, mul_zero]; exact zero_le'⟩
    · refine ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
      set L : ℤ := WithZero.log (Valued.v x) with hL
      have hxL : Valued.v x = WithZero.exp L := (WithZero.exp_log hx).symm
      rw [Nat.cast_pow, Valuation.map_mul, Valuation.map_pow, hxL]
      calc Valued.v ((q : ℕ) : F) ^ L.toNat * WithZero.exp L
          ≤ (WithZero.exp (-1 : ℤ)) ^ L.toNat * WithZero.exp L :=
            mul_le_mul_left (pow_le_pow_left' hvq _) _
        _ = WithZero.exp (-(L.toNat : ℤ) + L) := by
            rw [WithZero.exp_add, ← zpow_natCast, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]
        _ ≤ WithZero.exp 0 := by rw [WithZero.exp_le_exp]; omega
        _ = 1 := WithZero.exp_zero
  have h1 : NumberField.StandardAddChar.psiLocal ℚ p ((((q ^ n : ℕ)) : F) * x) = 1 :=
    LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p _
      (by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hn)
  have h2 : NumberField.StandardAddChar.psiLocal ℚ p ((((q ^ n : ℕ)) : F) * x) =
      (NumberField.StandardAddChar.psiLocal ℚ p x) ^ (q ^ n) := by
    rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  have h3 : ‖(NumberField.StandardAddChar.psiLocal ℚ p x : ℂ)‖ ^ (q ^ n) = 1 := by
    rw [← norm_pow, ← h2, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero n hq0)).mp h3

end Local

end GJC2

namespace GJC2

theorem rpow_le_of_bottom (B τ r d : ℝ) (hB : 1 ≤ B) (hr : 0 < r) (hrB : r ≤ B) (hd : 0 < d)
    (hdle : d ≤ 2 * B * r) :
    r ^ τ ≤ (2 * B ^ 3) ^ |τ| * d ^ (-|τ|) := by
  have hB0 : 0 < B := by linarith
  have h2B : 0 < 2 * B := by positivity
  have h2B3 : 0 < 2 * B ^ 3 := by positivity
  rcases le_or_gt 0 τ with hτ | hτ
  · rw [abs_of_nonneg hτ]
    have h1 : r ^ τ ≤ B ^ τ := Real.rpow_le_rpow hr.le hrB hτ
    have hBle : B ≤ 2 * B ^ 3 / d := by
      rw [le_div_iff₀ hd]
      calc B * d ≤ B * (2 * B * r) := mul_le_mul_of_nonneg_left hdle hB0.le
        _ ≤ B * (2 * B * B) := by gcongr
        _ = 2 * B ^ 3 := by ring
    have h2 : B ^ τ ≤ (2 * B ^ 3 / d) ^ τ := Real.rpow_le_rpow hB0.le hBle hτ
    rw [Real.div_rpow h2B3.le hd.le, div_eq_mul_inv, ← Real.rpow_neg hd.le] at h2
    exact h1.trans h2
  · rw [abs_of_neg hτ, neg_neg]
    have hle : d / (2 * B) ≤ r := by rw [div_le_iff₀ h2B]; linarith
    have hpos : 0 < d / (2 * B) := by positivity
    have h1 : r ^ τ ≤ (d / (2 * B)) ^ τ := Real.rpow_le_rpow_of_nonpos hpos hle hτ.le
    rw [Real.div_rpow hd.le h2B.le, div_eq_mul_inv, ← Real.rpow_neg h2B.le] at h1
    have hB3 : B ≤ B ^ 3 := by
      calc B = B * 1 * 1 := by ring
        _ ≤ B * B * B := by gcongr
        _ = B ^ 3 := by ring
    have h2 : (2 * B) ^ (-τ) ≤ (2 * B ^ 3) ^ (-τ) :=
      Real.rpow_le_rpow h2B.le (by linarith) (by linarith)
    calc r ^ τ ≤ d ^ τ * (2 * B) ^ (-τ) := h1
      _ ≤ d ^ τ * (2 * B ^ 3) ^ (-τ) := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hd.le _)
      _ = (2 * B ^ 3) ^ (-τ) * d ^ τ := mul_comm _ _

theorem max_inv_pow_le (B r d : ℝ) (A : ℕ) (hB : 1 ≤ B) (hr : 0 < r) (hrB : r ≤ B) (hd : 0 < d)
    (hdle : d ≤ 2 * B * r) :
    max 1 (((d / r ^ 2) ^ A)⁻¹) ≤ (2 * B ^ 2) ^ A * d ^ (-(A : ℝ)) := by
  have hB0 : 0 < B := by linarith
  have hq : 1 ≤ 2 * B ^ 2 / d := by
    rw [one_le_div hd]
    calc d ≤ 2 * B * r := hdle
      _ ≤ 2 * B * B := by gcongr
      _ = 2 * B ^ 2 := by ring
  have hq' : r ^ 2 / d ≤ 2 * B ^ 2 / d := by
    refine div_le_div_of_nonneg_right ?_ hd.le
    nlinarith
  rw [Real.rpow_neg hd.le, Real.rpow_natCast, ← div_eq_mul_inv, ← div_pow]
  refine max_le (one_le_pow₀ hq) ?_
  rw [← inv_pow, inv_div]
  exact pow_le_pow_left₀ (by positivity) hq' A

theorem exists_pow_dvd_and_not (p : HeightOneSpectrum (𝓞 ℚ)) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) :
    ∃ b : ℕ, p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N := by
  classical
  refine ⟨(Associates.mk p.asIdeal).count (Associates.mk N).factors, ?_, ?_⟩
  · have h := finprod_mem_dvd p (Ideal.hasFiniteMulSupport hN)
    rw [Ideal.finprod_heightOneSpectrum_factorization hN] at h
    exact h
  · have h := Ideal.finprod_not_dvd p N hN
    rwa [Ideal.finprod_heightOneSpectrum_factorization hN] at h

section Main

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "Mat" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)

theorem diagUnits2_one_one : (diagUnits2 (1 : (F)ˣ) 1 : G2) = 1 := by
  apply Units.ext
  rw [coe_diagUnits2, Units.val_one, Units.val_one, Matrix.one_fin_two]

theorem continuous_det : Continuous fun g : G2 => (Matrix.GeneralLinearGroup.det g : (F)ˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (fun g : G2 => ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)) = fun g : G2 => (g : Mat).det :=
      funext fun g => Matrix.GeneralLinearGroup.val_det_apply g
    rw [show (Units.val ∘ fun g : G2 => (Matrix.GeneralLinearGroup.det g : (F)ˣ)) =
        fun g : G2 => ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) from rfl, this]
    exact Units.continuous_val.matrix_det
  · have : (fun g : G2 => (((Matrix.GeneralLinearGroup.det g : (F)ˣ)⁻¹ : (F)ˣ) : F)) =
        fun g : G2 => ((g⁻¹ : G2) : Mat).det := by
      funext g
      rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact Units.continuous_coe_inv.matrix_det

theorem main
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
        ∀ s₀ : ℂ,
          ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + s₀)) μ₂ := by
  letI : MeasurableSpace F := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  letI : MeasurableSpace G2 := localGLBorel ℚ p
  haveI : BorelSpace G2 := borelSpace_localGLBorel ℚ p
  intro μ₂ hμ₂ w hwV Φ hΦlc hΦcs s₀

  obtain ⟨b, hb⟩ := exists_pow_dvd_and_not p N hN
  have hw₂Kb :=
    LanglandsTunnell.RankinSelberg.forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq
      p N w₂base hw₂K b hb
  obtain ⟨-, hVlaw, hVsm, hVcen⟩ :=
    AutomorphicForm.WhittakerModel.span_translates_stable_and_law_and_smooth_and_central p w₂base hw₂law b
      (fun k hk g => hw₂Kb k g hk) θ₀ hcentral
  have hwlaw := hVlaw w hwV
  have hwsm := hVsm w hwV
  have hwcen := hVcen w hwV
  have hwadm : ∀ U : Subgroup G2, IsOpen (U : Set G2) →
      ∃ B : Finset (G2 → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w (g * h)),
          (∀ k ∈ U, ∀ g : G2, w' (g * k) = w' g) → w' ∈ Submodule.span ℂ (B : Set (G2 → ℂ)) := by
    intro U hU
    obtain ⟨B, hB⟩ := hw₂adm U hU
    exact ⟨B, fun w' hw' hinv => hB w' (span_le_span_of_mem w w₂base hwV hw') hinv⟩

  obtain ⟨C, A, τ, m₁, hC, hKD⟩ :=
    AutomorphicForm.WhittakerModel.exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar
      p θ₀ w hwlaw hwsm hwadm hwcen
  have hwN : ∀ (x : F) (g : G2), ‖w (unipotent x * g)‖ = ‖w g‖ := fun x g => by
    rw [hwlaw, norm_mul, norm_psiLocal, one_mul]
  have hTG :=
    AutomorphicForm.WhittakerModel.norm_diagUnits2_mul_le_of_forall_mem_localLevelOne_norm_diagUnits2_mul_le
      p w hwN C τ A hC (fun k hk a₁ a₂ => (hKD k hk a₁ a₂).1)
  have hwbd : ∀ g : G2, ‖w g‖ ≤
      C * (max ‖(g : Mat) 1 0‖ ‖(g : Mat) 1 1‖) ^ τ *
        max 1 (((‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖ / (max ‖(g : Mat) 1 0‖ ‖(g : Mat) 1 1‖) ^ 2) ^ A)⁻¹) := by
    intro g
    have h := hTG g 1 1
    have e1 : ‖(((1 : (F)ˣ)) : F)‖ ^ τ = 1 := by rw [Units.val_one, norm_one, Real.one_rpow]
    have e2 : max 1 ((‖(((1 * 1⁻¹ : (F)ˣ)) : F)‖ ^ A)⁻¹) = 1 := by
      rw [mul_inv_cancel, Units.val_one, norm_one, one_pow, inv_one, max_self]
    rw [diagUnits2_one_one, one_mul, e1, mul_one, e2, mul_one] at h
    exact h

  obtain ⟨MΦ, hMΦ⟩ := hΦlc.continuous.bounded_above_of_compact_support hΦcs
  have hMΦ0 : 0 ≤ MΦ := (norm_nonneg _).trans (hMΦ 0)
  have hent : ∀ i j : Fin 2, ∃ Bij : ℝ, ∀ M ∈ tsupport Φ, ‖M i j‖ ≤ Bij := fun i j => by
    obtain ⟨Bij, hBij⟩ := hΦcs.exists_bound_of_continuousOn
      (f := fun M : Mat => M i j) ((continuous_id.matrix_elem i j).continuousOn)
    exact ⟨Bij, hBij⟩
  choose Bf hBf using hent
  set B : ℝ := max 1 (max (max (Bf 0 0) (Bf 0 1)) (max (Bf 1 0) (Bf 1 1))) with hBdef
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 < B := zero_lt_one.trans_le hB1
  have hBent : ∀ M ∈ tsupport Φ, ∀ i j : Fin 2, ‖M i j‖ ≤ B := by
    intro M hM i j
    refine (hBf i j M hM).trans ?_
    fin_cases i <;> fin_cases j <;> simp [hBdef]

  have hχcont : Continuous fun u : (F)ˣ => ((χ u : ℂˣ) : ℂ) := Units.continuous_val.comp hχ.continuous
  obtain ⟨Mχ, hMχ⟩ := (isCompact_units_sphere p).exists_bound_of_continuousOn hχcont.continuousOn
  have hMχ0 : 0 ≤ Mχ := (norm_nonneg _).trans (hMχ 1 (by simp))
  set ϖu : (F)ˣ := NumberField.AdelicLevel.uniformizerUnit ℚ p with hϖudef
  have hvϖ : Valued.v (ϖu : F) = WithZero.exp (-1 : ℤ) := NumberField.AdelicLevel.valued_uniformizerUnit ℚ p
  set cχ : ℝ := ‖((χ ϖu : ℂˣ) : ℂ)‖ with hcχdef
  have hcχ : 0 < cχ := norm_pos_iff.2 (χ ϖu).ne_zero
  set κ : ℝ := -Real.log cχ / Real.log (qR p) with hκdef
  have hχbd : ∀ y : (F)ˣ, ‖((χ y : ℂˣ) : ℂ)‖ ≤ Mχ * ‖(y : F)‖ ^ κ := by
    intro y
    obtain ⟨m, u, hu, rfl⟩ := exists_eq_zpow_mul_unit p ϖu hvϖ y
    rw [norm_eq_qR_zpow p _ m (v_zpow_mul_unit p ϖu hvϖ m u hu), map_mul, map_zpow, Units.val_mul, norm_mul,
      Units.val_zpow_eq_zpow_val, norm_zpow, ← hcχdef, zpow_eq_rpow p cχ hcχ m, mul_comm]
    exact mul_le_mul_of_nonneg_right (hMχ u hu) (Real.rpow_nonneg (zpow_nonneg (qR_pos p).le _) _)

  refine ⟨1 + (A : ℝ) + |τ| - κ - s₀.re, fun s hs => ?_⟩
  set t : ℝ := s.re + s₀.re + κ - |τ| - A with htdef
  have ht : 1 < t := by rw [htdef]; linarith
  have hFA := AutomorphicForm.lintegral_indicator_norm_le_mul_norm_det_rpow_lt_top p B t ht μ₂

  set Kst : ℝ := C * (2 * B ^ 3) ^ |τ| * (2 * B ^ 2) ^ A * MΦ * Mχ with hKstdef
  have hKst0 : 0 ≤ Kst := by
    have h1 : 0 ≤ (2 * B ^ 3) ^ |τ| := Real.rpow_nonneg (by positivity) _
    have h2 : 0 ≤ (2 * B ^ 2) ^ A := by positivity
    rw [hKstdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC h1) h2) hMΦ0) hMχ0
  have hmod : ∀ y : (F)ˣ, ((modulus (y : F) : NNReal) : ℝ) = ‖(y : F)‖ := modulus_coe_eq_norm p
  have key : ∀ g : G2,
      ‖w g * Φ (g : Mat) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) : ℝ) : ℂ) ^ (s + s₀)‖ₑ ≤
        ENNReal.ofReal Kst *
          (Set.indicator {h : G2 | ∀ i j : Fin 2, ‖((h : G2) : Mat) i j‖ ≤ B} (fun _ => (1 : ENNReal)) g *
            ENNReal.ofReal (‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖ ^ t)) := by
    intro g
    by_cases hg : g ∈ {h : G2 | ∀ i j : Fin 2, ‖((h : G2) : Mat) i j‖ ≤ B}
    · rw [Set.indicator_of_mem hg, one_mul, ← ENNReal.ofReal_mul hKst0, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Set.mem_setOf_eq] at hg

      set r : ℝ := max ‖(g : Mat) 1 0‖ ‖(g : Mat) 1 1‖ with hrdef
      set d : ℝ := ‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖ with hddef
      have hd : 0 < d := norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det g).ne_zero
      have hrB : r ≤ B := max_le (hg 1 0) (hg 1 1)
      have hdle : d ≤ 2 * B * r := by
        have hdet : ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) =
            (g : Mat) 0 0 * (g : Mat) 1 1 - (g : Mat) 0 1 * (g : Mat) 1 0 := by
          rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
        rw [hddef, hdet]
        calc ‖(g : Mat) 0 0 * (g : Mat) 1 1 - (g : Mat) 0 1 * (g : Mat) 1 0‖
            ≤ ‖(g : Mat) 0 0 * (g : Mat) 1 1‖ + ‖(g : Mat) 0 1 * (g : Mat) 1 0‖ := norm_sub_le _ _
          _ = ‖(g : Mat) 0 0‖ * ‖(g : Mat) 1 1‖ + ‖(g : Mat) 0 1‖ * ‖(g : Mat) 1 0‖ := by rw [norm_mul, norm_mul]
          _ ≤ B * r + B * r :=
              add_le_add (mul_le_mul (hg 0 0) (le_max_right _ _) (norm_nonneg _) hB0.le)
                (mul_le_mul (hg 0 1) (le_max_left _ _) (norm_nonneg _) hB0.le)
          _ = 2 * B * r := by ring
      have hr : 0 < r := by
        by_contra hr0
        push Not at hr0
        nlinarith [hd, hdle, hB0, hr0]

      have hE1 := rpow_le_of_bottom B τ r d hB1 hr hrB hd hdle
      have hE2 := max_inv_pow_le B r d A hB1 hr hrB hd hdle
      have hE1nn : 0 ≤ (2 * B ^ 3) ^ |τ| * d ^ (-|τ|) :=
        mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hd.le _)
      have hwle : ‖w g‖ ≤ C * ((2 * B ^ 3) ^ |τ| * d ^ (-|τ|)) * ((2 * B ^ 2) ^ A * d ^ (-(A : ℝ))) := by
        calc ‖w g‖ ≤ C * r ^ τ * max 1 (((d / r ^ 2) ^ A)⁻¹) := hwbd g
          _ ≤ C * ((2 * B ^ 3) ^ |τ| * d ^ (-|τ|)) * max 1 (((d / r ^ 2) ^ A)⁻¹) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE1 hC) (le_trans zero_le_one (le_max_left _ _))
          _ ≤ C * ((2 * B ^ 3) ^ |τ| * d ^ (-|τ|)) * ((2 * B ^ 2) ^ A * d ^ (-(A : ℝ))) :=
              mul_le_mul_of_nonneg_left hE2 (mul_nonneg hC hE1nn)
      have hWnn : 0 ≤ C * ((2 * B ^ 3) ^ |τ| * d ^ (-|τ|)) * ((2 * B ^ 2) ^ A * d ^ (-(A : ℝ))) :=
        mul_nonneg (mul_nonneg hC hE1nn) (mul_nonneg (by positivity) (Real.rpow_nonneg hd.le _))

      have hcpow : ‖(((modulus ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) : ℝ) : ℂ) ^ (s + s₀))‖ =
          d ^ (s.re + s₀.re) := by
        rw [hmod, ← hddef, Complex.norm_cpow_eq_rpow_re_of_pos hd, Complex.add_re]

      rw [norm_mul, norm_mul, norm_mul, hcpow]
      have s1 : ‖w g‖ * ‖Φ (g : Mat)‖ ≤
          C * ((2 * B ^ 3) ^ |τ| * d ^ (-|τ|)) * ((2 * B ^ 2) ^ A * d ^ (-(A : ℝ))) * MΦ :=
        mul_le_mul hwle (hMΦ _) (norm_nonneg _) hWnn
      have s2 : ‖w g‖ * ‖Φ (g : Mat)‖ * ‖((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ ≤
          C * ((2 * B ^ 3) ^ |τ| * d ^ (-|τ|)) * ((2 * B ^ 2) ^ A * d ^ (-(A : ℝ))) * MΦ * (Mχ * d ^ κ) :=
        mul_le_mul s1 (hχbd _) (norm_nonneg _) (mul_nonneg hWnn hMΦ0)
      have s3 := mul_le_mul_of_nonneg_right s2 (Real.rpow_nonneg hd.le (s.re + s₀.re))
      refine s3.trans (le_of_eq ?_)
      have hexp : d ^ (-|τ|) * d ^ (-(A : ℝ)) * d ^ κ * d ^ (s.re + s₀.re) = d ^ t := by
        rw [← Real.rpow_add hd, ← Real.rpow_add hd, ← Real.rpow_add hd, htdef]
        congr 1
        ring
      rw [hKstdef, ← hexp]
      ring
    ·
      have hΦ0 : Φ (g : Mat) = 0 := by
        by_contra hne
        exact hg (fun i j => hBent _ (subset_tsupport _ hne) i j)
      simp [hΦ0]

  have hwcont : Continuous w := continuous_of_open_stabilizer w hwsm
  have hΦcont : Continuous fun g : G2 => Φ (g : Mat) := hΦlc.continuous.comp Units.continuous_val
  have hdetc := continuous_det p
  have hχc : Continuous fun g : G2 => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (hχ.continuous.comp hdetc)
  have hmodc : Continuous fun g : G2 =>
      (((modulus ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) : ℝ) : ℂ)) := by
    have : (fun g : G2 => (((modulus ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) : ℝ) : ℂ))) =
        fun g : G2 => ((‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖ : ℝ) : ℂ) :=
      funext fun g => by rw [hmod]
    rw [this]
    exact Complex.continuous_ofReal.comp ((Units.continuous_val.comp hdetc).norm)
  have hmeas : Measurable fun g : G2 =>
      w g * Φ (g : Mat) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) : ℝ) : ℂ) ^ (s + s₀) :=
    ((hwcont.measurable.mul hΦcont.measurable).mul hχc.measurable).mul (hmodc.measurable.pow_const _)

  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono (fun g => key g)) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFA

end Main

end GJC2

end

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
        ∀ s₀ : ℂ,
          ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + s₀)) μ₂ :=
  GJC2.main p θ₀ N hN w₂base hw₂law hw₂K hw₂adm hcentral χ hχ

end S_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_whittaker_shift
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_whittaker_shift (solution)
