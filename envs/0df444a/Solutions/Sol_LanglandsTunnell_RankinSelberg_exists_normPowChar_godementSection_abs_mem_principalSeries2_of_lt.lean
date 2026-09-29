-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_normPowChar_godementSection_abs_mem_principalSeries2_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/83a831e4-6454-52c4-86d6-8b83c953fb38

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HaarQuotient
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_finset_forall_eq_sum_mul_prod_indicator_ball_of_isLocallyConstant_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_normPowChar_godementSection_abs_mem_principalSeries2_of_lt

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction Filter Topology

open scoped ENNReal NNReal Pointwise

noncomputable section

namespace Delta2xPG

section LocalField

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem norm_units_pos (u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : 0 < ‖(u : F)‖ :=
  norm_pos_iff.mpr u.ne_zero

scoped instance secondCountable_units : SecondCountableTopology (HeightOneSpectrum.adicCompletion ℚ p)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

scoped instance borelSpace_units_local : BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)ˣ := borelSpace_units

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p : Measure F).IsAddHaarMeasure := by
  set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

def mulHaar : Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ :=
  Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))

scoped instance isHaarMeasure_mulHaar : (mulHaar p).IsHaarMeasure := by
  haveI := isAddHaarMeasure_selfDualHaarAt p
  exact LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)

theorem map_mul_left_haar (ν : Measure F) [ν.IsAddHaarMeasure] (c : F) (hc : c ≠ 0) :
    ν.map (fun x => c * x) = (modulus c)⁻¹ • ν := by
  set u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ := Units.mk0 c hc with hu
  have hfun : (fun x : F => c * x) = fun x => u • x := by
    funext x; rw [hu, Units.smul_mk0]; rfl
  haveI : ν.Regular := inferInstance
  ext s hs
  rw [Measure.map_apply (measurable_const_mul c) hs, hfun, Set.preimage_smul, Measure.coe_nnreal_smul_apply,
    ← MeasureTheory.distribHaarChar_mul ν u⁻¹ s, map_inv, modulus_of_ne_zero hc, ← hu,
    ENNReal.coe_inv (ne_of_gt (distribHaarChar_pos))]

theorem measure_preimage_mul_left_haar (ν : Measure F) [ν.IsAddHaarMeasure] (c : F) (hc : c ≠ 0)
    (s : Set F) (hs : MeasurableSet s) :
    ν ((fun x => c * x) ⁻¹' s) = ((modulus c)⁻¹ : ℝ≥0∞) * ν s := by
  rw [← Measure.map_apply (measurable_const_mul c) hs, map_mul_left_haar p ν c hc,
    Measure.coe_nnreal_smul_apply, ENNReal.coe_inv (modulus_ne_zero hc)]

theorem integral_comp_mul_left_haar (ν : Measure F) [ν.IsAddHaarMeasure]
    (f : F → ℂ) (c : F) (hc : c ≠ 0) :
    ∫ x, f (c * x) ∂ν = ((((modulus c : ℝ≥0) : ℝ) : ℂ))⁻¹ * ∫ x, f x ∂ν := by
  have he : ((MeasurableEquiv.mulLeft₀ c hc : F ≃ᵐ F) : F → F) = fun x => c * x := rfl
  calc ∫ x, f (c * x) ∂ν = ∫ x, f ((MeasurableEquiv.mulLeft₀ c hc) x) ∂ν := rfl
    _ = ∫ y, f y ∂(ν.map (MeasurableEquiv.mulLeft₀ c hc)) := (integral_map_equiv _ f).symm
    _ = ((modulus c)⁻¹ : ℝ≥0) • ∫ x, f x ∂ν := by rw [he, map_mul_left_haar p ν c hc, integral_smul_nnreal_measure]
    _ = _ := by rw [NNReal.smul_def, NNReal.coe_inv, Complex.real_smul, Complex.ofReal_inv]

end LocalField

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

end Valuation

section Shell

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => p.adicCompletion ℚ
attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

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

def shell (n : ℤ) : Set Fˣ := {y : Fˣ | Valued.v (y : F) = WithZero.exp (-(n))}

theorem measurableSet_shell (n : ℤ) : MeasurableSet (shell p n) :=
  (hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p).1 n

theorem exists_mem_shell (a : Fˣ) : ∃ n : ℤ, a ∈ shell p n := by
  obtain ⟨n, hn, -⟩ := (hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p).2.1 a
  exact ⟨n, hn⟩

theorem measure_shell_eq (n : ℤ) :
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (shell p n) =
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (shell p 0) :=
  ((hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p).2.2.1 n).1

theorem measure_shell_zero_lt_top :
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (shell p 0) < ⊤ :=
  ((hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p).2.2.1 0).2.2

theorem norm_of_mem_shell {n : ℤ} {a : Fˣ} (h : a ∈ shell p n) : ‖(a : F)‖ = qR p ^ (-n) :=
  norm_eq_qR_zpow p (a : F) n h

theorem qR_pos : 0 < qR p := lt_trans zero_lt_one (one_lt_qR p)

theorem rpow_norm_shell (t : ℝ) (n₀ : ℤ) (m : ℕ) {a : Fˣ} (h : a ∈ shell p (n₀ + m)) :
    ENNReal.ofReal (‖(a : F)‖ ^ t) =
      ENNReal.ofReal (qR p ^ (-(n₀ : ℝ) * t)) * ENNReal.ofReal (qR p ^ (-t)) ^ m := by
  have hq := qR_pos p
  rw [norm_of_mem_shell p h, ← ENNReal.ofReal_pow (Real.rpow_nonneg hq.le _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hq.le _)]
  congr 1
  rw [← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul_natCast hq.le, ← Real.rpow_add hq]
  congr 1
  push_cast
  ring

theorem lintegral_indicator_norm_rpow_lt_top (B t : ℝ) (ht : 0 < t) :
    ∫⁻ a : Fˣ, Set.indicator {a : Fˣ | ‖(a : F)‖ ≤ B} (fun a => ENNReal.ofReal (‖(a : F)‖ ^ t)) a
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) < ⊤ := by
  have hq1 := one_lt_qR p

  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B hq1
  set n₀ : ℤ := 1 - (k : ℤ) with hn₀
  set c : ENNReal := ENNReal.ofReal (qR p ^ (-(n₀ : ℝ) * t)) with hc
  set r : ENNReal := ENNReal.ofReal (qR p ^ (-t)) with hr
  have hr1 : r < 1 := ENNReal.ofReal_lt_one.2 (Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith))

  have hpt : ∀ a : Fˣ,
      Set.indicator {a : Fˣ | ‖(a : F)‖ ≤ B} (fun a => ENNReal.ofReal (‖(a : F)‖ ^ t)) a ≤
        ∑' m : ℕ, (shell p (n₀ + m)).indicator (fun _ => c * r ^ m) a := by
    intro a
    by_cases hB : ‖(a : F)‖ ≤ B
    · obtain ⟨n, hn⟩ := exists_mem_shell p a
      have hnorm := norm_of_mem_shell p hn
      have hn₀n : n₀ ≤ n := by
        have h1 : qR p ^ (-n) < qR p ^ (k : ℤ) := by
          rw [← hnorm, zpow_natCast]; exact lt_of_le_of_lt hB hk
        have h2 := (zpow_lt_zpow_iff_right₀ hq1).1 h1
        omega
      obtain ⟨m, hm⟩ : ∃ m : ℕ, n = n₀ + m := ⟨(n - n₀).toNat, by omega⟩
      have hn' : a ∈ shell p (n₀ + m) := hm ▸ hn
      calc Set.indicator {a : Fˣ | ‖(a : F)‖ ≤ B} (fun a => ENNReal.ofReal (‖(a : F)‖ ^ t)) a
          = ENNReal.ofReal (‖(a : F)‖ ^ t) :=
            Set.indicator_of_mem (show a ∈ {a : Fˣ | ‖(a : F)‖ ≤ B} from hB) _
        _ = c * r ^ m := rpow_norm_shell p t n₀ m hn'
        _ = (shell p (n₀ + m)).indicator (fun _ => c * r ^ m) a :=
            (Set.indicator_of_mem hn' (fun _ => c * r ^ m)).symm
        _ ≤ ∑' m : ℕ, (shell p (n₀ + m)).indicator (fun _ => c * r ^ m) a :=
            ENNReal.le_tsum (f := fun m : ℕ => (shell p (n₀ + m)).indicator (fun _ => c * r ^ m) a) m
    · rw [Set.indicator_of_notMem (show a ∉ {a : Fˣ | ‖(a : F)‖ ≤ B} from hB)]; exact zero_le

  have hS0 := measure_shell_zero_lt_top p
  calc ∫⁻ a : Fˣ, Set.indicator {a : Fˣ | ‖(a : F)‖ ≤ B} (fun a => ENNReal.ofReal (‖(a : F)‖ ^ t)) a
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
      ≤ ∫⁻ a : Fˣ, ∑' m : ℕ, (shell p (n₀ + m)).indicator (fun _ => c * r ^ m) a
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := lintegral_mono hpt
    _ = ∑' m : ℕ, ∫⁻ a : Fˣ, (shell p (n₀ + m)).indicator (fun _ => c * r ^ m) a
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) :=
        lintegral_tsum fun m => ((measurable_const.indicator (measurableSet_shell p _))).aemeasurable
    _ = ∑' m : ℕ, c * r ^ m * (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (shell p 0) := by
        congr 1; funext m
        rw [lintegral_indicator_const (measurableSet_shell p _), measure_shell_eq p]
    _ = c * (∑' m : ℕ, r ^ m) * (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (shell p 0) := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_) hS0
        rw [ENNReal.tsum_geometric]
        exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt hr1)

end Shell

section Algebra

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem row_one_weyl_unip (w₀ : G) (hw₀ : (w₀ : Mat) = !![0, 1; 1, 0]) (y : F) (g : G) (j : Fin 2) :
    ((w₀ * unipotentGL2 y * g : G) : Mat) 1 j = (g : Mat) 0 j + y * (g : Mat) 1 j := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hw₀, unipotentGL2_coe]

theorem det_weyl (w₀ : G) (hw₀ : (w₀ : Mat) = !![0, 1; 1, 0]) :
    Matrix.GeneralLinearGroup.det w₀ = -1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, hw₀, Matrix.det_fin_two_of]
  simp

theorem det_unipotentGL2' (y : F) : Matrix.GeneralLinearGroup.det (unipotentGL2 y : G) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

theorem det_weyl_unip (w₀ : G) (hw₀ : (w₀ : Mat) = !![0, 1; 1, 0]) (y : F) (g : G) :
    Matrix.GeneralLinearGroup.det (w₀ * unipotentGL2 y * g) = -1 * Matrix.GeneralLinearGroup.det g := by
  rw [map_mul, map_mul, det_weyl p w₀ hw₀, det_unipotentGL2' p y, mul_one]

def invBound (g : G) : ℝ := ∑ i : Fin 2, ∑ j : Fin 2, ‖((g⁻¹ : G) : Mat) i j‖

theorem invBound_nonneg (g : G) : 0 ≤ invBound p g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_entry_le_invBound (g : G) (i j : Fin 2) : ‖((g⁻¹ : G) : Mat) i j‖ ≤ invBound p g := by
  have h1 : ‖((g⁻¹ : G) : Mat) i j‖ ≤ ∑ j' : Fin 2, ‖((g⁻¹ : G) : Mat) i j'‖ :=
    Finset.single_le_sum (f := fun j' => ‖((g⁻¹ : G) : Mat) i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have h2 : (∑ j' : Fin 2, ‖((g⁻¹ : G) : Mat) i j'‖) ≤ invBound p g :=
    Finset.single_le_sum (f := fun i' => ∑ j' : Fin 2, ‖((g⁻¹ : G) : Mat) i' j'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  exact h1.trans h2

theorem coord_eq_sum (g : G) (t u : F) (i : Fin 2) :
    (∑ j : Fin 2, (t * (g : Mat) 0 j + u * (g : Mat) 1 j) * ((g⁻¹ : G) : Mat) j i) = ![t, u] i := by
  have hmul : ((g : Mat) * ((g⁻¹ : G) : Mat)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h0 : ∑ j : Fin 2, (g : Mat) 0 j * ((g⁻¹ : G) : Mat) j i = (1 : Mat) 0 i := by
    rw [← hmul, Matrix.mul_apply]
  have h1 : ∑ j : Fin 2, (g : Mat) 1 j * ((g⁻¹ : G) : Mat) j i = (1 : Mat) 1 i := by
    rw [← hmul, Matrix.mul_apply]
  calc (∑ j : Fin 2, (t * (g : Mat) 0 j + u * (g : Mat) 1 j) * ((g⁻¹ : G) : Mat) j i)
      = t * (∑ j : Fin 2, (g : Mat) 0 j * ((g⁻¹ : G) : Mat) j i) +
          u * (∑ j : Fin 2, (g : Mat) 1 j * ((g⁻¹ : G) : Mat) j i) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, add_mul, mul_assoc]
    _ = t * (1 : Mat) 0 i + u * (1 : Mat) 1 i := by rw [h0, h1]
    _ = ![t, u] i := by
        fin_cases i
        · simp [Matrix.one_apply]
        · simp [Matrix.one_apply]

theorem norm_coord_le (g : G) (t u : F) (R : ℝ) (hR : 0 ≤ R)
    (hv : ‖(fun j : Fin 2 => t * (g : Mat) 0 j + u * (g : Mat) 1 j)‖ ≤ R) :
    ‖t‖ ≤ 2 * R * invBound p g ∧ ‖u‖ ≤ 2 * R * invBound p g := by
  have hvj : ∀ j : Fin 2, ‖t * (g : Mat) 0 j + u * (g : Mat) 1 j‖ ≤ R := fun j =>
    (norm_le_pi_norm (fun j : Fin 2 => t * (g : Mat) 0 j + u * (g : Mat) 1 j) j).trans hv
  have key : ∀ i : Fin 2, ‖![t, u] i‖ ≤ 2 * R * invBound p g := by
    intro i
    rw [← coord_eq_sum p g t u i, Fin.sum_univ_two]
    calc ‖(t * (g : Mat) 0 0 + u * (g : Mat) 1 0) * ((g⁻¹ : G) : Mat) 0 i +
            (t * (g : Mat) 0 1 + u * (g : Mat) 1 1) * ((g⁻¹ : G) : Mat) 1 i‖
        ≤ ‖t * (g : Mat) 0 0 + u * (g : Mat) 1 0‖ * ‖((g⁻¹ : G) : Mat) 0 i‖ +
            ‖t * (g : Mat) 0 1 + u * (g : Mat) 1 1‖ * ‖((g⁻¹ : G) : Mat) 1 i‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ R * invBound p g + R * invBound p g :=
          add_le_add
            (mul_le_mul (hvj 0) (norm_entry_le_invBound p g 0 i) (norm_nonneg _) hR)
            (mul_le_mul (hvj 1) (norm_entry_le_invBound p g 1 i) (norm_nonneg _) hR)
      _ = 2 * R * invBound p g := by ring
  refine ⟨?_, ?_⟩
  · simpa using key 0
  · simpa using key 1

theorem exists_bound_support (Φ : (Fin 2 → F) → ℂ) (hΦ : HasCompactSupport Φ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ v, Φ v ≠ 0 → ‖v‖ ≤ R := by
  obtain ⟨C, hC⟩ := hΦ.isCompact.isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun v hv => ?_⟩
  exact (hC v (subset_tsupport Φ (Function.mem_support.mpr hv))).trans (le_max_left _ _)

end Algebra

section NormChar

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

def normChar (σ : ℝ) : (HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ where
  toFun a := Units.mk0 (((‖(a : F)‖ ^ σ : ℝ)) : ℂ)
    (by exact_mod_cast (Real.rpow_pos_of_pos (norm_units_pos p a) σ).ne')
  map_one' := by
    apply Units.ext; simp
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mk0, Units.val_mul, norm_mul]
    rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    push_cast
    ring

theorem normChar_apply (σ : ℝ) (a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    ((normChar p σ a : ℂˣ) : ℂ) = (((‖(a : F)‖ ^ σ : ℝ)) : ℂ) := rfl

theorem norm_normChar (σ : ℝ) (a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    ‖((normChar p σ a : ℂˣ) : ℂ)‖ = ‖(a : F)‖ ^ σ := by
  rw [normChar_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

theorem isLocallyConstant_valued_units :
    IsLocallyConstant fun a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ => Valued.v (a : F) := by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun a => ?_
  have ha : Valued.v.restrict (a : F) ≠ 0 := by
    intro h0
    have : Valued.v.restrict (a : F) = Valued.v.restrict (0 : F) := by rw [h0, map_zero]
    rw [Valuation.restrict_inj, map_zero] at this
    exact a.ne_zero ((Valuation.zero_iff _).mp this)
  refine ⟨Units.val ⁻¹' {x : F | Valued.v.restrict x = Valued.v.restrict (a : F)},
    (Valued.isOpen_sphere F ha).preimage Units.continuous_val, by simp, fun b hb => ?_⟩
  have hb' : Valued.v.restrict (b : F) = Valued.v.restrict (a : F) := hb
  rwa [Valuation.restrict_inj] at hb'

theorem isLocallyConstant_norm_units :
    IsLocallyConstant fun a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ => ‖(a : F)‖ := by
  have h := (isLocallyConstant_valued_units p).comp
    (fun γ : WithZero (Multiplicative ℤ) => ((WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero p) γ : ℝ≥0) : ℝ))
  refine (IsLocallyConstant.iff_exists_open _).mpr fun a => ?_
  obtain ⟨U, hU, haU, hcU⟩ := (IsLocallyConstant.iff_exists_open _).mp (isLocallyConstant_valued_units p) a
  exact ⟨U, hU, haU, fun b hb => by rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, hcU b hb]⟩

theorem isLocallyConstant_normChar (σ : ℝ) : IsLocallyConstant (normChar p σ) := by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun a => ?_
  obtain ⟨U, hU, haU, hcU⟩ := (IsLocallyConstant.iff_exists_open _).mp (isLocallyConstant_norm_units p) a
  refine ⟨U, hU, haU, fun b hb => ?_⟩
  apply Units.ext
  rw [normChar_apply, normChar_apply, hcU b hb]

end NormChar

section Integrand

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

def gInt (σ : Fin 2 → ℝ) (Φ : (Fin 2 → F) → ℂ) (g : G) (t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : ℂ :=
  (fun v : Fin 2 → F => ((‖Φ v‖ : ℝ) : ℂ)) (fun j : Fin 2 => (t : F) * (g : Mat) 1 j) *
    ((normChar p (σ 0) t : ℂˣ) : ℂ) * (((normChar p (σ 1) t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : F) : ℝ) : ℂ)

def gIntR (σ : Fin 2 → ℝ) (Φ : (Fin 2 → F) → ℂ) (g : G) (t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : ℝ :=
  ‖Φ (fun j : Fin 2 => (t : F) * (g : Mat) 1 j)‖ * (‖(t : F)‖ ^ (σ 0) * (‖(t : F)‖ ^ (σ 1))⁻¹ * ‖(t : F)‖)

theorem gInt_eq_ofReal (σ : Fin 2 → ℝ) (Φ : (Fin 2 → F) → ℂ) (g : G) (t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    gInt p σ Φ g t = ((gIntR p σ Φ g t : ℝ) : ℂ) := by
  simp only [gInt, gIntR, normChar_apply, coe_modulus_eq_norm]
  push_cast
  ring

theorem gIntR_nonneg (σ : Fin 2 → ℝ) (Φ : (Fin 2 → F) → ℂ) (g : G) (t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    0 ≤ gIntR p σ Φ g t :=
  mul_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    (inv_nonneg.mpr (Real.rpow_nonneg (norm_nonneg _) _))) (norm_nonneg _))

theorem gIntR_eq_mul_rpow (σ : Fin 2 → ℝ) (Φ : (Fin 2 → F) → ℂ) (g : G) (t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    gIntR p σ Φ g t = ‖Φ (fun j : Fin 2 => (t : F) * (g : Mat) 1 j)‖ * ‖(t : F)‖ ^ (σ 0 - σ 1 + 1) := by
  have ht : 0 < ‖(t : F)‖ := norm_units_pos p t
  rw [gIntR, ← Real.rpow_neg ht.le, ← Real.rpow_add ht, ← Real.rpow_add_one ht.ne']
  ring_nf

theorem continuous_gIntR (σ : Fin 2 → ℝ) {Φ : (Fin 2 → F) → ℂ} (hΦ : IsLocallyConstant Φ) (g : G) :
    Continuous (gIntR p σ Φ g) := by
  have hrow : Continuous fun t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ => (fun j : Fin 2 => (t : F) * (g : Mat) 1 j) :=
    continuous_pi fun j => Units.continuous_val.mul continuous_const
  have hn : Continuous fun t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ => ‖(t : F)‖ := continuous_norm.comp Units.continuous_val
  have hne : ∀ t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ, ‖(t : F)‖ ≠ 0 := fun t => (norm_units_pos p t).ne'
  unfold gIntR
  exact (continuous_norm.comp (hΦ.continuous.comp hrow)).mul
    (((hn.rpow_const fun t => Or.inl (hne t)).mul ((hn.rpow_const fun t => Or.inl (hne t)).inv₀
      fun t => (Real.rpow_pos_of_pos (norm_units_pos p t) _).ne')).mul hn)

theorem integrable_gInt (σ : Fin 2 → ℝ) (h01 : σ 1 < σ 0) {Φ : (Fin 2 → F) → ℂ}
    (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) (g : G) :
    Integrable (gInt p σ Φ g) (mulHaar p) := by
  obtain ⟨hlc, hcs⟩ := hΦ
  obtain ⟨M, hM⟩ := hlc.continuous.bounded_above_of_compact_support hcs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨R, hR0, hR⟩ := exists_bound_support p Φ hcs
  set B : ℝ := 2 * R * invBound p g with hB
  set a : ℝ := σ 0 - σ 1 + 1 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  set A : Set (HeightOneSpectrum.adicCompletion ℚ p)ˣ := {t | ‖(t : F)‖ ≤ B} with hA
  have hAm : MeasurableSet A :=
    (isClosed_le (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet

  have hreal : Integrable (gIntR p σ Φ g) (mulHaar p) := by
    set maj : (HeightOneSpectrum.adicCompletion ℚ p)ˣ → ℝ := fun t => M * (A.indicator (fun t => ‖(t : F)‖ ^ a) t) with hmaj
    have hmaj_meas : Measurable maj := by
      rw [hmaj]
      exact (((continuous_norm.comp Units.continuous_val).measurable.pow_const a).indicator hAm).const_mul M
    have hmaj_nn : ∀ t, 0 ≤ maj t := fun t => by
      rw [hmaj]; exact mul_nonneg hM0 (Set.indicator_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _)
    have hmaj_int : Integrable maj (mulHaar p) := by
      refine ⟨hmaj_meas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hmaj_nn)).mpr ?_⟩
      have hfun : (fun t => ENNReal.ofReal (maj t)) =
          fun t => ENNReal.ofReal M * A.indicator (fun t => ENNReal.ofReal (‖(t : F)‖ ^ a)) t := by
        funext t
        rw [hmaj]
        beta_reduce
        by_cases ht : t ∈ A
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, ENNReal.ofReal_mul hM0]
        · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero, mul_zero, ENNReal.ofReal_zero]
      have hmeasA : Measurable (fun t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
          A.indicator (fun t => ENNReal.ofReal (‖(t : F)‖ ^ a)) t) :=
        (ENNReal.measurable_ofReal.comp ((continuous_norm.comp Units.continuous_val).measurable.pow_const a)).indicator hAm
      rw [hfun, lintegral_const_mul _ hmeasA]
      refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
      rw [hA]
      exact lintegral_indicator_norm_rpow_lt_top p B a ha0
    refine hmaj_int.mono' (continuous_gIntR p σ hlc g).measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (gIntR_nonneg p σ Φ g t), gIntR_eq_mul_rpow, ← ha]
    by_cases hΦ0 : Φ (fun j : Fin 2 => (t : F) * (g : Mat) 1 j) = 0
    · rw [hΦ0, norm_zero, zero_mul]; exact hmaj_nn t
    · have hvR := hR _ hΦ0
      have hv_eq : (fun j : Fin 2 => (t : F) * (g : Mat) 1 j) = fun j : Fin 2 => (0 : F) * (g : Mat) 0 j + (t : F) * (g : Mat) 1 j := by
        funext j; ring
      rw [hv_eq] at hvR
      have htB : t ∈ A := (norm_coord_le p g 0 (t : F) R hR0 hvR).2
      rw [hmaj]
      simp only [Set.indicator_of_mem htB]
      exact mul_le_mul_of_nonneg_right (hM _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hfun : gInt p σ Φ g = fun t => ((gIntR p σ Φ g t : ℝ) : ℂ) := funext (gInt_eq_ofReal p σ Φ g)
  rw [hfun]
  exact hreal.ofReal

theorem integral_gInt_eq_ofReal (σ : Fin 2 → ℝ) (Φ : (Fin 2 → F) → ℂ) (g : G) :
    ∫ t, gInt p σ Φ g t ∂(mulHaar p) = ((∫ t, gIntR p σ Φ g t ∂(mulHaar p) : ℝ) : ℂ) := by
  have hfun : gInt p σ Φ g = fun t => ((gIntR p σ Φ g t : ℝ) : ℂ) := funext (gInt_eq_ofReal p σ Φ g)
  rw [hfun]
  exact integral_ofReal

end Integrand

section Section

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

def posSection (σ : Fin 2 → ℝ) (Φ : (Fin 2 → F) → ℂ) (g : G) : ℂ :=
  ((normChar p (σ 0) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
    ∫ t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ, gInt p σ Φ g t ∂(mulHaar p)

theorem posSection_eq_ofReal (σ : Fin 2 → ℝ) (Φ : (Fin 2 → F) → ℂ) (g : G) :
    posSection p σ Φ g =
      (((‖((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)‖ ^ (σ 0) *
          ‖((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)‖ ^ (1 / 2 : ℝ) *
          ∫ t, gIntR p σ Φ g t ∂(mulHaar p) : ℝ)) : ℂ) := by
  rw [posSection, integral_gInt_eq_ofReal, normChar_apply, coe_modulus_eq_norm,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (norm_nonneg _)]
  push_cast
  ring

theorem posSection_re_nonneg_im_zero (σ : Fin 2 → ℝ) (Φ : (Fin 2 → F) → ℂ) (g : G) :
    0 ≤ (posSection p σ Φ g).re ∧ (posSection p σ Φ g).im = 0 := by
  rw [posSection_eq_ofReal, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨mul_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _))
    (integral_nonneg (gIntR_nonneg p σ Φ g)), rfl⟩

end Section

section Membership

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem row_one_upperUnipotent2_mul (x : F) (g : G) (j : Fin 2) :
    ((upperUnipotent2 p x * g : G) : Mat) 1 j = (g : Mat) 1 j := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, upperUnipotent2_coe]

theorem det_upperUnipotent2_mul (x : F) (g : G) :
    Matrix.GeneralLinearGroup.det (upperUnipotent2 p x * g) = Matrix.GeneralLinearGroup.det g := by
  have h : Matrix.GeneralLinearGroup.det (upperUnipotent2 p x) = 1 := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, upperUnipotent2_coe, Matrix.det_fin_two_of]
    simp
  rw [map_mul, h, one_mul]

theorem row_one_diagonal2_mul (a : Fin 2 → (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (g : G) (j : Fin 2) :
    ((diagonal2 p a * g : G) : Mat) 1 j = ((a 1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) * (g : Mat) 1 j := by
  simp [Units.val_mul, diagonal2_coe, Matrix.diagonal_mul]

theorem det_diagonal2_mul (a : Fin 2 → (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (g : G) :
    Matrix.GeneralLinearGroup.det (diagonal2 p a * g) = a 0 * a 1 * Matrix.GeneralLinearGroup.det g := by
  have h : Matrix.GeneralLinearGroup.det (diagonal2 p a) = a 0 * a 1 := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, diagonal2_coe, Matrix.det_diagonal, Fin.prod_univ_two, Units.val_mul]
  rw [map_mul, h]

theorem posSection_upperUnipotent2_mul (σ : Fin 2 → ℝ) (Φ : (Fin 2 → F) → ℂ) (x : F) (g : G) :
    posSection p σ Φ (upperUnipotent2 p x * g) = posSection p σ Φ g := by
  simp only [posSection, gInt, row_one_upperUnipotent2_mul, det_upperUnipotent2_mul]

theorem cpow_half_ofReal {r : ℝ} (hr : 0 ≤ r) : ((r : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt r : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr]
  norm_num

theorem gInt_diagonal2_mul (σ : Fin 2 → ℝ) (Φ : (Fin 2 → F) → ℂ)
    (a : Fin 2 → (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (g : G) (t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    gInt p σ Φ (diagonal2 p a * g) t =
      ((((normChar p (σ 0) (a 1) : ℂˣ) : ℂ))⁻¹ * ((normChar p (σ 1) (a 1) : ℂˣ) : ℂ) *
          (((modulus ((a 1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ))⁻¹) *
        gInt p σ Φ g (a 1 * t) := by
  have hrow : (fun j : Fin 2 => (t : F) * ((diagonal2 p a * g : G) : Mat) 1 j) =
      fun j : Fin 2 => (((a 1 * t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F) * (g : Mat) 1 j := by
    funext j; rw [row_one_diagonal2_mul, Units.val_mul]; ring
  have hm0 : (((modulus ((a 1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ)) ≠ 0 := by
    rw [coe_modulus_eq_norm]; exact_mod_cast (norm_units_pos p (a 1)).ne'
  have hn0 : ((normChar p (σ 0) (a 1) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hn1 : ((normChar p (σ 1) (a 1) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  simp only [gInt]
  rw [hrow, map_mul, map_mul, Units.val_mul, Units.val_mul, Units.val_mul, modulus_mul]
  push_cast
  field_simp

theorem integral_gInt_diagonal2_mul (σ : Fin 2 → ℝ) (Φ : (Fin 2 → F) → ℂ)
    (a : Fin 2 → (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (g : G) :
    ∫ t, gInt p σ Φ (diagonal2 p a * g) t ∂(mulHaar p) =
      ((((normChar p (σ 0) (a 1) : ℂˣ) : ℂ))⁻¹ * ((normChar p (σ 1) (a 1) : ℂˣ) : ℂ) *
          (((modulus ((a 1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ))⁻¹) *
        ∫ t, gInt p σ Φ g t ∂(mulHaar p) := by
  simp_rw [gInt_diagonal2_mul]
  rw [integral_const_mul]
  congr 1
  exact integral_mul_left_eq_self (fun t => gInt p σ Φ g t) (a 1)

theorem posSection_diagonal2_mul (σ : Fin 2 → ℝ) (Φ : (Fin 2 → F) → ℂ)
    (a : Fin 2 → (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (g : G) :
    posSection p σ Φ (diagonal2 p a * g) =
      torusChar2 p (fun i => normChar p (σ i)) a * halfModulus2 p a * posSection p σ Φ g := by
  have h0 : 0 < ‖((a 0 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)‖ := norm_units_pos p (a 0)
  have h1 : 0 < ‖((a 1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)‖ := norm_units_pos p (a 1)
  have hc : 0 < ‖((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)‖ := norm_units_pos p _
  rw [posSection, posSection, integral_gInt_diagonal2_mul, det_diagonal2_mul, map_mul, map_mul, Units.val_mul, Units.val_mul,
    Units.val_mul, Units.val_mul]
  simp only [torusChar2, Fin.prod_univ_two, halfModulus2, normChar_apply, coe_modulus_eq_norm, norm_mul]
  rw [cpow_half_ofReal (by positivity), cpow_half_ofReal hc.le,
    Real.sqrt_mul' _ hc.le, Real.sqrt_mul h0.le, Real.sqrt_div h0.le]
  have hs1 : ((Real.sqrt ‖((a 1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr h1).ne'
  have hr0 : ((‖((a 1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)‖ ^ σ 0 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos h1 _).ne'
  have hsq : ((‖((a 1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)‖ : ℝ) : ℂ) =
      ((Real.sqrt ‖((a 1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)‖ : ℝ) : ℂ) *
        ((Real.sqrt ‖((a 1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)‖ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h1.le]
  rw [hsq]
  push_cast
  field_simp

theorem exists_forall_valued_sub_le_apply_eq (Φ : (Fin 2 → F) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) :
    ∃ N : ℤ, ∀ v w : Fin 2 → F, (∀ j, Valued.v (v j - w j) ≤ WithZero.exp N) → Φ v = Φ w := by
  obtain ⟨N, S, -, hΦ⟩ :=
    LanglandsTunnell.TateLocal.exists_finset_forall_eq_sum_mul_prod_indicator_ball_of_isLocallyConstant_of_hasCompactSupport
      p 2 Φ hΦ.1 hΦ.2
  refine ⟨N, fun v w hvw => ?_⟩
  rw [hΦ v, hΦ w]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_

  have hiff : v j ∈ {x : F | Valued.v (x - c j) ≤ WithZero.exp N} ↔ w j ∈ {x : F | Valued.v (x - c j) ≤ WithZero.exp N} := by
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      have : w j - c j = (v j - c j) + -(v j - w j) := by ring
      rw [this]
      exact (Valuation.map_add _ _ _).trans (max_le h (by rw [Valuation.map_neg]; exact hvw j))
    · intro h
      have : v j - c j = (w j - c j) + (v j - w j) := by ring
      rw [this]
      exact (Valuation.map_add _ _ _).trans (max_le h (hvw j))
  by_cases h : v j ∈ {x : F | Valued.v (x - c j) ≤ WithZero.exp N}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hiff.mpr h)]

theorem exists_forall_apply_ne_zero_valued_le (Φ : (Fin 2 → F) → ℂ) (hΦ : HasCompactSupport Φ) :
    ∃ K : ℤ, ∀ v : Fin 2 → F, Φ v ≠ 0 → ∀ j, Valued.v (v j) ≤ WithZero.exp K := by
  obtain ⟨R, hR0, hR⟩ := exists_bound_support p Φ hΦ
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R (one_lt_qR p)
  refine ⟨k, fun v hv j => ?_⟩
  by_cases h0 : v j = 0
  · rw [h0, map_zero]; exact zero_le'
  · have hvj : Valued.v (v j) ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
    set m : ℤ := WithZero.log (Valued.v (v j)) with hm
    have hvm : Valued.v (v j) = WithZero.exp m := (WithZero.exp_log hvj).symm
    have hnorm : ‖v j‖ = qR p ^ (-(-m)) := norm_eq_qR_zpow p (v j) (-m) (by rw [neg_neg]; exact hvm)
    rw [neg_neg] at hnorm
    have hle : ‖v j‖ ≤ R := (norm_le_pi_norm v j).trans (hR v hv)
    have hlt : qR p ^ m < qR p ^ (k : ℤ) := by rw [← hnorm, zpow_natCast]; exact lt_of_le_of_lt hle hk
    have hmk : m < k := (zpow_lt_zpow_iff_right₀ (one_lt_qR p)).1 hlt
    rw [hvm, WithZero.exp_le_exp]
    exact hmk.le

theorem exists_open_forall_gInt_eq (σ : Fin 2 → ℝ) {Φ : (Fin 2 → F) → ℂ}
    (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) (g₀ : G) :
    ∃ U : Set G, IsOpen U ∧ g₀ ∈ U ∧ ∀ g ∈ U, ∀ t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ,
      gInt p σ Φ g t = gInt p σ Φ g₀ t := by
  obtain ⟨N, hN⟩ := exists_forall_valued_sub_le_apply_eq p Φ hΦ
  obtain ⟨K, hK⟩ := exists_forall_apply_ne_zero_valued_le p Φ hΦ.2

  have hrow0 : ∃ j₀ : Fin 2, (g₀ : Mat) 1 j₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hdet : (g₀ : Mat).det = 0 := by
      rw [Matrix.det_fin_two, hall 0, hall 1]; ring
    exact (Matrix.GeneralLinearGroup.det g₀).ne_zero (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hdet)
  obtain ⟨j₀, hj₀⟩ := hrow0
  set D : ℤ := WithZero.log (Valued.v ((g₀ : Mat) 1 j₀)) with hD
  have hvD : Valued.v ((g₀ : Mat) 1 j₀) = WithZero.exp D := (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hj₀)).symm
  set M : ℤ := min (D - 1) (N - K + D) with hM
  refine ⟨{g : G | ∀ j, Valued.v ((g : Mat) 1 j - (g₀ : Mat) 1 j) ≤ WithZero.exp M}, ?_, ?_, ?_⟩
  ·
    have hc : ∀ j : Fin 2, Continuous fun g : G => (g : Mat) 1 j - (g₀ : Mat) 1 j :=
      fun j => ((Units.continuous_val.matrix_elem 1 j).sub continuous_const)
    have : {g : G | ∀ j, Valued.v ((g : Mat) 1 j - (g₀ : Mat) 1 j) ≤ WithZero.exp M} =
        ⋂ j : Fin 2, (fun g : G => (g : Mat) 1 j - (g₀ : Mat) 1 j) ⁻¹' {x : F | Valued.v x ≤ WithZero.exp M} := by
      ext g; simp
    rw [this]
    exact isOpen_iInter_of_finite fun j => (isOpen_ball (K := ℚ) (v := p) M).preimage (hc j)
  · intro j; simp
  · intro g hg t

    have hgj₀ : Valued.v ((g : Mat) 1 j₀) = WithZero.exp D := by
      have hlt : Valued.v ((g : Mat) 1 j₀ - (g₀ : Mat) 1 j₀) < Valued.v ((g₀ : Mat) 1 j₀) := by
        rw [hvD]
        refine lt_of_le_of_lt (hg j₀) ?_
        rw [WithZero.exp_lt_exp, hM]; omega
      have := Valuation.map_add_eq_of_lt_left (Valued.v : Valuation F _) hlt
      rw [add_sub_cancel] at this
      rw [this, hvD]

    suffices hΦeq : Φ (fun j : Fin 2 => (t : F) * (g : Mat) 1 j) = Φ (fun j : Fin 2 => (t : F) * (g₀ : Mat) 1 j) by
      simp only [gInt, hΦeq]
    by_cases hboth : Φ (fun j : Fin 2 => (t : F) * (g : Mat) 1 j) = 0 ∧ Φ (fun j : Fin 2 => (t : F) * (g₀ : Mat) 1 j) = 0
    · rw [hboth.1, hboth.2]
    ·
      have ht : Valued.v (t : F) ≤ WithZero.exp (K - D) := by
        rw [not_and_or] at hboth
        have key : ∀ x : F, Valued.v x = WithZero.exp D → Valued.v ((t : F) * x) ≤ WithZero.exp K →
            Valued.v (t : F) ≤ WithZero.exp (K - D) := by
          intro x hx h
          rw [Valuation.map_mul, hx] at h
          have : Valued.v (t : F) = Valued.v (t : F) * WithZero.exp D * WithZero.exp (-D) := by
            rw [mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, mul_one]
          rw [this, show (K - D : ℤ) = K + -D by ring, WithZero.exp_add]
          exact mul_le_mul_left h _
        rcases hboth with h | h
        · exact key _ hgj₀ (hK _ h j₀)
        · exact key _ hvD (hK _ h j₀)
      apply hN
      intro j
      rw [← mul_sub, Valuation.map_mul]
      calc Valued.v (t : F) * Valued.v ((g : Mat) 1 j - (g₀ : Mat) 1 j)
          ≤ WithZero.exp (K - D) * WithZero.exp M := mul_le_mul' ht (hg j)
        _ = WithZero.exp (K - D + M) := (WithZero.exp_add _ _).symm
        _ ≤ WithZero.exp N := by rw [WithZero.exp_le_exp, hM]; omega

theorem isLocallyConstant_posSection (σ : Fin 2 → ℝ) {Φ : (Fin 2 → F) → ℂ}
    (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) : IsLocallyConstant (posSection p σ Φ) := by

  have h1 : IsLocallyConstant fun g : G => ((normChar p (σ 0) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) :=
    ((isLocallyConstant_normChar p (σ 0)).comp_continuous Matrix.GeneralLinearGroup.continuous_det).comp (fun u : ℂˣ => (u : ℂ))
  have h2 : IsLocallyConstant fun g : G =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
    have e : (fun g : G => ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) =
        (fun r : ℝ => ((r : ℝ) : ℂ) ^ (1 / 2 : ℂ)) ∘ (fun a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ => ‖(a : F)‖) ∘
          (fun g : G => Matrix.GeneralLinearGroup.det g) := by
      funext g; simp [coe_modulus_eq_norm]
    rw [e]
    exact ((isLocallyConstant_norm_units p).comp_continuous Matrix.GeneralLinearGroup.continuous_det).comp _
  have h3 : IsLocallyConstant fun g : G => ∫ t, gInt p σ Φ g t ∂(mulHaar p) := by
    refine (IsLocallyConstant.iff_exists_open _).mpr fun g₀ => ?_
    obtain ⟨U, hU, hg₀, hUeq⟩ := exists_open_forall_gInt_eq p σ hΦ g₀
    exact ⟨U, hU, hg₀, fun g hg => by simp_rw [hUeq g hg]⟩
  exact (h1.mul h2).mul h3

theorem posSection_mem (σ : Fin 2 → ℝ) {Φ : (Fin 2 → F) → ℂ} (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) :
    posSection p σ Φ ∈ principalSeries2 p (fun i => normChar p (σ i)) :=
  mem_principalSeries2_iff.mpr ⟨isLocallyConstant_posSection p σ hΦ,
    fun x g => posSection_upperUnipotent2_mul p σ Φ x g, fun a g => posSection_diagonal2_mul p σ Φ a g⟩

end Membership

section Final
variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem posSection_mem_principalSeries2 (σ : Fin 2 → ℝ) (h01 : σ 1 < σ 0) {Φ : (Fin 2 → F) → ℂ}
    (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) :
    posSection p σ Φ ∈ principalSeries2 p (fun i => normChar p (σ i)) :=
  posSection_mem p σ hΦ

end Final

end Delta2xPG
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_normPowChar_godementSection_abs_mem_principalSeries2_of_lt.Delta2xPG"

open Delta2xPG in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (σ : Fin 2 → ℝ) (h01 : σ 1 < σ 0)
    (Φ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) :
    letI := localBorel ℚ p
    ∃ (μa : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ i, IsLocallyConstant (μa i)) ∧
      (∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ((μa i a : ℂˣ) : ℂ) = (((‖(a : p.adicCompletion ℚ)‖ ^ (σ i) : ℝ)) : ℂ)) ∧
      (∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μa i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i)) ∧
      f ∈ principalSeries2 p μa ∧
      (∀ g : GL (Fin 2) (p.adicCompletion ℚ), 0 ≤ (f g).re ∧ (f g).im = 0) ∧
      ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        Integrable (fun t : (p.adicCompletion ℚ)ˣ => (fun v : Fin 2 → p.adicCompletion ℚ => ((‖Φ v‖ : ℝ) : ℂ)) (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) * ((μa 0 t : ℂˣ) : ℂ) * (((μa 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        f g = ((μa 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
          ∫ t : (p.adicCompletion ℚ)ˣ, (fun v : Fin 2 → p.adicCompletion ℚ => ((‖Φ v‖ : ℝ) : ℂ)) (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) * ((μa 0 t : ℂˣ) : ℂ) * (((μa 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
  refine ⟨fun i => normChar p (σ i), posSection p σ Φ, fun i => isLocallyConstant_normChar p (σ i),
    fun i a => normChar_apply p (σ i) a, fun i a => norm_normChar p (σ i) a,
    posSection_mem_principalSeries2 p σ h01 hΦ, fun g => posSection_re_nonneg_im_zero p σ Φ g, fun g => ⟨?_, rfl⟩⟩
  exact integrable_gInt p σ h01 hΦ g

end
end S_LanglandsTunnell_RankinSelberg_exists_normPowChar_godementSection_abs_mem_principalSeries2_of_lt
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_normPowChar_godementSection_abs_mem_principalSeries2_of_lt (solution)
