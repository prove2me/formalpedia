-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ee593e6c-5775-5a69-97da-045a2226c59f

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero

set_option autoImplicit false
set_option maxHeartbeats 3200000

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.TateLocal MeasureTheory
open scoped NNReal ENNReal Topology Pointwise

noncomputable section

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

namespace LTZeta30NV

open LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v

theorem surjV : Function.Surjective (Valued.v : 𝕂 → WithZero (Multiplicative ℤ)) :=
  HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v

theorem isClopen_le {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0) :
    IsClopen {x : 𝕂 | Valued.v x ≤ γ} := by
  obtain ⟨y, hy⟩ := surjV v γ
  have h : {x : 𝕂 | Valued.v x ≤ γ} = {x : 𝕂 | Valued.v.restrict x ≤ Valued.v.restrict y} := by
    ext x; simp [Valuation.restrict_le_iff, hy]
  rw [h]
  have hy0 : y ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hy; exact hγ hy.symm
  exact Valued.isClopen_closedBall _ ((Valuation.ne_zero_iff _).mpr hy0)

theorem isClopen_lt (γ : WithZero (Multiplicative ℤ)) :
    IsClopen {x : 𝕂 | Valued.v x < γ} := by
  obtain ⟨y, hy⟩ := surjV v γ
  have h : {x : 𝕂 | Valued.v x < γ} = {x : 𝕂 | Valued.v.restrict x < Valued.v.restrict y} := by
    ext x; simp [Valuation.restrict_lt_iff, hy]
  rw [h]
  exact Valued.isClopen_ball _ _

theorem isClopen_eq {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0) :
    IsClopen {x : 𝕂 | Valued.v x = γ} := by
  obtain ⟨y, hy⟩ := surjV v γ
  have h : {x : 𝕂 | Valued.v x = γ} = {x : 𝕂 | Valued.v.restrict x = Valued.v.restrict y} := by
    ext x; simp [Valuation.restrict_inj, hy]
  rw [h]
  have hy0 : y ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hy; exact hγ hy.symm
  exact Valued.isClopen_sphere _ ((Valuation.ne_zero_iff _).mpr hy0)

theorem exists_ball_sub_of_mem_nhds {s : Set 𝕂} {x : 𝕂} (h : s ∈ 𝓝 x) :
    ∃ n : ℤ, ∀ y : 𝕂, Valued.v (y - x) ≤ WithZero.exp n → y ∈ s := by
  rw [Valued.mem_nhds] at h
  obtain ⟨γ, hγ⟩ := h
  set g : WithZero (Multiplicative ℤ) :=
    MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg
  have hg0 : g ≠ 0 := by
    rw [hg]
    exact (map_ne_zero _).mpr γ.ne_zero
  refine ⟨WithZero.log g - 1, fun y hy => hγ ?_⟩
  show Valued.v.restrict (y - x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hg]
  calc Valued.v (y - x) ≤ WithZero.exp (WithZero.log g - 1) := hy
    _ < WithZero.exp (WithZero.log g) := by
        rw [WithZero.exp_lt_exp]; omega
    _ = g := WithZero.exp_log hg0

def lat (n : ℤ) : Set 𝕂 := {x : 𝕂 | Valued.v x ≤ WithZero.exp n}

theorem mem_lat {n : ℤ} {x : 𝕂} : x ∈ lat v n ↔ Valued.v x ≤ WithZero.exp n := Iff.rfl

theorem zero_mem_lat (n : ℤ) : (0 : 𝕂) ∈ lat v n := by simp [mem_lat]

theorem add_mem_lat {n : ℤ} {x y : 𝕂} (hx : x ∈ lat v n) (hy : y ∈ lat v n) : x + y ∈ lat v n := by
  rw [mem_lat] at hx hy ⊢
  exact le_trans (Valued.v.map_add x y) (max_le hx hy)

theorem neg_mem_lat {n : ℤ} {x : 𝕂} (hx : x ∈ lat v n) : -x ∈ lat v n := by
  rw [mem_lat, Valuation.map_neg]; exact hx

theorem sub_mem_lat {n : ℤ} {x y : 𝕂} (hx : x ∈ lat v n) (hy : y ∈ lat v n) : x - y ∈ lat v n := by
  rw [sub_eq_add_neg]; exact add_mem_lat v hx (neg_mem_lat v hy)

theorem lat_mono {m n : ℤ} (h : m ≤ n) : lat v m ⊆ lat v n := fun _ hx =>
  le_trans hx (WithZero.exp_le_exp.mpr h)

theorem mul_mem_lat {k m : ℤ} {a x : 𝕂} (ha : Valued.v a ≤ WithZero.exp k) (hx : x ∈ lat v m) :
    a * x ∈ lat v (k + m) := by
  rw [mem_lat, Valuation.map_mul, WithZero.exp_add]
  exact mul_le_mul' ha hx

theorem isClopen_lat (n : ℤ) : IsClopen (lat v n) := isClopen_le v WithZero.exp_ne_zero

theorem isOpen_lat (n : ℤ) : IsOpen (lat v n) := (isClopen_lat v n).isOpen

theorem measurableSet_lat (n : ℤ) : MeasurableSet (lat v n) := (isOpen_lat v n).measurableSet

theorem lat_zero_eq : lat v 0 = (v.adicCompletionIntegers ℚ : Set 𝕂) := by
  ext x
  rw [mem_lat, WithZero.exp_zero]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).symm

theorem isCompact_lat (n : ℤ) : IsCompact (lat v n) := by
  have h0 : IsCompact (lat v 0) := by
    rw [lat_zero_eq]
    exact isCompact_iff_compactSpace.mpr
      (show CompactSpace (v.adicCompletionIntegers ℚ) from inferInstance)
  obtain ⟨y, hy⟩ := surjV v (WithZero.exp n)
  have hy0 : y ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hy; exact WithZero.exp_ne_zero hy.symm
  have hset : lat v n = (fun x => y * x) '' lat v 0 := by
    ext x
    constructor
    · intro hx
      refine ⟨y⁻¹ * x, ?_, by field_simp⟩
      rw [mem_lat, Valuation.map_mul, map_inv₀, hy, WithZero.exp_zero]
      rw [mem_lat] at hx
      calc (WithZero.exp n)⁻¹ * Valued.v x ≤ (WithZero.exp n)⁻¹ * WithZero.exp n :=
            mul_le_mul' le_rfl hx
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · rintro ⟨z, hz, rfl⟩
      rw [mem_lat, Valuation.map_mul, hy]
      rw [mem_lat, WithZero.exp_zero] at hz
      calc WithZero.exp n * Valued.v z ≤ WithZero.exp n * 1 := mul_le_mul' le_rfl hz
        _ = WithZero.exp n := mul_one _
  rw [hset]
  exact h0.image (continuous_const.mul continuous_id)

theorem ball_eq_of_mem {j : ℤ} {a c : 𝕂} (hc : c - a ∈ lat v j) :
    {y : 𝕂 | y - a ∈ lat v j} = {y : 𝕂 | y - c ∈ lat v j} := by
  ext y
  constructor
  · intro hy
    have : y - c = (y - a) - (c - a) := by ring
    show y - c ∈ lat v j
    rw [this]; exact sub_mem_lat v hy hc
  · intro hy
    have : y - a = (y - c) + (c - a) := by ring
    show y - a ∈ lat v j
    rw [this]; exact add_mem_lat v hy hc

theorem isOpen_ball (a : 𝕂) (j : ℤ) : IsOpen {y : 𝕂 | y - a ∈ lat v j} :=
  (isOpen_lat v j).preimage (continuous_id.sub continuous_const)

theorem measurableSet_ball (a : 𝕂) (j : ℤ) : MeasurableSet {y : 𝕂 | y - a ∈ lat v j} :=
  (isOpen_ball v a j).measurableSet

theorem v_natCast_le_one (k : ℕ) : Valued.v ((k : 𝕂)) ≤ 1 := by
  have : ((k : 𝕂)) ∈ (v.adicCompletionIntegers ℚ : Set 𝕂) := by
    have h := natCast_mem (v.adicCompletionIntegers ℚ) k
    exact_mod_cast h
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp this

section AddChar

variable {v}
variable (ψ : AddChar (HeightOneSpectrum.adicCompletion ℚ v) ℂ)

theorem continuous_of_lat_ker {n₀ : ℤ} (hker : ∀ x ∈ lat v n₀, ψ x = 1) : Continuous ψ := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  have hev : (fun y => ψ y) =ᶠ[𝓝 x₀] fun _ => ψ x₀ := by
    have hmem : {y : 𝕂 | y - x₀ ∈ lat v n₀} ∈ 𝓝 x₀ :=
      (isOpen_ball v x₀ n₀).mem_nhds (by simp [zero_mem_lat])
    filter_upwards [hmem] with y hy
    have : y = x₀ + (y - x₀) := by ring
    rw [this, AddChar.map_add_eq_mul, hker _ hy, mul_one]
  exact (continuousAt_const.congr hev.symm)

theorem norm_apply_eq_one (hc : Continuous ψ) (z : 𝕂) : ‖ψ z‖ = 1 := by

  have key : ∀ z : 𝕂, ‖ψ z‖ ≤ 1 := by
    intro z
    by_cases hz : z = 0
    · rw [hz, AddChar.map_zero_eq_one, norm_one]
    have hvz : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz
    set n := WithZero.log (Valued.v z) with hn
    have hzn : z ∈ lat v n := by
      rw [mem_lat, hn, WithZero.exp_log hvz]
    obtain ⟨C, hC⟩ := (isCompact_lat v n).exists_bound_of_continuousOn hc.continuousOn
    have hpow : ∀ k : ℕ, ‖ψ z‖ ^ k ≤ C := by
      intro k
      have hkz : (k • z) ∈ lat v n := by
        rw [nsmul_eq_mul, mem_lat, Valuation.map_mul]
        calc Valued.v (k : 𝕂) * Valued.v z ≤ 1 * Valued.v z :=
              mul_le_mul' (v_natCast_le_one v k) le_rfl
          _ = Valued.v z := one_mul _
          _ ≤ WithZero.exp n := hzn
      have := hC _ hkz
      rwa [AddChar.map_nsmul_eq_pow, norm_pow] at this
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hlt
    exact absurd (hpow k) (not_le.mpr hk)
  have h1 : ‖ψ z‖ * ‖ψ (-z)‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, norm_one]
  have hz := key z
  have hnz := key (-z)
  by_contra hne
  have hlt : ‖ψ z‖ < 1 := lt_of_le_of_ne hz hne
  have : ‖ψ z‖ * ‖ψ (-z)‖ < 1 := by
    calc ‖ψ z‖ * ‖ψ (-z)‖ ≤ ‖ψ z‖ * 1 := mul_le_mul_of_nonneg_left hnz (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hlt
  exact absurd h1 (ne_of_lt this)

theorem exists_level (hψ : ψ ≠ 1) {n₀ : ℤ} (hker : ∀ x ∈ lat v n₀, ψ x = 1) :
    ∃ d : ℤ, (∀ x ∈ lat v d, ψ x = 1) ∧ ∃ t ∈ lat v (d + 1), ψ t ≠ 1 := by
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.mp hψ
  have ht0 : t ≠ 0 := by
    intro h; rw [h, AddChar.map_zero_eq_one] at ht; exact ht rfl
  have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).mpr ht0
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, (∀ x ∈ lat v z, ψ x = 1) → z ≤ b := by
    refine ⟨WithZero.log (Valued.v t), fun z hz => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have : t ∈ lat v z := by
      rw [mem_lat, ← WithZero.exp_log hvt]
      exact WithZero.exp_le_exp.mpr hlt.le
    exact ht (hz t this)
  obtain ⟨d, hd, hmax⟩ := Int.exists_greatest_of_bdd hbdd ⟨n₀, hker⟩
  refine ⟨d, hd, ?_⟩
  by_contra h
  push Not at h
  have := hmax (d + 1) h
  omega

variable (μ : Measure (HeightOneSpectrum.adicCompletion ℚ v))

theorem setIntegral_lat_char_of_forall_eq_one {m : ℤ} {b : 𝕂}
    (h : ∀ x ∈ lat v m, ψ (b * x) = 1) :
    ∫ x in lat v m, ψ (b * x) ∂μ = (μ.real (lat v m) : ℂ) := by
  rw [setIntegral_congr_fun (measurableSet_lat v m) (fun x hx => h x hx), setIntegral_const]
  simp

theorem setIntegral_lat_char_eq_zero [μ.IsAddHaarMeasure] {m : ℤ} {b : 𝕂} {x₀ : 𝕂} (hx₀ : x₀ ∈ lat v m)
    (h : ψ (b * x₀) ≠ 1) :
    ∫ x in lat v m, ψ (b * x) ∂μ = 0 := by
  set I := ∫ x in lat v m, ψ (b * x) ∂μ with hI
  have hind : I = ∫ x, (lat v m).indicator (fun x => ψ (b * x)) x ∂μ := by
    rw [hI, integral_indicator (measurableSet_lat v m)]
  have htrans : ∫ x, (lat v m).indicator (fun x => ψ (b * x)) (x₀ + x) ∂μ =
      ∫ x, (lat v m).indicator (fun x => ψ (b * x)) x ∂μ :=
    integral_add_left_eq_self _ x₀
  have hpt : ∀ x, (lat v m).indicator (fun x => ψ (b * x)) (x₀ + x) =
      ψ (b * x₀) * (lat v m).indicator (fun x => ψ (b * x)) x := by
    intro x
    by_cases hx : x ∈ lat v m
    · have hx' : x₀ + x ∈ lat v m := add_mem_lat v hx₀ hx
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx, mul_add, AddChar.map_add_eq_mul]
    · have hx' : x₀ + x ∉ lat v m := by
        intro h'
        apply hx
        have : x = (x₀ + x) - x₀ := by ring
        rw [this]; exact sub_mem_lat v h' hx₀
      rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, mul_zero]
  simp_rw [hpt] at htrans
  rw [integral_const_mul, ← hind] at htrans

  have : (ψ (b * x₀) - 1) * I = 0 := by rw [sub_mul, one_mul, htrans, sub_self]
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) h
  · exact h1

theorem forall_lat_char_eq_one_iff {d : ℤ} (hd : ∀ x ∈ lat v d, ψ x = 1) {t : 𝕂}
    (ht : t ∈ lat v (d + 1)) (hψt : ψ t ≠ 1) (m : ℤ) (b : 𝕂) :
    (∀ x ∈ lat v m, ψ (b * x) = 1) ↔ Valued.v b ≤ WithZero.exp (d - m) := by
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have hb0 : b ≠ 0 := by
      intro hb; rw [hb, Valuation.map_zero] at hlt; exact not_lt_of_ge zero_le' hlt
    have hvb : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb0

    have hle : WithZero.exp (d - m + 1) ≤ Valued.v b := by
      rw [← WithZero.exp_log hvb] at hlt ⊢
      rw [WithZero.exp_lt_exp] at hlt
      rw [WithZero.exp_le_exp]
      omega

    have hx : b⁻¹ * t ∈ lat v m := by
      rw [mem_lat, Valuation.map_mul, map_inv₀]
      rw [mem_lat] at ht
      have h1 : Valued.v t ≤ Valued.v b * WithZero.exp m := by
        calc Valued.v t ≤ WithZero.exp (d + 1) := ht
          _ = WithZero.exp (d - m + 1) * WithZero.exp m := by
              rw [← WithZero.exp_add]; congr 1; ring
          _ ≤ Valued.v b * WithZero.exp m := mul_le_mul' hle le_rfl
      calc (Valued.v b)⁻¹ * Valued.v t ≤ (Valued.v b)⁻¹ * (Valued.v b * WithZero.exp m) :=
            mul_le_mul' le_rfl h1
        _ = WithZero.exp m := by rw [← mul_assoc, inv_mul_cancel₀ hvb, one_mul]
    have := h _ hx
    rw [← mul_assoc, mul_inv_cancel₀ hb0, one_mul] at this
    exact hψt this
  · intro hb x hx
    apply hd
    have := mul_mem_lat v hb hx
    rwa [sub_add_cancel] at this

end AddChar

section Modulus

def μ₀ : Measure 𝕂 := Measure.addHaarMeasure (integersPositiveCompacts ℚ v)

scoped instance : (μ₀ v).IsAddHaarMeasure := by unfold μ₀; infer_instance
scoped instance : (μ₀ v).Regular := by unfold μ₀; infer_instance

theorem μ₀_lat_zero_ne_zero : μ₀ v (lat v 0) ≠ 0 :=
  ((isOpen_lat v 0).measure_pos (μ₀ v) ⟨0, zero_mem_lat v 0⟩).ne'

theorem μ₀_lat_zero_ne_top : μ₀ v (lat v 0) ≠ ∞ := (isCompact_lat v 0).measure_lt_top.ne

theorem smul_lat_zero_of_v_eq_one (u : 𝕂ˣ) (hu : Valued.v (u : 𝕂) = 1) :
    u • lat v 0 = lat v 0 := by
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Units.smul_def, smul_eq_mul, mem_lat, Valuation.map_mul, hu, one_mul]
    exact hy
  · intro hx
    refine ⟨(u⁻¹ : 𝕂ˣ) • x, ?_, smul_inv_smul u x⟩
    rw [Units.smul_def, smul_eq_mul, mem_lat, Valuation.map_mul, Units.val_inv_eq_inv_val, map_inv₀, hu,
      inv_one, one_mul]
    exact hx

theorem distribHaarChar_eq_one_of_v_eq_one (u : 𝕂ˣ) (hu : Valued.v (u : 𝕂) = 1) :
    distribHaarChar 𝕂 u = 1 := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ₀ v) (μ₀_lat_zero_ne_zero v)
    (μ₀_lat_zero_ne_top v) ?_
  rw [smul_lat_zero_of_v_eq_one v u hu, ENNReal.coe_one, one_mul]

theorem modulus_eq_one_of_v_eq_one {a : 𝕂} (ha : Valued.v a = 1) : modulus a = 1 := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at ha; exact zero_ne_one ha
  rw [modulus_of_ne_zero ha0]
  exact distribHaarChar_eq_one_of_v_eq_one v (Units.mk0 a ha0) ha

theorem distribHaarChar_lt_one_of_uniformizer (ϖ : 𝕂ˣ) (hϖ : Valued.v (ϖ : 𝕂) = WithZero.exp (-1)) :
    distribHaarChar 𝕂 ϖ < 1 := by
  have hsmul : ϖ • lat v 0 = lat v (-1) := by
    ext x
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Units.smul_def, smul_eq_mul, mem_lat, Valuation.map_mul, hϖ]
      rw [mem_lat, WithZero.exp_zero] at hy
      calc WithZero.exp (-1) * Valued.v y ≤ WithZero.exp (-1) * 1 := mul_le_mul' le_rfl hy
        _ = WithZero.exp (-1) := mul_one _
    · intro hx
      refine ⟨(ϖ⁻¹ : 𝕂ˣ) • x, ?_, smul_inv_smul ϖ x⟩
      rw [Units.smul_def, smul_eq_mul, mem_lat, Valuation.map_mul, Units.val_inv_eq_inv_val, map_inv₀, hϖ,
        WithZero.exp_zero]
      rw [mem_lat] at hx
      calc (WithZero.exp (-1))⁻¹ * Valued.v x ≤ (WithZero.exp (-1))⁻¹ * WithZero.exp (-1) :=
            mul_le_mul' le_rfl hx
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero

  have hsub : {x : 𝕂 | Valued.v x = 1} ⊆ lat v 0 \ lat v (-1) := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    refine ⟨?_, ?_⟩
    · rw [mem_lat, hx, WithZero.exp_zero]
    · rw [mem_lat, hx, not_le, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hpos : μ₀ v (lat v 0 \ lat v (-1)) ≠ 0 := by
    refine (lt_of_lt_of_le ?_ (measure_mono hsub)).ne'
    exact (isClopen_eq v one_ne_zero).isOpen.measure_pos (μ₀ v) ⟨1, by simp⟩
  have hlt : μ₀ v (ϖ • lat v 0) < μ₀ v (lat v 0) := by
    rw [hsmul]
    have hunion : lat v (-1) ∪ lat v 0 = lat v 0 :=
      Set.union_eq_right.mpr (lat_mono v (by norm_num))
    calc μ₀ v (lat v (-1)) < μ₀ v (lat v (-1)) + μ₀ v (lat v 0 \ lat v (-1)) :=
          ENNReal.lt_add_right
            ((measure_mono (lat_mono v (by norm_num))).trans_lt
              (isCompact_lat v 0).measure_lt_top).ne hpos
      _ = μ₀ v (lat v 0) := by
          rw [measure_add_diff (measurableSet_lat v (-1)).nullMeasurableSet, hunion]
  have hmul := distribHaarChar_mul (μ₀ v) ϖ (lat v 0)
  rw [← hmul] at hlt
  have : (distribHaarChar 𝕂 ϖ : ℝ≥0∞) < 1 := by
    by_contra h
    rw [not_lt] at h
    have := mul_le_mul' h (le_refl (μ₀ v (lat v 0)))
    rw [one_mul] at this
    exact absurd hlt (not_lt.mpr this)
  exact_mod_cast this

theorem exists_theta : ∃ Θ : ℝ, 1 < Θ ∧
    ∀ a : 𝕂ˣ, ((modulus (a : 𝕂) : ℝ≥0) : ℝ) = Θ ^ ((WithZero.log (Valued.v (a : 𝕂)) : ℤ) : ℝ) := by
  obtain ⟨p, hp⟩ := surjV v (WithZero.exp (-1))
  have hp0 : p ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hp; exact WithZero.exp_ne_zero hp.symm
  set ϖ : 𝕂ˣ := Units.mk0 p hp0 with hϖdef
  have hϖ : Valued.v (ϖ : 𝕂) = WithZero.exp (-1) := hp
  set c : ℝ≥0 := distribHaarChar 𝕂 ϖ with hc
  have hc0 : 0 < c := distribHaarChar_pos
  have hc1 : c < 1 := distribHaarChar_lt_one_of_uniformizer v ϖ hϖ
  refine ⟨((c⁻¹ : ℝ≥0) : ℝ), ?_, fun a => ?_⟩
  · have : 1 < c⁻¹ := (one_lt_inv₀ hc0).mpr hc1
    exact_mod_cast this
  · set n : ℤ := WithZero.log (Valued.v (a : 𝕂)) with hn
    have hva : Valued.v (a : 𝕂) = WithZero.exp n := by
      rw [hn, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr a.ne_zero)]

    have hpow : (WithZero.exp (-1 : ℤ)) ^ n = WithZero.exp (-n) := by
      have h0 : (WithZero.exp (-1 : ℤ)) ^ n ≠ 0 := zpow_ne_zero _ WithZero.exp_ne_zero
      rw [← WithZero.exp_log h0, WithZero.log_zpow, WithZero.log_exp]
      simp
    have hunit : Valued.v ((a * ϖ ^ n : 𝕂ˣ) : 𝕂) = 1 := by
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Valuation.map_mul, map_zpow₀, hva, hϖ, hpow,
        ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    have h1 : distribHaarChar 𝕂 (a * ϖ ^ n) = 1 := distribHaarChar_eq_one_of_v_eq_one v _ hunit
    rw [map_mul, map_zpow, ← hc] at h1
    have hda : distribHaarChar 𝕂 a = c⁻¹ ^ n := by
      rw [inv_zpow']
      have hcn : c ^ n ≠ 0 := zpow_ne_zero _ hc0.ne'
      calc distribHaarChar 𝕂 a = distribHaarChar 𝕂 a * c ^ n * (c ^ n)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hcn, mul_one]
        _ = (c ^ n)⁻¹ := by rw [h1, one_mul]
        _ = c ^ (-n) := (zpow_neg c n).symm
    rw [modulus_coe_units, hda, NNReal.coe_zpow, Real.rpow_intCast]

end Modulus

section MulMeasure

theorem measurableEmbedding_val : MeasurableEmbedding (Units.val : 𝕂ˣ → 𝕂) where
  injective := Units.val_injective
  measurable := comap_measurable Units.val
  measurableSet_image' := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have : Units.val '' (Units.val ⁻¹' t) = t ∩ {x : 𝕂 | x ≠ 0} := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩; exact ⟨hu, u.ne_zero⟩
      · rintro ⟨hx, hx0⟩; exact ⟨Units.mk0 x hx0, hx, rfl⟩
    rw [this]
    exact ht.inter (measurableSet_singleton (0 : 𝕂)).compl

theorem measurable_val : Measurable (Units.val : 𝕂ˣ → 𝕂) := comap_measurable Units.val

theorem mulMeasure_apply_of_subset_sphere (μ : Measure 𝕂) {t : Set 𝕂} (ht : MeasurableSet t)
    (hsub : t ⊆ {x : 𝕂 | Valued.v x = 1}) : mulMeasure μ t = μ t := by
  have h0 : t ⊆ ({0}ᶜ : Set 𝕂) := by
    intro x hx h
    have := hsub hx
    simp only [Set.mem_setOf_eq] at this
    rw [Set.mem_singleton_iff] at h
    rw [h, Valuation.map_zero] at this
    exact zero_ne_one this
  rw [mulMeasure, withDensity_apply _ ht, Measure.restrict_restrict ht,
    Set.inter_eq_left.mpr h0]
  have : ∀ x ∈ t, ((modulus x : ℝ≥0∞))⁻¹ = 1 := by
    intro x hx
    rw [modulus_eq_one_of_v_eq_one v (hsub hx)]
    simp
  rw [setLIntegral_congr_fun ht this, setLIntegral_const, one_mul]

theorem comap_val_apply_of_subset_sphere (μ : Measure 𝕂) {t : Set 𝕂} (ht : MeasurableSet t)
    (hsub : t ⊆ {x : 𝕂 | Valued.v x = 1}) :
    Measure.comap Units.val (mulMeasure μ) (Units.val ⁻¹' t) = μ t := by
  rw [(measurableEmbedding_val v).comap_apply, Set.image_preimage_eq_inter_range]
  have : t ∩ Set.range (Units.val : 𝕂ˣ → 𝕂) = t := by
    refine Set.inter_eq_left.mpr fun x hx => ?_
    have h1 := hsub hx
    simp only [Set.mem_setOf_eq] at h1
    have hx0 : x ≠ 0 := by
      intro h; rw [h, Valuation.map_zero] at h1; exact zero_ne_one h1
    exact ⟨Units.mk0 x hx0, rfl⟩
  rw [this]
  exact mulMeasure_apply_of_subset_sphere v μ ht hsub

end MulMeasure

section Whittaker

variable {v}
variable (ψ : AddChar (HeightOneSpectrum.adicCompletion ℚ v) ℂ) (W : LocalGL3 v → ℂ)
  (U : Subgroup (LocalGL3 v))

theorem continuous_upperUnipotent : Continuous fun y : 𝕂 => (upperUnipotent3 y 0 0 : LocalGL3 v) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun y : 𝕂 => ((upperUnipotent3 y 0 0 : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop
  · change Continuous fun y : 𝕂 => (upperUnipotent3 y 0 0 : LocalGL3 v).inv
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop

theorem continuous_iotaDiag : Continuous fun b : 𝕂ˣ => (iotaGL (diagUnitGL2 b) : LocalGL3 v) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun b : 𝕂ˣ => ((iotaGL (diagUnitGL2 b) : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [embedMat2] <;> fun_prop
  · change Continuous fun b : 𝕂ˣ => embedMat2 (((diagUnitGL2 b)⁻¹ : GL (Fin 2) 𝕂) : Matrix (Fin 2) (Fin 2) 𝕂)
    have : ∀ b : 𝕂ˣ, (((diagUnitGL2 b)⁻¹ : GL (Fin 2) 𝕂) : Matrix (Fin 2) (Fin 2) 𝕂) =
        !![((b⁻¹ : 𝕂ˣ) : 𝕂), 0; 0, 1] := fun b => rfl
    simp_rw [this]
    have hinv : Continuous fun b : 𝕂ˣ => ((b⁻¹ : 𝕂ˣ) : 𝕂) := Units.continuous_coe_inv
    have hinv' : Continuous fun b : 𝕂ˣ => ((b : 𝕂))⁻¹ := by
      simpa [Units.val_inv_eq_inv_val] using hinv
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [embedMat2] <;> fun_prop

theorem iotaDiag_mul_upperUnipotent (a : 𝕂ˣ) (x : 𝕂) :
    (iotaGL (diagUnitGL2 a) : LocalGL3 v) * upperUnipotent3 x 0 0 =
      upperUnipotent3 ((a : 𝕂) * x) 0 0 * iotaGL (diagUnitGL2 a) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, embedMat2, upperUnipotent3]

variable {ψ W}

theorem apply_iotaDiag_upperUnipotent (hW : IsGL3PsiWhittakerFn ψ W) (a : 𝕂ˣ) (x : 𝕂) (g : LocalGL3 v) :
    W (iotaGL (diagUnitGL2 a) * (upperUnipotent3 x 0 0 * g)) =
      ψ ((a : 𝕂) * x) * W (iotaGL (diagUnitGL2 a) * g) := by
  rw [← mul_assoc, iotaDiag_mul_upperUnipotent, mul_assoc, hW, add_zero]

variable {U}

theorem exists_lat_conj_upperUnipotent_mem (hU : IsOpen (U : Set (LocalGL3 v))) (g : LocalGL3 v) :
    ∃ n : ℤ, ∀ y ∈ lat v n, g⁻¹ * upperUnipotent3 y 0 0 * g ∈ U := by
  have hc : Continuous fun y : 𝕂 => g⁻¹ * (upperUnipotent3 y 0 0 : LocalGL3 v) * g :=
    (continuous_const.mul (continuous_upperUnipotent (v := v))).mul continuous_const
  have hmem : (fun y : 𝕂 => g⁻¹ * (upperUnipotent3 y 0 0 : LocalGL3 v) * g) ⁻¹' (U : Set (LocalGL3 v)) ∈
      𝓝 (0 : 𝕂) := by
    refine (hU.preimage hc).mem_nhds ?_
    simp [upperUnipotent3_zero, U.one_mem]
  obtain ⟨n, hn⟩ := exists_ball_sub_of_mem_nhds v hmem
  refine ⟨n, fun y hy => hn y ?_⟩
  rw [sub_zero]; exact hy

theorem exists_lat_psi_eq_one (hW : IsGL3PsiWhittakerFn ψ W) (hU : IsOpen (U : Set (LocalGL3 v)))
    (hUW : ∀ k ∈ U, ∀ g : LocalGL3 v, W (g * k) = W g) {g₀ : LocalGL3 v} (hg₀ : W g₀ ≠ 0) :
    ∃ n₀ : ℤ, ∀ y ∈ lat v n₀, ψ y = 1 := by
  obtain ⟨n, hn⟩ := exists_lat_conj_upperUnipotent_mem hU g₀
  refine ⟨n, fun y hy => ?_⟩
  have h1 := hUW _ (hn y hy) g₀
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, hW, add_zero] at h1

  have : (ψ y - 1) * W g₀ = 0 := by rw [sub_mul, one_mul, h1, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hg₀

theorem exists_apply_iotaDiag_eq_zero (hW : IsGL3PsiWhittakerFn ψ W) (hψ : ψ ≠ 1)
    (hU : IsOpen (U : Set (LocalGL3 v))) (hUW : ∀ k ∈ U, ∀ g : LocalGL3 v, W (g * k) = W g)
    (g : LocalGL3 v) :
    ∃ N : ℤ, ∀ a : 𝕂ˣ, WithZero.exp N ≤ Valued.v (a : 𝕂) → W (iotaGL (diagUnitGL2 a) * g) = 0 := by
  obtain ⟨n, hn⟩ := exists_lat_conj_upperUnipotent_mem hU g
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.mp hψ
  have ht0 : t ≠ 0 := by
    intro h; rw [h, AddChar.map_zero_eq_one] at ht; exact ht rfl
  have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).mpr ht0
  refine ⟨WithZero.log (Valued.v t) - n, fun a ha => ?_⟩

  have hva : Valued.v (a : 𝕂) ≠ 0 := (Valuation.ne_zero_iff _).mpr a.ne_zero
  have hy : (a : 𝕂)⁻¹ * t ∈ lat v n := by
    rw [mem_lat, Valuation.map_mul, map_inv₀]
    rw [← WithZero.exp_log hva, WithZero.exp_le_exp] at ha
    rw [← WithZero.exp_log hva, ← WithZero.exp_log hvt, ← WithZero.exp_neg, ← WithZero.exp_add,
      WithZero.exp_le_exp]
    omega
  have hk := hUW _ (hn _ hy) (iotaGL (diagUnitGL2 a) * g)
  have heq : iotaGL (diagUnitGL2 a) * g * (g⁻¹ * upperUnipotent3 ((a : 𝕂)⁻¹ * t) 0 0 * g) =
      iotaGL (diagUnitGL2 a) * (upperUnipotent3 ((a : 𝕂)⁻¹ * t) 0 0 * g) := by group
  rw [heq, apply_iotaDiag_upperUnipotent hW, ← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul] at hk
  have : (ψ t - 1) * W (iotaGL (diagUnitGL2 a) * g) = 0 := by rw [sub_mul, one_mul, hk, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) ht
  · exact h

end Whittaker

section StepA

variable {v}

theorem setIntegral_ball_eq_zero_of_forall (μ : Measure 𝕂) [μ.IsAddHaarMeasure]
    (ψ : AddChar 𝕂 ℂ) (hψc : Continuous ψ)
    {d : ℤ} (hd : ∀ x ∈ lat v d, ψ x = 1) {t : 𝕂} (ht : t ∈ lat v (d + 1)) (hψt : ψ t ≠ 1)
    (ρ : Measure 𝕂) [IsFiniteMeasure ρ] (H : 𝕂 → ℂ) (hH : Integrable H ρ)
    (hvan : ∀ x : 𝕂, ∫ y, ψ (y * x) * H y ∂ρ = 0) (a₀ : 𝕂) (j : ℤ) :
    ∫ y in {y : 𝕂 | y - a₀ ∈ lat v j}, H y ∂ρ = 0 := by
  set m : ℤ := d - j with hm
  set ν : Measure 𝕂 := μ.restrict (lat v m) with hν
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (isCompact_lat v m).measure_lt_top.ne
  set G : 𝕂 → 𝕂 → ℂ := fun y x => ψ ((y - a₀) * x) * H y with hG

  have hGint : Integrable (Function.uncurry G) (ρ.prod ν) := by
    have hcont : Continuous fun p : 𝕂 × 𝕂 => ψ ((p.1 - a₀) * p.2) :=
      hψc.comp ((continuous_fst.sub continuous_const).mul continuous_snd)
    have hae : AEStronglyMeasurable (Function.uncurry G) (ρ.prod ν) :=
      hcont.aestronglyMeasurable.mul hH.1.comp_fst
    have hbound : Integrable (fun p : 𝕂 × 𝕂 => ‖H p.1‖ * (1 : ℝ)) (ρ.prod ν) :=
      hH.norm.mul_prod (integrable_const (1 : ℝ))
    refine hbound.mono' hae (Filter.Eventually.of_forall fun p => ?_)
    show ‖ψ ((p.1 - a₀) * p.2) * H p.1‖ ≤ ‖H p.1‖ * 1
    rw [norm_mul, norm_apply_eq_one ψ hψc, one_mul, mul_one]
  have hswap := integral_integral_swap hGint

  have hR : ∫ x, ∫ y, G y x ∂ρ ∂ν = 0 := by
    have : ∀ x, ∫ y, G y x ∂ρ = 0 := by
      intro x
      have hpt : ∀ y, G y x = ψ (-(a₀ * x)) * (ψ (y * x) * H y) := by
        intro y
        show ψ ((y - a₀) * x) * H y = _
        rw [show (y - a₀) * x = y * x + -(a₀ * x) by ring, AddChar.map_add_eq_mul]
        ring
      simp_rw [hpt]
      rw [integral_const_mul, hvan x, mul_zero]
    simp_rw [this]
    simp

  have hball : ∀ y : 𝕂, (∀ x ∈ lat v m, ψ ((y - a₀) * x) = 1) ↔ y - a₀ ∈ lat v j := by
    intro y
    rw [forall_lat_char_eq_one_iff ψ hd ht hψt m (y - a₀), mem_lat, hm, sub_sub_cancel]
  have hL : ∀ y, ∫ x, G y x ∂ν =
      {y : 𝕂 | y - a₀ ∈ lat v j}.indicator (fun y => (μ.real (lat v m) : ℂ) * H y) y := by
    intro y
    show ∫ x, ψ ((y - a₀) * x) * H y ∂ν = _
    rw [integral_mul_const]
    by_cases hy : y - a₀ ∈ lat v j
    · have hy' : y ∈ {y : 𝕂 | y - a₀ ∈ lat v j} := hy
      rw [Set.indicator_of_mem hy', hν,
        setIntegral_lat_char_of_forall_eq_one ψ μ ((hball y).mpr hy)]
    · have hy' : y ∉ {y : 𝕂 | y - a₀ ∈ lat v j} := hy
      rw [Set.indicator_of_notMem hy']
      have : ∃ x₀ ∈ lat v m, ψ ((y - a₀) * x₀) ≠ 1 := by
        by_contra h
        push Not at h
        exact hy ((hball y).mp h)
      obtain ⟨x₀, hx₀, hne⟩ := this
      rw [hν, setIntegral_lat_char_eq_zero ψ μ hx₀ hne, zero_mul]
  simp_rw [hL] at hswap
  rw [hR, integral_indicator (measurableSet_ball v a₀ j), integral_const_mul] at hswap
  have hvol : (μ.real (lat v m) : ℂ) ≠ 0 := by
    have : 0 < μ.real (lat v m) :=
      ENNReal.toReal_pos ((isOpen_lat v m).measure_pos μ ⟨0, zero_mem_lat v m⟩).ne'
        (isCompact_lat v m).measure_lt_top.ne
    exact_mod_cast this.ne'
  exact (mul_eq_zero.mp hswap).resolve_left hvol

theorem ae_eq_zero_of_forall_integral_char_mul_eq_zero (μ : Measure 𝕂) [μ.IsAddHaarMeasure]
    (ψ : AddChar 𝕂 ℂ) (hψc : Continuous ψ)
    {d : ℤ} (hd : ∀ x ∈ lat v d, ψ x = 1) {t : 𝕂} (ht : t ∈ lat v (d + 1)) (hψt : ψ t ≠ 1)
    (ρ : Measure 𝕂) [IsFiniteMeasure ρ] (H : 𝕂 → ℂ) (hH : Integrable H ρ)
    (hvan : ∀ x : 𝕂, ∫ y, ψ (y * x) * H y ∂ρ = 0) :
    H =ᵐ[ρ] 0 := by
  set S : Set (Set 𝕂) := {B | ∃ (a : 𝕂) (j : ℤ), B = {y : 𝕂 | y - a ∈ lat v j}} with hS
  have hpi : IsPiSystem S := by
    rintro B₁ ⟨a, j, rfl⟩ B₂ ⟨b, k, rfl⟩ ⟨c, hc1, hc2⟩
    have hc1' : c - a ∈ lat v j := hc1
    have hc2' : c - b ∈ lat v k := hc2
    rw [ball_eq_of_mem v hc1', ball_eq_of_mem v hc2']
    rcases le_total j k with hjk | hkj
    · refine ⟨c, j, ?_⟩
      ext y
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨fun h => h.1, fun h => ⟨h, lat_mono v hjk h⟩⟩
    · refine ⟨c, k, ?_⟩
      ext y
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨fun h => h.2, fun h => ⟨lat_mono v hkj h, h⟩⟩
  have hbasis : TopologicalSpace.IsTopologicalBasis S := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨a, j, rfl⟩
      exact isOpen_ball v a j
    · intro a u hau hu
      obtain ⟨n, hn⟩ := exists_ball_sub_of_mem_nhds v (hu.mem_nhds hau)
      refine ⟨{y : 𝕂 | y - a ∈ lat v n}, ⟨a, n, rfl⟩, ?_, fun y hy => hn y hy⟩
      simp [zero_mem_lat]
  have hgen : (localBorel ℚ v : MeasurableSpace 𝕂) = MeasurableSpace.generateFrom S :=
    hbasis.borel_eq_generateFrom
  have htot : ∫ y, H y ∂ρ = 0 := by simpa using hvan 0
  have hall : ∀ (u : Set 𝕂) (hu : MeasurableSet u), ∫ y in u, H y ∂ρ = 0 := by
    refine MeasurableSpace.induction_on_inter (C := fun u _ => ∫ y in u, H y ∂ρ = 0) hgen hpi ?_ ?_ ?_ ?_
    · simp
    · rintro u ⟨a, j, rfl⟩
      exact setIntegral_ball_eq_zero_of_forall μ ψ hψc hd ht hψt ρ H hH hvan a j
    · intro u hum hC
      have h1 := integral_add_compl hum hH
      rw [hC, htot, zero_add] at h1
      exact h1
    · intro f hdisj hfm hC
      rw [integral_iUnion hfm hdisj hH.integrableOn]
      simp [hC]
  exact hH.ae_eq_zero_of_forall_setIntegral_eq_zero fun u hu _ => hall u hu

end StepA

section StepB

variable {v}

theorem integral_ne_zero_of_shell (ρ : Measure 𝕂ˣ) (Fn : 𝕂ˣ → ℂ) {Θ : ℝ} (hΘ : 1 < Θ)
    (w : 𝕂ˣ → ℝ) (nn : 𝕂ˣ → ℤ) (hnn : Measurable nn) (hw : ∀ a, w a = Θ ^ ((nn a : ℤ) : ℝ))
    {σ : ℝ} (hint : ∀ s : ℂ, σ < s.re → Integrable (fun a => Fn a * ((w a : ℝ) : ℂ) ^ (s - 1)) ρ)
    {N : ℤ} (hvan : ∀ a, N ≤ nn a → Fn a = 0)
    {n₁ : ℤ} (hA : ∫ a in {a | nn a = n₁}, Fn a ∂ρ ≠ 0) :
    ∃ σ' : ℝ, σ ≤ σ' ∧ ∀ s : ℂ, σ' < s.re → ∫ a, Fn a * ((w a : ℝ) : ℂ) ^ (s - 1) ∂ρ ≠ 0 := by
  have hΘ0 : 0 < Θ := by linarith
  set A : ℤ → ℂ := fun n => ∫ a in {a | nn a = n}, Fn a ∂ρ with hAdef
  have hmeas : ∀ n, MeasurableSet {a : 𝕂ˣ | nn a = n} := fun n => hnn (measurableSet_singleton n)
  have hAvan : ∀ n, N ≤ n → A n = 0 := fun n hn =>
    setIntegral_eq_zero_of_forall_eq_zero fun a ha => hvan a (hn.trans_eq (Eq.symm ha))
  obtain ⟨n₀, hn₀, hmax⟩ := Int.exists_greatest_of_bdd (P := fun n => A n ≠ 0)
    ⟨N, fun z hz => le_of_lt (not_le.mp fun h => hz (hAvan z h))⟩ ⟨n₁, hA⟩
  have hgt : ∀ n, n₀ < n → A n = 0 := fun n hn => by
    by_contra h; exact absurd (hmax n h) (not_le.mpr hn)
  set s₁ : ℝ := σ + 1 with hs₁
  have hΦ₁ := hint (s₁ : ℂ) (by simp [hs₁])
  set T : ℝ := ∫ a, ‖Fn a * ((w a : ℝ) : ℂ) ^ ((s₁ : ℂ) - 1)‖ ∂ρ with hT
  have hT0 : 0 ≤ T := integral_nonneg fun _ => norm_nonneg _
  set D : ℝ := Θ ^ ((n₀ : ℝ) * (s₁ - 1)) * ‖A n₀‖ with hD
  have hD0 : 0 < D := mul_pos (Real.rpow_pos_of_pos hΘ0 _) (norm_pos_iff.mpr hn₀)
  set R : ℝ := T / D with hR
  have hR0 : 0 ≤ R := div_nonneg hT0 hD0.le
  have hlogb : 0 ≤ Real.logb Θ (R + 1) := Real.logb_nonneg hΘ (by linarith)
  refine ⟨s₁ + Real.logb Θ (R + 1), by linarith, fun s hs => ?_⟩
  set x : ℝ := s.re with hx
  have hxs₁ : s₁ < x := by linarith
  have hΦ := hint s (by linarith)
  have hkey : R < Θ ^ (x - s₁) := by
    calc R < R + 1 := by linarith
      _ = Θ ^ (Real.logb Θ (R + 1)) := (Real.rpow_logb hΘ0 hΘ.ne' (by linarith)).symm
      _ < Θ ^ (x - s₁) := Real.rpow_lt_rpow_of_exponent_lt hΘ (by linarith)
  set Φ : 𝕂ˣ → ℂ := fun a => Fn a * ((w a : ℝ) : ℂ) ^ (s - 1) with hΦdef

  have hshell : ∀ n : ℤ, ∫ a in {a | nn a = n}, Φ a ∂ρ =
      A n * (((Θ ^ ((n : ℤ) : ℝ) : ℝ) : ℂ) ^ (s - 1)) := by
    intro n
    have heq : Set.EqOn Φ (fun a => Fn a * (((Θ ^ ((n : ℤ) : ℝ) : ℝ) : ℂ) ^ (s - 1))) {a | nn a = n} := by
      intro a ha
      have ha' : nn a = n := ha
      simp only [hΦdef, hw a, ha']
    rw [setIntegral_congr_fun (hmeas n) heq, integral_mul_const]

  set Lo : Set 𝕂ˣ := {a | nn a < n₀} with hLodef
  set Mid : Set 𝕂ˣ := {a | nn a = n₀} with hMiddef
  set Hi : Set 𝕂ˣ := {a | n₀ < nn a} with hHidef
  have hLo : MeasurableSet Lo := hnn measurableSet_Iio
  have hMid : MeasurableSet Mid := hmeas n₀
  have hHi : MeasurableSet Hi := hnn measurableSet_Ioi
  have hsplit : ∀ a, Φ a = Lo.indicator Φ a + Mid.indicator Φ a + Hi.indicator Φ a := by
    intro a
    rcases lt_trichotomy (nn a) n₀ with h | h | h
    · have h1 : a ∈ Lo := h
      have h2 : a ∉ Mid := fun h' => absurd (h' : nn a = n₀) h.ne
      have h3 : a ∉ Hi := fun h' => absurd (h' : n₀ < nn a) (not_lt.mpr h.le)
      simp [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, Set.indicator_of_notMem h3]
    · have h1 : a ∉ Lo := by simp [hLodef, h]
      have h2 : a ∈ Mid := h
      have h3 : a ∉ Hi := by simp [hHidef, h]
      simp [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, Set.indicator_of_notMem h3]
    · have h1 : a ∉ Lo := fun h' => absurd (h' : nn a < n₀) (not_lt.mpr h.le)
      have h2 : a ∉ Mid := fun h' => absurd (h' : nn a = n₀) h.ne'
      have h3 : a ∈ Hi := h
      simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, Set.indicator_of_mem h3]
  have hI : ∫ a, Φ a ∂ρ = ∫ a in Lo, Φ a ∂ρ + ∫ a in Mid, Φ a ∂ρ + ∫ a in Hi, Φ a ∂ρ := by
    have h12 : Integrable (fun a => Lo.indicator Φ a + Mid.indicator Φ a) ρ :=
      (hΦ.indicator hLo).add (hΦ.indicator hMid)
    have h1 : Integrable (fun a => Lo.indicator Φ a) ρ := hΦ.indicator hLo
    have h2 : Integrable (fun a => Mid.indicator Φ a) ρ := hΦ.indicator hMid
    have h3 : Integrable (fun a => Hi.indicator Φ a) ρ := hΦ.indicator hHi
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_add h12 h3,
      integral_add h1 h2, integral_indicator hLo, integral_indicator hMid, integral_indicator hHi]

  have hHi0 : ∫ a in Hi, Φ a ∂ρ = 0 := by
    have hUnion : Hi = ⋃ n : {n : ℤ // n₀ < n}, {a : 𝕂ˣ | nn a = n.1} := by
      ext a
      rw [hHidef]
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro h; exact ⟨⟨nn a, h⟩, rfl⟩
      · rintro ⟨n, hn⟩; rw [hn]; exact n.2
    have hdisj : Pairwise (Function.onFun Disjoint fun n : {n : ℤ // n₀ < n} => {a : 𝕂ˣ | nn a = n.1}) := by
      intro i k hik
      refine Set.disjoint_left.mpr fun a hai hak => hik (Subtype.ext ?_)
      exact (Eq.symm hai).trans hak
    rw [hUnion, integral_iUnion (fun n : {n : ℤ // n₀ < n} => hmeas n.1) hdisj hΦ.integrableOn]
    have : ∀ n : {n : ℤ // n₀ < n}, ∫ a in {a | nn a = n.1}, Φ a ∂ρ = 0 := fun n => by
      rw [hshell n.1, hgt n.1 n.2, zero_mul]
    simp [this]

  have hnormMid : ‖∫ a in Mid, Φ a ∂ρ‖ = D * Θ ^ ((n₀ : ℝ) * (x - s₁)) := by
    rw [hshell n₀, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hΘ0 _),
      ← Real.rpow_mul hΘ0.le, hD]
    simp only [Complex.sub_re, Complex.one_re]
    have : Θ ^ ((n₀ : ℝ) * (x - 1)) = Θ ^ ((n₀ : ℝ) * (s₁ - 1)) * Θ ^ ((n₀ : ℝ) * (x - s₁)) := by
      rw [← Real.rpow_add hΘ0]; congr 1; ring
    rw [← hx, this]; ring

  set C : ℝ := Θ ^ (((n₀ : ℝ) - 1) * (x - s₁)) with hC
  have hC0 : 0 < C := Real.rpow_pos_of_pos hΘ0 _
  have hLoBound : ‖∫ a in Lo, Φ a ∂ρ‖ ≤ C * T := by
    have hpt : ∀ a ∈ Lo, ‖Φ a‖ ≤ C * ‖Fn a * ((w a : ℝ) : ℂ) ^ ((s₁ : ℂ) - 1)‖ := by
      intro a ha
      have ha' : nn a < n₀ := ha
      have hwpos : 0 < w a := by rw [hw a]; exact Real.rpow_pos_of_pos hΘ0 _
      simp only [hΦdef, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hwpos, Complex.sub_re,
        Complex.one_re, Complex.ofReal_re, ← hx]
      have hle : w a ^ (x - 1) ≤ C * w a ^ (s₁ - 1) := by
        rw [show x - 1 = (x - s₁) + (s₁ - 1) by ring, Real.rpow_add hwpos]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hwpos.le _)
        rw [hw a, ← Real.rpow_mul hΘ0.le, hC]
        apply Real.rpow_le_rpow_of_exponent_le hΘ.le
        have h1 : ((nn a : ℤ) : ℝ) ≤ (n₀ : ℝ) - 1 := by
          have : nn a ≤ n₀ - 1 := by omega
          exact_mod_cast this
        have h2 : 0 ≤ x - s₁ := by linarith
        nlinarith
      calc ‖Fn a‖ * w a ^ (x - 1) ≤ ‖Fn a‖ * (C * w a ^ (s₁ - 1)) :=
            mul_le_mul_of_nonneg_left hle (norm_nonneg _)
        _ = C * (‖Fn a‖ * w a ^ (s₁ - 1)) := by ring
    calc ‖∫ a in Lo, Φ a ∂ρ‖ ≤ ∫ a in Lo, C * ‖Fn a * ((w a : ℝ) : ℂ) ^ ((s₁ : ℂ) - 1)‖ ∂ρ :=
          norm_integral_le_of_norm_le ((hΦ₁.norm.const_mul C).integrableOn)
            ((ae_restrict_iff' hLo).mpr (Filter.Eventually.of_forall hpt))
      _ = C * ∫ a in Lo, ‖Fn a * ((w a : ℝ) : ℂ) ^ ((s₁ : ℂ) - 1)‖ ∂ρ := integral_const_mul _ _
      _ ≤ C * T := by
          refine mul_le_mul_of_nonneg_left ?_ hC0.le
          exact setIntegral_le_integral hΦ₁.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)

  intro h0
  rw [hI, hHi0, add_zero] at h0
  have hMid_eq : ∫ a in Mid, Φ a ∂ρ = -(∫ a in Lo, Φ a ∂ρ) := by
    linear_combination h0
  have hle : D * Θ ^ ((n₀ : ℝ) * (x - s₁)) ≤ C * T := by
    rw [← hnormMid, hMid_eq, norm_neg]; exact hLoBound
  have hTlt : T < Θ ^ (x - s₁) * D := by
    have : T = R * D := by rw [hR, div_mul_cancel₀ _ hD0.ne']
    rw [this]
    exact mul_lt_mul_of_pos_right hkey hD0
  have hexp : C * Θ ^ (x - s₁) = Θ ^ ((n₀ : ℝ) * (x - s₁)) := by
    rw [hC, ← Real.rpow_add hΘ0]; congr 1; ring
  have : D * Θ ^ ((n₀ : ℝ) * (x - s₁)) < D * Θ ^ ((n₀ : ℝ) * (x - s₁)) :=
    calc D * Θ ^ ((n₀ : ℝ) * (x - s₁)) ≤ C * T := hle
      _ < C * (Θ ^ (x - s₁) * D) := mul_lt_mul_of_pos_left hTlt hC0
      _ = D * Θ ^ ((n₀ : ℝ) * (x - s₁)) := by rw [← mul_assoc, hexp, mul_comm]
  exact lt_irrefl _ this

end StepB

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^
    (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos (pos_iff_ne_zero.mpr (HeightOneSpectrum.absNorm_ne_zero v))).ne'
  have hdef : selfDualHaarAt ℚ v = c • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) := rfl
  have h : selfDualHaarAt ℚ v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) := by
    rw [hdef]
    ext s _
    rw [Measure.coe_nnreal_smul_apply, Measure.smul_apply, smul_eq_mul]
  rw [h]
  exact Measure.IsAddHaarMeasure.smul _ (ENNReal.coe_ne_zero.mpr hc0) ENNReal.coe_ne_top

theorem diagUnitGL2_one : diagUnitGL2 (1 : 𝕂ˣ) = 1 := by
  rw [← diagHom_apply, map_one]

end LTZeta30NV
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero.LTZeta30NV"

open LanglandsTunnell.CubicInduction LTZeta30NV

theorem solution
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψv : ψv ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hW0 : W ≠ 0)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hconv : ∀ g : LocalGL3 v, ∃ σ : ℝ,
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ g σ) :
    letI := localBorel ℚ v
    (∃ (g : LocalGL3 v) (σ : ℝ),
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ g σ ∧
      ∀ s : ℂ, σ < s.re →
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g ≠ 0) := by
  obtain ⟨U, hUo, hUW⟩ := hsm
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, W g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hW0 (funext fun g => h g)

  obtain ⟨n₀, hn₀⟩ := exists_lat_psi_eq_one hW hUo hUW hg₀
  have hψc : Continuous ψv := continuous_of_lat_ker ψv hn₀
  obtain ⟨d, hd, t, ht, hψt⟩ := exists_level ψv hψv hn₀

  set μ : Measure (v.adicCompletion ℚ) := selfDualHaarAt ℚ v with hμ
  haveI : μ.IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt v
  set μx : Measure (v.adicCompletion ℚ)ˣ := Measure.comap Units.val (mulMeasure μ) with hμx

  obtain ⟨Θ, hΘ, hmod⟩ := exists_theta v
  set nn : (v.adicCompletion ℚ)ˣ → ℤ := fun a => WithZero.log (Valued.v (a : v.adicCompletion ℚ)) with hnn
  have hshell_iff : ∀ (a : (v.adicCompletion ℚ)ˣ) (n : ℤ),
      nn a = n ↔ Valued.v (a : v.adicCompletion ℚ) = WithZero.exp n := by
    intro a n
    have hva : Valued.v (a : v.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr a.ne_zero
    constructor
    · intro h; rw [← h]; simp only [hnn]; exact (WithZero.exp_log hva).symm
    · intro h; simp only [hnn, h, WithZero.log_exp]
  have hnn_meas : Measurable nn := by
    refine measurable_to_countable' fun n => ?_
    have : nn ⁻¹' {n} = Units.val ⁻¹' {x : v.adicCompletion ℚ | Valued.v x = WithZero.exp n} := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      exact hshell_iff a n
    rw [this]
    exact measurable_val v (isClopen_eq v WithZero.exp_ne_zero).isOpen.measurableSet

  set Sh : Set (v.adicCompletion ℚ)ˣ := {a | nn a = 0} with hSh
  have hSh_eq : Sh = Units.val ⁻¹' {x : v.adicCompletion ℚ | Valued.v x = 1} := by
    ext a
    rw [hSh]
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [hshell_iff a 0, WithZero.exp_zero]
  have hsphere_meas : MeasurableSet {x : v.adicCompletion ℚ | Valued.v x = 1} :=
    (isClopen_eq v one_ne_zero).isOpen.measurableSet
  have hSh_meas : MeasurableSet Sh := by rw [hSh_eq]; exact measurable_val v hsphere_meas
  have hSh_v : ∀ a ∈ Sh, Valued.v (a : v.adicCompletion ℚ) = 1 := fun a ha => by
    have := (hshell_iff a 0).mp ha; rwa [WithZero.exp_zero] at this
  by_cases hex : ∃ (g : LocalGL3 v) (n : ℤ),
      ∫ a in {a : (v.adicCompletion ℚ)ˣ | nn a = n},
        W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) ∂μx ≠ 0
  ·
    obtain ⟨g, n₁, hA⟩ := hex
    obtain ⟨σ, hσ⟩ := hconv g
    have hσ' : ∀ s : ℂ, σ < s.re → Integrable (fun a : (v.adicCompletion ℚ)ˣ =>
        W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) μx := hσ
    obtain ⟨N, hN⟩ := exists_apply_iotaDiag_eq_zero hW hψv hUo hUW g
    obtain ⟨σ', hσσ', hZ⟩ := integral_ne_zero_of_shell μx
      (fun a => W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ)) hΘ
      (fun a => ((modulus (a : v.adicCompletion ℚ) : ℝ≥0) : ℝ)) nn hnn_meas hmod
      (σ := σ) hσ' (N := N) (fun a ha => by
        show W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) = 0
        rw [hN a ((WithZero.le_log_iff_exp_le ((Valuation.ne_zero_iff _).mpr a.ne_zero)).mp ha),
          zero_mul])
      (n₁ := n₁) hA
    refine ⟨g, σ', fun s hs => hσ' s (lt_of_le_of_lt hσσ' hs), fun s hs => ?_⟩
    exact hZ s hs
  ·
    exfalso
    push Not at hex

    have hμxSh : μx Sh < ∞ := by
      rw [hSh_eq, hμx, comap_val_apply_of_subset_sphere v μ hsphere_meas subset_rfl]
      refine (measure_mono fun x hx => ?_).trans_lt (isCompact_lat v 0).measure_lt_top
      simp only [Set.mem_setOf_eq] at hx
      rw [mem_lat, hx, WithZero.exp_zero]
    set H : (v.adicCompletion ℚ)ˣ → ℂ := fun a => W (iotaGL (diagUnitGL2 a) * g₀) * ((χ a : ℂˣ) : ℂ) with hH
    obtain ⟨σ₀, hσ₀⟩ := hconv g₀
    have hσ₀' : ∀ s : ℂ, σ₀ < s.re → Integrable (fun a : (v.adicCompletion ℚ)ˣ =>
        W (iotaGL (diagUnitGL2 a) * g₀) * ((χ a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) μx := hσ₀
    have hHint : IntegrableOn H Sh μx := by
      have h1 := (hσ₀' ((σ₀ + 1 : ℝ) : ℂ) (by simp)).integrableOn (s := Sh)
      refine h1.congr_fun (fun a ha => ?_) hSh_meas
      simp only [hH, modulus_eq_one_of_v_eq_one v (hSh_v a ha), NNReal.coe_one, Complex.ofReal_one,
        Complex.one_cpow, mul_one]
    set ρ : Measure (v.adicCompletion ℚ)ˣ := μx.restrict Sh with hρ
    haveI : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr hμxSh.ne
    set ρ' : Measure (v.adicCompletion ℚ) := ρ.map Units.val with hρ'
    classical
    set H' : v.adicCompletion ℚ → ℂ := fun y => if h : y = 0 then 0 else H (Units.mk0 y h) with hH'
    have hH'val : ∀ a : (v.adicCompletion ℚ)ˣ, H' (a : v.adicCompletion ℚ) = H a := by
      intro a; simp only [hH', dif_neg a.ne_zero, Units.mk0_val]
    have hme := measurableEmbedding_val v
    have hH'int : Integrable H' ρ' := by
      rw [hρ', hme.integrable_map_iff]
      have : H' ∘ Units.val = H := funext hH'val
      rw [this]; exact hHint
    have hvan : ∀ x : v.adicCompletion ℚ, ∫ y, ψv (y * x) * H' y ∂ρ' = 0 := by
      intro x
      rw [hρ', hme.integral_map]
      simp only [hH'val]
      have h := hex (upperUnipotent3 x 0 0 * g₀) 0
      rw [← hSh] at h
      simp_rw [apply_iotaDiag_upperUnipotent hW] at h
      rw [hρ, hH]
      simpa only [mul_assoc] using h
    have hae := ae_eq_zero_of_forall_integral_char_mul_eq_zero μ ψv hψc hd ht hψt ρ' H' hH'int hvan

    set P : Set (v.adicCompletion ℚ)ˣ :=
      {b | Valued.v (b : v.adicCompletion ℚ) = 1} ∩ {b | g₀⁻¹ * iotaGL (diagUnitGL2 b) * g₀ ∈ U} with hP
    have hPopen : IsOpen P := by
      refine IsOpen.inter ?_ ?_
      · exact (isClopen_eq v one_ne_zero).isOpen.preimage Units.continuous_val
      · exact hUo.preimage ((continuous_const.mul continuous_iotaDiag).mul continuous_const)
    have h1P : (1 : (v.adicCompletion ℚ)ˣ) ∈ P := by
      refine ⟨by simp, ?_⟩
      show g₀⁻¹ * iotaGL (diagUnitGL2 1) * g₀ ∈ U
      rw [diagUnitGL2_one, map_one, mul_one, inv_mul_cancel]
      exact U.one_mem
    set E : Set (v.adicCompletion ℚ) := Units.val '' P with hE
    have hEopen : IsOpen E := IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap P hPopen
    have hEne : E.Nonempty := ⟨_, 1, h1P, rfl⟩
    have hEsub : E ⊆ {x : v.adicCompletion ℚ | Valued.v x = 1} := by
      rintro _ ⟨b, hb, rfl⟩; exact hb.1
    have hEpos : 0 < ρ' E := by
      rw [hρ', hme.map_apply, hρ, Measure.restrict_apply' hSh_meas]
      have hpre : Units.val ⁻¹' E ∩ Sh = Units.val ⁻¹' E := by
        refine Set.inter_eq_left.mpr fun a ha => ?_
        rw [hSh_eq]; exact hEsub ha
      rw [hpre, hμx, comap_val_apply_of_subset_sphere v μ hEopen.measurableSet hEsub]
      exact hEopen.measure_pos μ hEne
    have hEnz : E ⊆ {y | H' y ≠ 0} := by
      rintro _ ⟨b, hb, rfl⟩
      rw [Set.mem_setOf_eq, hH'val, hH]
      have hk := hUW _ hb.2 g₀
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at hk
      show W (iotaGL (diagUnitGL2 b) * g₀) * ((χ b : ℂˣ) : ℂ) ≠ 0
      rw [hk]
      exact mul_ne_zero hg₀ (Units.ne_zero _)
    have hzero : ρ' {y | H' y ≠ 0} = 0 := by
      have := ae_iff.mp hae
      simpa using this
    have hle := measure_mono (μ := ρ') hEnz
    rw [hzero] at hle
    exact absurd hle (not_le.mpr hEpos)

end
end S_LanglandsTunnell_CubicInduction_exists_forall_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero (solution)
