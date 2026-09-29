-- Prove2me | solution 1 for NumberField.AdelicBox.exists_eq_sum_indicator_image_integralFiniteAdeles
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/17f532d3-2cc0-5cb6-8e17-9b6e3e5f954b

import Definitions.Def_NumberField_AdelicBox
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.Group.Measure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicBox_exists_eq_sum_indicator_image_integralFiniteAdeles

set_option autoImplicit false

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped nonZeroDivisors

namespace LatKer0

open IsDedekindDomain Filter Topology

theorem re_sq_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) : (w ^ 2).re = 2 * w.re ^ 2 - 1 := by
  have h : w.re * w.re + w.im * w.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hw, one_pow]
  rw [sq, Complex.mul_re]
  nlinarith

theorem norm_le_one_of_forall_pow_mem {H : Set ℂ} (hbdd : Bornology.IsBounded H) {a : ℂ}
    (ha : ∀ n : ℕ, a ^ (n + 1) ∈ H) : ‖a‖ ≤ 1 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨M, hM⟩ := hbdd.exists_norm_le
  obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop M |>.exists
  have h1 : ‖a‖ ^ n ≤ ‖a‖ ^ (n + 1) := pow_le_pow_right₀ h.le (Nat.le_succ n)
  have h2 : ‖a ^ (n + 1)‖ ≤ M := hM _ (ha n)
  rw [norm_pow] at h2
  linarith

theorem eq_one_of_forall_re_pow_two_pow_gt {a : ℂ} (ha : ‖a‖ = 1)
    (h : ∀ n : ℕ, 1 / 2 < (a ^ (2 ^ n)).re) : a = 1 := by

  set c : ℕ → ℝ := fun n => (a ^ (2 ^ n)).re with hc
  have hnorm : ∀ n : ℕ, ‖a ^ (2 ^ n)‖ = 1 := fun n => by rw [norm_pow, ha, one_pow]
  have hrec : ∀ n : ℕ, c (n + 1) = 2 * c n ^ 2 - 1 := fun n => by
    simp only [hc]
    rw [pow_succ, pow_mul, re_sq_of_norm_eq_one (hnorm n)]
  have hc0 : c 0 = a.re := by simp [hc]
  have hgt : ∀ n, 1 / 2 < c n := fun n => h n

  by_cases hre : a.re = 1
  · apply Complex.ext
    · simpa using hre
    · have : a.re * a.re + a.im * a.im = 1 := by
        rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, ha, one_pow]
      rw [hre] at this
      simpa using (by nlinarith : a.im * a.im = 0)

  have hre1 : a.re < 1 := lt_of_le_of_ne (by simpa [ha] using Complex.re_le_norm a) hre
  set δ : ℝ := 2 * (1 - a.re) with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hstep : ∀ n : ℕ, c n ≤ c 0 - n * δ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : 1 / 2 < c n := hgt n
      have h2 : c n ≤ a.re := by
        have := ih; rw [hc0] at this
        have : (n : ℝ) * δ ≥ 0 := by positivity
        linarith
      rw [hrec n, Nat.cast_succ]
      nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((c 0 - 1 / 2) / δ)
  have h1 := hstep n
  have h2 := hgt n
  have h3 : (c 0 - 1 / 2) < n * δ := by rwa [div_lt_iff₀ hδpos] at hn
  linarith

theorem eq_one_of_mem {H : Set ℂ} (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H) (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    (hbdd : Bornology.IsBounded H) (hre : ∀ a ∈ H, 1 / 2 < a.re) {a : ℂ} (ha : a ∈ H) : a = 1 := by
  have hpow : ∀ b ∈ H, ∀ n : ℕ, b ^ (n + 1) ∈ H := fun b hb n => by
    induction n with
    | zero => simpa using hb
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hb
  have ha0 : a ≠ 0 := fun h0 => by have := hre a ha; rw [h0] at this; norm_num at this
  have hle : ‖a‖ ≤ 1 := norm_le_one_of_forall_pow_mem hbdd (hpow a ha)
  have hge : 1 ≤ ‖a‖ := by
    have := norm_le_one_of_forall_pow_mem hbdd (hpow a⁻¹ (hinv a ha))
    rwa [norm_inv, inv_le_one₀ (norm_pos_iff.mpr ha0)] at this
  refine eq_one_of_forall_re_pow_two_pow_gt (le_antisymm hle hge) fun n => hre _ ?_
  have := hpow a ha (2 ^ n - 1)
  rwa [Nat.sub_add_cancel Nat.one_le_two_pow] at this

variable (F : Type) [Field F] [NumberField F]

private def _root_.LatKer0.dBox (d : 𝓞 F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
    integralFiniteAdeles (𝓞 F) F

p2m_export "LatKer0" "dBox"
theorem algebraMap_integer_apply (a : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v
      = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := rfl

theorem mul_mem_integralFiniteAdeles (a : 𝓞 F) {z : FiniteAdeleRing (𝓞 F) F}
    (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) * z ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  mul_mem (algebraMap_mem_adicCompletionIntegers (𝓞 F) F v a) (hz v)

theorem add_mem_integralFiniteAdeles {z w : FiniteAdeleRing (𝓞 F) F}
    (hz : z ∈ integralFiniteAdeles (𝓞 F) F) (hw : w ∈ integralFiniteAdeles (𝓞 F) F) :
    z + w ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  add_mem (hz v) (hw v)

theorem neg_mem_integralFiniteAdeles {z : FiniteAdeleRing (𝓞 F) F}
    (hz : z ∈ integralFiniteAdeles (𝓞 F) F) : -z ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  neg_mem (hz v)

theorem isCompact_dBox (d : 𝓞 F) : IsCompact (dBox F d) :=
  (isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)

theorem dBox_mul_subset (d e : 𝓞 F) : dBox F (d * e) ⊆ dBox F d := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) (e : F) * z, mul_mem_integralFiniteAdeles F e hz, ?_⟩
  simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, mul_assoc]

theorem eq_zero_of_forall_mem_dBox {x : FiniteAdeleRing (𝓞 F) F}
    (hx : ∀ d : 𝓞 F, d ≠ 0 → x ∈ dBox F d) : x = 0 := by
  refine FiniteAdeleRing.ext F fun v => ?_
  rw [show (0 : FiniteAdeleRing (𝓞 F) F) v = 0 from rfl]

  have hle : ∀ n : ℕ, Valued.v (x v) ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    have hI : (v.asIdeal ^ n : Ideal (𝓞 F)) ≠ ⊥ := pow_ne_zero _ v.ne_bot
    obtain ⟨d, hdI, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨z, hz, hxz⟩ := hx d hd0
    rw [← hxz, show (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) v
        = (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v * z v from rfl, map_mul,
      algebraMap_integer_apply,
      show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d)
        = ((algebraMap (𝓞 F) F d : F) : v.adicCompletion F) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
    have hz1 : Valued.v (z v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hz v)
    calc v.intValuation d * Valued.v (z v) ≤ v.intValuation d * 1 := by gcongr
      _ ≤ WithZero.exp (-(n : ℤ)) := by
          rw [mul_one]; exact (HeightOneSpectrum.intValuation_le_pow_iff_mem v d n).mpr hdI
  by_contra hne
  have hne' : Valued.v (x v) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (x v) = WithZero.exp m :=
    ⟨WithZero.log (Valued.v (x v)), (WithZero.exp_log hne').symm⟩
  have := hle ((-m).toNat + 1)
  rw [hm, WithZero.exp_le_exp] at this
  omega

theorem exists_dBox_subset {U : Set (FiniteAdeleRing (𝓞 F) F)} (hU : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ dBox F d ⊆ U := by
  haveI : Nonempty {d : 𝓞 F // d ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  have hdir : Directed (· ⊇ ·) (fun d : {d : 𝓞 F // d ≠ 0} => dBox F d.1) := by
    rintro ⟨d, hd⟩ ⟨e, he⟩
    have h2 : dBox F (d * e) ⊆ dBox F e := by rw [mul_comm]; exact dBox_mul_subset F e d
    exact ⟨⟨d * e, mul_ne_zero hd he⟩, dBox_mul_subset F d e, h2⟩
  obtain ⟨⟨d, hd⟩, h⟩ := exists_subset_nhds_of_isCompact' hdir (fun d => isCompact_dBox F d.1)
    (fun d => (isCompact_dBox F d.1).isClosed) (U := U) (fun x hx => by
      have hx0 : x = 0 := eq_zero_of_forall_mem_dBox F fun d hd => by
        have := Set.mem_iInter.mp hx ⟨d, hd⟩; exact this
      rwa [hx0])
  exact ⟨d, hd, h⟩

theorem exists_ne_zero_forall_eq_one
    {ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ} (hψf : Continuous ψf) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
      ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) = 1 := by

  set U : Set (FiniteAdeleRing (𝓞 F) F) := {x | 1 / 2 < (ψf x).re} with hU
  have hU0 : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := by
    refine (isOpen_lt continuous_const (Complex.continuous_re.comp hψf)).mem_nhds ?_
    show 1 / 2 < (ψf 0).re
    rw [AddChar.map_zero_eq_one, Complex.one_re]; norm_num
  obtain ⟨d, hd, hdU⟩ := exists_dBox_subset F hU0
  refine ⟨d, hd, fun z hz => ?_⟩

  set H : Set ℂ := ψf '' dBox F d with hH
  have hmem : ∀ {x}, x ∈ dBox F d ↔ ∃ w ∈ integralFiniteAdeles (𝓞 F) F,
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w = x := fun {x} => Iff.rfl
  refine eq_one_of_mem (H := H) ?_ ?_ ?_ ?_ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  · rintro _ ⟨x, ⟨w₁, hw₁, rfl⟩, rfl⟩ _ ⟨y, ⟨w₂, hw₂, rfl⟩, rfl⟩
    refine ⟨_, ⟨w₁ + w₂, add_mem_integralFiniteAdeles F hw₁ hw₂, rfl⟩, ?_⟩
    dsimp only
    rw [mul_add, AddChar.map_add_eq_mul]
  · rintro _ ⟨x, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨_, ⟨-w, neg_mem_integralFiniteAdeles F hw, rfl⟩, ?_⟩
    dsimp only
    rw [mul_neg]
    apply eq_inv_of_mul_eq_one_left
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  · exact ((isCompact_dBox F d).image hψf).isBounded
  · rintro _ ⟨x, hx, rfl⟩
    exact hdU hx

end LatKer0

namespace LatIdx

open IsDedekindDomain MeasureTheory

variable (F : Type) [Field F] [NumberField F]

def dBox (d : 𝓞 F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
    integralFiniteAdeles (𝓞 F) F

theorem algebraMap_integer_apply (a : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v
      = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := rfl

theorem valued_algebraMap_integer (a : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v) = v.intValuation a := by
  rw [algebraMap_integer_apply, show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)
        = ((algebraMap (𝓞 F) F a : F) : v.adicCompletion F) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

theorem mul_apply' (x y : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (x * y) v = x v * y v := rfl

theorem sub_apply' (x y : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (x - y) v = x v - y v := rfl

theorem algebraMap_integer_mem (a : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  algebraMap_mem_adicCompletionIntegers (𝓞 F) F v a

theorem mul_integer_mem (a : 𝓞 F) {z : FiniteAdeleRing (𝓞 F) F} (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) * z ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  mul_mem (algebraMap_mem_adicCompletionIntegers (𝓞 F) F v a) (hz v)

theorem add_mem' {z w : FiniteAdeleRing (𝓞 F) F} (hz : z ∈ integralFiniteAdeles (𝓞 F) F)
    (hw : w ∈ integralFiniteAdeles (𝓞 F) F) : z + w ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  add_mem (hz v) (hw v)

theorem sub_mem' {z w : FiniteAdeleRing (𝓞 F) F} (hz : z ∈ integralFiniteAdeles (𝓞 F) F)
    (hw : w ∈ integralFiniteAdeles (𝓞 F) F) : z - w ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  sub_mem (hz v) (hw v)

theorem dBox_sub_mem {d : 𝓞 F} {y y' : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ dBox F d) (hy' : y' ∈ dBox F d) :
    y - y' ∈ dBox F d := by
  obtain ⟨w, hw, rfl⟩ := hy
  obtain ⟨w', hw', rfl⟩ := hy'
  exact ⟨w - w', sub_mem' F hw hw', by simp only [mul_sub]⟩

theorem isCompact_dBox (d : 𝓞 F) : IsCompact (dBox F d) :=
  (isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)

variable {F}

theorem exists_sub_mem_dBox {d : 𝓞 F} (hd : d ≠ 0) {z : FiniteAdeleRing (𝓞 F) F}
    (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    ∃ a : 𝓞 F, z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ dBox F d := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  obtain ⟨a, ha⟩ := exists_forall_valued_sub_le (𝓞 F) F hz hd
  refine ⟨a, algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹
      * (z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)), fun v => ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, mul_apply', map_mul, sub_apply']
    have hdv : Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v) ≠ 0 := by
      rw [valued_algebraMap_integer]; exact v.intValuation_ne_zero d hd
    have hinv : Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹) v)
        = (Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v))⁻¹ := by
      rw [show (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹) v
          = algebraMap F (v.adicCompletion F) (d : F)⁻¹ from rfl, map_inv₀, Valuation.map_inv]
      rfl
    have ha' : Valued.v (z v - (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v)
        ≤ Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v) := ha v
    rw [hinv]
    calc (Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v))⁻¹
          * Valued.v (z v - (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v)
        ≤ (Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v))⁻¹
          * Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v) := by gcongr
      _ = 1 := inv_mul_cancel₀ hdv
  · show algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹
      * (z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F))) = z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hd', map_one, one_mul]

theorem sub_mem_span_of_sub_mem_dBox {d a a' : 𝓞 F} (hd : d ≠ 0)
    (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a' : F)
      ∈ dBox F d) : a - a' ∈ Ideal.span {d} := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  obtain ⟨w, hw, hw'⟩ := h
  set y : F := (d : F)⁻¹ * ((a : F) - (a' : F)) with hy
  have hwy : w = algebraMap F (FiniteAdeleRing (𝓞 F) F) y := by
    have h1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w
        = algebraMap F (FiniteAdeleRing (𝓞 F) F) ((a : F) - (a' : F)) := by rw [map_sub]; exact hw'
    calc w = algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹ * (d : F)) * w := by
            rw [inv_mul_cancel₀ hd', map_one, one_mul]
      _ = algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w) := by
            rw [map_mul, mul_assoc]
      _ = algebraMap F (FiniteAdeleRing (𝓞 F) F) y := by rw [h1, ← map_mul]
  have hyint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F y ≤ 1 := fun v => by
    have hv : (algebraMap F (FiniteAdeleRing (𝓞 F) F) y) v ∈ v.adicCompletionIntegers F := by
      rw [← hwy]; exact hw v
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap F (FiniteAdeleRing (𝓞 F) F) y) v = (y : v.adicCompletion F) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F y hyint
  rw [Ideal.mem_span_singleton']
  refine ⟨b, RingOfIntegers.coe_injective ?_⟩
  have hb' : (b : F) = y := hb
  show ((b * d : 𝓞 F) : F) = ((a - a' : 𝓞 F) : F)
  have e1 : ((b * d : 𝓞 F) : F) = (b : F) * (d : F) := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul]
  have e2 : ((a - a' : 𝓞 F) : F) = (a : F) - (a' : F) := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_sub]
  rw [e1, e2, hb', hy, mul_comm, ← mul_assoc, mul_inv_cancel₀ hd', one_mul]

end LatIdx

namespace LatDec

open IsDedekindDomain Filter Topology

variable {F : Type} [Field F] [NumberField F]

def coset (k : F) (d : 𝓞 F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
    + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F

theorem coset_eq_image_dBox (k : F) (d : 𝓞 F) :
    coset k d = (fun y ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k + y) '' LatIdx.dBox F d := by
  rw [coset, LatIdx.dBox, Set.image_image]

theorem coset_eq_of_mem {k : F} {d : 𝓞 F} {x : FiniteAdeleRing (𝓞 F) F} (hx : x ∈ coset k d) :
    coset k d = (fun y ↦ x + y) '' LatIdx.dBox F d := by
  rw [coset_eq_image_dBox] at hx ⊢
  obtain ⟨y₀, hy₀, rfl⟩ := hx
  dsimp only
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y - y₀, LatIdx.dBox_sub_mem F hy hy₀, ?_⟩
    show algebraMap F (FiniteAdeleRing (𝓞 F) F) k + y₀ + (y - y₀)
      = algebraMap F (FiniteAdeleRing (𝓞 F) F) k + y
    rw [add_assoc, add_sub_cancel]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y₀ + y, ?_, ?_⟩
    · obtain ⟨w, hw, rfl⟩ := hy; obtain ⟨w₀, hw₀, rfl⟩ := hy₀
      exact ⟨w₀ + w, LatIdx.add_mem' F hw₀ hw, by simp only [mul_add]⟩
    · show algebraMap F (FiniteAdeleRing (𝓞 F) F) k + (y₀ + y)
        = algebraMap F (FiniteAdeleRing (𝓞 F) F) k + y₀ + y
      rw [add_assoc]

theorem isOpen_coset (k : F) {d : 𝓞 F} (hd : d ≠ 0) : IsOpen (coset k d) := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hS : coset k d = (fun y : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹
      * (y - algebraMap F (FiniteAdeleRing (𝓞 F) F) k)) ⁻¹' integralFiniteAdeles (𝓞 F) F := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      show algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F) k
        + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z - algebraMap F (FiniteAdeleRing (𝓞 F) F) k)
        ∈ integralFiniteAdeles (𝓞 F) F
      rwa [add_sub_cancel_left, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd', map_one, one_mul]
    · intro hy
      refine ⟨_, hy, ?_⟩
      show algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)
        * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹ * (y - algebraMap F (FiniteAdeleRing (𝓞 F) F) k)) = y
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hd', map_one, one_mul, add_sub_cancel]
  rw [hS]
  exact (isOpen_integralFiniteAdeles F).preimage (continuous_const.mul (continuous_id.sub continuous_const))

theorem exists_mem_coset {d : 𝓞 F} (hd : d ≠ 0) (x : FiniteAdeleRing (𝓞 F) F) :
    ∃ k : F, x ∈ coset k d := by
  obtain ⟨k₀, hk₀⟩ := exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F x
  obtain ⟨a, ⟨z, hz, hz'⟩⟩ := LatIdx.exists_sub_mem_dBox hd hk₀
  refine ⟨(a : F) - k₀, z, hz, ?_⟩
  dsimp only at hz'
  show algebraMap F (FiniteAdeleRing (𝓞 F) F) ((a : F) - k₀)
    + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z = x
  rw [hz', map_sub]
  abel

theorem exists_nhds_forall_add_eq {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {h : G → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    ∃ W ∈ 𝓝 (0 : G), ∀ x, ∀ w ∈ W, h (x + w) = h x := by

  have key : ∀ x : G, ∃ V W : Set G, IsOpen V ∧ x ∈ V ∧ W ∈ 𝓝 (0 : G) ∧ ∀ v ∈ V, ∀ w ∈ W, h (v + w) = h x := by
    intro x
    obtain ⟨U, hU, hxU, hUc⟩ := (IsLocallyConstant.iff_exists_open h).mp hlc x
    have hcont : ContinuousAt (fun p : G × G => p.1 + p.2) (x, 0) := continuous_add.continuousAt
    have hmem : (fun p : G × G => p.1 + p.2) ⁻¹' U ∈ 𝓝 ((x, 0) : G × G) :=
      hcont.preimage_mem_nhds (by simpa using hU.mem_nhds hxU)
    obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hmem
    obtain ⟨V', hV'V, hV'o, hxV'⟩ := mem_nhds_iff.mp hV
    exact ⟨V', W, hV'o, hxV', hW, fun v hv w hw => hUc _ (hVW (Set.mk_mem_prod (hV'V hv) hw))⟩
  choose V W hVo hxV hW hVW using key

  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover V hVo (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)

  set W₀ : Set G := ⋂ x ∈ t, W x with hW₀
  have hW₀ : W₀ ∈ 𝓝 (0 : G) := (Filter.biInter_finset_mem t).mpr fun x _ => hW x
  refine ⟨W₀ ∩ (fun w => -w) ⁻¹' W₀, Filter.inter_mem hW₀ ?_, ?_⟩
  · exact (continuous_neg.tendsto' 0 0 neg_zero) hW₀

  have hK : ∀ x ∈ tsupport h, ∀ w ∈ W₀, h (x + w) = h x := by
    intro x hx w hw
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    have hw' : w ∈ W i := Set.mem_iInter₂.mp hw i hi
    rw [hVW i x hxi w hw', ← hVW i x hxi 0 (mem_of_mem_nhds (hW i)), add_zero]
  intro x w hw
  obtain ⟨hw1, hw2⟩ := hw
  by_cases hx : x ∈ tsupport h
  · exact hK x hx w hw1
  by_cases hxw : x + w ∈ tsupport h
  · have := hK (x + w) hxw (-w) hw2
    rw [add_neg_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxw]

theorem main {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∃ (s : Finset F) (c : F → ℂ),
      h = ∑ k ∈ s, c k • (coset k d).indicator 1 := by
  classical

  obtain ⟨W, hW, hWh⟩ := exists_nhds_forall_add_eq hlc hcs
  obtain ⟨d, hd, hdW⟩ := LatKer0.exists_dBox_subset F hW
  have hper : ∀ x, ∀ y ∈ LatIdx.dBox F d, h (x + y) = h x := fun x y hy => hWh x y (hdW hy)
  have hconst : ∀ {k : F} {x}, x ∈ coset k d → h x = h (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) := by
    intro k x hx
    rw [coset_eq_image_dBox] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hper _ y hy
  refine ⟨d, hd, ?_⟩

  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover (fun k : F => coset k d)
    (fun k => isOpen_coset k hd) (fun x _ => by
      obtain ⟨k, hk⟩ := exists_mem_coset hd x
      exact Set.mem_iUnion.mpr ⟨k, hk⟩)
  set C : Finset (Set (FiniteAdeleRing (𝓞 F) F)) := t.image fun k => coset k d with hC
  have hCrep : ∀ c ∈ C, ∃ k : F, coset k d = c := fun c hc => by
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hc; exact ⟨k, rfl⟩
  set rep : Set (FiniteAdeleRing (𝓞 F) F) → F := fun c =>
    if hc : c ∈ C then (hCrep c hc).choose else 0 with hrep
  have hrep_spec : ∀ c ∈ C, coset (rep c) d = c := fun c hc => by
    simp only [hrep, dif_pos hc]; exact (hCrep c hc).choose_spec
  set s : Finset F := C.image rep with hs
  refine ⟨s, fun k => h (algebraMap F (FiniteAdeleRing (𝓞 F) F) k), ?_⟩

  have hinj : ∀ c ∈ C, ∀ c' ∈ C, rep c = rep c' → c = c' := fun c hc c' hc' e => by
    rw [← hrep_spec c hc, ← hrep_spec c' hc', e]
  have hs_mem : ∀ {k}, k ∈ s → coset k d ∈ C ∧ rep (coset k d) = k := by
    intro k hk
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hk
    rw [hrep_spec c hc]; exact ⟨hc, rfl⟩
  have hdisj : ∀ {k k' : F} {x}, k ∈ s → k' ∈ s → x ∈ coset k d → x ∈ coset k' d → k = k' := by
    intro k k' x hk hk' hx hx'
    have e : coset k d = coset k' d := by rw [coset_eq_of_mem hx, coset_eq_of_mem hx']
    rw [← (hs_mem hk).2, ← (hs_mem hk').2, e]

  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Set.indicator_apply, Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hx : ∃ k ∈ s, x ∈ coset k d
  · obtain ⟨k₀, hk₀, hxk₀⟩ := hx
    rw [Finset.sum_eq_single k₀, if_pos hxk₀, hconst hxk₀]
    · intro k hk hne
      rw [if_neg]
      intro hxk
      exact hne (hdisj hk hk₀ hxk hxk₀)
    · intro h0; exact absurd hk₀ h0
  · simp only [not_exists, not_and] at hx
    rw [Finset.sum_eq_zero fun k hk => if_neg (hx k hk)]

    by_contra hne
    have hxK : x ∈ tsupport h := subset_tsupport _ (Function.mem_support.mpr hne)
    obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp (ht hxK)
    have hc : coset k d ∈ C := Finset.mem_image.mpr ⟨k, hk, rfl⟩
    have hrs : rep (coset k d) ∈ s := Finset.mem_image.mpr ⟨_, hc, rfl⟩
    apply hx _ hrs
    rw [hrep_spec _ hc]; exact hxk

end LatDec

theorem solution
    (F : Type) [Field F] [NumberField F]
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∃ (s : Finset F) (c : F → ℂ),
      h = ∑ k ∈ s, c k •
        ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1 :=
  LatDec.main hlc hcs

end S_NumberField_AdelicBox_exists_eq_sum_indicator_image_integralFiniteAdeles
end P2MW
export P2MW.S_NumberField_AdelicBox_exists_eq_sum_indicator_image_integralFiniteAdeles (solution)
