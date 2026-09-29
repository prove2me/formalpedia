-- Prove2me | solution 1 for NumberField.AdelicBox.exists_ne_zero_forall_addChar_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/28f8063a-0750-5647-92b6-bdfdaa80c336

import Definitions.Def_NumberField_AdelicBox
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactness.Compact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicBox_exists_ne_zero_forall_addChar_mul_eq_one

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

def dBox (d : 𝓞 F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
    integralFiniteAdeles (𝓞 F) F

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

theorem solution
    (F : Type) [Field F] [NumberField F]
    {ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ} (hψf : Continuous ψf) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
      ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) = 1 :=
  LatKer0.exists_ne_zero_forall_eq_one F hψf

end S_NumberField_AdelicBox_exists_ne_zero_forall_addChar_mul_eq_one
end P2MW
export P2MW.S_NumberField_AdelicBox_exists_ne_zero_forall_addChar_mul_eq_one (solution)
