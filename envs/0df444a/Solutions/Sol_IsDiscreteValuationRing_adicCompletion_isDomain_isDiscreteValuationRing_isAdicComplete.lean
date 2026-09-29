-- Prove2me | solution 1 for IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c8a40646-de82-5693-82eb-fc9693205e2f

import Mathlib
import Definitions.Def_AdicCompletionLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete

set_option autoImplicit false

universe u

open IsLocalRing

namespace ADICDVRe133

variable {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]

theorem maximalIdeal_eq_span (ϖ : C) (hϖ : Irreducible ϖ) :
    maximalIdeal (AdicCompletion (maximalIdeal C) C) =
      Ideal.span {algebraMap C (AdicCompletion (maximalIdeal C) C) ϖ} := by
  rw [AdicCompletion.maximalIdeal_eq_map, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

theorem maximalIdeal_pow_eq_span (ϖ : C) (hϖ : Irreducible ϖ) (n : ℕ) :
    maximalIdeal (AdicCompletion (maximalIdeal C) C) ^ n =
      Ideal.span {algebraMap C (AdicCompletion (maximalIdeal C) C) ϖ ^ n} := by
  rw [maximalIdeal_eq_span ϖ hϖ, Ideal.span_singleton_pow]

theorem eq_zero_of_forall_mem_pow (x : AdicCompletion (maximalIdeal C) C)
    (h : ∀ n, x ∈ maximalIdeal (AdicCompletion (maximalIdeal C) C) ^ n) : x = 0 := by
  refine AdicCompletion.ext_evalₐ (fun n => ?_)
  have hn := h n
  rw [AdicCompletion.maximalIdeal_pow_eq_ker_evalₐ, RingHom.mem_ker] at hn
  rw [hn, map_zero]

theorem algebraMap_pow_ne_zero (ϖ : C) (hϖ : Irreducible ϖ) (m : ℕ) :
    algebraMap C (AdicCompletion (maximalIdeal C) C) ϖ ^ m ≠ 0 := by
  intro h
  have h1 : AdicCompletion.evalₐ (maximalIdeal C) (m + 1)
      (algebraMap C (AdicCompletion (maximalIdeal C) C) (ϖ ^ m)) = 0 := by
    rw [map_pow, h, map_zero]
  rw [AdicCompletion.evalₐ_algebraMap, Ideal.Quotient.eq_zero_iff_mem, hϖ.maximalIdeal_eq,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1

  obtain ⟨c, hc⟩ := h1
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have h2 : ϖ ^ m * 1 = ϖ ^ m * (ϖ * c) := by rw [mul_one, ← mul_assoc, ← pow_succ]; exact hc
  have h3 : (1 : C) = ϖ * c := mul_left_cancel₀ (pow_ne_zero m hϖ0) h2
  exact hϖ.not_isUnit (isUnit_iff_exists_inv.mpr ⟨c, h3.symm⟩)

theorem exists_eq_unit_mul_pow (ϖ : C) (hϖ : Irreducible ϖ) (x : AdicCompletion (maximalIdeal C) C) (hx : x ≠ 0) :
    ∃ (n : ℕ) (v : (AdicCompletion (maximalIdeal C) C)ˣ),
      x = (v : AdicCompletion (maximalIdeal C) C) * algebraMap C (AdicCompletion (maximalIdeal C) C) ϖ ^ n := by
  classical

  have hex : ∃ n, x ∉ maximalIdeal (AdicCompletion (maximalIdeal C) C) ^ n := by
    by_contra hall
    push Not at hall
    exact hx (eq_zero_of_forall_mem_pow x hall)

  let N := Nat.find hex
  have hN : x ∉ maximalIdeal (AdicCompletion (maximalIdeal C) C) ^ N := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h0
    apply hN
    rw [h0, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hxn : x ∈ maximalIdeal (AdicCompletion (maximalIdeal C) C) ^ n := by
    have hlt : n < N := by rw [hn]; exact Nat.lt_succ_self n
    have := Nat.find_min hex hlt
    simpa using this
  rw [maximalIdeal_pow_eq_span ϖ hϖ n, Ideal.mem_span_singleton] at hxn
  obtain ⟨x', hx'⟩ := hxn

  have hx'u : IsUnit x' := by
    by_contra hnu
    apply hN
    rw [hn, maximalIdeal_pow_eq_span ϖ hϖ, Ideal.mem_span_singleton, hx']
    have hmem : x' ∈ maximalIdeal (AdicCompletion (maximalIdeal C) C) := (mem_maximalIdeal x').mpr hnu
    rw [maximalIdeal_eq_span ϖ hϖ, Ideal.mem_span_singleton] at hmem
    obtain ⟨x'', rfl⟩ := hmem
    exact ⟨x'', by rw [Nat.succ_eq_add_one, pow_succ]; ring⟩
  refine ⟨n, hx'u.unit, ?_⟩
  rw [hx', IsUnit.unit_spec, mul_comm]

theorem isDomain (ϖ : C) (hϖ : Irreducible ϖ) : IsDomain (AdicCompletion (maximalIdeal C) C) := by
  haveI : NoZeroDivisors (AdicCompletion (maximalIdeal C) C) := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨m, v, hv⟩ := exists_eq_unit_mul_pow ϖ hϖ a hne.1
    obtain ⟨n, w, hw⟩ := exists_eq_unit_mul_pow ϖ hϖ b hne.2
    have h : (v : AdicCompletion (maximalIdeal C) C) * w * algebraMap C _ ϖ ^ (m + n) = 0 := by
      rw [← hab, hv, hw]; ring
    have h' : algebraMap C (AdicCompletion (maximalIdeal C) C) ϖ ^ (m + n) = 0 := by
      have hu : IsUnit ((v : AdicCompletion (maximalIdeal C) C) * w) := (Units.isUnit v).mul (Units.isUnit w)
      exact (hu.mul_right_eq_zero).mp h
    exact algebraMap_pow_ne_zero ϖ hϖ (m + n) h'
  exact NoZeroDivisors.to_isDomain _

theorem irreducible_algebraMap (ϖ : C) (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap C (AdicCompletion (maximalIdeal C) C) ϖ) := by
  haveI := isDomain ϖ hϖ
  have hπ0 : algebraMap C (AdicCompletion (maximalIdeal C) C) ϖ ≠ 0 := by
    have := algebraMap_pow_ne_zero ϖ hϖ 1
    rwa [pow_one] at this
  have hπnu : ¬ IsUnit (algebraMap C (AdicCompletion (maximalIdeal C) C) ϖ) := by
    intro hu
    have hmem : algebraMap C (AdicCompletion (maximalIdeal C) C) ϖ ∈ maximalIdeal _ := by
      rw [maximalIdeal_eq_span ϖ hϖ]; exact Ideal.mem_span_singleton_self _
    exact (mem_maximalIdeal _).mp hmem hu
  refine ⟨hπnu, fun a b hab => ?_⟩
  by_cases ha0 : a = 0
  · exact absurd (by rw [hab, ha0, zero_mul]) hπ0
  by_cases hb0 : b = 0
  · exact absurd (by rw [hab, hb0, mul_zero]) hπ0
  obtain ⟨m, v, hv⟩ := exists_eq_unit_mul_pow ϖ hϖ a ha0
  obtain ⟨n, w, hw⟩ := exists_eq_unit_mul_pow ϖ hϖ b hb0
  rcases Nat.eq_zero_or_pos m with hm | hm
  · left
    rw [hv, hm, pow_zero, mul_one]
    exact Units.isUnit v
  rcases Nat.eq_zero_or_pos n with hn | hn
  · right
    rw [hw, hn, pow_zero, mul_one]
    exact Units.isUnit w

  exfalso
  obtain ⟨k, hk⟩ : ∃ k, m + n = k + 2 := ⟨m + n - 2, by omega⟩
  have h1 : algebraMap C (AdicCompletion (maximalIdeal C) C) ϖ =
      (v : AdicCompletion (maximalIdeal C) C) * w * algebraMap C _ ϖ ^ (k + 2) := by
    calc algebraMap C (AdicCompletion (maximalIdeal C) C) ϖ = a * b := hab
      _ = ((v : AdicCompletion (maximalIdeal C) C) * algebraMap C _ ϖ ^ m) *
            ((w : AdicCompletion (maximalIdeal C) C) * algebraMap C _ ϖ ^ n) := by rw [hv, hw]
      _ = (v : AdicCompletion (maximalIdeal C) C) * w * algebraMap C _ ϖ ^ (m + n) := by ring
      _ = (v : AdicCompletion (maximalIdeal C) C) * w * algebraMap C _ ϖ ^ (k + 2) := by rw [hk]
  have h2 : algebraMap C (AdicCompletion (maximalIdeal C) C) ϖ * 1 =
      algebraMap C (AdicCompletion (maximalIdeal C) C) ϖ *
        ((v : AdicCompletion (maximalIdeal C) C) * w * algebraMap C _ ϖ ^ (k + 1)) := by
    rw [mul_one]
    conv_lhs => rw [h1]
    ring
  have h3 : (1 : AdicCompletion (maximalIdeal C) C) =
      (v : AdicCompletion (maximalIdeal C) C) * w * algebraMap C _ ϖ ^ (k + 1) :=
    mul_left_cancel₀ hπ0 h2
  have hu : IsUnit (algebraMap C (AdicCompletion (maximalIdeal C) C) ϖ ^ (k + 1)) :=
    isUnit_iff_exists_inv.mpr ⟨(v : AdicCompletion (maximalIdeal C) C) * w, by rw [mul_comm]; exact h3.symm⟩
  exact hπnu ((isUnit_pow_iff (Nat.succ_ne_zero k)).mp hu)

theorem isDiscreteValuationRing (ϖ : C) (hϖ : Irreducible ϖ) :
    @IsDiscreteValuationRing (AdicCompletion (maximalIdeal C) C) _ (isDomain ϖ hϖ) := by
  haveI := isDomain ϖ hϖ
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨algebraMap C _ ϖ, irreducible_algebraMap ϖ hϖ, fun {x} hx => by
      obtain ⟨n, v, hv⟩ := exists_eq_unit_mul_pow ϖ hϖ x hx
      exact ⟨n, v, by rw [hv, mul_comm]⟩⟩

theorem isAdicComplete_maximalIdeal :
    IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal C) C)) (AdicCompletion (maximalIdeal C) C) := by
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact (IsAdicComplete.map_algebraMap_iff (maximalIdeal C) (AdicCompletion (maximalIdeal C) C)).mpr
    (AdicCompletion.isAdicComplete AdicCompletion.maximalIdeal_fg)

end ADICDVRe133

open ADICDVRe133 in

theorem solution
    (C : Type u) [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] (ϖ : C) (hϖ : Irreducible ϖ) :
    ∃ (_ : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal C) C))
      (_ : IsDiscreteValuationRing (AdicCompletion (IsLocalRing.maximalIdeal C) C))
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal C) C)) (AdicCompletion (IsLocalRing.maximalIdeal C) C)),
      Irreducible (algebraMap C (AdicCompletion (IsLocalRing.maximalIdeal C) C) ϖ) ∧
      (∀ (n : ℕ) (c : C), algebraMap C (AdicCompletion (IsLocalRing.maximalIdeal C) C) c ∈
          Ideal.span {algebraMap C (AdicCompletion (IsLocalRing.maximalIdeal C) C) ϖ ^ n} → c ∈ Ideal.span {ϖ ^ n}) ∧
      (∀ (n : ℕ) (w : AdicCompletion (IsLocalRing.maximalIdeal C) C), ∃ c : C,
          w - algebraMap C (AdicCompletion (IsLocalRing.maximalIdeal C) C) c ∈
            Ideal.span {algebraMap C (AdicCompletion (IsLocalRing.maximalIdeal C) C) ϖ ^ n}) := by
  haveI := isDomain ϖ hϖ
  haveI := isDiscreteValuationRing ϖ hϖ
  refine ⟨inferInstance, inferInstance, isAdicComplete_maximalIdeal, irreducible_algebraMap ϖ hϖ, fun n c hc => ?_,
    fun n w => ?_⟩
  · rw [← maximalIdeal_pow_eq_span ϖ hϖ n, AdicCompletion.maximalIdeal_pow_eq_ker_evalₐ, RingHom.mem_ker,
      AdicCompletion.evalₐ_algebraMap, Ideal.Quotient.eq_zero_iff_mem, hϖ.maximalIdeal_eq,
      Ideal.span_singleton_pow] at hc
    exact hc
  · obtain ⟨a, y, hy, hw⟩ :=
      AdicCompletion.exists_eq_algebraMap_add (maximalIdeal C) AdicCompletion.maximalIdeal_fg n w
    refine ⟨a, ?_⟩
    rw [hw, add_sub_cancel_left, ← maximalIdeal_pow_eq_span ϖ hϖ n, AdicCompletion.maximalIdeal_pow_eq_ker_evalₐ,
      AdicCompletion.ker_evalₐ_eq_map_pow _ AdicCompletion.maximalIdeal_fg]
    exact hy

end S_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
end P2MW
export P2MW.S_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete (solution)
