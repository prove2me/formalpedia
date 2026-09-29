-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.natCard_adicCompletionIntegers_quotient_span_singleton_mul_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/50bbda73-e51d-5296-b323-6f2a7fc758b0

import Mathlib
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_quotient_span_singleton_mul_norm_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace P2mResidueCount

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem one_lt_q : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem q_pos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := lt_trans zero_lt_one (one_lt_q K v)

theorem exists_norm_eq_zpow_and_v_eq {x : v.adicCompletion K} (hx : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k ∧
      (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k := by
  have hv0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv0), ?_, ?_⟩
  · rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv0]
    push_cast
    rfl
  · conv_lhs => rw [← WithZero.coe_unzero hv0]
    rfl

theorem norm_eq_zpow_of_v_eq_exp {x : v.adicCompletion K} {k : ℤ}
    (h : (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, map_zero] at h
    exact WithZero.coe_ne_zero h.symm
  obtain ⟨k', hk', hv⟩ := exists_norm_eq_zpow_and_v_eq K v hx
  rw [hv] at h
  have : k' = k := WithZero.exp_injective h
  rw [hk', this]

theorem mem_integers_iff_v (x : v.adicCompletion K) :
    x ∈ v.adicCompletionIntegers K ↔ (Valued.v x : WithZero (Multiplicative ℤ)) ≤ 1 :=
  HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem exp_neg_one_pow (m : ℕ) : (WithZero.exp (-1 : ℤ)) ^ m = WithZero.exp (-(m : ℤ)) := by
  rw [← WithZero.exp_nsmul, smul_neg, nsmul_one]

theorem isUnit_int_iff (x : v.adicCompletionIntegers K) :
    IsUnit x ↔ (Valued.v (x : v.adicCompletion K) : WithZero (Multiplicative ℤ)) = 1 :=
  Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)

theorem v_irreducible {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    (Valued.v (ϖ : v.adicCompletion K) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) := by

  have hlt : (Valued.v (ϖ : v.adicCompletion K) : WithZero (Multiplicative ℤ)) < 1 :=
    (Valuation.Integer.not_isUnit_iff_valuation_lt_one (x := ϖ)).1 hϖ.not_isUnit
  refine le_antisymm (le_exp_neg_one_of_lt_one hlt) ?_

  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hπv : (Valued.v ((π : K) : v.adicCompletion K) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ
  have hπO : ((π : K) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    rw [mem_integers_iff_v, hπv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  set πO : v.adicCompletionIntegers K := ⟨_, hπO⟩ with hπO_def
  have hπmax : πO ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one]
    change (Valued.v ((π : K) : v.adicCompletion K) : WithZero (Multiplicative ℤ)) < 1
    rw [hπv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hπmax
  obtain ⟨c, hc⟩ := hπmax
  have hcv : (Valued.v (c : v.adicCompletion K) : WithZero (Multiplicative ℤ)) ≤ 1 := c.2
  have hmul : (Valued.v (ϖ : v.adicCompletion K) : WithZero (Multiplicative ℤ)) *
      Valued.v (c : v.adicCompletion K) = WithZero.exp (-1) := by
    rw [← map_mul, ← hπv]
    congr 1
    exact (congrArg Subtype.val hc).symm
  calc WithZero.exp (-1) = (Valued.v (ϖ : v.adicCompletion K) : WithZero (Multiplicative ℤ)) *
        Valued.v (c : v.adicCompletion K) := hmul.symm
    _ ≤ Valued.v (ϖ : v.adicCompletion K) * 1 := by gcongr
    _ = Valued.v (ϖ : v.adicCompletion K) := mul_one _

theorem natCard_residueField :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = Ideal.absNorm v.asIdeal := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  let f : 𝓞 K ⧸ v.asIdeal →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    Ideal.Quotient.lift v.asIdeal
      ((IsLocalRing.residue (v.adicCompletionIntegers K)).comp
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K)))
      (fun a ha => NumberField.AdelicHaar.residue_algebraMap_eq_zero_of_mem (𝓞 K) K v ha)
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨a, ha⟩ := NumberField.AdelicHaar.residue_algebraMap_surjective (𝓞 K) K v z
    exact ⟨Ideal.Quotient.mk _ a, ha⟩
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hinj : Function.Injective f := f.injective
  rw [← Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩, Ideal.absNorm_apply, Submodule.cardQuot_apply]

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3200000 in

theorem natCard_quotient_span_singleton_mul_norm_eq_one
    (a : v.adicCompletionIntegers K) (ha : a ≠ 0) :
    (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span ({a} : Set (v.adicCompletionIntegers K))) : ℝ) *
      ‖(a : v.adicCompletion K)‖ = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ

  have hspan : Ideal.span ({a} : Set (v.adicCompletionIntegers K)) =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.mpr hn

  have hcard : Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span ({a} : Set (v.adicCompletionIntegers K))) =
      Ideal.absNorm v.asIdeal ^ n := by
    rw [Nat.card_congr (Ideal.quotEquivOfEq hspan).toEquiv,
      IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow n, natCard_residueField]

  obtain ⟨u, hu⟩ := hn.symm
  have hva : (Valued.v (a : v.adicCompletion K) : WithZero (Multiplicative ℤ)) = WithZero.exp (-(n : ℤ)) := by
    have hu1 : (Valued.v (((u : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) :
        v.adicCompletion K) : WithZero (Multiplicative ℤ)) = 1 :=
      (isUnit_int_iff K v _).1 (Units.isUnit u)
    rw [← hu, Subring.coe_mul, map_mul, hu1, mul_one, SubmonoidClass.coe_pow, map_pow,
      v_irreducible K v hϖ, exp_neg_one_pow]
  have hnorm : ‖(a : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n : ℤ)) :=
    norm_eq_zpow_of_v_eq_exp K v hva
  rw [hcard, hnorm, Nat.cast_pow, zpow_neg, zpow_natCast]
  exact mul_inv_cancel₀ (pow_ne_zero _ (q_pos K v).ne')

end P2mResidueCount

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a : v.adicCompletionIntegers K) (ha : a ≠ 0) :
    (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span ({a} : Set (v.adicCompletionIntegers K))) : ℝ) *
      ‖(a : v.adicCompletion K)‖ = 1 :=
  P2mResidueCount.natCard_quotient_span_singleton_mul_norm_eq_one K v a ha

end

end S_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_quotient_span_singleton_mul_norm_eq_one
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_quotient_span_singleton_mul_norm_eq_one (solution)
