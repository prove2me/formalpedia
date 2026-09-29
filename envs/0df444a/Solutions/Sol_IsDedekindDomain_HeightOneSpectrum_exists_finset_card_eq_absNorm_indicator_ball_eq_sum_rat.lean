-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.exists_finset_card_eq_absNorm_indicator_ball_eq_sum_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/10b3e4ba-85e9-528c-a0f4-f577d75a4f8a

import Mathlib
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_quot_span_eq_absNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_finset_card_eq_absNorm_indicator_ball_eq_sum_rat

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace WsF
namespace BallSplit

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => p.adicCompletion ℚ
local notation "O" => p.adicCompletionIntegers ℚ

theorem exp_mul_le_exp_iff (a b : ℤ) (y : WithZero (Multiplicative ℤ)) :
    WithZero.exp a * y ≤ WithZero.exp b ↔ y ≤ WithZero.exp (b - a) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, y = WithZero.exp k := ⟨WithZero.log y, (WithZero.exp_log hy).symm⟩
    rw [← WithZero.exp_add, WithZero.exp_le_exp, WithZero.exp_le_exp]
    omega

theorem mem_span_of_valued_le {ϖ : O} (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ)) {z : O}
    (hz : Valued.v (z : F) ≤ WithZero.exp (-1 : ℤ)) : z ∈ Ideal.span ({ϖ} : Set O) := by
  have hϖ0 : (ϖ : F) ≠ 0 := by intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  rw [Ideal.mem_span_singleton']
  refine ⟨⟨(z : F) * (ϖ : F)⁻¹, ?_⟩, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg,
      mul_comm, ← WithZero.exp_zero, exp_mul_le_exp_iff]
    simpa using hz
  · apply Subtype.ext
    show (z : F) * (ϖ : F)⁻¹ * ϖ = z
    rw [inv_mul_cancel_right₀ hϖ0]

theorem valued_le_of_mem_span {ϖ : O} (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ)) {z : O}
    (hz : z ∈ Ideal.span ({ϖ} : Set O)) : Valued.v (z : F) ≤ WithZero.exp (-1 : ℤ) := by
  rw [Ideal.mem_span_singleton'] at hz
  obtain ⟨a, rfl⟩ := hz
  show Valued.v ((a : F) * (ϖ : F)) ≤ _
  rw [map_mul, hϖ]
  calc Valued.v (a : F) * WithZero.exp (-1 : ℤ) ≤ 1 * WithZero.exp (-1 : ℤ) := mul_le_mul_left a.2 _
    _ = WithZero.exp (-1 : ℤ) := one_mul _

theorem main (n : ℤ) (t : F) :
    ∃ S : Finset F, S.card = Ideal.absNorm p.asIdeal ∧
      ∀ x : F,
        (if Valued.v (x - t) ≤ WithZero.exp (-n) then (1 : ℂ) else 0) =
          ∑ s ∈ S, (if Valued.v (x - s) ≤ WithZero.exp (-(n + 1)) then (1 : ℂ) else 0) := by
  classical

  let ϖu : Fˣ := AdelicLevel.uniformizerUnit ℚ p
  have hϖu : Valued.v (ϖu : F) = WithZero.exp (-1 : ℤ) := AdelicLevel.valued_uniformizerUnit ℚ p
  have hmem : (ϖu : F) ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hϖu, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  let ϖ : O := ⟨(ϖu : F), hmem⟩
  have hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ) := hϖu
  have hϖ0 : (ϖu : F) ≠ 0 := ϖu.ne_zero

  let I : Ideal O := Ideal.span ({ϖ} : Set O)
  have hcard : Nat.card (O ⧸ I) = Ideal.absNorm p.asIdeal :=
    IsDedekindDomain.HeightOneSpectrum.natCard_adicCompletionIntegers_quot_span_eq_absNorm ℚ p ϖ hϖ
  have hq0 : Ideal.absNorm p.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot
  haveI : Finite (O ⧸ I) := Nat.finite_of_card_ne_zero (hcard ▸ hq0)
  letI : Fintype (O ⧸ I) := Fintype.ofFinite _

  let rep : O ⧸ I → O := Function.surjInv Ideal.Quotient.mk_surjective
  have hrep : ∀ c : O ⧸ I, Ideal.Quotient.mk I (rep c) = c := Function.surjInv_eq Ideal.Quotient.mk_surjective
  let πn : F := ((ϖu ^ n : Fˣ) : F)
  have hπn : Valued.v πn = WithZero.exp (-n) := by
    show Valued.v (((ϖu ^ n : Fˣ)) : F) = _
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖu, ← WithZero.exp_zsmul]; simp
  have hπn0 : πn ≠ 0 := (ϖu ^ n).ne_zero
  let ctr : O ⧸ I → F := fun c => t + πn * (rep c : F)
  have hinj : Function.Injective ctr := by
    intro c c' h
    have : (rep c : F) = rep c' := by
      have := congrArg (fun y => (y - t) * πn⁻¹) h
      simpa [ctr, mul_comm πn, mul_assoc, mul_inv_cancel₀ hπn0] using this
    rw [← hrep c, ← hrep c', Subtype.ext this]
  refine ⟨Finset.univ.image ctr, ?_, fun x => ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
  rw [Finset.sum_image fun c _ c' _ h => hinj h]

  set y : F := (x - t) * πn⁻¹ with hy
  have hxy : x - t = πn * y := by rw [hy, mul_comm, inv_mul_cancel_right₀ hπn0]
  have hxs : ∀ c, x - ctr c = πn * (y - rep c) := by intro c; simp only [ctr]; rw [mul_sub, ← hxy]; ring
  have hball : (Valued.v (x - t) ≤ WithZero.exp (-n)) ↔ Valued.v y ≤ 1 := by
    rw [hxy, map_mul, hπn, exp_mul_le_exp_iff, sub_self, WithZero.exp_zero]
  have hsub : ∀ c, (Valued.v (x - ctr c) ≤ WithZero.exp (-(n + 1))) ↔ Valued.v (y - rep c) ≤ WithZero.exp (-1 : ℤ) := by
    intro c; rw [hxs, map_mul, hπn, exp_mul_le_exp_iff]; congr! 2; ring
  simp_rw [hsub]
  by_cases hyO : Valued.v y ≤ 1
  ·
    rw [if_pos (hball.mpr hyO)]
    let yO : O := ⟨y, hyO⟩
    let c₀ : O ⧸ I := Ideal.Quotient.mk I yO
    have hcoe : ∀ c, (((yO - rep c : O)) : F) = y - rep c := fun c => by
      rw [AddSubgroupClass.coe_sub]
    have hc₀ : Valued.v (y - rep c₀) ≤ WithZero.exp (-1 : ℤ) := by
      have hm : yO - rep c₀ ∈ I := by rw [← Ideal.Quotient.eq, hrep]
      have h := valued_le_of_mem_span hϖ hm
      rwa [hcoe] at h
    have hother : ∀ c, c ≠ c₀ → ¬ Valued.v (y - rep c) ≤ WithZero.exp (-1 : ℤ) := by
      intro c hc hle
      apply hc
      have hm : yO - rep c ∈ I := mem_span_of_valued_le hϖ (z := yO - rep c) (by rwa [hcoe])
      rw [← hrep c, eq_comm, Ideal.Quotient.eq]
      exact hm
    rw [Finset.sum_eq_single c₀ (fun c _ hc => if_neg (hother c hc)) (fun h => (h (Finset.mem_univ _)).elim),
      if_pos hc₀]
  ·
    rw [if_neg (fun h => hyO (hball.mp h))]
    symm
    refine Finset.sum_eq_zero fun c _ => if_neg fun hle => hyO ?_

    have h1 : Valued.v (y - rep c) ≤ 1 := hle.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
    have h2 : Valued.v ((rep c : O) : F) ≤ 1 := (rep c).2
    have := Valuation.map_add Valued.v (y - rep c) (rep c : F)
    rw [sub_add_cancel] at this
    exact this.trans (max_le h1 h2)

end WsF.BallSplit

end

theorem solution
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℤ) (t : p.adicCompletion ℚ) :
    ∃ S : Finset (p.adicCompletion ℚ), S.card = Ideal.absNorm p.asIdeal ∧
      ∀ x : p.adicCompletion ℚ,
        (if Valued.v (x - t) ≤ WithZero.exp (-n) then (1 : ℂ) else 0) =
          ∑ s ∈ S, (if Valued.v (x - s) ≤ WithZero.exp (-(n + 1)) then (1 : ℂ) else 0) :=
  WsF.BallSplit.main n t

end S_IsDedekindDomain_HeightOneSpectrum_exists_finset_card_eq_absNorm_indicator_ball_eq_sum_rat
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_finset_card_eq_absNorm_indicator_ball_eq_sum_rat (solution)
