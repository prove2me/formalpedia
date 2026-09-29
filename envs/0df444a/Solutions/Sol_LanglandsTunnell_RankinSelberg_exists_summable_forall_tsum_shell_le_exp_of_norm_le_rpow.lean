-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_summable_forall_tsum_shell_le_exp_of_norm_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/364c9d7f-94b4-5179-8f60-5151629d2011

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_ConstantTerm

import Theorems.Thm_UnramifiedWhittaker_norm_heckeRecursionSeq_le_mul_pow_of_norm_le_rpow
import Theorems.Thm_NumberField_summable_heightOneSpectrum_tsum_pow_mul_absNorm_rpow_neg_rat
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_summable_forall_tsum_shell_le_exp_of_norm_le_rpow

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel

open MeasureTheory NumberField AutomorphicForm IsDedekindDomain UnramifiedWhittaker
p2m_open "LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_summable_forall_tsum_shell_le_exp_of_norm_le_rpow.LanglandsTunnell.RankinSelberg"

open scoped ENNReal

namespace LanglandsTunnell
namespace RankinSelberg
namespace PlaceBound
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

theorem tsum_cone_eq (f : ℤ × ℤ → ℝ≥0∞) (hf : ∀ p : ℤ × ℤ, ¬ (0 ≤ p.1 - p.2 ∧ 0 ≤ p.2) → f p = 0) :
    ∑' p : ℤ × ℤ, f p = ∑' mn : ℕ × ℕ, f (((mn.1 : ℤ) + mn.2, (mn.2 : ℤ))) := by
  symm
  apply Function.Injective.tsum_eq (g := fun mn : ℕ × ℕ => (((mn.1 : ℤ) + mn.2, (mn.2 : ℤ)) : ℤ × ℤ))
  · intro a b h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hb2 : a.2 = b.2 := by exact_mod_cast h2
    have hb1 : a.1 = b.1 := by have := h1; rw [hb2] at this; exact_mod_cast (add_right_cancel this)
    exact Prod.ext hb1 hb2
  · intro p hp
    by_contra hrange
    apply hp
    apply hf
    intro hcone
    apply hrange
    obtain ⟨h1, h2⟩ := hcone
    refine ⟨((p.1 - p.2).toNat, p.2.toNat), ?_⟩
    simp only [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2, sub_add_cancel]

theorem inv_one_sub_le_exp_two_mul {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) : (1 - r)⁻¹ ≤ Real.exp (2 * r) := by
  have hpos : 0 < 1 - r := by linarith
  rw [inv_le_iff_one_le_mul₀ hpos]
  have h2 : 2 * r + 1 ≤ Real.exp (2 * r) := Real.add_one_le_exp _
  nlinarith [Real.exp_pos (2 * r)]

end LanglandsTunnell.RankinSelberg.PlaceBound

open LanglandsTunnell.RankinSelberg.PlaceBound in
theorem solution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (lam om lam' om' : HeightOneSpectrum (𝓞 ℚ) → ℂ) (κ : ℝ)
    (hbd : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ‖lam v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖lam' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
    (τ : ℝ) (hτ : 2 * |κ| + 4 < τ) :
    ∃ b : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} → ℝ, (∀ v, 0 ≤ b v) ∧ Summable b ∧
      ∀ v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
        (∑' p : ℤ × ℤ,
            ENNReal.ofReal
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (p.1 - p.2) *
                ‖(if 0 ≤ p.1 - p.2 ∧ 0 ≤ p.2 then
                    (om v.1 * om' v.1) ^ p.2.toNat *
                      heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam v.1) (om v.1) (p.1 - p.2).toNat *
                      heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam' v.1) (om' v.1) (p.1 - p.2).toNat
                  else 0)‖ *
                (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(p.1 + p.2))) ^ τ)) ≤ ENNReal.ofReal (Real.exp (b v)) := by

  set θ : ℝ := τ - 2 * |κ| - 3 with hθ
  have hθ1 : 1 < θ := by rw [hθ]; linarith [abs_nonneg κ]
  set σ₀ : ℝ := 2 * (τ - |κ|) with hσ₀
  have hσ₀1 : 1 < σ₀ := by rw [hσ₀]; linarith [abs_nonneg κ]
  have hκa : 0 ≤ |κ| := abs_nonneg κ

  obtain ⟨hD3a, hD3⟩ := NumberField.summable_heightOneSpectrum_tsum_pow_mul_absNorm_rpow_neg_rat θ 1 hθ1 zero_le_one 2
  have hSV := NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt ℚ hσ₀1

  let s : HeightOneSpectrum (𝓞 ℚ) → ℝ := fun v =>
    1 * ∑' m : ℕ, ((m : ℝ) + 2) ^ 2 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((m : ℝ) + 1) * θ)
  let r : HeightOneSpectrum (𝓞 ℚ) → ℝ := fun v => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ₀)
  have hs0 : ∀ v, 0 ≤ s v := fun v => by
    show 0 ≤ 1 * _; rw [one_mul]; exact tsum_nonneg fun m => by positivity
  have hr0 : ∀ v, 0 ≤ r v := fun v => by positivity
  refine ⟨fun v => s v.1 + 2 * r v.1, fun v => by linarith [hs0 v.1, hr0 v.1],
    ((hD3.subtype _).add ((hSV.subtype _).mul_left 2)), fun v => ?_⟩

  obtain ⟨v, hv⟩ := v
  obtain ⟨hl, ho, hl', ho'⟩ := hbd v hv
  set q : ℝ := ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) with hq
  have hq2 : (2 : ℝ) ≤ q := by
    have h1 : 1 < Ideal.absNorm v.asIdeal := by
      rw [Nat.one_lt_iff_ne_zero_and_ne_one]
      exact ⟨by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot, by rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top⟩
    rw [hq]; exact_mod_cast h1
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hqC : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = (q : ℂ) := by rw [hq]; norm_cast

  have hκle : q ^ κ ≤ q ^ |κ| := Real.rpow_le_rpow_of_exponent_le hq1 (le_abs_self κ)
  have hu := fun m => UnramifiedWhittaker.norm_heckeRecursionSeq_le_mul_pow_of_norm_le_rpow q |κ| hq1 hκa (lam v) (om v)
    (hl.trans hκle) (ho.trans hκle) m
  have hu' := fun m => UnramifiedWhittaker.norm_heckeRecursionSeq_le_mul_pow_of_norm_le_rpow q |κ| hq1 hκa (lam' v) (om' v)
    (hl'.trans hκle) (ho'.trans hκle) m

  set ρ : ℝ := ‖om v‖ * ‖om' v‖ * q ^ (-(2 * τ)) with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρle : ρ ≤ r v := by
    show ρ ≤ q ^ (-σ₀)
    rw [hρ, hσ₀]
    calc ‖om v‖ * ‖om' v‖ * q ^ (-(2 * τ)) ≤ q ^ |κ| * q ^ |κ| * q ^ (-(2 * τ)) := by
          gcongr
          · exact ho.trans hκle
          · exact ho'.trans hκle
      _ = q ^ (-(2 * (τ - |κ|))) := by
          rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; congr 1; ring
  have hrhalf : r v ≤ 1 / 2 := by
    show q ^ (-σ₀) ≤ 1 / 2
    calc q ^ (-σ₀) ≤ (2 : ℝ) ^ (-σ₀) := Real.rpow_le_rpow_of_nonpos (by norm_num) hq2 (by linarith)
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hρ1 : ρ < 1 := by linarith

  set a : ℕ → ℝ := fun m => q ^ (m : ℝ) * (‖heckeRecursionSeq (q : ℂ) (lam v) (om v) m‖ *
    ‖heckeRecursionSeq (q : ℂ) (lam' v) (om' v) m‖) * q ^ (-((m : ℝ) * τ)) with ha
  have ha0 : ∀ m, 0 ≤ a m := fun m => by rw [ha]; positivity
  have hale : ∀ m : ℕ, a m ≤ ((m : ℝ) + 1) ^ 2 * q ^ (-((m : ℝ) * θ)) := by
    intro m
    rw [ha]
    have h4 : (4 : ℝ) ^ m ≤ q ^ ((2 : ℝ) * m) := by
      rw [Real.rpow_mul hq0.le, Real.rpow_natCast, Real.rpow_two]
      exact pow_le_pow_left₀ (by norm_num) (by nlinarith) m
    calc q ^ (m : ℝ) * (‖heckeRecursionSeq (q : ℂ) (lam v) (om v) m‖ * ‖heckeRecursionSeq (q : ℂ) (lam' v) (om' v) m‖) *
          q ^ (-((m : ℝ) * τ))
        ≤ q ^ (m : ℝ) * ((((m : ℝ) + 1) * (2 * q ^ |κ|) ^ m) * (((m : ℝ) + 1) * (2 * q ^ |κ|) ^ m)) * q ^ (-((m : ℝ) * τ)) := by
          gcongr
          · exact hu m
          · exact hu' m
      _ = ((m : ℝ) + 1) ^ 2 * (4 : ℝ) ^ m * (q ^ (m : ℝ) * (q ^ |κ|) ^ m * (q ^ |κ|) ^ m * q ^ (-((m : ℝ) * τ))) := by
          rw [mul_pow, show ((4 : ℝ) ^ m) = ((2 : ℝ) ^ m) * ((2 : ℝ) ^ m) by rw [← mul_pow]; norm_num]; ring
      _ ≤ ((m : ℝ) + 1) ^ 2 * q ^ ((2 : ℝ) * m) * (q ^ (m : ℝ) * (q ^ |κ|) ^ m * (q ^ |κ|) ^ m * q ^ (-((m : ℝ) * τ))) := by
          gcongr
      _ = ((m : ℝ) + 1) ^ 2 * q ^ (-((m : ℝ) * θ)) := by
          rw [← Real.rpow_natCast (q ^ |κ|) m, ← Real.rpow_mul hq0.le, hθ]
          rw [show ((m : ℝ) + 1) ^ 2 * q ^ ((2 : ℝ) * m) * (q ^ (m : ℝ) * q ^ (|κ| * m) * q ^ (|κ| * m) * q ^ (-((m : ℝ) * τ))) =
            ((m : ℝ) + 1) ^ 2 * (q ^ ((2 : ℝ) * m) * q ^ (m : ℝ) * q ^ (|κ| * m) * q ^ (|κ| * m) * q ^ (-((m : ℝ) * τ))) by ring,
            ← Real.rpow_add hq0, ← Real.rpow_add hq0, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
          congr 2; ring

  have hmaj : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ 2 * q ^ (-((m : ℝ) * θ))) := by
    have h := (hD3a v)
    rw [← summable_nat_add_iff 1]
    refine h.congr (fun m => ?_)
    push_cast
    rw [hq]; congr 1 <;> [ring; (congr 1; ring)]
  have hmajsum : ∑' m : ℕ, ((m : ℝ) + 1) ^ 2 * q ^ (-((m : ℝ) * θ)) = 1 + s v := by
    rw [hmaj.tsum_eq_zero_add]
    congr 1
    · simp
    · show _ = 1 * _
      rw [one_mul]
      refine tsum_congr (fun m => ?_)
      push_cast; rw [hq]; congr 1 <;> [ring; (congr 1; ring)]
  have hasum : Summable a := Summable.of_nonneg_of_le ha0 hale hmaj
  have haval : ∑' m, a m ≤ Real.exp (s v) := by
    calc ∑' m, a m ≤ ∑' m : ℕ, ((m : ℝ) + 1) ^ 2 * q ^ (-((m : ℝ) * θ)) := hasum.tsum_le_tsum hale hmaj
      _ = 1 + s v := hmajsum
      _ ≤ Real.exp (s v) := by linarith [Real.add_one_le_exp (s v)]
  have hgeo : ∑' n : ℕ, ρ ^ n ≤ Real.exp (2 * r v) := by
    rw [tsum_geometric_of_lt_one hρ0 hρ1]
    calc (1 - ρ)⁻¹ ≤ (1 - r v)⁻¹ := by
          apply inv_anti₀ (by linarith) (by linarith)
      _ ≤ Real.exp (2 * r v) := inv_one_sub_le_exp_two_mul (hr0 v) hrhalf

  rw [tsum_cone_eq _ (fun p hp => by rw [if_neg hp, norm_zero, mul_zero, zero_mul, ENNReal.ofReal_zero])]
  have hterm : ∀ mn : ℕ × ℕ,
      ENNReal.ofReal (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ((((mn.1 : ℤ) + mn.2) : ℤ) - (mn.2 : ℤ)) *
        ‖(if 0 ≤ (((mn.1 : ℤ) + mn.2) : ℤ) - (mn.2 : ℤ) ∧ 0 ≤ (mn.2 : ℤ) then
            (om v * om' v) ^ (mn.2 : ℤ).toNat *
              heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam v) (om v) ((((mn.1 : ℤ) + mn.2) : ℤ) - (mn.2 : ℤ)).toNat *
              heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam' v) (om' v) ((((mn.1 : ℤ) + mn.2) : ℤ) - (mn.2 : ℤ)).toNat
          else 0)‖ *
        (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((((mn.1 : ℤ) + mn.2) : ℤ) + (mn.2 : ℤ)))) ^ τ) =
      ENNReal.ofReal (a mn.1) * ENNReal.ofReal (ρ ^ mn.2) := by
    intro mn
    obtain ⟨m, n⟩ := mn
    rw [← ENNReal.ofReal_mul (ha0 m)]
    congr 1
    simp only [add_sub_cancel_right, Int.toNat_natCast, hqC, ← hq]
    rw [if_pos ⟨by positivity, by positivity⟩, norm_mul, norm_mul, norm_pow, norm_mul, zpow_natCast,
      ← Real.rpow_intCast q (-(((m : ℤ) + n) + n)), ← Real.rpow_mul hq0.le, ha, hρ]
    push_cast
    have e : q ^ (-(((m : ℝ) + n) + n) * τ) = q ^ (-((m : ℝ) * τ)) * (q ^ (-(2 * τ))) ^ n := by
      rw [← Real.rpow_natCast (q ^ (-(2 * τ))) n, ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0]; congr 1; ring
    rw [e, ← Real.rpow_natCast q m, mul_pow, mul_pow]
    ring
  rw [tsum_congr hterm, ENNReal.tsum_prod']
  simp only [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun n => pow_nonneg hρ0 n) (summable_geometric_of_lt_one hρ0 hρ1),
    ← ENNReal.ofReal_tsum_of_nonneg ha0 hasum, ← ENNReal.ofReal_mul (tsum_nonneg ha0), Real.exp_add]
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul haval hgeo (tsum_nonneg fun n => pow_nonneg hρ0 n) (Real.exp_pos _).le

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_exists_summable_forall_tsum_shell_le_exp_of_norm_le_rpow
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_summable_forall_tsum_shell_le_exp_of_norm_le_rpow (solution)
