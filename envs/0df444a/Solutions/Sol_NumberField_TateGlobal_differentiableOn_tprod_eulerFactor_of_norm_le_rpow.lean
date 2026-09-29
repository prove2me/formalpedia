-- Prove2me | solution 1 for NumberField.TateGlobal.differentiableOn_tprod_eulerFactor_of_norm_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ae5bc6b9-3d19-5a57-98a6-613b7f38c9a1

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_differentiableOn_tprod_eulerFactor_of_norm_le_rpow

set_option autoImplicit false
set_option maxHeartbeats 1600000

open NumberField NumberField.TateGlobal IsDedekindDomain AutomorphicForm Polynomial

noncomputable section

namespace Ws1
namespace EC

theorem eval_quad (u w x : ℂ) : (C 1 - C u * X + C w * X ^ 2 : ℂ[X]).eval x = 1 - u * x + w * x ^ 2 := by
  simp [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]

theorem exists_roots (u w : ℂ) : ∃ α β : ℂ, α + β = u ∧ α * β = w ∧ ‖α‖ ≤ (‖u‖ + ‖α - β‖) / 2 ∧ ‖β‖ ≤ (‖u‖ + ‖α - β‖) / 2
    ∧ (α - β) ^ 2 = u ^ 2 - 4 * w := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (u ^ 2 - 4 * w) (n := 2) two_pos
  refine ⟨(u + d) / 2, (u - d) / 2, by ring, ?_, ?_, ?_, ?_⟩
  · have : (u + d) / 2 * ((u - d) / 2) = (u ^ 2 - d ^ 2) / 4 := by ring
    rw [this, hd]; ring
  · have h : (u + d) / 2 - (u - d) / 2 = d := by ring
    rw [h, norm_div, Complex.norm_two]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) two_pos.le
  · have h : (u + d) / 2 - (u - d) / 2 = d := by ring
    rw [h, norm_div, Complex.norm_two]
    exact div_le_div_of_nonneg_right ((norm_sub_le _ _).trans le_rfl) two_pos.le
  · have h : (u + d) / 2 - (u - d) / 2 = d := by ring
    rw [h, hd]

end Ws1.EC

end

open scoped Classical in

theorem solution
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (a b : HeightOneSpectrum (𝓞 F) → ℂ)
    (τ : ℝ)
    (hτ : ∀ v ∉ S, ‖((χ (uniformizerIdele F v) : ℂˣ) : ℂ)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ τ)
    (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      ‖a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖b v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
    (σ₀ : ℝ) (hσ₀ : κ + τ + 4 ≤ σ₀) :
    (∀ s : ℂ, σ₀ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
        ((if IsUnramifiedCharAt χ v.1
          then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * a v.1) * X
            + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * b v.1) * X ^ 2
          else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
        (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          ((if IsUnramifiedCharAt χ v.1
            then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * a v.1) * X
              + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * b v.1) * X ^ 2
            else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)) ∧
    DifferentiableOn ℂ (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        ((if IsUnramifiedCharAt χ v.1
          then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * a v.1) * X
            + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * b v.1) * X ^ 2
          else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
      {s : ℂ | σ₀ < s.re} := by
  classical

  set V := {v : HeightOneSpectrum (𝓞 F) // v ∉ S}
  have hqr1 : ∀ v : V, (1 : ℝ) < (Ideal.absNorm v.1.asIdeal : ℕ) := fun v => by
    have h0 : Ideal.absNorm v.1.asIdeal ≠ 0 := by rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact v.1.ne_bot
    have h1 : Ideal.absNorm v.1.asIdeal ≠ 1 := fun h => v.1.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    exact_mod_cast Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨h0, h1⟩
  have hqr2 : ∀ v : V, (2 : ℝ) ≤ (Ideal.absNorm v.1.asIdeal : ℕ) := fun v => by
    have h0 : Ideal.absNorm v.1.asIdeal ≠ 0 := by rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact v.1.ne_bot
    have h1 : Ideal.absNorm v.1.asIdeal ≠ 1 := fun h => v.1.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    exact_mod_cast (Nat.two_le_iff _).mpr ⟨h0, h1⟩
  have hqr0 : ∀ v : V, (0 : ℝ) < (Ideal.absNorm v.1.asIdeal : ℕ) := fun v => lt_trans one_pos (hqr1 v)
  have hqC : ∀ v : V, ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ≠ 0 := fun v => by exact_mod_cast (hqr0 v).ne'
  have hqCeq : ∀ v : V, ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) = (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) : ℂ) :=
    fun v => by push_cast; rfl

  set c₁ : V → ℂ := fun v => if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * a v.1 else 0
    with hc₁def
  set c₂ : V → ℂ := fun v => if IsUnramifiedCharAt χ v.1 then ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ)) * b v.1 else 0
    with hc₂def
  have hfac_eval : ∀ (v : V) (x : ℂ), ((if IsUnramifiedCharAt χ v.1
      then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * a v.1) * X
        + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * b v.1) * X ^ 2
      else C 1 : ℂ[X]).eval x) = 1 - c₁ v * x + c₂ v * x ^ 2 := by
    intro v x
    rw [hc₁def, hc₂def]
    dsimp only
    split_ifs
    · exact Ws1.EC.eval_quad _ _ _
    · simp

  have hc₁n : ∀ v : V, ‖c₁ v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (τ + κ) := by
    intro v
    rw [hc₁def]; dsimp only
    split_ifs
    · rw [norm_mul, Real.rpow_add (hqr0 v)]
      exact mul_le_mul (hτ v.1 v.2) (hκ v.1 v.2).1 (norm_nonneg _) (Real.rpow_nonneg (hqr0 v).le _)
    · rw [norm_zero]; exact Real.rpow_nonneg (hqr0 v).le _
  have hc₂n : ∀ v : V, ‖c₂ v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (2 * (τ + κ)) := by
    intro v
    rw [hc₂def]; dsimp only
    split_ifs
    · rw [norm_mul, Units.val_pow_eq_pow_val, norm_pow]
      calc ‖((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ)‖ ^ 2 * ‖b v.1‖
          ≤ (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ τ) ^ 2 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hτ v.1 v.2) 2) (hκ v.1 v.2).2 (norm_nonneg _)
              (pow_nonneg (Real.rpow_nonneg (hqr0 v).le _) 2)
        _ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (2 * (τ + κ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (hqr0 v).le, ← Real.rpow_add (hqr0 v)]
            refine Real.rpow_le_rpow_of_exponent_le (hqr1 v).le ?_
            push_cast
            linarith
    · rw [norm_zero]; exact Real.rpow_nonneg (hqr0 v).le _

  have hroots : ∀ v : V, ∃ α β : ℂ, α + β = c₁ v ∧ α * β = c₂ v ∧
      ‖α‖ ≤ 2 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (τ + κ) ∧ ‖β‖ ≤ 2 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (τ + κ) := by
    intro v
    obtain ⟨α, β, h1, h2, h3, h4, h5⟩ := Ws1.EC.exists_roots (c₁ v) (c₂ v)
    set Q : ℝ := ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (τ + κ) with hQ
    have hQ0 : 0 ≤ Q := Real.rpow_nonneg (hqr0 v).le _
    have hd : ‖α - β‖ ≤ 3 * Q := by
      have hsq : ‖α - β‖ ^ 2 ≤ (3 * Q) ^ 2 := by
        rw [← norm_pow, h5]
        calc ‖c₁ v ^ 2 - 4 * c₂ v‖ ≤ ‖c₁ v ^ 2‖ + ‖4 * c₂ v‖ := norm_sub_le _ _
          _ = ‖c₁ v‖ ^ 2 + 4 * ‖c₂ v‖ := by rw [norm_pow, norm_mul]; norm_num
          _ ≤ Q ^ 2 + 4 * Q ^ 2 := by
              refine add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hc₁n v) 2) (mul_le_mul_of_nonneg_left ?_ (by norm_num))
              rw [hQ, ← Real.rpow_natCast, ← Real.rpow_mul (hqr0 v).le]
              refine (hc₂n v).trans (le_of_eq ?_)
              congr 1
              push_cast
              ring
          _ ≤ (3 * Q) ^ 2 := by nlinarith
      have h9 : (0 : ℝ) ≤ 3 * Q := by positivity
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) h9 two_ne_zero).mp hsq
    refine ⟨α, β, h1, h2, ?_, ?_⟩
    · have := hc₁n v; rw [← hQ] at this; linarith
    · have := hc₁n v; rw [← hQ] at this; linarith
  choose α β hαβ1 hαβ2 hαn hβn using hroots

  set σ₁ : ℝ := τ + κ + 1 with hσ₁def
  set z₁ : V → ℂ := fun v => α v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ₁ : ℂ)) with hz₁def
  set z₂ : V → ℂ := fun v => β v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ₁ : ℂ)) with hz₂def
  have hnormq : ∀ (v : V) (r : ℝ), ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(r : ℂ))‖ =
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-r) := by
    intro v r
    rw [hqCeq, Complex.norm_cpow_eq_rpow_re_of_pos (hqr0 v)]
    simp
  have hzbound : ∀ (γ : V → ℂ), (∀ v, ‖γ v‖ ≤ 2 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (τ + κ)) →
      ∀ v, ‖γ v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ₁ : ℂ))‖ ≤ 1 := by
    intro γ hγ v
    rw [norm_mul, hnormq]
    calc ‖γ v‖ * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-σ₁)
        ≤ 2 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (τ + κ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-σ₁) :=
          mul_le_mul_of_nonneg_right (hγ v) (Real.rpow_nonneg (hqr0 v).le _)
      _ = 2 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ)⁻¹ := by
          rw [mul_assoc, ← Real.rpow_add (hqr0 v), hσ₁def, show τ + κ + -(τ + κ + 1) = (-1 : ℝ) by ring,
            Real.rpow_neg_one]
      _ ≤ 1 := by
          rw [mul_inv_le_iff₀ (hqr0 v), one_mul]
          exact hqr2 v
  have hz₁ : ∀ v, ‖z₁ v‖ ≤ 1 := hzbound α hαn
  have hz₂ : ∀ v, ‖z₂ v‖ ≤ 1 := hzbound β hβn
  obtain ⟨hM₁, hD₁, -⟩ := NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F S z₁ hz₁
  obtain ⟨hM₂, hD₂, -⟩ := NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F S z₂ hz₂

  have hfg : ∀ (s : ℂ) (v : V), ((if IsUnramifiedCharAt χ v.1
          then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * a v.1) * X
            + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * b v.1) * X ^ 2
          else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ =
      (1 - z₁ v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s - σ₁)))⁻¹ *
        (1 - z₂ v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s - σ₁)))⁻¹ := by
    intro s v
    have hx : ∀ γ : ℂ, γ * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ₁ : ℂ)) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s - σ₁)) = γ * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s) := by
      intro γ
      rw [mul_assoc, ← Complex.cpow_add _ _ (hqC v)]
      congr 2
      ring
    rw [hfac_eval, hz₁def, hz₂def]
    dsimp only
    rw [hx, hx, ← mul_inv, ← hαβ1, ← hαβ2]
    congr 1
    ring

  refine ⟨fun s hs => ?_, ?_⟩
  · have hs' : 1 < (s - (σ₁ : ℂ)).re := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith
    have hmul := (hM₁ _ hs').mul (hM₂ _ hs')
    have hfun : (fun v : V => ((if IsUnramifiedCharAt χ v.1
          then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * a v.1) * X
            + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * b v.1) * X ^ 2
          else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) =
        fun v : V => (1 - z₁ v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s - σ₁)))⁻¹ *
          (1 - z₂ v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s - σ₁)))⁻¹ := funext (hfg s)
    rw [hfun]
    exact hmul.hasProd
  · have hmaps : Set.MapsTo (fun s : ℂ => s - (σ₁ : ℂ)) {s : ℂ | σ₀ < s.re} {s : ℂ | 1 < s.re} := by
      intro s hs
      simp only [Set.mem_setOf_eq, Complex.sub_re, Complex.ofReal_re] at hs ⊢
      linarith
    have hD : DifferentiableOn ℂ (fun s : ℂ =>
        (∏' v : V, (1 - z₁ v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s - σ₁)))⁻¹) *
          ∏' v : V, (1 - z₂ v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s - σ₁)))⁻¹) {s : ℂ | σ₀ < s.re} :=
      (hD₁.comp (differentiableOn_id.sub_const _) hmaps).mul (hD₂.comp (differentiableOn_id.sub_const _) hmaps)
    refine hD.congr fun s hs => ?_
    have hs' : 1 < (s - (σ₁ : ℂ)).re := hmaps hs
    show (∏' v : V, ((if IsUnramifiedCharAt χ v.1
          then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * a v.1) * X
            + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * b v.1) * X ^ 2
          else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) = _
    rw [← (hM₁ _ hs').tprod_mul (hM₂ _ hs')]
    exact tprod_congr (hfg s)

end S_NumberField_TateGlobal_differentiableOn_tprod_eulerFactor_of_norm_le_rpow
end P2MW
export P2MW.S_NumberField_TateGlobal_differentiableOn_tprod_eulerFactor_of_norm_le_rpow (solution)
