-- Prove2me | solution 1 for IAFTRL.proposition_D_2_ftrl
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T08:41:59.845245+00:00
-- url     : https://prove2.me/submissions/68d9fb15-bacf-44d0-8fcc-7c00d6ab5e02

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_IAFTRL_regretVs

import Theorems.Thm_IAFTRL_lemma_D_18

open Matrix MeasureTheory IAFTRL

theorem solution {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ)
    (hA : IsActionSet arms) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℕ) (hT : 1 ≤ T) (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R)
    (u : Fin K) :
    regretVs P arms T R u ≤
      16 * (d : ℝ) * Real.log (Real.exp 1 * K) +
        21 * Real.sqrt ((d : ℝ) * T * Real.log (Real.exp 1 * K)) := by
  classical
  -- basic facts
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ u).elim0)
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hKr
  have hL : 0 < 1 + Real.log K := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have heK : Real.log (Real.exp 1 * K) = 1 + Real.log K := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  have hβpos : ∀ t, 0 < beta d K t := fun t => by unfold beta; positivity
  have hβmono : ∀ t, beta d K t ≤ beta d K (t + 1) := by
    intro t
    unfold beta
    apply add_le_add le_rfl
    apply Real.sqrt_le_sqrt
    apply (div_le_div_iff_of_pos_right hL).mpr
    push_cast
    nlinarith
  -- `√(y L) = L √(y / L)`
  have hsqrtL : ∀ y : ℝ, Real.sqrt (y * (1 + Real.log K)) =
      (1 + Real.log K) * Real.sqrt (y / (1 + Real.log K)) := by
    intro y
    rw [show y * (1 + Real.log K) = (1 + Real.log K) ^ 2 * (y / (1 + Real.log K)) by
      field_simp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hL.le]
  -- integrals of functions bounded above by a nonnegative constant
  have intLe : ∀ (f : Ω → ℝ) (c : ℝ), 0 ≤ c → (∀ ω, f ω ≤ c) → ∫ ω, f ω ∂P ≤ c := by
    intro f c hc hf
    by_cases hi : Integrable f P
    · calc ∫ ω, f ω ∂P ≤ ∫ _ω, c ∂P := integral_mono hi (integrable_const c) hf
        _ = c := by simp
    · rw [integral_undef hi]; exact hc
  -- exponential weights: positive and summing to one
  have hsumpos : ∀ (β : ℝ) (S : Fin d → ℝ), 0 < ∑ b, Real.exp (-(arms b ⬝ᵥ S) / β) :=
    fun β S => Finset.sum_pos (fun b _ => Real.exp_pos _) ⟨u, Finset.mem_univ u⟩
  have hqpos : ∀ (β : ℝ) (S : Fin d → ℝ) (a : Fin K), 0 < qSoft β arms S a := by
    intro β S a
    unfold qSoft
    exact div_pos (Real.exp_pos _) (hsumpos β S)
  have hqsum : ∀ (β : ℝ) (S : Fin d → ℝ), ∑ a, qSoft β arms S a = 1 := by
    intro β S
    unfold qSoft
    rw [← Finset.sum_div]
    exact div_self (hsumpos β S).ne'
  -- the entropy of a positive probability vector is at most `log K`
  have hH : ∀ q : Fin K → ℝ, (∀ a, 0 < q a) → ∑ a, q a = 1 →
      -∑ a, q a * Real.log (q a) ≤ Real.log K := by
    intro q hq hs
    have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := Finset.univ) (w := q)
      (p := fun a => (q a)⁻¹) (fun a _ => (hq a).le) hs
      (fun a _ => Set.mem_Ioi.mpr (inv_pos.mpr (hq a)))
    simp only [smul_eq_mul] at hJ
    have h1 : ∑ a, q a * (q a)⁻¹ = (K : ℝ) := by
      rw [Finset.sum_congr rfl fun a _ => mul_inv_cancel₀ (hq a).ne']
      simp
    rw [h1] at hJ
    calc -∑ a, q a * Real.log (q a) = ∑ a, q a * Real.log (q a)⁻¹ := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Real.log_inv]; ring
      _ ≤ Real.log K := hJ
  -- per-round consequences of feasibility for (2.3)
  have hround : ∀ t < T, ∀ ω,
      proxyC arms (t + 1) (R.cumEst arms t ω) (R.p t ω) ≤ 2 * (d : ℝ) / beta d K (t + 1) ∧
      ∑ a, (R.p t ω a - qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a) *
          (arms a ⬝ᵥ (R.θs t ω - 0)) ≤ 2 * Gam d K (t + 1) := by
    intro t ht ω
    obtain ⟨-, ⟨-, hmin⟩, -, -, hnorm⟩ := hR t ht
    obtain ⟨⟨-, -, ⟨w, hw0, hwG, hpw⟩, -, -, hprox⟩, -⟩ := hmin ω
    refine ⟨hprox, ?_⟩
    have hℓ : ∀ a, |arms a ⬝ᵥ R.θs t ω| ≤ 1 := fun a =>
      (le_ciSup (f := fun j => |arms j ⬝ᵥ R.θs t ω|) (Set.finite_range _).bddAbove a).trans
        (hnorm ω)
    set q := qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) with hqdef
    set γ := ∑ b, w b with hγ
    have hγ0 : 0 ≤ γ := Finset.sum_nonneg fun b _ => hw0 b
    rw [hpw]
    simp only [sub_zero]
    have hsplit : ∑ a, ((1 - γ) * q a + w a - q a) * (arms a ⬝ᵥ R.θs t ω) =
        ∑ a, w a * (arms a ⬝ᵥ R.θs t ω) - γ * ∑ a, q a * (arms a ⬝ᵥ R.θs t ω) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hsplit]
    have hw : ∑ a, w a * (arms a ⬝ᵥ R.θs t ω) ≤ γ := by
      rw [hγ]
      exact Finset.sum_le_sum fun a _ =>
        mul_le_of_le_one_right (hw0 a) (abs_le.mp (hℓ a)).2
    have hq : -1 ≤ ∑ a, q a * (arms a ⬝ᵥ R.θs t ω) := by
      have : ∑ a, q a * (-1) ≤ ∑ a, q a * (arms a ⬝ᵥ R.θs t ω) :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (abs_le.mp (hℓ a)).1 (hqpos _ _ a).le
      rw [← Finset.sum_mul, hqsum, one_mul] at this
      exact this
    nlinarith
  -- Lemma D.18 at the center `θ = 0`, for the point-mass comparator at `u`
  set uvec : Fin K → ℝ := fun a => if a = u then 1 else 0 with huvec
  have hu0 : ∀ a, 0 ≤ uvec a := fun a => by simp only [uvec]; split_ifs <;> norm_num
  have hu1 : ∑ a, uvec a = 1 := by simp [uvec]
  have hD := (lemma_D_18 hd arms hA P T R hR 0 u uvec hu0 hu1).2.2
  have hreg : regretVs P arms T R u = regretDist P arms T R uvec := by
    unfold regretVs regretDist
    have : ∑ a, uvec a • arms a = arms u := by simp [uvec, ite_smul]
    rw [this]
  rw [hreg]
  refine le_trans hD ?_
  -- the four terms of (D.167)
  have hexplo : ∑ t ∈ Finset.range T, ∫ ω, ∑ a, (R.p t ω a -
      qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a) *
        ((arms a - arms u) ⬝ᵥ (0 : Fin d → ℝ)) ∂P = 0 := by simp
  have hpen : beta d K 1 * Real.log K + ∑ t ∈ Finset.Ico 1 T, (beta d K (t + 1) - beta d K t) *
      ∫ ω, -∑ a, qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a *
        Real.log (qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a) ∂P ≤
      beta d K T * Real.log K := by
    have htel : ∀ n, 1 ≤ n →
        beta d K 1 + ∑ t ∈ Finset.Ico 1 n, (beta d K (t + 1) - beta d K t) = beta d K n := by
      intro n hn
      induction n with
      | zero => omega
      | succ m ih =>
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp
        · rw [Finset.sum_Ico_succ_top hm, ← add_assoc, ih hm]
          ring
    calc beta d K 1 * Real.log K + ∑ t ∈ Finset.Ico 1 T, (beta d K (t + 1) - beta d K t) *
          ∫ ω, -∑ a, qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a *
            Real.log (qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a) ∂P
        ≤ beta d K 1 * Real.log K + ∑ t ∈ Finset.Ico 1 T,
            (beta d K (t + 1) - beta d K t) * Real.log K := by
          gcongr with t ht
          · exact sub_nonneg.mpr (hβmono t)
          · exact intLe _ _ hlogK fun ω => hH _ (hqpos _ _) (hqsum _ _)
      _ = (beta d K 1 + ∑ t ∈ Finset.Ico 1 T, (beta d K (t + 1) - beta d K t)) *
            Real.log K := by rw [add_mul, Finset.sum_mul]
      _ = beta d K T * Real.log K := by rw [htel T hT]
  have hprox : ∑ t ∈ Finset.range T,
      ∫ ω, proxyC arms (t + 1) (R.cumEst arms t ω) (R.p t ω) ∂P ≤
      ∑ t ∈ Finset.range T, 2 * (d : ℝ) / beta d K (t + 1) := by
    refine Finset.sum_le_sum fun t ht => ?_
    exact intLe _ _ (by have := hβpos (t + 1); positivity)
      fun ω => (hround t (Finset.mem_range.mp ht) ω).1
  have hcorr : ∑ t ∈ Finset.range T, ∫ ω, ∑ a, (R.p t ω a -
      qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a) * (arms a ⬝ᵥ (R.θs t ω - 0)) ∂P ≤
      ∑ t ∈ Finset.range T, 2 * Gam d K (t + 1) := by
    refine Finset.sum_le_sum fun t ht => ?_
    exact intLe _ _ (by unfold Gam; have := hβpos (t + 1); positivity)
      fun ω => (hround t (Finset.mem_range.mp ht) ω).2
  -- summing `10d/β_{t+1}` against `√(d t L)`
  set g : ℕ → ℝ := fun t => Real.sqrt ((d : ℝ) * t * (1 + Real.log K)) with hgdef
  have hterm : ∀ t : ℕ, 2 * (d : ℝ) / beta d K (t + 1) + 2 * Gam d K (t + 1) ≤
      20 * (g (t + 1) - g t) := by
    intro t
    have hβ := hβpos (t + 1)
    have hGam : 2 * (d : ℝ) / beta d K (t + 1) + 2 * Gam d K (t + 1) =
        10 * d / beta d K (t + 1) := by unfold Gam; ring
    rw [hGam]
    set x : ℝ := (d : ℝ) * ((t + 1 : ℕ) : ℝ) with hx
    have hxpos : 0 < x := by positivity
    have hu2 : g (t + 1) ^ 2 = x * (1 + Real.log K) := Real.sq_sqrt (by positivity)
    have hv2 : g t ^ 2 = (d : ℝ) * t * (1 + Real.log K) := Real.sq_sqrt (by positivity)
    have hupos : 0 < g (t + 1) := Real.sqrt_pos.mpr (by positivity)
    have hv0 : 0 ≤ g t := Real.sqrt_nonneg _
    have huv : g (t + 1) ^ 2 - g t ^ 2 = d * (1 + Real.log K) := by
      rw [hu2, hv2, hx]; push_cast; ring
    have hβu : g (t + 1) / (1 + Real.log K) ≤ beta d K (t + 1) := by
      have : g (t + 1) = (1 + Real.log K) * Real.sqrt (x / (1 + Real.log K)) := hsqrtL x
      rw [this, mul_div_cancel_left₀ _ hL.ne']
      unfold beta
      have := Real.sqrt_nonneg (x / (1 + Real.log K))
      simp only [hx]
      linarith [hdpos]
    calc 10 * (d : ℝ) / beta d K (t + 1)
        ≤ 10 * d / (g (t + 1) / (1 + Real.log K)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hβu
      _ = 10 * d * (1 + Real.log K) / g (t + 1) := by field_simp
      _ ≤ 20 * (g (t + 1) - g t) := by
          rw [div_le_iff₀ hupos]
          nlinarith [sq_nonneg (g (t + 1) - g t)]
  have hsum : ∑ t ∈ Finset.range T, (2 * (d : ℝ) / beta d K (t + 1) + 2 * Gam d K (t + 1)) ≤
      20 * g T := by
    calc ∑ t ∈ Finset.range T, (2 * (d : ℝ) / beta d K (t + 1) + 2 * Gam d K (t + 1))
        ≤ ∑ t ∈ Finset.range T, 20 * (g (t + 1) - g t) := Finset.sum_le_sum fun t _ => hterm t
      _ = 20 * g T := by
          rw [← Finset.mul_sum, Finset.sum_range_sub (f := g)]
          simp [g]
  have hβT : beta d K T * Real.log K ≤ 16 * d * (1 + Real.log K) + g T := by
    have hgT : g T = (1 + Real.log K) * Real.sqrt ((d : ℝ) * T / (1 + Real.log K)) :=
      hsqrtL ((d : ℝ) * T)
    rw [hgT]
    unfold beta
    have := Real.sqrt_nonneg ((d : ℝ) * T / (1 + Real.log K))
    nlinarith
  -- assemble
  rw [heK]
  have hsplit2 := Finset.sum_add_distrib (s := Finset.range T)
    (f := fun t => 2 * (d : ℝ) / beta d K (t + 1)) (g := fun t => 2 * Gam d K (t + 1))
  have hgT' : g T = Real.sqrt ((d : ℝ) * T * (1 + Real.log K)) := rfl
  rw [hexplo]
  linarith [hpen, hprox, hcorr, hsum, hβT, hsplit2]
