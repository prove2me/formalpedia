-- Prove2me | solution 1 for IAFTRL.proposition_2_1_stochastic
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T09:31:22.76585+00:00
-- url     : https://prove2.me/submissions/25da8589-0db0-474c-983d-1b5dcaacad55

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_actionNorm
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsCorrupted
import Definitions.Def_IAFTRL_regretVs
import Definitions.Def_IAFTRL_IsFeasibleAlloc
import Definitions.Def_IAFTRL_allocCost

import Theorems.Thm_IAFTRL_lemma_D_18
import Theorems.Thm_IAFTRL_lemma_D_14
import Theorems.Thm_IAFTRL_proposition_2_1_penalty
import Theorems.Thm_IAFTRL_proposition_2_1_stability
import Theorems.Thm_IAFTRL_proposition_2_1_exploration

open Matrix MeasureTheory IAFTRL

namespace P21S

lemma sqrt6_bound : 16 * Real.sqrt 2 * Real.sqrt 3 ≤ 40 := by
  have ha := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hb := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have ha0 := Real.sqrt_nonneg 2
  have hb0 := Real.sqrt_nonneg 3
  have hprod : Real.sqrt 2 * Real.sqrt 3 ≤ 5 / 2 := by
    nlinarith [sq_nonneg (Real.sqrt 2 * Real.sqrt 3 - 5 / 2), mul_nonneg ha0 hb0]
  have : 16 * Real.sqrt 2 * Real.sqrt 3 = 16 * (Real.sqrt 2 * Real.sqrt 3) := by ring
  linarith

lemma cR_le (d K : ℕ) (hK : 2 ≤ K) :
    IAFTRL.cR d K ≤ Real.sqrt 3 * Real.sqrt ((d : ℝ) * Real.log K) := by
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogK2 : Real.log 2 ≤ Real.log K := Real.log_le_log (by norm_num) hK2
  have heK : Real.log (Real.exp 1 * K) = 1 + Real.log K := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  unfold IAFTRL.cR
  rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num)]
  apply Real.sqrt_le_sqrt
  rw [heK]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  nlinarith

lemma corr_le (d K : ℕ) (hK : 2 ≤ K) (C Δ₀ : ℝ) (hΔ₀ : 0 < Δ₀) (hΔ₀1 : Δ₀ ≤ 1) :
    16 * Real.sqrt 2 * IAFTRL.cR d K * Real.sqrt C ≤
      40 * (Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) := by
  have hpow : 1 ≤ Δ₀ ^ (-(128 : ℝ) / 255) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hΔ₀ hΔ₀1 (by norm_num)
  have hsC := Real.sqrt_nonneg C
  have hsd := Real.sqrt_nonneg ((d : ℝ) * Real.log K)
  have h1 := cR_le d K hK
  have h2 := sqrt6_bound
  calc 16 * Real.sqrt 2 * IAFTRL.cR d K * Real.sqrt C
      ≤ 16 * Real.sqrt 2 * (Real.sqrt 3 * Real.sqrt ((d : ℝ) * Real.log K)) * Real.sqrt C := by
        gcongr
    _ = (16 * Real.sqrt 2 * Real.sqrt 3) * (Real.sqrt ((d : ℝ) * Real.log K) * Real.sqrt C) := by
        ring
    _ ≤ 40 * (Real.sqrt ((d : ℝ) * Real.log K) * Real.sqrt C) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg hsd hsC)
    _ ≤ 40 * (Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) := by
        have := mul_le_mul_of_nonneg_left hpow (mul_nonneg hsd hsC)
        have e : Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C =
            Real.sqrt ((d : ℝ) * Real.log K) * Real.sqrt C * Δ₀ ^ (-(128 : ℝ) / 255) := by ring
        rw [e]
        linarith

end P21S

theorem solution : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d K : ℕ}, 1 ≤ d → ∀ (arms : Fin K → Fin d → ℝ), IsActionSet arms →
      ∀ (θ : Fin d → ℝ) (jstar : Fin K) (Δ₀ : ℝ),
        actionNorm arms θ ≤ 1 → IsUniqueMin arms θ jstar → 0 < Δ₀ → Δ₀ ≤ 1 →
        (∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) →
        ∀ n : Fin K → ℝ, IsFeasibleAlloc arms θ jstar n →
        ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : Run d K Ω), 1 ≤ T → 0 ≤ C →
          IsIAFTRLRun P arms T R → IsCorrupted P arms θ C T R →
          ∀ u : Fin K, regretVs P arms T R u ≤
            c₀ * (allocCost arms θ jstar n * Real.log K * Real.log T +
              Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) + M := by
  classical
  obtain ⟨c1, hc1, h1⟩ := proposition_2_1_penalty
  obtain ⟨c2, hc2, h2⟩ := proposition_2_1_stability
  obtain ⟨c3, hc3, h3⟩ := proposition_2_1_exploration
  refine ⟨c1 + c2 + c3 + 40, by positivity, ?_⟩
  intro d K hd arms hA θ jstar Δ₀ hθ huniq hΔ₀ hΔ₀1 hgap n hn
  obtain ⟨M1, hM1⟩ := h1 hd arms hA θ jstar Δ₀ hθ huniq hΔ₀ hΔ₀1 hgap n hn
  obtain ⟨M2, hM2⟩ := h2 hd arms hA θ jstar Δ₀ hθ huniq hΔ₀ hΔ₀1 hgap n hn
  obtain ⟨M3, hM3⟩ := h3 hd arms hA θ jstar Δ₀ hθ huniq hΔ₀ hΔ₀1 hgap n hn
  refine ⟨|M1| + |M2| + |M3|, ?_⟩
  intro Ω _ P _ T C R hT hC hR hcor u
  have hpen := hM1 P T C R hT hC hR hcor
  have hstab := hM2 P T C R hT hC hR hcor
  have hexpl := hM3 P T C R hT hC hR hcor
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ u).elim0)
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hKr
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT'
  -- the bracket of (2.5) and its pieces are nonnegative
  have hcost : 0 ≤ allocCost arms θ jstar n := by
    unfold allocCost
    refine Finset.sum_nonneg fun j _ => mul_nonneg (hn.1 j) ?_
    by_cases hj : j = jstar
    · simp [hj]
    · have := huniq j hj
      rw [sub_dotProduct]; linarith
  have hpow : 1 ≤ Δ₀ ^ (-(128 : ℝ) / 255) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hΔ₀ hΔ₀1 (by norm_num)
  set J := Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C with hJdef
  have hJ : 0 ≤ J := by positivity
  set X := allocCost arms θ jstar n * Real.log K * Real.log T + J with hXdef
  have hX : 0 ≤ X := by positivity
  have hJX : J ≤ X := by
    have : 0 ≤ allocCost arms θ jstar n * Real.log K * Real.log T := by positivity
    linarith
  have hMabs : M1 + M2 + M3 ≤ |M1| + |M2| + |M3| := by
    linarith [le_abs_self M1, le_abs_self M2, le_abs_self M3]
  have hc0X : 0 ≤ (c1 + c2 + c3 + 40) * X := by positivity
  rcases Nat.lt_or_ge K 2 with hK | hK
  · -- a single action: the regret is zero
    have hK' : K = 1 := by omega
    have hsub : Subsingleton (Fin K) := by rw [hK']; infer_instance
    have h0 : regretVs P arms T R u = 0 := by
      unfold regretVs
      have : ∀ ω, ∑ t ∈ Finset.range T, (arms (R.A t ω) - arms u) ⬝ᵥ R.θs t ω = 0 := by
        intro ω
        refine Finset.sum_eq_zero fun t _ => ?_
        rw [Subsingleton.elim (R.A t ω) u, sub_self, zero_dotProduct]
      simp only [this, integral_zero]
    rw [h0]
    have : 0 ≤ |M1| + |M2| + |M3| := by positivity
    linarith [hc0X]
  -- `K ≥ 2`: the four-term decomposition (D.167) at center `θ`
  set uvec : Fin K → ℝ := fun a => if a = u then 1 else 0 with huvec
  have hu0 : ∀ a, 0 ≤ uvec a := fun a => by simp only [uvec]; split_ifs <;> norm_num
  have hu1 : ∑ a, uvec a = 1 := by simp [uvec]
  have hD := (lemma_D_18 hd arms hA P T R hR θ jstar uvec hu0 hu1).2.2
  have hreg : regretVs P arms T R u = regretDist P arms T R uvec := by
    unfold regretVs regretDist
    have : ∑ a, uvec a • arms a = arms u := by simp [uvec, ite_smul]
    rw [this]
  rw [hreg]
  refine le_trans hD ?_
  -- the direct corruption term (Lemma D.14)
  obtain ⟨-, hD14⟩ := lemma_D_14 hd arms hA P T R hR θ jstar C hC hcor
  have hcorr : ∑ t ∈ Finset.range T, ∫ ω, ∑ a, (R.p t ω a -
      qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a) * (arms a ⬝ᵥ (R.θs t ω - θ)) ∂P ≤
      16 * Real.sqrt 2 * cR d K * Real.sqrt C := by
    refine le_trans (Finset.sum_le_sum fun t _ => ?_) hD14
    exact (le_abs_self _).trans (abs_integral_le_integral_abs)
  have hcorrJ := P21S.corr_le d K hK C Δ₀ hΔ₀ hΔ₀1
  rw [← hJdef] at hcorrJ
  -- assemble
  have hexpand : (c1 + c2 + c3 + 40) * X = c1 * X + c2 * X + c3 * X + 40 * X := by ring
  have hfinal : c1 * X + M1 + (c2 * X + M2) + (c3 * X + M3) + 40 * J ≤
      (c1 + c2 + c3 + 40) * X + (|M1| + |M2| + |M3|) := by
    rw [hexpand]
    linarith [hJX, hMabs]
  linarith [hpen, hstab, hexpl, hcorr, hcorrJ, hfinal]
