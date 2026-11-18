-- Prove2me | solution 2 for IAFTRL.proposition_G_2
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-17T12:53:23.201244+00:00
-- url     : https://prove2.me/submissions/89faa594-9a2d-457a-a535-3c11a42abee3

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Theorems.Thm_IAFTRL_lemma_G_11
import Theorems.Thm_IAFTRL_lemma_G_2_ftrl

namespace G2S

open MeasureTheory Matrix Set IAFTRL

variable {d : ℕ}

lemma le_setNorm {X : Set (Fin d → ℝ)} (hX : IsCompact X) {a : Fin d → ℝ} (ha : a ∈ X)
    (z : Fin d → ℝ) : |a ⬝ᵥ z| ≤ setNorm X z := by
  have hc : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ z| := by
    simp only [dotProduct]; fun_prop
  exact le_csSup (hX.image hc).bddAbove ⟨a, ha, rfl⟩

lemma convex_absdot (z : Fin d → ℝ) (s : ℝ) : Convex ℝ {x : Fin d → ℝ | |x ⬝ᵥ z| ≤ s} := by
  have hl : IsLinearMap ℝ (fun x : Fin d → ℝ => x ⬝ᵥ z) :=
    ⟨fun x y => add_dotProduct x y z, fun c x => smul_dotProduct c x z⟩
  have : {x : Fin d → ℝ | |x ⬝ᵥ z| ≤ s} = {w | w ⬝ᵥ z ≤ s} ∩ {w | -s ≤ w ⬝ᵥ z} := by
    ext x; simp [abs_le, and_comm]
  rw [this]
  exact (convex_halfSpace_le hl s).inter (convex_halfSpace_ge hl (-s))

/-- losses are bounded by the action seminorm on the convex hull -/
lemma abs_dot_le_hull {𝒜 : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) {z : Fin d → ℝ}
    {x : Fin d → ℝ} (hx : x ∈ convexHull ℝ 𝒜) : |x ⬝ᵥ z| ≤ setNorm 𝒜 z :=
  convexHull_min (fun a ha => le_setNorm h𝒜 ha z) (convex_absdot z _) hx

lemma sum_inv_sqrt (T : ℕ) :
    ∑ t ∈ Finset.range T, 1 / Real.sqrt ((t : ℝ) + 1) ≤ 2 * Real.sqrt T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ]
    have ha := Real.sq_sqrt (show (0 : ℝ) ≤ (T : ℝ) + 1 by positivity)
    have hb := Real.sq_sqrt (show (0 : ℝ) ≤ (T : ℝ) by positivity)
    have hapos : 0 < Real.sqrt ((T : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have hb0 : 0 ≤ Real.sqrt (T : ℝ) := Real.sqrt_nonneg _
    have hkey : 1 / Real.sqrt ((T : ℝ) + 1) ≤
        2 * Real.sqrt ((T : ℝ) + 1) - 2 * Real.sqrt T := by
      rw [div_le_iff₀ hapos]
      nlinarith [sq_nonneg (Real.sqrt ((T : ℝ) + 1) - Real.sqrt T)]
    push_cast
    linarith

end G2S

namespace IAFTRL

open MeasureTheory

theorem _root_.solution {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (he : Function.Surjective e) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℕ) (R : GRun d Ω) (hT : 1 ≤ T) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R)
    (u : Fin d → ℝ) (hu : u ∈ Kset ℬ) :
    gRegretVs P T R u ≤ 320 * ((d : ℝ) + 1) * Real.sqrt T * Real.log (Real.exp 1 * T) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog : Real.log (Real.exp 1 * T) = 1 + Real.log T := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hL1 : 1 ≤ Real.log (Real.exp 1 * T) := by rw [hlog]; linarith
  have hsT : 1 ≤ Real.sqrt T := by rw [Real.one_le_sqrt]; exact hT1
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ T by positivity)
  have hconv : convexHull ℝ 𝒜 = convexHull ℝ ℬ :=
    (convexHull_min hgen.2 (convex_convexHull ℝ ℬ)).antisymm (convexHull_mono hgen.1)
  have hu𝒜 : u ∈ convexHull ℝ 𝒜 := by rw [hconv]; exact hu
  -- the trivial bound `2T`
  have htriv : gRegretVs P T R u ≤ 2 * T := by
    have hb : ∀ ω, ‖∑ t ∈ Finset.range T, (R.A t ω - u) ⬝ᵥ R.θs t ω‖ ≤ 2 * T := by
      intro ω
      refine (norm_sum_le _ _).trans ?_
      calc ∑ t ∈ Finset.range T, ‖(R.A t ω - u) ⬝ᵥ R.θs t ω‖
          ≤ ∑ t ∈ Finset.range T, (2 : ℝ) := by
            refine Finset.sum_le_sum fun t ht => ?_
            obtain ⟨-, -, -, ⟨hA, -⟩, -, hθ⟩ := hR t (Finset.mem_range.1 ht)
            rw [Real.norm_eq_abs, sub_dotProduct]
            have h1 := (G2S.le_setNorm h𝒜 (hgen.1 (hA ω)) (R.θs t ω)).trans (hθ ω)
            have h2 := (G2S.abs_dot_le_hull h𝒜 hu𝒜 (z := R.θs t ω)).trans (hθ ω)
            calc |R.A t ω ⬝ᵥ R.θs t ω - u ⬝ᵥ R.θs t ω|
                ≤ |R.A t ω ⬝ᵥ R.θs t ω| + |u ⬝ᵥ R.θs t ω| := abs_sub _ _
              _ ≤ 2 := by linarith
        _ = 2 * T := by simp [mul_comm]
    have := norm_integral_le_of_norm_le_const (μ := P) (ae_of_all _ hb)
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at this
    exact (le_abs_self _).trans (by simpa [gRegretVs] using this)
  by_cases hsmall : (T : ℝ) < (d : ℝ) ^ 2
  · -- small horizon
    have hsd : Real.sqrt T ≤ d := by
      rw [Real.sqrt_le_left (by positivity)]; exact hsmall.le
    refine htriv.trans ?_
    have h2T : 2 * (T : ℝ) ≤ 2 * d * Real.sqrt T := by nlinarith
    have : 2 * (d : ℝ) * Real.sqrt T ≤ 320 * ((d : ℝ) + 1) * Real.sqrt T *
        Real.log (Real.exp 1 * T) := by
      have h0 : 0 ≤ (d : ℝ) * Real.sqrt T := by positivity
      nlinarith
    linarith
  · -- large horizon
    push Not at hsmall
    have hds : (d : ℝ) ≤ Real.sqrt T := Real.le_sqrt_of_sq_le hsmall
    obtain ⟨q, hqP, hqK, hqμ, hKLi, hKL, hmean⟩ :=
      lemma_G_11 hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk u hu T hT
    have hmain := lemma_G_2_ftrl hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk he P T R hT hR u hu q hqK
      hqμ hKLi (2 / T) hmean
    have hkd : (kdim ℬ : ℝ) ≤ d := by
      have : kdim ℬ ≤ d := by
        have := Submodule.finrank_le (vectorSpan ℝ (Kset ℬ))
        simpa [kdim, Module.finrank_fin_fun] using this
      exact_mod_cast this
    have hβT : gbeta d T ≤ 17 * Real.sqrt T := by simp only [gbeta]; linarith
    have hβ0 : 0 ≤ gbeta d T := by simp only [gbeta]; positivity
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    have hKLb : Real.log 2 + 16 * (kdim ℬ : ℝ) * Real.log T ≤
        (1 + 16 * d) * Real.log (Real.exp 1 * T) := by
      rw [hlog]; nlinarith
    have hKL0 : 0 ≤ Real.log 2 + 16 * (kdim ℬ : ℝ) * Real.log T := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num); positivity
    have hterm1 : gbeta d T * ∫ x, Real.log (q.rnDeriv (refMu ℬ e) x).toReal ∂q ≤
        17 * Real.sqrt T * ((1 + 16 * d) * Real.log (Real.exp 1 * T)) := by
      calc gbeta d T * ∫ x, Real.log (q.rnDeriv (refMu ℬ e) x).toReal ∂q
          ≤ gbeta d T * (Real.log 2 + 16 * (kdim ℬ : ℝ) * Real.log T) :=
            mul_le_mul_of_nonneg_left hKL hβ0
        _ ≤ 17 * Real.sqrt T * ((1 + 16 * d) * Real.log (Real.exp 1 * T)) :=
            mul_le_mul hβT hKLb hKL0 (by positivity)
    have hterm2 : ∑ t ∈ Finset.range T, 10 * (d : ℝ) / gbeta d (t + 1) ≤
        20 * d * Real.sqrt T := by
      calc ∑ t ∈ Finset.range T, 10 * (d : ℝ) / gbeta d (t + 1)
          ≤ ∑ t ∈ Finset.range T, 10 * (d : ℝ) * (1 / Real.sqrt ((t : ℝ) + 1)) := by
            refine Finset.sum_le_sum fun t _ => ?_
            have hs : 0 < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
            rw [mul_one_div]
            refine div_le_div_of_nonneg_left (by positivity) hs ?_
            simp only [gbeta]; push_cast; linarith
        _ = 10 * d * ∑ t ∈ Finset.range T, 1 / Real.sqrt ((t : ℝ) + 1) := by
            rw [Finset.mul_sum]
        _ ≤ 10 * d * (2 * Real.sqrt T) :=
            mul_le_mul_of_nonneg_left (G2S.sum_inv_sqrt T) (by positivity)
        _ = 20 * d * Real.sqrt T := by ring
    have hterm3 : (T : ℝ) * (2 / T) = 2 := by field_simp
    have hfin : 17 * Real.sqrt T * ((1 + 16 * d) * Real.log (Real.exp 1 * T)) +
        20 * d * Real.sqrt T + 2 ≤
        320 * ((d : ℝ) + 1) * Real.sqrt T * Real.log (Real.exp 1 * T) := by
      have hP : 1 ≤ Real.sqrt T * Real.log (Real.exp 1 * T) := by nlinarith
      have h20 : 20 * (d : ℝ) * Real.sqrt T ≤
          20 * d * (Real.sqrt T * Real.log (Real.exp 1 * T)) := by
        have : Real.sqrt T ≤ Real.sqrt T * Real.log (Real.exp 1 * T) := by nlinarith
        nlinarith
      nlinarith
    linarith

end IAFTRL
