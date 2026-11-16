-- Prove2me | solution 1 for IAFTRL.lemma_C_13_good_event
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T11:28:12.257211+00:00
-- url     : https://prove2.me/submissions/46a08d3e-2b84-4802-b7de-eac87f8296b4

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_actionNorm
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsCorrupted
import Definitions.Def_IAFTRL_cR
import Definitions.Def_IAFTRL_gapHat
import Definitions.Def_IAFTRL_Zd
import Definitions.Def_IAFTRL_refArm
import Definitions.Def_IAFTRL_vCoef
import Definitions.Def_IAFTRL_Run_cumEst
import Definitions.Def_IAFTRL_Run_thetaHat
import Theorems.Thm_IAFTRL_lemma_C_30_local_moments


open Matrix IAFTRL MeasureTheory

namespace C13

variable {d K : ℕ}

/-! ### Deterministic facts about gaps and the reference action -/

lemma abs_dot_le (arms : Fin K → Fin d → ℝ) (θ : Fin d → ℝ) (j : Fin K) :
    |arms j ⬝ᵥ θ| ≤ actionNorm arms θ :=
  le_ciSup (f := fun j => |arms j ⬝ᵥ θ|) (Set.finite_range _).bddAbove j

lemma gap_le_two (arms : Fin K → Fin d → ℝ) (θ : Fin d → ℝ) (jstar a : Fin K)
    (hθ : actionNorm arms θ ≤ 1) : (arms a - arms jstar) ⬝ᵥ θ ≤ 2 := by
  rw [sub_dotProduct]
  have h1 := abs_dot_le arms θ a
  have h2 := abs_dot_le arms θ jstar
  have h3 := le_abs_self (arms a ⬝ᵥ θ)
  have h4 := neg_abs_le (arms jstar ⬝ᵥ θ)
  linarith

lemma gap_pos (arms : Fin K → Fin d → ℝ) (θ : Fin d → ℝ) (jstar a : Fin K)
    (hu : IsUniqueMin arms θ jstar) (ha : a ≠ jstar) : 0 < (arms a - arms jstar) ⬝ᵥ θ := by
  have := hu a ha; rw [sub_dotProduct]; linarith

/-- the reference action is `a*` when `a*` is the strict minimizer -/
lemma refArm_eq (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (jstar : Fin K)
    (hmin : ∀ a, a ≠ jstar → arms jstar ⬝ᵥ S < arms a ⬝ᵥ S) : refArm arms S = arms jstar := by
  classical
  unfold refArm
  have hne : (Finset.univ.filter fun j : Fin K => ∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S).Nonempty := by
    refine ⟨jstar, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => ?_⟩⟩
    by_cases hi : i = jstar
    · rw [hi]
    · exact (hmin i hi).le
  rw [dif_pos hne]
  have hmem := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  congr 1
  by_contra hj
  exact absurd (hmem jstar) (not_le.mpr (hmin _ hj))

/-- on separated histories the empirical gap is `min{2, X_a/(t+1)}` (C.151) -/
lemma gapHat_eq (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (jstar : Fin K) (t : ℕ)
    (hsep : ∀ a, a ≠ jstar → 0 < (arms a - arms jstar) ⬝ᵥ S) (a : Fin K) :
    gapHat arms (t + 1) S a = min 2 ((arms a - arms jstar) ⬝ᵥ S / ((t : ℝ) + 1)) := by
  have href : refArm arms S = arms jstar := refArm_eq arms S jstar fun b hb => by
    have := hsep b hb; rw [sub_dotProduct] at this; linarith
  unfold gapHat Zd
  rw [href, sub_dotProduct]
  push_cast
  ring_nf

/-! ### Measurability of the cumulative estimates -/

lemma meas_vCoef (arms : Fin K → Fin d → ℝ) (b : Fin K) :
    Measurable (fun p : Fin K → ℝ => vCoef arms p b) := by
  have hM : Continuous (fun p : Fin K → ℝ => BanditAlgorithm.linearAllocationMatrix arms p) := by
    unfold BanditAlgorithm.linearAllocationMatrix
    exact continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const
  have e : (fun p : Fin K → ℝ => vCoef arms p b) = fun p =>
      (BanditAlgorithm.linearAllocationMatrix arms p).det⁻¹ •
        ((BanditAlgorithm.linearAllocationMatrix arms p).adjugate *ᵥ arms b) := by
    funext p
    unfold vCoef
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec]
  rw [e]
  exact (hM.matrix_det.measurable.inv).smul
    ((hM.matrix_adjugate.matrix_mulVec continuous_const).measurable)

lemma meas_cumEst {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (arms : Fin K → Fin d → ℝ)
    (T : ℕ) (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) (t : ℕ) (ht : t ≤ T) :
    Measurable (fun ω => R.cumEst arms t ω) := by
  have hθ : ∀ s < T, Measurable (fun ω => R.thetaHat arms s ω) := by
    intro s hs
    obtain ⟨⟨hA, hY, -, hGle, hhG, -⟩, ⟨hp, -⟩, -⟩ := hR s hs
    have hp' : Measurable (R.p s) := hp.mono (le_trans hhG hGle) le_rfl
    have h2 : Measurable (fun q : (Fin K → ℝ) × Fin K => vCoef arms q.1 q.2) :=
      measurable_from_prod_countable_left fun b => meas_vCoef arms b
    have hv := h2.comp (hp'.prodMk hA)
    dsimp only [Function.comp_def] at hv
    have h3 := hY.smul hv
    exact h3
  unfold Run.cumEst
  exact Finset.measurable_sum _ fun s hs => hθ s (by have := Finset.mem_range.mp hs; omega)

lemma meas_X {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (arms : Fin K → Fin d → ℝ)
    (T : ℕ) (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) (t : ℕ) (ht : t ≤ T) (v : Fin d → ℝ) :
    Measurable (fun ω => v ⬝ᵥ R.cumEst arms t ω) :=
  (continuous_const.dotProduct continuous_id).measurable.comp (meas_cumEst P arms T R hR t ht)

/-! ### Weighted AM–GM (generalized Hölder in pointwise form) -/

lemma rpow_inv_pow (x : ℝ) (hx : 0 ≤ x) (p : ℕ) (hp : p ≠ 0) : (x ^ ((1 : ℝ) / p)) ^ p = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, one_div_mul_cancel (by exact_mod_cast hp),
    Real.rpow_one]

/-- `x^j y ≤ (j/p) x^p + (1/p) y^p + (p − j − 1)/p`, the pointwise form of Hölder with exponents
`p/j`, `p`, `p/(p − j − 1)` used in (C.116a) -/
lemma amgm (j p : ℕ) (hjp : j + 1 ≤ p) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ j * y ≤ (j / p : ℝ) * x ^ p + (1 / p : ℝ) * y ^ p + (((p : ℝ) - j - 1) / p) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hjp' : (j : ℝ) + 1 ≤ p := by exact_mod_cast hjp
  have hw3 : 0 ≤ ((p : ℝ) - j - 1) / p := div_nonneg (by linarith) hp.le
  have h := Real.geom_mean_le_arith_mean3_weighted (w₁ := (j / p : ℝ)) (w₂ := (1 / p : ℝ))
    (w₃ := ((p : ℝ) - j - 1) / p) (p₁ := x ^ p) (p₂ := y ^ p) (p₃ := 1) (by positivity)
    (by positivity) hw3 (by positivity) (by positivity) zero_le_one (by field_simp; ring)
  have hq1 : (p : ℝ) * (j / p) = j := by field_simp
  have hq2 : (p : ℝ) * (1 / p) = 1 := by field_simp
  have e1 : (x ^ p) ^ (j / p : ℝ) = x ^ j := by
    rw [← Real.rpow_natCast x p, ← Real.rpow_mul hx, hq1, Real.rpow_natCast]
  have e2 : (y ^ p) ^ (1 / p : ℝ) = y := by
    rw [← Real.rpow_natCast y p, ← Real.rpow_mul hy, hq2, Real.rpow_one]
  rw [e1, e2, Real.one_rpow, mul_one, mul_one] at h
  exact h

lemma pow8_le (x : ℝ) (hx : 0 ≤ x) (p : ℕ) (hp : 8 ≤ p) : x ^ 8 ≤ 1 + x ^ p := by
  rcases le_or_gt x 1 with h | h
  · have : x ^ 8 ≤ 1 := pow_le_one₀ hx h
    have : 0 ≤ x ^ p := pow_nonneg hx p
    linarith
  · have : x ^ 8 ≤ x ^ p := pow_le_pow_right₀ h.le hp
    linarith

/-- `1 + K 8^p ≤ 17^p` and `K 8^p ≤ 16^p` when `K ≤ 2^p` -/
lemma count_bound (K p : ℕ) (hp : 1 ≤ p) (hK : (K : ℝ) ≤ 2 ^ p) (c : ℝ) (hc : 0 ≤ c) :
    (K : ℝ) * (8 * c) ^ p ≤ (16 * c) ^ p := by
  calc (K : ℝ) * (8 * c) ^ p ≤ 2 ^ p * (8 * c) ^ p :=
        mul_le_mul_of_nonneg_right hK (by positivity)
    _ = (16 * c) ^ p := by rw [← mul_pow]; ring_nf

lemma one_add_16 (p : ℕ) (hp : 1 ≤ p) : 1 + (16 : ℝ) ^ p ≤ 17 ^ p := by
  have h : (16 : ℕ) ^ p < 17 ^ p := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have h' : 1 + (16 : ℕ) ^ p ≤ 17 ^ p := by omega
  exact_mod_cast h'

end C13

namespace C13

lemma harm (T : ℕ) : ∑ t ∈ Finset.range T, 1 / ((t : ℝ) + 1) ≤ 1 + Real.log T := by
  have h := harmonic_le_one_add_log T
  have e : ((harmonic T : ℚ) : ℝ) = ∑ t ∈ Finset.range T, 1 / ((t : ℝ) + 1) := by
    simp [harmonic, one_div]
  rw [← e]
  exact h

end C13

namespace C13

/-- (C.114)–(C.116): the mixed ratio moment `E[1_G L^j U] ≤ 17^j · 16Ψ` from per-action moments,
with `L = (1 + Σ r_a^p)^{1/p} ≥ max{1, max r_a}` and `U = (Σ s_a^p)^{1/p} ≥ max s_a` -/
lemma moment_j {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {K : ℕ} (S : Finset (Fin K)) (hS : (S.card : ℝ) ≤ K) (p : ℕ) (hp8 : 8 ≤ p)
    (hKp : (K : ℝ) ≤ 2 ^ p) (G : Set Ω) (hG : MeasurableSet G) (r s : Fin K → Ω → ℝ)
    (hr : ∀ a, Measurable (r a)) (hs : ∀ a, Measurable (s a))
    (hr0 : ∀ ω ∈ G, ∀ a ∈ S, 0 ≤ r a ω) (hs0 : ∀ ω ∈ G, ∀ a ∈ S, 0 ≤ s a ω)
    (hri : ∀ a ∈ S, Integrable (G.indicator fun ω => r a ω ^ p) P ∧
      ∫ ω, G.indicator (fun ω => r a ω ^ p) ω ∂P ≤ 8 ^ p)
    (Ψ : ℝ) (hΨ : 1 ≤ Ψ)
    (hsi : ∀ a ∈ S, Integrable (G.indicator fun ω => s a ω ^ p) P ∧
      ∫ ω, G.indicator (fun ω => s a ω ^ p) ω ∂P ≤ (8 * Ψ) ^ p)
    (j : ℕ) (hj : j + 1 ≤ p) :
    Integrable (G.indicator fun ω => ((1 + ∑ a ∈ S, r a ω ^ p) ^ ((1 : ℝ) / p)) ^ j *
        (∑ a ∈ S, s a ω ^ p) ^ ((1 : ℝ) / p)) P ∧
      ∫ ω, G.indicator (fun ω => ((1 + ∑ a ∈ S, r a ω ^ p) ^ ((1 : ℝ) / p)) ^ j *
        (∑ a ∈ S, s a ω ^ p) ^ ((1 : ℝ) / p)) ω ∂P ≤ 17 ^ j * (16 * Ψ) := by
  classical
  have hp0 : p ≠ 0 := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hjR : (j : ℝ) + 1 ≤ p := by exact_mod_cast hj
  have hΨ0 : 0 ≤ Ψ := by linarith
  set A : ℝ := 17 with hAdef
  set B : ℝ := 16 * Ψ with hBdef
  have hA : 0 < A := by norm_num [A]
  have hB : 0 < B := by simp only [B]; linarith
  have hD1 : Integrable (G.indicator fun _ => (1 : ℝ)) P := (integrable_const (1 : ℝ)).indicator hG
  have hRi : Integrable (fun ω => ∑ a ∈ S, G.indicator (fun ω => r a ω ^ p) ω) P :=
    integrable_finsetSum S fun a ha => (hri a ha).1
  have hEi : Integrable (fun ω => ∑ a ∈ S, G.indicator (fun ω => s a ω ^ p) ω) P :=
    integrable_finsetSum S fun a ha => (hsi a ha).1
  have hDi : Integrable (fun ω => G.indicator (fun _ => (1 : ℝ)) ω +
      ∑ a ∈ S, G.indicator (fun ω => r a ω ^ p) ω) P := hD1.add hRi
  have hPG : P.real G ≤ 1 := measureReal_le_one
  have hPG0 : 0 ≤ P.real G := measureReal_nonneg
  have hDint : ∫ ω, (G.indicator (fun _ => (1 : ℝ)) ω +
      ∑ a ∈ S, G.indicator (fun ω => r a ω ^ p) ω) ∂P ≤ A ^ p := by
    rw [integral_add hD1 hRi, integral_finsetSum S fun a ha => (hri a ha).1,
      integral_indicator_const _ hG, smul_eq_mul, mul_one]
    have h2 : ∑ a ∈ S, ∫ ω, G.indicator (fun ω => r a ω ^ p) ω ∂P ≤ ∑ _a ∈ S, (8 : ℝ) ^ p :=
      Finset.sum_le_sum fun a ha => (hri a ha).2
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have h3 := count_bound K p (by omega) hKp 1 zero_le_one
    have h4 : (S.card : ℝ) * 8 ^ p ≤ K * 8 ^ p := mul_le_mul_of_nonneg_right hS (by positivity)
    have h5 := one_add_16 p (by omega)
    simp only [mul_one] at h3
    simp only [A]
    linarith
  have hEint : ∫ ω, (∑ a ∈ S, G.indicator (fun ω => s a ω ^ p) ω) ∂P ≤ B ^ p := by
    rw [integral_finsetSum S fun a ha => (hsi a ha).1]
    have h2 : ∑ a ∈ S, ∫ ω, G.indicator (fun ω => s a ω ^ p) ω ∂P ≤ ∑ _a ∈ S, (8 * Ψ) ^ p :=
      Finset.sum_le_sum fun a ha => (hsi a ha).2
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have h3 := count_bound K p (by omega) hKp Ψ hΨ0
    have h4 : (S.card : ℝ) * (8 * Ψ) ^ p ≤ K * (8 * Ψ) ^ p :=
      mul_le_mul_of_nonneg_right hS (pow_nonneg (by linarith) p)
    simp only [B]
    linarith
  set c1 : ℝ := A ^ j * B * ((j / p : ℝ) / A ^ p) with hc1
  set c2 : ℝ := A ^ j * B * ((1 / p : ℝ) / B ^ p) with hc2
  set c3 : ℝ := A ^ j * B * (((p : ℝ) - j - 1) / p) with hc3
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  have hc30 : 0 ≤ c3 := by
    have : 0 ≤ ((p : ℝ) - j - 1) / p := div_nonneg (by linarith) hpR.le
    positivity
  have hmeas : Measurable (fun ω => ((1 + ∑ a ∈ S, r a ω ^ p) ^ ((1 : ℝ) / p)) ^ j *
      (∑ a ∈ S, s a ω ^ p) ^ ((1 : ℝ) / p)) :=
    (((measurable_const.add (Finset.measurable_sum S fun a _ => (hr a).pow_const p)).pow_const
      _).pow_const j).mul ((Finset.measurable_sum S fun a _ => (hs a).pow_const p).pow_const _)
  have hnn : ∀ ω, 0 ≤ G.indicator (fun ω => ((1 + ∑ a ∈ S, r a ω ^ p) ^ ((1 : ℝ) / p)) ^ j *
      (∑ a ∈ S, s a ω ^ p) ^ ((1 : ℝ) / p)) ω := by
    intro ω
    apply Set.indicator_nonneg
    intro ω hω
    have h1 : 0 ≤ 1 + ∑ a ∈ S, r a ω ^ p := by
      have := Finset.sum_nonneg fun a ha => pow_nonneg (hr0 ω hω a ha) p
      linarith
    have h2 : 0 ≤ ∑ a ∈ S, s a ω ^ p := Finset.sum_nonneg fun a ha => pow_nonneg (hs0 ω hω a ha) p
    exact mul_nonneg (pow_nonneg (Real.rpow_nonneg h1 _) j) (Real.rpow_nonneg h2 _)
  have hpt : ∀ ω, G.indicator (fun ω => ((1 + ∑ a ∈ S, r a ω ^ p) ^ ((1 : ℝ) / p)) ^ j *
      (∑ a ∈ S, s a ω ^ p) ^ ((1 : ℝ) / p)) ω ≤
      c1 * (G.indicator (fun _ => (1 : ℝ)) ω + ∑ a ∈ S, G.indicator (fun ω => r a ω ^ p) ω) +
        c2 * (∑ a ∈ S, G.indicator (fun ω => s a ω ^ p) ω) +
        c3 * G.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [Set.indicator_of_mem hω]
      set Dv := 1 + ∑ a ∈ S, r a ω ^ p with hDv
      set Ev := ∑ a ∈ S, s a ω ^ p with hEv
      have hDv0 : 0 ≤ Dv := by
        have := Finset.sum_nonneg fun a ha => pow_nonneg (hr0 ω hω a ha) p
        simp only [Dv]; linarith
      have hEv0 : 0 ≤ Ev := Finset.sum_nonneg fun a ha => pow_nonneg (hs0 ω hω a ha) p
      set x := Dv ^ ((1 : ℝ) / p) / A with hx
      set y := Ev ^ ((1 : ℝ) / p) / B with hy
      have hx0 : 0 ≤ x := div_nonneg (Real.rpow_nonneg hDv0 _) hA.le
      have hy0 : 0 ≤ y := div_nonneg (Real.rpow_nonneg hEv0 _) hB.le
      have h := amgm j p hj x y hx0 hy0
      have hxp : x ^ p = Dv / A ^ p := by rw [hx, div_pow, rpow_inv_pow Dv hDv0 p hp0]
      have hyp : y ^ p = Ev / B ^ p := by rw [hy, div_pow, rpow_inv_pow Ev hEv0 p hp0]
      have e : (Dv ^ ((1 : ℝ) / p)) ^ j * Ev ^ ((1 : ℝ) / p) = A ^ j * B * (x ^ j * y) := by
        rw [hx, hy, div_pow]; field_simp
      rw [e]
      calc A ^ j * B * (x ^ j * y) ≤ A ^ j * B * ((j / p : ℝ) * x ^ p + (1 / p : ℝ) * y ^ p +
            (((p : ℝ) - j - 1) / p)) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = c1 * Dv + c2 * Ev + c3 * 1 := by
            rw [hxp, hyp, hc1, hc2, hc3]; field_simp
    · simp only [Set.indicator_of_notMem hω, Finset.sum_const_zero]
      simp
  have hbound : Integrable (fun ω =>
      c1 * (G.indicator (fun _ => (1 : ℝ)) ω + ∑ a ∈ S, G.indicator (fun ω => r a ω ^ p) ω) +
        c2 * (∑ a ∈ S, G.indicator (fun ω => s a ω ^ p) ω) +
        c3 * G.indicator (fun _ => (1 : ℝ)) ω) P :=
    ((hDi.const_mul c1).add (hEi.const_mul c2)).add (hD1.const_mul c3)
  have hint : Integrable (G.indicator fun ω => ((1 + ∑ a ∈ S, r a ω ^ p) ^ ((1 : ℝ) / p)) ^ j *
      (∑ a ∈ S, s a ω ^ p) ^ ((1 : ℝ) / p)) P := by
    refine hbound.mono' (hmeas.indicator hG).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn ω)]
    exact hpt ω
  refine ⟨hint, ?_⟩
  have hle := integral_mono hint hbound hpt
  have hcalc : ∫ ω, (c1 * (G.indicator (fun _ => (1 : ℝ)) ω +
      ∑ a ∈ S, G.indicator (fun ω => r a ω ^ p) ω) +
        c2 * (∑ a ∈ S, G.indicator (fun ω => s a ω ^ p) ω) +
        c3 * G.indicator (fun _ => (1 : ℝ)) ω) ∂P =
      c1 * ∫ ω, (G.indicator (fun _ => (1 : ℝ)) ω +
        ∑ a ∈ S, G.indicator (fun ω => r a ω ^ p) ω) ∂P +
        c2 * ∫ ω, (∑ a ∈ S, G.indicator (fun ω => s a ω ^ p) ω) ∂P + c3 * P.real G := by
    have j1 : Integrable (fun ω => c1 * (G.indicator (fun _ => (1 : ℝ)) ω +
        ∑ a ∈ S, G.indicator (fun ω => r a ω ^ p) ω)) P := hDi.const_mul c1
    have j2 : Integrable (fun ω => c2 * (∑ a ∈ S, G.indicator (fun ω => s a ω ^ p) ω)) P :=
      hEi.const_mul c2
    have j3 : Integrable (fun ω => c3 * G.indicator (fun _ => (1 : ℝ)) ω) P := hD1.const_mul c3
    have j12 : Integrable (fun ω => c1 * (G.indicator (fun _ => (1 : ℝ)) ω +
        ∑ a ∈ S, G.indicator (fun ω => r a ω ^ p) ω) +
        c2 * (∑ a ∈ S, G.indicator (fun ω => s a ω ^ p) ω)) P := j1.add j2
    rw [integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_indicator_const _ hG, smul_eq_mul, mul_one]
  rw [hcalc] at hle
  have k1 : c1 * ∫ ω, (G.indicator (fun _ => (1 : ℝ)) ω +
      ∑ a ∈ S, G.indicator (fun ω => r a ω ^ p) ω) ∂P ≤ c1 * A ^ p :=
    mul_le_mul_of_nonneg_left hDint hc10
  have k2 : c2 * ∫ ω, (∑ a ∈ S, G.indicator (fun ω => s a ω ^ p) ω) ∂P ≤ c2 * B ^ p :=
    mul_le_mul_of_nonneg_left hEint hc20
  have k3 : c3 * P.real G ≤ c3 := by nlinarith
  have k4 : c1 * A ^ p + c2 * B ^ p + c3 = A ^ j * B := by
    rw [hc1, hc2, hc3]; field_simp; ring
  have k5 : A ^ j * B = 17 ^ j * (16 * Ψ) := by simp only [A, B]
  linarith

/-- `E[1_G L^8] ≤ 2 · 17^8` -/
lemma moment_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {K : ℕ} (S : Finset (Fin K)) (hS : (S.card : ℝ) ≤ K) (p : ℕ) (hp8 : 8 ≤ p)
    (hKp : (K : ℝ) ≤ 2 ^ p) (G : Set Ω) (hG : MeasurableSet G) (r : Fin K → Ω → ℝ)
    (hr : ∀ a, Measurable (r a)) (hr0 : ∀ ω ∈ G, ∀ a ∈ S, 0 ≤ r a ω)
    (hri : ∀ a ∈ S, Integrable (G.indicator fun ω => r a ω ^ p) P ∧
      ∫ ω, G.indicator (fun ω => r a ω ^ p) ω ∂P ≤ 8 ^ p) :
    Integrable (G.indicator fun ω => ((1 + ∑ a ∈ S, r a ω ^ p) ^ ((1 : ℝ) / p)) ^ 8) P ∧
      ∫ ω, G.indicator (fun ω => ((1 + ∑ a ∈ S, r a ω ^ p) ^ ((1 : ℝ) / p)) ^ 8) ω ∂P ≤
        2 * 17 ^ 8 := by
  classical
  have hp0 : p ≠ 0 := by omega
  set A : ℝ := 17 with hAdef
  have hA : 0 < A := by norm_num [A]
  have hD1 : Integrable (G.indicator fun _ => (1 : ℝ)) P := (integrable_const (1 : ℝ)).indicator hG
  have hRi : Integrable (fun ω => ∑ a ∈ S, G.indicator (fun ω => r a ω ^ p) ω) P :=
    integrable_finsetSum S fun a ha => (hri a ha).1
  have hDi : Integrable (fun ω => G.indicator (fun _ => (1 : ℝ)) ω +
      ∑ a ∈ S, G.indicator (fun ω => r a ω ^ p) ω) P := hD1.add hRi
  have hPG : P.real G ≤ 1 := measureReal_le_one
  have hDint : ∫ ω, (G.indicator (fun _ => (1 : ℝ)) ω +
      ∑ a ∈ S, G.indicator (fun ω => r a ω ^ p) ω) ∂P ≤ A ^ p := by
    rw [integral_add hD1 hRi, integral_finsetSum S fun a ha => (hri a ha).1,
      integral_indicator_const _ hG, smul_eq_mul, mul_one]
    have h2 : ∑ a ∈ S, ∫ ω, G.indicator (fun ω => r a ω ^ p) ω ∂P ≤ ∑ _a ∈ S, (8 : ℝ) ^ p :=
      Finset.sum_le_sum fun a ha => (hri a ha).2
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have h3 := count_bound K p (by omega) hKp 1 zero_le_one
    have h4 : (S.card : ℝ) * 8 ^ p ≤ K * 8 ^ p := mul_le_mul_of_nonneg_right hS (by positivity)
    have h5 := one_add_16 p (by omega)
    simp only [mul_one] at h3
    simp only [A]
    linarith
  set c1 : ℝ := A ^ 8 / A ^ p with hc1
  have hc10 : 0 ≤ c1 := by positivity
  have hmeas : Measurable (fun ω => ((1 + ∑ a ∈ S, r a ω ^ p) ^ ((1 : ℝ) / p)) ^ 8) :=
    ((measurable_const.add (Finset.measurable_sum S fun a _ => (hr a).pow_const p)).pow_const
      _).pow_const 8
  have hnn : ∀ ω, 0 ≤ G.indicator
      (fun ω => ((1 + ∑ a ∈ S, r a ω ^ p) ^ ((1 : ℝ) / p)) ^ 8) ω :=
    fun ω => Set.indicator_nonneg (fun ω _ => by positivity) ω
  have hpt : ∀ ω, G.indicator (fun ω => ((1 + ∑ a ∈ S, r a ω ^ p) ^ ((1 : ℝ) / p)) ^ 8) ω ≤
      c1 * (G.indicator (fun _ => (1 : ℝ)) ω + ∑ a ∈ S, G.indicator (fun ω => r a ω ^ p) ω) +
        A ^ 8 * G.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [Set.indicator_of_mem hω]
      set Dv := 1 + ∑ a ∈ S, r a ω ^ p with hDv
      have hDv0 : 0 ≤ Dv := by
        have := Finset.sum_nonneg fun a ha => pow_nonneg (hr0 ω hω a ha) p
        simp only [Dv]; linarith
      set x := Dv ^ ((1 : ℝ) / p) / A with hx
      have hx0 : 0 ≤ x := div_nonneg (Real.rpow_nonneg hDv0 _) hA.le
      have h := pow8_le x hx0 p hp8
      have hxp : x ^ p = Dv / A ^ p := by rw [hx, div_pow, rpow_inv_pow Dv hDv0 p hp0]
      have e : (Dv ^ ((1 : ℝ) / p)) ^ 8 = A ^ 8 * x ^ 8 := by
        rw [hx, div_pow]; field_simp
      rw [e]
      calc A ^ 8 * x ^ 8 ≤ A ^ 8 * (1 + x ^ p) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = c1 * Dv + A ^ 8 * 1 := by rw [hxp, hc1]; field_simp; ring
    · simp only [Set.indicator_of_notMem hω, Finset.sum_const_zero]
      simp
  have hbound : Integrable (fun ω =>
      c1 * (G.indicator (fun _ => (1 : ℝ)) ω + ∑ a ∈ S, G.indicator (fun ω => r a ω ^ p) ω) +
        A ^ 8 * G.indicator (fun _ => (1 : ℝ)) ω) P :=
    (hDi.const_mul c1).add (hD1.const_mul _)
  have hint : Integrable
      (G.indicator fun ω => ((1 + ∑ a ∈ S, r a ω ^ p) ^ ((1 : ℝ) / p)) ^ 8) P := by
    refine hbound.mono' (hmeas.indicator hG).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn ω)]
    exact hpt ω
  refine ⟨hint, ?_⟩
  have hle := integral_mono hint hbound hpt
  have j1 : Integrable (fun ω => c1 * (G.indicator (fun _ => (1 : ℝ)) ω +
      ∑ a ∈ S, G.indicator (fun ω => r a ω ^ p) ω)) P := hDi.const_mul c1
  have j3 : Integrable (fun ω => A ^ 8 * G.indicator (fun _ => (1 : ℝ)) ω) P := hD1.const_mul _
  rw [integral_add j1 j3, integral_const_mul, integral_const_mul, integral_indicator_const _ hG,
    smul_eq_mul, mul_one] at hle
  have k1 := mul_le_mul_of_nonneg_left hDint hc10
  have k2 : c1 * A ^ p = A ^ 8 := by rw [hc1]; field_simp
  have k3 : A ^ 8 * P.real G ≤ A ^ 8 := by
    have : 0 ≤ A ^ 8 := by positivity
    nlinarith
  have k5 : A ^ 8 = 17 ^ 8 := by simp only [A]
  linarith

end C13

open Matrix IAFTRL MeasureTheory

theorem solution : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d K : ℕ}, 1 ≤ d → ∀ (arms : Fin K → Fin d → ℝ), IsActionSet arms →
      ∀ (θ : Fin d → ℝ) (jstar : Fin K) (Δ₀ : ℝ),
        actionNorm arms θ ≤ 1 → IsUniqueMin arms θ jstar → 0 < Δ₀ → Δ₀ ≤ 1 →
        (∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) →
        ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : Run d K Ω), 1 ≤ T → 0 ≤ C →
          IsIAFTRLRun P arms T R → IsCorrupted P arms θ C T R →
          ∃ (G : ℕ → Set Ω) (L U : ℕ → Ω → ℝ), (∀ t, MeasurableSet (G t)) ∧
            (∀ t < T, ∀ ω ∈ G t, ∀ a, a ≠ jstar →
              4 * (t + 1 : ℝ) ^ ((3 : ℝ) / 4) ≤ (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω) ∧
            cR d K * ∑ t ∈ Finset.range T, (P (G t)ᶜ).toReal / Real.sqrt (t + 1) ≤
              c₀ * (Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) +
                M ∧
            (∀ t < T, ∀ ω ∈ G t, 1 ≤ L t ω ∧ 0 ≤ U t ω ∧
              (∀ a, a ≠ jstar → (t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) ≤
                L t ω * ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)) ∧
              ∀ a, (arms a - arms jstar) ⬝ᵥ θ ≤
                  L t ω * gapHat arms (t + 1) (R.cumEst arms t ω) a ∧
                gapHat arms (t + 1) (R.cumEst arms t ω) a ≤
                  U t ω * ((arms a - arms jstar) ⬝ᵥ θ)) ∧
            (∀ t < T, Integrable ((G t).indicator fun ω => L t ω ^ 8) P ∧
              ∫ ω, (G t).indicator (fun ω => L t ω ^ 8) ω ∂P ≤ c₀) ∧
            (∀ t < T, Integrable ((G t).indicator fun ω => L t ω * U t ω) P ∧
              ∫ ω, (G t).indicator (fun ω => L t ω * U t ω) ω ∂P ≤ M) ∧
            (∀ t < T, Integrable ((G t).indicator fun ω => L t ω ^ 3 * U t ω) P) ∧
            ∑ t ∈ Finset.range T,
                (∫ ω, (G t).indicator (fun ω => L t ω ^ 3 * U t ω) ω ∂P) / (t + 1) ≤
              c₀ * (1 + Real.log T) + M := by
  classical
  obtain ⟨c₁, hc₁, hG⟩ := lemma_C_30_local_moments
  refine ⟨c₁ + 2 * 17 ^ 8 + 17 ^ 3 * 16, by positivity, ?_⟩
  intro d K hd arms hA θ jstar Δ₀ hθ hu hΔ₀ hΔ₀1 hgap
  obtain ⟨M₁, hM₁⟩ := hG hd arms hA θ jstar Δ₀ hθ hu hΔ₀ hΔ₀1 hgap
  refine ⟨80000 * |M₁|, ?_⟩
  intro Ω _ P _ T C R hT hC hR hcor
  obtain ⟨G, p, Ψ, hGm, hp8, hKp, hsep, hfail, hinv, hpos, hΨ, hΨsum⟩ :=
    hM₁ P T C R hT hC hR hcor
  have hp0 : p ≠ 0 := by omega
  set S : Finset (Fin K) := Finset.univ.erase jstar with hSdef
  have hScard : (S.card : ℝ) ≤ K := by
    have : S.card ≤ K := by
      rw [hSdef, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    exact_mod_cast this
  have hM₁abs : M₁ ≤ |M₁| := le_abs_self M₁
  have hM₁0 : 0 ≤ |M₁| := abs_nonneg M₁
  have hrs : ∀ t < T,
      (∀ a, Measurable (fun ω => (t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) /
        ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω))) ∧
      (∀ a, Measurable (fun ω => (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω /
        ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ)))) ∧
      (∀ ω ∈ G t, ∀ a ∈ S, 0 ≤ (t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) /
        ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)) ∧
      (∀ ω ∈ G t, ∀ a ∈ S, 0 ≤ (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω /
        ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ))) := by
    intro t ht
    have ht1 : (0 : ℝ) < t + 1 := by positivity
    have hpos' : ∀ ω ∈ G t, ∀ a, a ≠ jstar → 0 < (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω := by
      intro ω hω a ha
      have h1 := hsep t ht ω hω a ha
      have h2 : 0 < 4 * (t + 1 : ℝ) ^ ((3 : ℝ) / 4) := by positivity
      linarith
    refine ⟨fun a => measurable_const.div (C13.meas_X P arms T R hR t ht.le _),
      fun a => (C13.meas_X P arms T R hR t ht.le _).div_const _, fun ω hω a ha => ?_,
      fun ω hω a ha => ?_⟩
    · exact div_nonneg (mul_nonneg ht1.le
        (C13.gap_pos arms θ jstar a hu (Finset.ne_of_mem_erase ha)).le)
        (hpos' ω hω a (Finset.ne_of_mem_erase ha)).le
    · exact div_nonneg (hpos' ω hω a (Finset.ne_of_mem_erase ha)).le
        (mul_nonneg ht1.le (C13.gap_pos arms θ jstar a hu (Finset.ne_of_mem_erase ha)).le)
  have hmj : ∀ t < T, ∀ j, j + 1 ≤ p →
      Integrable ((G t).indicator fun ω => ((1 + ∑ a ∈ S, ((t + 1 : ℝ) *
        ((arms a - arms jstar) ⬝ᵥ θ) / ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)) ^ p) ^
        ((1 : ℝ) / p)) ^ j * (∑ a ∈ S, ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω /
        ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ))) ^ p) ^ ((1 : ℝ) / p)) P ∧
      ∫ ω, (G t).indicator (fun ω => ((1 + ∑ a ∈ S, ((t + 1 : ℝ) *
        ((arms a - arms jstar) ⬝ᵥ θ) / ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)) ^ p) ^
        ((1 : ℝ) / p)) ^ j * (∑ a ∈ S, ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω /
        ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ))) ^ p) ^ ((1 : ℝ) / p)) ω ∂P ≤
        17 ^ j * (16 * Ψ t) := by
    intro t ht j hj
    obtain ⟨hr, hs, hr0, hs0⟩ := hrs t ht
    exact C13.moment_j P S hScard p hp8 hKp (G t) (hGm t) _ _ hr hs hr0 hs0
      (fun a ha => hinv t ht a (Finset.ne_of_mem_erase ha)) (Ψ t) (hΨ t ht).1
      (fun a ha => hpos t ht a (Finset.ne_of_mem_erase ha)) j hj
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by exact_mod_cast hT)
  -- the ratios of Definition C.12
  refine ⟨G,
    fun t ω => (1 + ∑ a ∈ S, ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) /
      ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)) ^ p) ^ ((1 : ℝ) / p),
    fun t ω => (∑ a ∈ S, ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω /
      ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ))) ^ p) ^ ((1 : ℝ) / p),
    hGm, hsep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the failure sum is unchanged
    have hX0 : 0 ≤ Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hΔ₀.le _)) (Real.sqrt_nonneg _)
    have := mul_le_mul_of_nonneg_right
      (show c₁ ≤ c₁ + 2 * 17 ^ 8 + 17 ^ 3 * 16 by linarith [show (0 : ℝ) ≤ 2 * 17 ^ 8 + 17 ^ 3 * 16 by norm_num]) hX0
    linarith
  · -- pathwise comparisons (C.117)
    intro t ht ω hω
    have hpos' : ∀ a, a ≠ jstar → 0 < (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω := by
      intro a ha
      have h1 := hsep t ht ω hω a ha
      have h2 : 0 < 4 * (t + 1 : ℝ) ^ ((3 : ℝ) / 4) := by positivity
      linarith
    have ht1 : (0 : ℝ) < t + 1 := by positivity
    have hr0 : ∀ a ∈ S, 0 ≤ (t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) /
        ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω) := fun a ha =>
      div_nonneg (mul_nonneg ht1.le (C13.gap_pos arms θ jstar a hu (Finset.ne_of_mem_erase ha)).le)
        (hpos' a (Finset.ne_of_mem_erase ha)).le
    have hs0 : ∀ a ∈ S, 0 ≤ (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω /
        ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ)) := fun a ha =>
      div_nonneg (hpos' a (Finset.ne_of_mem_erase ha)).le
        (mul_nonneg ht1.le (C13.gap_pos arms θ jstar a hu (Finset.ne_of_mem_erase ha)).le)
    set Lb := 1 + ∑ a ∈ S, ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) /
      ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)) ^ p with hLb
    set Ub := ∑ a ∈ S, ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω /
      ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ))) ^ p with hUb
    have hsumr : 0 ≤ ∑ a ∈ S, ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) /
        ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)) ^ p :=
      Finset.sum_nonneg fun a ha => pow_nonneg (hr0 a ha) p
    have hLb1 : 1 ≤ Lb := by simp only [Lb]; linarith
    have hUb0 : 0 ≤ Ub := Finset.sum_nonneg fun a ha => pow_nonneg (hs0 a ha) p
    have hL1 : 1 ≤ Lb ^ ((1 : ℝ) / p) := Real.one_le_rpow hLb1 (by positivity)
    have hL0 : 0 ≤ Lb ^ ((1 : ℝ) / p) := by linarith
    have hU0 : 0 ≤ Ub ^ ((1 : ℝ) / p) := Real.rpow_nonneg hUb0 _
    have hrL : ∀ a, a ≠ jstar → (t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) /
        ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω) ≤ Lb ^ ((1 : ℝ) / p) := by
      intro a ha
      have haS : a ∈ S := Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩
      apply le_of_pow_le_pow_left₀ hp0 hL0
      rw [C13.rpow_inv_pow Lb (by linarith) p hp0]
      have := Finset.single_le_sum (f := fun a => ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) /
        ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)) ^ p)
        (fun b hb => pow_nonneg (hr0 b hb) p) haS
      simp only [Lb]; linarith
    have hsU : ∀ a, a ≠ jstar → (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω /
        ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ)) ≤ Ub ^ ((1 : ℝ) / p) := by
      intro a ha
      have haS : a ∈ S := Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩
      apply le_of_pow_le_pow_left₀ hp0 hU0
      rw [C13.rpow_inv_pow Ub hUb0 p hp0]
      exact Finset.single_le_sum (f := fun a => ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω /
        ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ))) ^ p)
        (fun b hb => pow_nonneg (hs0 b hb) p) haS
    have hLX : ∀ a, a ≠ jstar → (t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) ≤
        Lb ^ ((1 : ℝ) / p) * ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω) := by
      intro a ha
      have := hrL a ha
      rwa [div_le_iff₀ (hpos' a ha)] at this
    refine ⟨hL1, hU0, hLX, fun a => ?_⟩
    rw [C13.gapHat_eq arms (R.cumEst arms t ω) jstar t hpos' a]
    by_cases ha : a = jstar
    · subst ha
      simp
    · have hΔ := C13.gap_pos arms θ jstar a hu ha
      have hΔ2 := C13.gap_le_two arms θ jstar a hθ
      have hX := hpos' a ha
      constructor
      · rw [mul_min_of_nonneg _ _ hL0]
        refine le_min (by linarith) ?_
        have := hLX a ha
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        linarith
      · have h1 : min 2 ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω / ((t : ℝ) + 1)) ≤
            (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω / ((t : ℝ) + 1) := min_le_right _ _
        have h2 := mul_le_mul_of_nonneg_right (hsU a ha) hΔ.le
        have e : (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω /
            ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ)) * ((arms a - arms jstar) ⬝ᵥ θ) =
            (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω / ((t : ℝ) + 1) := by
          field_simp
        linarith
  -- moment bounds (C.112), via `C13.moment_j` and `C13.moment_8`
  · intro t ht
    obtain ⟨hr, -, hr0, -⟩ := hrs t ht
    have hm := C13.moment_8 P S hScard p hp8 hKp (G t) (hGm t) _ hr hr0
      (fun a ha => hinv t ht a (Finset.ne_of_mem_erase ha))
    refine ⟨hm.1, hm.2.trans ?_⟩
    linarith [show (0 : ℝ) ≤ 17 ^ 3 * 16 by norm_num]
  · intro t ht
    have hm := hmj t ht 1 (by omega)
    simp only [pow_one] at hm
    refine ⟨hm.1, hm.2.trans ?_⟩
    have h1 := (hΨ t ht).2
    nlinarith
  · intro t ht
    exact (hmj t ht 3 (by omega)).1
  · have hterm : ∀ t ∈ Finset.range T, (∫ ω, (G t).indicator (fun ω => ((1 + ∑ a ∈ S,
        ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ) /
          ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω)) ^ p) ^ ((1 : ℝ) / p)) ^ 3 *
        (∑ a ∈ S, ((arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω /
          ((t + 1 : ℝ) * ((arms a - arms jstar) ⬝ᵥ θ))) ^ p) ^ ((1 : ℝ) / p)) ω ∂P) / (t + 1) ≤
        17 ^ 3 * 16 * (1 / ((t : ℝ) + 1)) + 17 ^ 3 * 16 * ((Ψ t - 1) / ((t : ℝ) + 1)) := by
      intro t htT
      have ht := Finset.mem_range.mp htT
      have hm := (hmj t ht 3 (by omega)).2
      have ht1 : (0 : ℝ) < t + 1 := by positivity
      have e : 17 ^ 3 * 16 * (1 / ((t : ℝ) + 1)) + 17 ^ 3 * 16 * ((Ψ t - 1) / ((t : ℝ) + 1)) =
          17 ^ 3 * (16 * Ψ t) / ((t : ℝ) + 1) := by field_simp; ring
      rw [e]
      exact div_le_div_of_nonneg_right hm ht1.le
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    have hh := C13.harm T
    have k1 := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 17 ^ 3 * 16 by norm_num)
    have k2 := mul_le_mul_of_nonneg_left hΨsum (show (0 : ℝ) ≤ 17 ^ 3 * 16 by norm_num)
    have k3 := mul_le_mul_of_nonneg_right
      (show (17 : ℝ) ^ 3 * 16 ≤ c₁ + 2 * 17 ^ 8 + 17 ^ 3 * 16 by
        linarith [show (0 : ℝ) ≤ 2 * 17 ^ 8 by norm_num]) (show 0 ≤ 1 + Real.log T by linarith)
    have k4 : (17 : ℝ) ^ 3 * 16 * M₁ ≤ 80000 * |M₁| := by nlinarith
    linarith
