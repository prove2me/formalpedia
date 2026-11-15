-- Prove2me | solution 1 for IAFTRL.lemma_D_14
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T05:20:19.847035+00:00
-- url     : https://prove2.me/submissions/637a696e-cb24-4b45-a627-703f3994a58e

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_IAFTRL_IsCorrupted
import Definitions.Def_IAFTRL_cR

open Finset Matrix MeasureTheory
set_option maxHeartbeats 1000000

namespace D14Proof

/-- A capped corruption budget, proved by telescoping square roots of prefix sums. -/
private lemma capped_sum (k : ℕ → ℝ) (T : ℕ) (C : ℝ)
    (hk : ∀ t < T, 0 ≤ k t ∧ k t ≤ 2)
    (hC : ∑ t ∈ range T, k t ≤ C) :
    ∑ t ∈ range T, k t / Real.sqrt (t + 1) ≤ 2 * Real.sqrt 2 * Real.sqrt C := by
  let S (n : ℕ) : ℝ := ∑ t ∈ range n, k t
  have hS0 (n : ℕ) (hn : n ≤ T) : 0 ≤ S n :=
    sum_nonneg fun t ht => (hk t (lt_of_lt_of_le (mem_range.mp ht) hn)).1
  have hS2 (n : ℕ) (hn : n ≤ T) : S n ≤ 2 * n := by
    calc
      S n ≤ ∑ _t ∈ range n, (2 : ℝ) :=
        sum_le_sum fun t ht => (hk t (lt_of_lt_of_le (mem_range.mp ht) hn)).2
      _ = _ := by simp; ring
  have hstep (t : ℕ) (ht : t < T) :
      k t / Real.sqrt (t + 1) ≤
        2 * Real.sqrt 2 * (Real.sqrt (S (t + 1)) - Real.sqrt (S t)) := by
    have hs0 := hS0 t (by omega)
    have hs1 := hS0 (t + 1) (by omega)
    have hrec : S (t + 1) = S t + k t := sum_range_succ _ _
    have hsq0 := Real.sq_sqrt hs0
    have hsq1 := Real.sq_sqrt hs1
    have hab : Real.sqrt (S t) ≤ Real.sqrt (S (t + 1)) :=
      Real.sqrt_le_sqrt (by rw [hrec]; linarith [(hk t ht).1])
    have hb : Real.sqrt (S (t + 1)) ≤ Real.sqrt 2 * Real.sqrt (t + 1) := by
      calc
        _ ≤ Real.sqrt (2 * (t + 1)) := Real.sqrt_le_sqrt (by simpa using hS2 (t+1) (by omega))
        _ = _ := Real.sqrt_mul (by norm_num) _
    have hprod := mul_le_mul_of_nonneg_right
      (show Real.sqrt (S (t + 1)) + Real.sqrt (S t) ≤
        2 * Real.sqrt 2 * Real.sqrt (t + 1) by linarith)
      (sub_nonneg.mpr hab)
    apply (div_le_iff₀ (Real.sqrt_pos.2 (by positivity))).2
    nlinarith
  calc
    _ ≤ ∑ t ∈ range T, 2 * Real.sqrt 2 *
        (Real.sqrt (S (t + 1)) - Real.sqrt (S t)) :=
      sum_le_sum fun t ht => hstep t (mem_range.mp ht)
    _ = 2 * Real.sqrt 2 * Real.sqrt (S T) := by
      rw [← mul_sum, sum_range_sub (fun n => Real.sqrt (S n)) T]
      simp [S]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hC) (by positivity)

private lemma q_prob {d K : ℕ} [Nonempty (Fin K)] (β : ℝ)
    (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) :
    (∀ a, 0 ≤ IAFTRL.qSoft β arms S a) ∧ ∑ a, IAFTRL.qSoft β arms S a = 1 := by
  have hp : 0 < ∑ a, Real.exp (-(arms a ⬝ᵥ S) / β) :=
    sum_pos (fun a _ => Real.exp_pos _) univ_nonempty
  constructor
  · intro a; exact div_nonneg (Real.exp_pos _).le hp.le
  · simp only [IAFTRL.qSoft]
    rw [← sum_div, div_self (ne_of_gt hp)]

/-- The prescribed exploration cap is bounded by the inverse-square-root schedule. -/
private lemma gamma_bound {d K : ℕ} (hd : 1 ≤ d) (hK : 1 ≤ K) (t : ℕ) :
    IAFTRL.Gam d K (t + 1) ≤ 4 * IAFTRL.cR d K / Real.sqrt (t + 1) := by
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (K : ℝ) ≠ 0 := by linarith
  have hl : 0 < 1 + Real.log K := by have := Real.log_nonneg hK1; linarith
  have ht : 0 < (t : ℝ) + 1 := by positivity
  have hc : IAFTRL.cR d K = Real.sqrt d * Real.sqrt (1 + Real.log K) := by
    rw [IAFTRL.cR, Real.log_mul (Real.exp_ne_zero _) hK0, Real.log_exp,
      Real.sqrt_mul hd0.le]
  have hs : IAFTRL.cR d K * Real.sqrt ((d : ℝ) * (t + 1) / (1 + Real.log K)) =
      d * Real.sqrt (t + 1) := by
    rw [hc, Real.sqrt_div (by positivity), Real.sqrt_mul hd0.le]
    calc
      _ = Real.sqrt d ^ 2 * Real.sqrt (t + 1) := by
        field_simp [(Real.sqrt_pos.2 hl).ne']
      _ = _ := by rw [Real.sq_sqrt hd0.le]
  have hb : 0 < IAFTRL.beta d K (t + 1) := by
    dsimp [IAFTRL.beta]
    positivity
  rw [IAFTRL.Gam]
  apply (div_le_div_iff₀ hb (Real.sqrt_pos.2 ht)).2
  dsimp [IAFTRL.beta]
  push_cast
  have hn := mul_nonneg (show 0 ≤ IAFTRL.cR d K from Real.sqrt_nonneg _)
    (show 0 ≤ (16 : ℝ) * d from by positivity)
  nlinarith

private lemma norm_nonneg {d K : ℕ} [Nonempty (Fin K)]
    (arms : Fin K → Fin d → ℝ) (z : Fin d → ℝ) : 0 ≤ IAFTRL.actionNorm arms z := by
  obtain ⟨a⟩ := ‹Nonempty (Fin K)›
  change 0 ≤ ⨆ j, |arms j ⬝ᵥ z|
  exact (abs_nonneg (arms a ⬝ᵥ z)).trans
    (le_ciSup (f := fun j : Fin K => |arms j ⬝ᵥ z|) (Set.finite_range _).bddAbove a)

private lemma norm_bound {d K : ℕ} (arms : Fin K → Fin d → ℝ)
    (z : Fin d → ℝ) (a : Fin K) : |arms a ⬝ᵥ z| ≤ IAFTRL.actionNorm arms z := by
  unfold IAFTRL.actionNorm
  exact le_ciSup (f := fun j : Fin K => |arms j ⬝ᵥ z|) (Set.finite_range _).bddAbove a

private lemma norm_sub_le_two {d K : ℕ} [Nonempty (Fin K)]
    (arms : Fin K → Fin d → ℝ) (z θ : Fin d → ℝ)
    (hz : IAFTRL.actionNorm arms z ≤ 1) (hθ : IAFTRL.actionNorm arms θ ≤ 1) :
    IAFTRL.actionNorm arms (z - θ) ≤ 2 := by
  apply ciSup_le
  intro a
  rw [dotProduct_sub]
  exact (abs_sub _ _).trans (by linarith [norm_bound arms z a, norm_bound arms θ a])

/-- The exploration perturbation has action-norm cost at most twice its mass. -/
private lemma mixture_bound {d K : ℕ} [Nonempty (Fin K)]
    (arms : Fin K → Fin d → ℝ) (t : ℕ) (S z : Fin d → ℝ)
    (p : Fin K → ℝ)
    (hp : ∃ w : Fin K → ℝ, (∀ a, 0 ≤ w a) ∧ ∑ a, w a ≤ IAFTRL.Gam d K t ∧
      p = fun a => (1 - ∑ b, w b) * IAFTRL.qSoft (IAFTRL.beta d K t) arms S a + w a) :
    |∑ a, (p a - IAFTRL.qSoft (IAFTRL.beta d K t) arms S a) * (arms a ⬝ᵥ z)| ≤
      2 * IAFTRL.Gam d K t * IAFTRL.actionNorm arms z := by
  let q := IAFTRL.qSoft (IAFTRL.beta d K t) arms S
  obtain ⟨hq0, hq1⟩ := q_prob (IAFTRL.beta d K t) arms S
  obtain ⟨w, hw, hcap, hmix⟩ := hp
  let γ := ∑ a, w a
  have hγ : 0 ≤ γ := sum_nonneg fun a _ => hw a
  have hdiff (a : Fin K) : p a - q a = w a - γ * q a := by
    rw [hmix]; dsimp [q, γ]; ring
  have habs (a : Fin K) : |p a - q a| ≤ w a + γ * q a := by
    rw [hdiff]
    have hn : 0 ≤ γ * q a := mul_nonneg hγ (hq0 a)
    calc
      _ ≤ |w a| + |γ * q a| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg (hw a), abs_of_nonneg hn]
  calc
    _ ≤ ∑ a, |(p a - q a) * (arms a ⬝ᵥ z)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, (w a + γ * q a) * IAFTRL.actionNorm arms z := by
      apply sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul (habs a) (norm_bound arms z a) (abs_nonneg _)
        (add_nonneg (hw a) (mul_nonneg hγ (hq0 a)))
    _ = 2 * γ * IAFTRL.actionNorm arms z := by
      rw [← sum_mul, sum_add_distrib, ← mul_sum, hq1]
      dsimp [γ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg arms z)


end D14Proof

/-- Lemma D.14: the direct corruption contribution for the executed IA-FTRL law. -/
theorem solution {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ)
    (hA : IAFTRL.IsActionSet arms)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
    (R : IAFTRL.Run d K Ω) (hR : IAFTRL.IsIAFTRLRun P arms T R)
    (θ : Fin d → ℝ) (jstar : Fin K) (C : ℝ) (hC : 0 ≤ C)
    (hcor : IAFTRL.IsCorrupted P arms θ C T R) :
    let q : ℕ → Ω → Fin K → ℝ := fun t ω =>
      IAFTRL.qSoft (IAFTRL.beta d K (t + 1)) arms (R.cumEst arms t ω)
    (∑ t ∈ Finset.range T,
        ∫ ω, ∑ a, (R.p t ω a - q t ω a) * ((arms a - arms jstar) ⬝ᵥ (R.θs t ω - θ)) ∂P) ≤
      ∑ t ∈ Finset.range T,
        ∫ ω, |∑ a, (R.p t ω a - q t ω a) * (arms a ⬝ᵥ (R.θs t ω - θ))| ∂P ∧
    (∑ t ∈ Finset.range T,
        ∫ ω, |∑ a, (R.p t ω a - q t ω a) * (arms a ⬝ᵥ (R.θs t ω - θ))| ∂P) ≤
      16 * Real.sqrt 2 * IAFTRL.cR d K * Real.sqrt C := by
  classical
  let : Nonempty (Fin K) := ⟨jstar⟩
  have hK : 1 ≤ K := by have := jstar.isLt; omega
  let q : ℕ → Ω → Fin K → ℝ := fun t ω =>
    IAFTRL.qSoft (IAFTRL.beta d K (t + 1)) arms (R.cumEst arms t ω)
  let κ : ℕ → Ω → ℝ := fun t ω => IAFTRL.actionNorm arms (R.θs t ω - θ)
  -- Apply the deterministic capped-sum bound to expected corruption magnitudes.
  let k : ℕ → ℝ := fun t => ∫ ω, κ t ω ∂P
  have hfeas (t : ℕ) (ht : t < T) (ω : Ω) :
      IAFTRL.IsFeasible2_3 arms (t + 1) (R.cumEst arms t ω) (R.p t ω) :=
    ((hR t ht).2.1.2 ω).1
  have hκ0 (t : ℕ) (ω : Ω) : 0 ≤ κ t ω := D14Proof.norm_nonneg arms _
  have hκ2 (t : ℕ) (ht : t < T) (ω : Ω) : κ t ω ≤ 2 :=
    D14Proof.norm_sub_le_two arms _ θ ((hR t ht).2.2.2.2 ω) hcor.1
  have hκmeas (t : ℕ) (ht : t < T) : Measurable (κ t) := by
    have hm := (hR t ht).1.2.2.1
    change Measurable fun ω => ⨆ a, |∑ i, arms a i * (R.θs t ω i - θ i)|
    apply Measurable.iSup
    intro a
    apply Measurable.abs
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul (((measurable_pi_apply i).comp hm).sub measurable_const)
  have hκint (t : ℕ) (ht : t < T) : Integrable (κ t) P :=
    (integrable_const (2 : ℝ)).mono_nonneg (hκmeas t ht).aestronglyMeasurable
      (ae_of_all _ (hκ0 t)) (ae_of_all _ (hκ2 t ht))
  have hk (t : ℕ) (ht : t < T) : 0 ≤ k t ∧ k t ≤ 2 := by
    constructor
    · exact integral_nonneg (hκ0 t)
    · calc
        k t ≤ ∫ _ω : Ω, (2 : ℝ) ∂P :=
          integral_mono (hκint t ht) (integrable_const _) (hκ2 t ht)
        _ = 2 := by simp
  have hkC : ∑ t ∈ range T, k t ≤ C := by
    change (∑ t ∈ range T, ∫ ω, κ t ω ∂P) ≤ C
    rw [← integral_finsetSum _ (fun t ht => hκint t (mem_range.mp ht))]
    calc
      _ ≤ ∫ _ω : Ω, C ∂P :=
        integral_mono_ae (integrable_finsetSum _ fun t ht => hκint t (mem_range.mp ht))
          (integrable_const _) hcor.2
      _ = C := by simp
  have hround (t : ℕ) (ht : t < T) :
      (∫ ω, |∑ a, (R.p t ω a - q t ω a) * (arms a ⬝ᵥ (R.θs t ω - θ))| ∂P) ≤
        8 * IAFTRL.cR d K * (k t / Real.sqrt (t + 1)) := by
    calc
      _ ≤ ∫ ω, (8 * IAFTRL.cR d K / Real.sqrt (t + 1)) * κ t ω ∂P := by
        apply integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          ((hκint t ht).const_mul _)
        apply ae_of_all
        intro ω
        calc
          _ ≤ 2 * IAFTRL.Gam d K (t + 1) * κ t ω :=
            D14Proof.mixture_bound arms (t + 1) (R.cumEst arms t ω) _ _
              (hfeas t ht ω).2.2.1
          _ ≤ (8 * IAFTRL.cR d K / Real.sqrt (t + 1)) * κ t ω := by
            apply mul_le_mul_of_nonneg_right _ (hκ0 t ω)
            have hg := D14Proof.gamma_bound hd hK t
            calc
              _ ≤ 2 * (4 * IAFTRL.cR d K / Real.sqrt (t + 1)) :=
                mul_le_mul_of_nonneg_left hg (by norm_num)
              _ = _ := by ring
      _ = _ := by rw [integral_const_mul]; dsimp [k]; ring
  constructor
  · apply sum_le_sum
    intro t ht
    change (∫ ω, ∑ a, (R.p t ω a - q t ω a) *
      ((arms a - arms jstar) ⬝ᵥ (R.θs t ω - θ)) ∂P) ≤
      ∫ ω, |∑ a, (R.p t ω a - q t ω a) * (arms a ⬝ᵥ (R.θs t ω - θ))| ∂P
    have hshift (ω : Ω) :
        (∑ a, (R.p t ω a - q t ω a) * ((arms a - arms jstar) ⬝ᵥ (R.θs t ω - θ))) =
        ∑ a, (R.p t ω a - q t ω a) * (arms a ⬝ᵥ (R.θs t ω - θ)) := by
      simp only [sub_dotProduct, mul_sub, sum_sub_distrib, ← sum_mul]
      have hp1 := (hfeas t (mem_range.mp ht) ω).2.1
      have hq1 := (D14Proof.q_prob (IAFTRL.beta d K (t + 1)) arms (R.cumEst arms t ω)).2
      change _ - ((∑ a, R.p t ω a) - ∑ a, q t ω a) * _ = _
      rw [hp1, hq1]
      ring
    simp_rw [hshift]
    exact (le_abs_self _).trans abs_integral_le_integral_abs
  · calc
      _ ≤ ∑ t ∈ range T, 8 * IAFTRL.cR d K * (k t / Real.sqrt (t + 1)) :=
        sum_le_sum fun t ht => hround t (mem_range.mp ht)
      _ = 8 * IAFTRL.cR d K * ∑ t ∈ range T, k t / Real.sqrt (t + 1) := by
        rw [mul_sum]
      _ ≤ 8 * IAFTRL.cR d K * (2 * Real.sqrt 2 * Real.sqrt C) :=
        mul_le_mul_of_nonneg_left (D14Proof.capped_sum k T C hk hkC) (by
          unfold IAFTRL.cR; positivity)
      _ = _ := by ring

