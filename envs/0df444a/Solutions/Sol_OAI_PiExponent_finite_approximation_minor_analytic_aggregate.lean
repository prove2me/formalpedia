-- Prove2me | solution 1 for OAI.PiExponent.finite_approximation_minor_analytic_aggregate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T09:29:00.014996+00:00
-- url     : https://prove2.me/submissions/55d490c2-9f9c-4c6e-b914-0b4b36ce50f9

import Definitions.Def_PiExponent_FiniteMinorComparison
import Definitions.Def_PiExponent_FiniteTranslationData_690acb6f
import Theorems.Thm_OAI_PiExponent_FiniteMinorAnalysis_690acb6f_translation_expansion_geometry
import Theorems.Thm_OAI_PiExponent_FiniteMinorAnalysis_690acb6f_scalar_bound_and_support
import Theorems.Thm_OAI_PiExponent_FiniteMinorAnalysis_690acb6f_period_matrix_collision_bound
import Theorems.Thm_OAI_PiExponent_FiniteMinorAnalysis_690acb6f_remainder_tendsto_zero
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open OAI.PiExponent
open OAI.PiExponent.FiniteMinorAnalysis_690acb6f
open Filter Topology
open scoped BigOperators

/- The occupancy argument is proved here. In particular, the analytic child does
   not assume the target's maximum or either of its two quantitative gaps. -/
lemma finite_two_case_exponent
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (w : κ → ℝ)
    {H A eta nu c N b E : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta) (hnu : 0 ≤ nu)
    (hc : 0 ≤ c) (hN : 0 < N) (hw : ∀ a, 0 ≤ w a)
    (hbeta : (Fintype.card ι : ℝ) * H * b ≤ ∑ i, w (group i))
    (hcap : (((Finset.univ : Finset κ).filter (fun a => w a ≤ A * H)).card : ℝ) ≤ N) :
    -nu * ((∑ i, w (group i)) - (Fintype.card ι : ℝ) * H * b) -
      c * (∑ a, (OAI.PiExponent.FiniteMinorAnalysis_690acb6f.multiplicity group a : ℝ) ^ 2) +
      (Fintype.card ι : ℝ) * H * E ≤
    (Fintype.card ι : ℝ) * H *
      (E + max (-c * eta ^ 2 * (Fintype.card ι : ℝ) / (H * N))
        (-nu * (A * (1 - eta) - b))) := by
  classical
  let S := (Finset.univ : Finset κ).filter (fun a => w a ≤ A * H)
  let M : ℝ := Fintype.card ι
  let Z : ℝ := ∑ a, (OAI.PiExponent.FiniteMinorAnalysis_690acb6f.multiplicity group a : ℝ) ^ 2
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmass : (∑ a ∈ S, (OAI.PiExponent.FiniteMinorAnalysis_690acb6f.multiplicity group a : ℝ)) =
      (((Finset.univ : Finset ι).filter (fun i => w (group i) ≤ A * H)).card : ℝ) := by
    have hh := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset ι) S group
    have hh' : (∑ a ∈ S, OAI.PiExponent.FiniteMinorAnalysis_690acb6f.multiplicity group a) =
        ((Finset.univ : Finset ι).filter (fun i => w (group i) ≤ A * H)).card := by
      simpa only [OAI.PiExponent.FiniteMinorAnalysis_690acb6f.multiplicity, S, Finset.mem_filter, Finset.mem_univ, true_and] using hh
    exact_mod_cast hh'
  by_cases hlow : eta * M ≤ ∑ a ∈ S, (OAI.PiExponent.FiniteMinorAnalysis_690acb6f.multiplicity group a : ℝ)
  · have hcs : (∑ a ∈ S, (OAI.PiExponent.FiniteMinorAnalysis_690acb6f.multiplicity group a : ℝ)) ^ 2 ≤
        (S.card : ℝ) * ∑ a ∈ S, (OAI.PiExponent.FiniteMinorAnalysis_690acb6f.multiplicity group a : ℝ) ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq S
        (fun _ : κ => (1 : ℝ)) (fun a => (OAI.PiExponent.FiniteMinorAnalysis_690acb6f.multiplicity group a : ℝ))
    have hsub : (∑ a ∈ S, (OAI.PiExponent.FiniteMinorAnalysis_690acb6f.multiplicity group a : ℝ) ^ 2) ≤ Z :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ => sq_nonneg _)
    have hsq : eta ^ 2 * M ^ 2 ≤ N * Z := by
      calc
        _ = (eta * M) ^ 2 := by ring
        _ ≤ (∑ a ∈ S, (OAI.PiExponent.FiniteMinorAnalysis_690acb6f.multiplicity group a : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg heta hM) hlow 2
        _ ≤ (S.card : ℝ) * ∑ a ∈ S, (OAI.PiExponent.FiniteMinorAnalysis_690acb6f.multiplicity group a : ℝ) ^ 2 := hcs
        _ ≤ (S.card : ℝ) * Z := mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _)
        _ ≤ N * Z := mul_le_mul_of_nonneg_right hcap hZ
    have hz : eta ^ 2 * M ^ 2 / N ≤ Z :=
      (div_le_iff₀ hN).mpr (by nlinarith [hsq])
    have hcollision : -c * Z ≤ M * H * (-c * eta ^ 2 * M / (H * N)) := by
      have hh := mul_le_mul_of_nonneg_left hz hc
      have he : M * H * (-c * eta ^ 2 * M / (H * N)) =
          -c * (eta ^ 2 * M ^ 2 / N) := by
        field_simp [hH.ne', hN.ne']
        <;> ring
      rw [he]
      nlinarith [hh]
    have hscalar : -nu * ((∑ i, w (group i)) - M * H * b) ≤ 0 := by
      have hp := mul_nonneg hnu (sub_nonneg.mpr hbeta)
      nlinarith [hp]
    have hmax := mul_le_mul_of_nonneg_left
      (le_max_left (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - b)))
      (mul_nonneg hM hH.le)
    change -nu * ((∑ i, w (group i)) - M * H * b) - c * Z + M * H * E ≤ _
    change _ ≤ M * H * (E + max (-c * eta ^ 2 * M / (H * N))
      (-nu * (A * (1 - eta) - b)))
    nlinarith
  · have hl : (((Finset.univ : Finset ι).filter (fun i => w (group i) ≤ A * H)).card : ℝ)
        ≤ eta * M := by
      rw [← hmass]
      exact le_of_not_ge hlow
    have hp : ∀ i : ι, A * H ≤ w (group i) +
        (if w (group i) ≤ A * H then A * H else 0) := by
      intro i
      split_ifs with hi
      · linarith [hw (group i)]
      · linarith [lt_of_not_ge hi]
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hp i)
    simp only [Finset.sum_add_distrib] at hsum
    rw [← Finset.sum_filter] at hsum
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    have hlowbound := mul_le_mul_of_nonneg_right hl (mul_nonneg hA hH.le)
    have hwgt : A * H * (1 - eta) * M ≤ ∑ i, w (group i) := by
      dsimp [M] at *
      nlinarith [hsum, hlowbound]
    have hmul := mul_le_mul_of_nonneg_left hwgt hnu
    have hscalar : -nu * ((∑ i, w (group i)) - M * H * b) ≤
        M * H * (-nu * (A * (1 - eta) - b)) := by nlinarith [hmul]
    have hcollision : -c * Z ≤ 0 := by nlinarith [mul_nonneg hc hZ]
    have hmax := mul_le_mul_of_nonneg_left
      (le_max_right (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - b)))
      (mul_nonneg hM hH.le)
    change -nu * ((∑ i, w (group i)) - M * H * b) - c * Z + M * H * E ≤ _
    change _ ≤ M * H * (E + max (-c * eta ^ 2 * M / (H * N))
      (-nu * (A * (1 - eta) - b)))
    nlinarith

lemma finite_log_norm_sum_le {Ω : Type*} [Fintype Ω]
    (term : Ω → ℂ) (delta : ℂ) {M : ℕ} {H Q E : ℝ}
    (hM : 0 < M) (hH : 0 < H) (hQ : 0 < Q)
    (hcard : (Fintype.card Ω : ℝ) ≤ Q ^ M)
    (hexpansion : delta = ∑ x, term x) (hne : delta ≠ 0)
    (hterm : ∀ x, ‖term x‖ ≤ Real.exp ((M : ℝ) * H * E)) :
    Real.log ‖delta‖ / ((M : ℝ) * H) ≤ E + Real.log Q / H := by
  have hbound : ‖delta‖ ≤ Real.exp ((M : ℝ) * H * (E + Real.log Q / H)) := by
    calc
      _ = ‖∑ x, term x‖ := by rw [hexpansion]
      _ ≤ ∑ x, ‖term x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : Ω, Real.exp ((M : ℝ) * H * E) :=
        Finset.sum_le_sum fun x _ => hterm x
      _ = (Fintype.card Ω : ℝ) * Real.exp ((M : ℝ) * H * E) := by simp
      _ ≤ Q ^ M * Real.exp ((M : ℝ) * H * E) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ = _ := by
        have he : Q ^ M = Real.exp ((M : ℝ) * Real.log Q) := by
          rw [Real.exp_nat_mul, Real.exp_log hQ]
        rw [he, ← Real.exp_add]
        congr 1
        field_simp [hH.ne']
        <;> ring
  have hlog := Real.log_le_log (norm_pos_iff.mpr hne) hbound
  rw [Real.log_exp] at hlog
  apply (div_le_iff₀ (mul_pos (by exact_mod_cast hM) hH)).mpr
  nlinarith [hlog]

theorem solution
    (m K : ℕ) (w0 v0 theta : ℚ) (nu A eta F wmin : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hm : 0 < m) (hK : 0 < K)
    (hw0 : 0 < w0) (hv0 : 0 < v0)
    (htheta : 0 < theta) (htheta1 : theta < 1)
    (hnu : 0 ≤ nu) (hA : 0 < A) (hA1 : A < 1)
    (heta : 0 < eta) (heta1 : eta < 1)
    (hF : 0 < F) (hFlarge : 2 / (theta : ℝ) < F)
    (hmin : 0 < wmin) (hq : ∀ i, 2 ≤ q i)
    (hwmin : ∀ i, wmin ≤ OAI.PiExponent.MatrixArithmetic.logWeights q i)
    (happrox : ∀ i,
      |Real.pi - (p i : ℝ) / (q i : ℝ)| ≤ (q i : ℝ) ^ (-nu)) :
    ∃ error : ℝ → ℝ, Tendsto error atTop (𝓝 0) ∧
      ∀ᶠ H : ℝ in atTop, ∀ selection :
        OAI.PiExponent.InterpolationMatrix.Row K (v0 : ℝ) (theta : ℝ)
          (OAI.PiExponent.MatrixArithmetic.logWeights q) H →
        OAI.PiExponent.InterpolationMatrix.Column (w0 : ℝ)
          (OAI.PiExponent.MatrixArithmetic.logWeights q) H,
        (OAI.PiExponent.MatrixArithmetic.selectedMinor K
          (w0 : ℝ) (v0 : ℝ) (theta : ℝ) F H p q selection).det ≠ 0 →
        Real.log ‖(OAI.PiExponent.MatrixArithmetic.selectedMinor K
          (w0 : ℝ) (v0 : ℝ) (theta : ℝ) F H p q selection).det‖ /
          ((Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K
            (v0 : ℝ) (theta : ℝ)
            (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) * H) ≤
        OAI.PiExponent.FiniteMinorComparison.analyticError K
          nu F (v0 : ℝ) (w0 : ℝ) wmin + error H +
        max (-OAI.PiExponent.FiniteMinorComparison.collisionRate
          K (v0 : ℝ) (theta : ℝ) A eta q H)
          (-nu * (A * (1 - eta) -
            OAI.PiExponent.MatrixArithmetic.meanRowWeight K
              (v0 : ℝ) (theta : ℝ) q H)) := by
  classical
  have hw0r : 0 < (w0 : ℝ) := by exact_mod_cast hw0
  have hv0r : 0 < (v0 : ℝ) := by exact_mod_cast hv0
  have hthetar : 0 < (theta : ℝ) := by exact_mod_cast htheta
  refine ⟨remainder K (v0 : ℝ) (theta : ℝ) q,
    remainder_tendsto_zero K (v0 : ℝ) (theta : ℝ) q hK hv0r hthetar hq, ?_⟩
  apply (eventually_gt_atTop (0 : ℝ)).mono
  intro H hH selection hne
  obtain ⟨hM, hcard, hmean, hweight, hN, hcap, hexpansion⟩ :=
    translation_expansion_geometry K (w0 : ℝ) (v0 : ℝ) (theta : ℝ) F A H p q
      hK hw0r hv0r hthetar hA.le hH hq
  have hscalar := scalar_bound_and_support K (v0 : ℝ) (theta : ℝ) nu F wmin H p q
    hK hv0r hthetar hnu hF hmin hH hq hwmin happrox
  let Etr : ℝ := translationError K nu F (v0 : ℝ) wmin
  let Ehol : ℝ := holomorphicError K (w0 : ℝ) (v0 : ℝ) wmin
  let rho : ℝ := collisionRemainder (rowCount K (v0 : ℝ) (theta : ℝ) q H) H
  have hsplit : Etr + Ehol =
      FiniteMinorComparison.analyticError K nu F (v0 : ℝ) (w0 : ℝ) wmin := by
    dsimp [Etr, Ehol, translationError, holomorphicError, FiniteMinorComparison.analyticError]
    ring
  have hrate :
      -(Real.log 2 / 4) * eta ^ 2 *
          (rowCount K (v0 : ℝ) (theta : ℝ) q H : ℝ) /
            (H * (lowCount q A H : ℝ)) =
        -FiniteMinorComparison.collisionRate K (v0 : ℝ) (theta : ℝ) A eta q H := by
    dsimp [FiniteMinorComparison.collisionRate, rowCount, lowCount, Rows]
    ring
  have hterm : ∀ f : Choices K (v0 : ℝ) (theta : ℝ) q H,
      ‖(∏ r, scalar F p q r (f r)) * (periodMatrix selection f).det‖ ≤
        Real.exp ((rowCount K (v0 : ℝ) (theta : ℝ) q H : ℝ) * H *
          (Etr + Ehol + rho +
            max (-FiniteMinorComparison.collisionRate K (v0 : ℝ) (theta : ℝ) A eta q H)
              (-nu * (A * (1 - eta) -
                MatrixArithmetic.meanRowWeight K (v0 : ℝ) (theta : ℝ) q H)))) := by
    intro f
    by_cases hs : (∏ r, scalar F p q r (f r)) = 0
    · simp only [hs, zero_mul, norm_zero]
      exact (Real.exp_pos _).le
    have hbeta :
        (rowCount K (v0 : ℝ) (theta : ℝ) q H : ℝ) * H *
            MatrixArithmetic.meanRowWeight K (v0 : ℝ) (theta : ℝ) q H ≤
          ∑ r, weight q (f r).1.1 := by
      rw [← hmean]
      apply Finset.sum_le_sum
      intro r _
      apply (hscalar r (f r)).2
      exact Finset.prod_ne_zero_iff.mp hs r (Finset.mem_univ r)
    have hprod : ‖∏ r, scalar F p q r (f r)‖ ≤ Real.exp
        (-nu * ((∑ r, weight q (f r).1.1) -
          (rowCount K (v0 : ℝ) (theta : ℝ) q H : ℝ) * H *
            MatrixArithmetic.meanRowWeight K (v0 : ℝ) (theta : ℝ) q H) +
          (rowCount K (v0 : ℝ) (theta : ℝ) q H : ℝ) * H * Etr) := by
      rw [norm_prod]
      calc
        _ ≤ ∏ r : Rows K (v0 : ℝ) (theta : ℝ) q H,
            Real.exp (-nu * (weight q (f r).1.1 - weight q (beta r)) + H * Etr) :=
          Finset.prod_le_prod (fun r _ => norm_nonneg _)
            (fun r _ => (hscalar r (f r)).1)
        _ = _ := by
          rw [← Real.exp_sum]
          congr 1
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [hmean]
          change _ = _
          dsimp [rowCount]
          ring
    have hdet := period_matrix_collision_bound K (w0 : ℝ) (v0 : ℝ) (theta : ℝ) wmin H q
      hK hw0r hv0r hthetar hmin hH hwmin selection f
    have hb := finite_two_case_exponent
      (fun r : Rows K (v0 : ℝ) (theta : ℝ) q H => (f r).1)
      (fun a : Transverse q H => weight q a.1)
      (E := Etr + Ehol + rho) hH hA.le heta.le hnu
      (show 0 ≤ Real.log 2 / 4 from div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num))
      (show (0 : ℝ) < (lowCount q A H : ℝ) by exact_mod_cast hN)
      hweight hbeta hcap
    change
      -nu * ((∑ r, weight q (f r).1.1) -
        (rowCount K (v0 : ℝ) (theta : ℝ) q H : ℝ) * H *
          MatrixArithmetic.meanRowWeight K (v0 : ℝ) (theta : ℝ) q H) -
        (Real.log 2 / 4) * (∑ a : Transverse q H,
          (OAI.PiExponent.FiniteMinorAnalysis_690acb6f.multiplicity (fun r => (f r).1) a : ℝ) ^ 2) +
        (rowCount K (v0 : ℝ) (theta : ℝ) q H : ℝ) * H * (Etr + Ehol + rho) ≤
      (rowCount K (v0 : ℝ) (theta : ℝ) q H : ℝ) * H *
        (Etr + Ehol + rho +
          max (-(Real.log 2 / 4) * eta ^ 2 *
            (rowCount K (v0 : ℝ) (theta : ℝ) q H : ℝ) / (H * (lowCount q A H : ℝ)))
            (-nu * (A * (1 - eta) -
              MatrixArithmetic.meanRowWeight K (v0 : ℝ) (theta : ℝ) q H))) at hb
    rw [hrate] at hb
    rw [norm_mul]
    apply (mul_le_mul hprod hdet (norm_nonneg _) (Real.exp_pos _).le).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change _ ≤ _
    dsimp [Ehol, rho] at hb ⊢
    nlinarith [hb]
  have hQ : (0 : ℝ) < (termCount m (v0 : ℝ) H : ℝ) := by
    unfold termCount
    positivity
  have hcardr : (Fintype.card (Choices K (v0 : ℝ) (theta : ℝ) q H) : ℝ) ≤
      (termCount m (v0 : ℝ) H : ℝ) ^ rowCount K (v0 : ℝ) (theta : ℝ) q H := by
    exact_mod_cast hcard
  have hb := finite_log_norm_sum_le
    (fun f : Choices K (v0 : ℝ) (theta : ℝ) q H =>
      (∏ r, scalar F p q r (f r)) * (periodMatrix selection f).det)
    (MatrixArithmetic.selectedMinor K (w0 : ℝ) (v0 : ℝ) (theta : ℝ) F H p q selection).det
    hM hH hQ hcardr (hexpansion selection) hne hterm
  calc
    _ ≤ (Etr + Ehol + rho +
          max (-FiniteMinorComparison.collisionRate K (v0 : ℝ) (theta : ℝ) A eta q H)
            (-nu * (A * (1 - eta) -
              MatrixArithmetic.meanRowWeight K (v0 : ℝ) (theta : ℝ) q H))) +
        Real.log (termCount m (v0 : ℝ) H : ℝ) / H := hb
    _ = _ := by
      rw [← hsplit]
      dsimp [rho, remainder]
      ring
