-- Prove2me | solution 1 for InfoLossLAR.WorstCase.BDD.amplification_joint_tv
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:12:04.978137+00:00
-- url     : https://prove2.me/submissions/f37713d6-2fd3-40e7-a127-3199a088b013

import Definitions.Def_InfoLossLAR_LoadedBatchBundle_05

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AFT
open scoped BigOperators
noncomputable section

private def badCount {Outcome Secret : Type*} [DecidableEq Secret] {trials : ℕ}
    (readout : Fin trials → Outcome → Secret) (secret : Secret)
    (outcomes : Fin trials → Outcome) : ℕ :=
  ∑ i, if readout i (outcomes i) = secret then 0 else 1

private def moment {Outcome Secret : Type*} [DecidableEq Secret] {trials : ℕ}
    (readout : Fin trials → Outcome → Secret) (secret : Secret)
    (outcomes : Fin trials → Outcome) : ℝ :=
  ∏ i, if readout i (outcomes i) = secret then 1 else 4

private theorem moment_eq {Outcome Secret : Type*} [DecidableEq Secret] {trials : ℕ}
    (readout : Fin trials → Outcome → Secret) (secret : Secret) (outcomes : Fin trials → Outcome) :
    moment readout secret outcomes = (4 : ℝ) ^ badCount readout secret outcomes := by
  unfold moment badCount
  have hp (i : Fin trials) : (if readout i (outcomes i) = secret then (1 : ℝ) else 4) =
      (4 : ℝ) ^ (if readout i (outcomes i) = secret then (0 : ℕ) else 1) := by split_ifs <;> norm_num
  simp_rw [hp]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem solution {Outcome Secret : Type*} [Fintype Outcome] [DecidableEq Secret]
    (trials : ℕ) (law : Fin trials → FiniteDist Outcome)
    (readout : Fin trials → Outcome → Secret) (secret : Secret)
    (fail : (Fin trials → Outcome) → Prop) [DecidablePred fail]
    (hsuccess : ∀ i, (3/4 : ℝ) ≤ ∑ x, if readout i x = secret then (law i).weight x else 0)
    (hfail : ∀ outcomes, fail outcomes → trials ≤ 2 *
      (∑ i, if readout i (outcomes i) = secret then 0 else 1))
    (actual : FiniteDist (Fin trials → Outcome)) (jointError : ℝ)
    (hjoint : FiniteDist.TVBound actual (FiniteDist.independent law) jointError) :
    (∑ outcomes, if fail outcomes then actual.weight outcomes else 0) ≤
      (7/8 : ℝ)^trials + jointError := by
  have hsingle (i : Fin trials) :
      (∑ x, (law i).weight x * (if readout i x = secret then (1 : ℝ) else 4)) ≤ 7/4 := by
    have hp (x : Outcome) : (law i).weight x * (if readout i x = secret then (1 : ℝ) else 4) =
        4 * (law i).weight x - 3 * (if readout i x = secret then (law i).weight x else 0) := by
      split_ifs <;> ring
    simp_rw [hp]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (law i).sum_one]
    linarith [hsuccess i]
  have hm : (∑ outcomes : Fin trials → Outcome, (FiniteDist.independent law).weight outcomes *
      moment readout secret outcomes) ≤ (7/4 : ℝ)^trials := by
    change (∑ outcomes : Fin trials → Outcome, (∏ i, (law i).weight (outcomes i)) *
      (∏ i, if readout i (outcomes i) = secret then (1 : ℝ) else 4)) ≤ _
    simp_rw [← Finset.prod_mul_distrib]
    have hp := Fintype.prod_sum (fun i : Fin trials => fun x : Outcome =>
      (law i).weight x * (if readout i x = secret then (1 : ℝ) else 4))
    rw [← hp]
    have h := Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => Finset.sum_nonneg (fun x _ => mul_nonneg ((law i).nonneg x) (by split_ifs <;> positivity)))
      (fun i _ => hsingle i)
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  have hpoint (outcomes : Fin trials → Outcome) :
      (if fail outcomes then (1 : ℝ) else 0) ≤ moment readout secret outcomes / (2 : ℝ)^trials := by
    by_cases hf : fail outcomes
    · rw [if_pos hf, moment_eq]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^trials)).mpr
      have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (hfail outcomes hf)
      convert h using 1 <;> simp only [one_mul,pow_mul,badCount] <;> norm_num
    · rw [if_neg hf, moment_eq]
      positivity
  have hideal : (∑ outcomes : Fin trials → Outcome, if fail outcomes then
      (FiniteDist.independent law).weight outcomes else 0) ≤ (7/8 : ℝ)^trials := by
    calc
      _ ≤ ∑ outcomes : Fin trials → Outcome, (FiniteDist.independent law).weight outcomes *
          (moment readout secret outcomes / (2 : ℝ)^trials) := by
        apply Finset.sum_le_sum
        intro outcomes _
        have h := mul_le_mul_of_nonneg_left (hpoint outcomes) ((FiniteDist.independent law).nonneg outcomes)
        simpa only [mul_ite,mul_one,mul_zero] using h
      _ = (∑ outcomes : Fin trials → Outcome, (FiniteDist.independent law).weight outcomes *
          moment readout secret outcomes) / (2 : ℝ)^trials := by simp only [mul_div_assoc,Finset.sum_div]
      _ ≤ (7/4 : ℝ)^trials / (2 : ℝ)^trials := div_le_div_of_nonneg_right hm (by positivity)
      _ = (7/8 : ℝ)^trials := by rw [←div_pow]; norm_num
  let bad : Finset (Fin trials → Outcome) := Finset.univ.filter fail
  have he := (abs_le.mp (hjoint bad)).2
  simp only [FiniteDist.event,bad,Finset.sum_filter] at he
  linarith
