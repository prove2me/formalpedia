-- Prove2me | solution 1 for MDPFinance.Stationary.reward_iteration_stationary
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:42:28.014848+00:00
-- url     : https://prove2.me/submissions/464c94b0-4374-41c4-8381-9178423036ad

import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model
import Definitions.Def_MDPFinance_Stationary_Policy
import Definitions.Def_MDPFinance_Stationary_Operators
import Definitions.Def_MDPFinance_Stationary_ValueFunction

open MeasureTheory ProbabilityTheory MDPFinance.Stationary

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace AffineAux

noncomputable def eI {E : Type*} [MeasurableSpace E] (μ : Measure E) (v : E → EReal) :
    EReal :=
  (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal))

theorem pos_coe (s : ℝ) : ((s : EReal) ⊔ 0).toENNReal = ENNReal.ofReal s := by
  rcases le_total s 0 with h | h
  · rw [sup_eq_right.mpr (by exact_mod_cast h)]
    simp [ENNReal.ofReal_of_nonpos h]
  · rw [sup_eq_left.mpr (by exact_mod_cast h)]
    rfl

theorem neg_coe (s : ℝ) : ((-(s : EReal)) ⊔ 0).toENNReal = ENNReal.ofReal (-s) := by
  rw [← EReal.coe_neg, pos_coe]

theorem real_id (c d t : ℝ) :
    max (c + d * t) 0 + d * max (-t) 0 + max (-c) 0 =
      max (-(c + d * t)) 0 + d * max t 0 + max c 0 := by
  rcases le_total (c + d * t) 0 with h1 | h1 <;> rcases le_total t 0 with h2 | h2 <;>
    rcases le_total c 0 with h3 | h3 <;>
    simp only [max_eq_left, max_eq_right, h1, h2, h3, neg_nonneg, neg_nonpos] <;> ring_nf


/-- positive / negative parts as `ℝ≥0∞`. -/
noncomputable abbrev pp (y : EReal) : ENNReal := (y ⊔ 0).toENNReal
noncomputable abbrev nn (y : EReal) : ENNReal := ((-y) ⊔ 0).toENNReal

theorem pp_top : pp ⊤ = ⊤ := by simp [pp]
theorem nn_top : nn ⊤ = 0 := by simp [nn]
theorem pp_bot : pp ⊥ = 0 := by simp [pp]
theorem nn_bot : nn ⊥ = ⊤ := by simp [nn]

theorem ptwise (c d : ℝ) (hd : 0 < d) (y : EReal) :
    pp ((c : EReal) + (d : EReal) * y) + ENNReal.ofReal d * nn y + ENNReal.ofReal (-c) =
      nn ((c : EReal) + (d : EReal) * y) + ENNReal.ofReal d * pp y + ENNReal.ofReal c := by
  induction y using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos hd, EReal.add_bot, nn_bot, pp_bot]
    simp [ENNReal.mul_top, (ENNReal.ofReal_pos.mpr hd).ne']
  | top =>
    rw [EReal.coe_mul_top_of_pos hd, EReal.coe_add_top, nn_top, pp_top]
    simp [ENNReal.mul_top, (ENNReal.ofReal_pos.mpr hd).ne']
  | coe t =>
    simp only [pp, nn]
    rw [← EReal.coe_mul, ← EReal.coe_add, pos_coe, neg_coe, pos_coe, neg_coe]
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_mul, ENNReal.toReal_mul]
    simp only [ENNReal.toReal_ofReal', max_eq_left hd.le]
    exact real_id c d t

theorem ineq1 (c d : ℝ) (hd : 0 < d) (y : EReal) :
    ENNReal.ofReal d * pp y ≤ pp ((c : EReal) + (d : EReal) * y) + ENNReal.ofReal (-c) := by
  induction y using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos hd, EReal.add_bot]
    simp [pp, nn, ENNReal.mul_top, (ENNReal.ofReal_pos.mpr hd).ne']
  | top =>
    rw [EReal.coe_mul_top_of_pos hd, EReal.coe_add_top]
    simp [pp, nn, ENNReal.mul_top, (ENNReal.ofReal_pos.mpr hd).ne']
  | coe t =>
    simp only [pp, nn]
    rw [← EReal.coe_mul, ← EReal.coe_add]
    simp only [pos_coe, neg_coe]
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal', max_eq_left hd.le]
    rcases le_total (c + d * t) 0 with h1 | h1 <;> rcases le_total t 0 with h2 | h2 <;>
      rcases le_total c 0 with h3 | h3 <;>
      simp only [max_eq_left, max_eq_right, h1, h2, h3, neg_nonneg, neg_nonpos] <;>
      nlinarith

theorem ineq2 (c d : ℝ) (hd : 0 < d) (y : EReal) :
    pp ((c : EReal) + (d : EReal) * y) ≤ ENNReal.ofReal d * pp y + ENNReal.ofReal c := by
  induction y using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos hd, EReal.add_bot]
    simp [pp, nn, ENNReal.mul_top, (ENNReal.ofReal_pos.mpr hd).ne']
  | top =>
    rw [EReal.coe_mul_top_of_pos hd, EReal.coe_add_top]
    simp [pp, nn, ENNReal.mul_top, (ENNReal.ofReal_pos.mpr hd).ne']
  | coe t =>
    simp only [pp, nn]
    rw [← EReal.coe_mul, ← EReal.coe_add]
    simp only [pos_coe, neg_coe]
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal', max_eq_left hd.le]
    rcases le_total (c + d * t) 0 with h1 | h1 <;> rcases le_total t 0 with h2 | h2 <;>
      rcases le_total c 0 with h3 | h3 <;>
      simp only [max_eq_left, max_eq_right, h1, h2, h3, neg_nonneg, neg_nonpos] <;>
      nlinarith

theorem ineq3 (c d : ℝ) (hd : 0 < d) (y : EReal) :
    ENNReal.ofReal d * nn y ≤ nn ((c : EReal) + (d : EReal) * y) + ENNReal.ofReal c := by
  induction y using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos hd, EReal.add_bot]
    simp [pp, nn, ENNReal.mul_top, (ENNReal.ofReal_pos.mpr hd).ne']
  | top =>
    rw [EReal.coe_mul_top_of_pos hd, EReal.coe_add_top]
    simp [pp, nn, ENNReal.mul_top, (ENNReal.ofReal_pos.mpr hd).ne']
  | coe t =>
    simp only [pp, nn]
    rw [← EReal.coe_mul, ← EReal.coe_add]
    simp only [pos_coe, neg_coe]
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal', max_eq_left hd.le]
    rcases le_total (c + d * t) 0 with h1 | h1 <;> rcases le_total t 0 with h2 | h2 <;>
      rcases le_total c 0 with h3 | h3 <;>
      simp only [max_eq_left, max_eq_right, h1, h2, h3, neg_nonneg, neg_nonpos] <;>
      nlinarith

theorem ineq4 (c d : ℝ) (hd : 0 < d) (y : EReal) :
    nn ((c : EReal) + (d : EReal) * y) ≤ ENNReal.ofReal d * nn y + ENNReal.ofReal (-c) := by
  induction y using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos hd, EReal.add_bot]
    simp [pp, nn, ENNReal.mul_top, (ENNReal.ofReal_pos.mpr hd).ne']
  | top =>
    rw [EReal.coe_mul_top_of_pos hd, EReal.coe_add_top]
    simp [pp, nn, ENNReal.mul_top, (ENNReal.ofReal_pos.mpr hd).ne']
  | coe t =>
    simp only [pp, nn]
    rw [← EReal.coe_mul, ← EReal.coe_add]
    simp only [pos_coe, neg_coe]
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal', max_eq_left hd.le]
    rcases le_total (c + d * t) 0 with h1 | h1 <;> rcases le_total t 0 with h2 | h2 <;>
      rcases le_total c 0 with h3 | h3 <;>
      simp only [max_eq_left, max_eq_right, h1, h2, h3, neg_nonneg, neg_nonpos] <;>
      nlinarith

theorem final (c d : ℝ) (hd : 0 < d) (P' N' P Nn : ENNReal)
    (H : P' + ENNReal.ofReal d * Nn + ENNReal.ofReal (-c) = N' + ENNReal.ofReal d * P + ENNReal.ofReal c)
    (I1 : ENNReal.ofReal d * P ≤ P' + ENNReal.ofReal (-c))
    (I2 : P' ≤ ENNReal.ofReal d * P + ENNReal.ofReal c)
    (I3 : ENNReal.ofReal d * Nn ≤ N' + ENNReal.ofReal c)
    (I4 : N' ≤ ENNReal.ofReal d * Nn + ENNReal.ofReal (-c)) :
    (P' : EReal) + -(N' : EReal) = (c : EReal) + (d : EReal) * ((P : EReal) + -(Nn : EReal)) := by
  have hd' : ENNReal.ofReal d ≠ 0 := (ENNReal.ofReal_pos.mpr hd).ne'
  by_cases hP : P = ⊤
  · have hP' : P' = ⊤ := by
      subst hP
      rw [ENNReal.mul_top hd'] at I1
      by_contra h
      exact absurd (top_le_iff.mp I1) (by finiteness)
    by_cases hN : Nn = ⊤
    · have hN' : N' = ⊤ := by
        subst hN
        rw [ENNReal.mul_top hd'] at I3
        by_contra h
        exact absurd (top_le_iff.mp I3) (by finiteness)
      subst hP hN hP' hN'
      simp [EReal.coe_mul_bot_of_pos hd]
    · have hN' : N' ≠ ⊤ := by
        intro h
        rw [h, top_le_iff] at I4
        exact absurd I4 (by finiteness)
      subst hP hP'
      have e1 : ((N' : EReal)) = ((N'.toReal : ℝ) : EReal) := (EReal.coe_ennreal_toReal hN').symm
      have e2 : ((Nn : EReal)) = ((Nn.toReal : ℝ) : EReal) := (EReal.coe_ennreal_toReal hN).symm
      rw [e1, e2, EReal.coe_ennreal_top, ← EReal.coe_neg, ← EReal.coe_neg, EReal.top_add_coe,
        EReal.top_add_coe, EReal.coe_mul_top_of_pos hd, EReal.coe_add_top]
  · have hP' : P' ≠ ⊤ := by
      intro h
      rw [h, top_le_iff] at I2
      exact absurd I2 (by finiteness)
    by_cases hN : Nn = ⊤
    · have hN' : N' = ⊤ := by
        subst hN
        rw [ENNReal.mul_top hd'] at I3
        by_contra h
        exact absurd (top_le_iff.mp I3) (by finiteness)
      subst hN hN'
      have e1 : ((P' : EReal)) = ((P'.toReal : ℝ) : EReal) := (EReal.coe_ennreal_toReal hP').symm
      have e2 : ((P : EReal)) = ((P.toReal : ℝ) : EReal) := (EReal.coe_ennreal_toReal hP).symm
      rw [e1, e2, EReal.coe_ennreal_top, EReal.neg_top, EReal.add_bot, EReal.add_bot,
        EReal.coe_mul_bot_of_pos hd, EReal.add_bot]
    · have hN' : N' ≠ ⊤ := by
        intro h
        rw [h, top_le_iff] at I4
        exact absurd I4 (by finiteness)
      rw [← EReal.coe_ennreal_toReal hP', ← EReal.coe_ennreal_toReal hN',
        ← EReal.coe_ennreal_toReal hP, ← EReal.coe_ennreal_toReal hN]
      have HR := congrArg ENNReal.toReal H
      rw [ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness)] at HR
      simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal', max_eq_left hd.le] at HR
      have hc : max c 0 - max (-c) 0 = c := by
        rcases le_total c 0 with h | h <;> simp [h]
      have : P'.toReal + -N'.toReal = c + d * (P.toReal + -Nn.toReal) := by
        linarith
      rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_mul,
        ← EReal.coe_add, this]

theorem eI_affine {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (F : E → EReal) (hF : Measurable F) (c d : ℝ) (hd : 0 < d) :
    eI μ (fun x => (c : EReal) + (d : EReal) * F x) = (c : EReal) + (d : EReal) * eI μ F := by
  have m1 : Measurable (fun x => pp ((c : EReal) + (d : EReal) * F x)) := by
    unfold pp; fun_prop
  have m2 : Measurable (fun x => nn ((c : EReal) + (d : EReal) * F x)) := by
    unfold nn; fun_prop
  have m3 : Measurable (fun x => pp (F x)) := by unfold pp; fun_prop
  have m4 : Measurable (fun x => nn (F x)) := by unfold nn; fun_prop
  unfold eI
  beta_reduce
  apply final c d hd
  · have := congrArg (fun f => ∫⁻ x, f x ∂μ) (funext (fun x => ptwise c d hd (F x)))
    simp only at this
    rw [lintegral_add_right _ measurable_const, lintegral_add_left m1,
      lintegral_add_right _ measurable_const, lintegral_add_left m2,
      lintegral_const_mul _ m4, lintegral_const_mul _ m3, lintegral_const, lintegral_const,
      measure_univ, mul_one, mul_one] at this
    exact this
  · have := lintegral_mono (μ := μ) (fun x => ineq1 c d hd (F x))
    rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ m3, lintegral_const,
      measure_univ, mul_one] at this
    exact this
  · have := lintegral_mono (μ := μ) (fun x => ineq2 c d hd (F x))
    rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ m3, lintegral_const,
      measure_univ, mul_one] at this
    exact this
  · have := lintegral_mono (μ := μ) (fun x => ineq3 c d hd (F x))
    rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ m4, lintegral_const,
      measure_univ, mul_one] at this
    exact this
  · have := lintegral_mono (μ := μ) (fun x => ineq4 c d hd (F x))
    rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ m4, lintegral_const,
      measure_univ, mul_one] at this
    exact this

end AffineAux

namespace StatRIAux

open AffineAux

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

theorem eI_eq (μ : Measure E) (v : E → EReal) : erealIntegral μ v = eI μ v := rfl

theorem distrib (d r β : ℝ) (hd : 0 < d) (hβ : 0 < β) (I : EReal) :
    (d : EReal) * ((r : EReal) + (β : EReal) * I) = ((d * r : ℝ) : EReal) + ((d * β : ℝ) : EReal) * I := by
  induction I using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos hβ, EReal.add_bot, EReal.coe_mul_bot_of_pos hd,
      EReal.coe_mul_bot_of_pos (mul_pos hd hβ), EReal.add_bot]
  | top =>
    rw [EReal.coe_mul_top_of_pos hβ, EReal.coe_add_top, EReal.coe_mul_top_of_pos hd,
      EReal.coe_mul_top_of_pos (mul_pos hd hβ), EReal.coe_add_top]
  | coe t =>
    simp only [← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    ring

theorem acc_lin (M : StationaryMarkovDecisionModel E A) (term : E → EReal)
    (hterm : Measurable term) :
    ∀ k (π : ℕ → E → A), (∀ j < k, Measurable (π j)) →
      (Measurable (fun x => EFromToAcc M π term k x 0 1)) ∧
      ∀ (a d : ℝ), 0 < d → ∀ x, EFromToAcc M π term k x (a : EReal) d =
        (a : EReal) + (d : EReal) * EFromToAcc M π term k x 0 1 := by
  intro k
  induction k with
  | zero =>
    intro π _
    refine ⟨?_, fun a d _ x => ?_⟩
    · simp only [EFromToAcc, zero_add, EReal.coe_one, one_mul]
      exact hterm
    · simp only [EFromToAcc, zero_add, EReal.coe_one, one_mul]
  | succ k ih =>
    intro π hπ
    obtain ⟨hmeas, hlin⟩ := ih (fun j => π (j + 1)) (fun j hj => hπ (j + 1) (by omega))
    have hprob := M.hQ_prob
    have key : ∀ (a d : ℝ), 0 < d → ∀ x, EFromToAcc M π term (k + 1) x (a : EReal) d =
        ((a + d * M.r (x, π 0 x) : ℝ) : EReal) + ((d * M.β : ℝ) : EReal) *
          erealIntegral (M.Q (x, π 0 x))
            (fun x' => EFromToAcc M (fun j => π (j + 1)) term k x' 0 1) := by
      intro a d hd x
      have : (fun x' => EFromToAcc M (fun j => π (j + 1)) term k x'
          ((a : EReal) + (d : EReal) * (M.r (x, π 0 x) : EReal)) (d * M.β)) =
          fun x' => ((a + d * M.r (x, π 0 x) : ℝ) : EReal) +
            ((d * M.β : ℝ) : EReal) * EFromToAcc M (fun j => π (j + 1)) term k x' 0 1 := by
        funext x'
        rw [← EReal.coe_mul, ← EReal.coe_add, hlin _ _ (mul_pos hd M.hβ_pos)]
      simp only [EFromToAcc]
      rw [this, eI_eq, eI_affine _ _ hmeas _ _ (mul_pos hd M.hβ_pos), ← eI_eq]
    refine ⟨?_, fun a d hd x => ?_⟩
    · have e : (fun x => EFromToAcc M π term (k + 1) x 0 1) = fun x =>
          ((0 + 1 * M.r (x, π 0 x) : ℝ) : EReal) + ((1 * M.β : ℝ) : EReal) *
            erealIntegral (M.Q (x, π 0 x))
              (fun x' => EFromToAcc M (fun j => π (j + 1)) term k x' 0 1) := by
        funext x
        rw [← key 0 1 one_pos, EReal.coe_zero]
      rw [e]
      have hpm : Measurable (fun x => (x, π 0 x)) := measurable_id.prodMk (hπ 0 (by omega))
      have hr : Measurable (fun x => ((0 + 1 * M.r (x, π 0 x) : ℝ) : EReal)) :=
        measurable_coe_real_ereal.comp (measurable_const.add
          (measurable_const.mul (M.hr_meas.comp hpm)))
      have h1 : Measurable (fun x => ∫⁻ x', (EFromToAcc M (fun j => π (j + 1)) term k x' 0 1 ⊔ 0).toENNReal
          ∂(M.Q (x, π 0 x))) := by
        have := Measurable.lintegral_kernel (κ := M.Q)
          (f := fun x' => (EFromToAcc M (fun j => π (j + 1)) term k x' 0 1 ⊔ 0).toENNReal)
          (by fun_prop)
        exact this.comp hpm
      have h2 : Measurable (fun x => ∫⁻ x',
          ((-EFromToAcc M (fun j => π (j + 1)) term k x' 0 1) ⊔ 0).toENNReal
          ∂(M.Q (x, π 0 x))) := by
        have := Measurable.lintegral_kernel (κ := M.Q)
          (f := fun x' => ((-EFromToAcc M (fun j => π (j + 1)) term k x' 0 1) ⊔ 0).toENNReal)
          (by fun_prop)
        exact this.comp hpm
      unfold erealIntegral
      exact hr.add (measurable_const.mul ((measurable_coe_ennreal_ereal.comp h1).add
        (measurable_coe_ennreal_ereal.comp h2).neg))
    · have k0 := key 0 1 one_pos x
      rw [EReal.coe_zero] at k0
      rw [key a d hd, k0, zero_add, one_mul, one_mul, distrib d _ _ hd M.hβ_pos, ← add_assoc,
        ← EReal.coe_add]

end StatRIAux

open StatRIAux in
theorem solution {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : StationaryMarkovDecisionModel E A) (N : ℕ) (hAN : IntegrabilityAssumption M N)
    (π : ℕ → E → A) (n : ℕ) (hn : n ≤ N) (hπ : IsPolicySeq M n π) :
    Jpi M π n = TfComposeChain M π n (fun x => (M.g x : EReal)) := by
  have hg : Measurable (fun x => (M.g x : EReal)) := measurable_coe_real_ereal.comp M.hg_meas
  clear hAN hn
  induction n generalizing π with
  | zero =>
    funext x
    simp [Jpi, EFromToAcc, TfComposeChain]
  | succ n ih =>
    have hπ' : IsPolicySeq M n (fun j => π (j + 1)) := fun j hj => hπ (j + 1) (by omega)
    have hm : ∀ j < n, Measurable ((fun j => π (j + 1)) j) := fun j hj => (hπ' j hj).1
    obtain ⟨hmeas, hlin⟩ := acc_lin M _ hg n (fun j => π (j + 1)) hm
    funext x
    have e1 : Jpi M π (n + 1) x = erealIntegral (M.Q (x, π 0 x))
        (fun x' => ((M.r (x, π 0 x) : ℝ) : EReal) + (M.β : EReal) *
          Jpi M (fun j => π (j + 1)) n x') := by
      show erealIntegral (M.Q (x, π 0 x)) (fun x' => EFromToAcc M (fun j => π (j + 1))
        (fun x => (M.g x : EReal)) n x' (0 + ((1 : ℝ) : EReal) * (M.r (x, π 0 x) : EReal))
          (1 * M.β)) = _
      congr 1
      funext x'
      rw [EReal.coe_one, one_mul, zero_add, one_mul, hlin _ _ M.hβ_pos]
      rfl
    have hP := M.hQ_prob (x, π 0 x)
    rw [e1, eI_eq, AffineAux.eI_affine _ (fun x' => Jpi M (fun j => π (j + 1)) n x') hmeas _ _ M.hβ_pos, ← eI_eq, ih _ hπ']
    rfl

#print axioms solution
