-- Prove2me | solution 1 for MDPFinance.Bellman.verification_theorem
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:40:30.171205+00:00
-- url     : https://prove2.me/submissions/311fbfe8-d012-47b6-a9db-b202efe9d89d

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_ValueFunction

open MeasureTheory ProbabilityTheory MDPFinance.Bellman

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

namespace RewardIterAux

open AffineAux

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

theorem eI_eq (μ : Measure E) (v : E → EReal) : erealIntegral μ v = eI μ v := rfl

theorem acc_lin (M : MarkovDecisionModel E A N) (π : Policy M) (term : E → EReal)
    (hterm : Measurable term) :
    ∀ k m, m + k ≤ N →
      (Measurable (fun x => EFromToAcc M π term k m x 0)) ∧
      ∀ (a : ℝ) x, EFromToAcc M π term k m x (a : EReal) =
        (a : EReal) + EFromToAcc M π term k m x 0 := by
  intro k
  induction k with
  | zero =>
    intro m _
    refine ⟨?_, fun a x => ?_⟩
    · simp only [EFromToAcc, zero_add]
      exact hterm
    · simp only [EFromToAcc, zero_add]
  | succ k ih =>
    intro m hmk
    have hm : m < N := by omega
    obtain ⟨hmeas, hlin⟩ := ih (m + 1) (by omega)
    have hprob : ∀ xa, IsProbabilityMeasure (M.Q m xa) := M.hQ_prob m hm
    have key : ∀ (a : ℝ) x, EFromToAcc M π term (k + 1) m x (a : EReal) =
        ((a + M.r m (x, π.1 m x) : ℝ) : EReal) +
          erealIntegral (M.Q m (x, π.1 m x)) (fun x' => EFromToAcc M π term k (m + 1) x' 0) := by
      intro a x
      have : (fun x' => EFromToAcc M π term k (m + 1) x'
          ((a : EReal) + (M.r m (x, π.1 m x) : EReal))) =
          fun x' => ((a + M.r m (x, π.1 m x) : ℝ) : EReal) +
            ((1 : ℝ) : EReal) * EFromToAcc M π term k (m + 1) x' 0 := by
        funext x'
        rw [← EReal.coe_add, hlin, EReal.coe_one, one_mul]
      simp only [EFromToAcc]
      rw [this, eI_eq, eI_affine _ _ hmeas _ _ one_pos, EReal.coe_one, one_mul, ← eI_eq]
    refine ⟨?_, fun a x => ?_⟩
    · have e : (fun x => EFromToAcc M π term (k + 1) m x 0) = fun x =>
          ((0 + M.r m (x, π.1 m x) : ℝ) : EReal) +
            erealIntegral (M.Q m (x, π.1 m x)) (fun x' => EFromToAcc M π term k (m + 1) x' 0) := by
        funext x
        rw [← key, EReal.coe_zero]
      rw [e]
      have hpm : Measurable (fun x => (x, π.1 m x)) := measurable_id.prodMk (π.2.1 m)
      have hr : Measurable (fun x => ((0 + M.r m (x, π.1 m x) : ℝ) : EReal)) :=
        measurable_coe_real_ereal.comp (measurable_const.add ((M.hr_meas m hm).comp hpm))
      have h1 : Measurable (fun x => ∫⁻ x', (EFromToAcc M π term k (m + 1) x' 0 ⊔ 0).toENNReal
          ∂(M.Q m (x, π.1 m x))) := by
        have := Measurable.lintegral_kernel (κ := M.Q m)
          (f := fun x' => (EFromToAcc M π term k (m + 1) x' 0 ⊔ 0).toENNReal) (by fun_prop)
        exact this.comp hpm
      have h2 : Measurable (fun x => ∫⁻ x', ((-EFromToAcc M π term k (m + 1) x' 0) ⊔ 0).toENNReal
          ∂(M.Q m (x, π.1 m x))) := by
        have := Measurable.lintegral_kernel (κ := M.Q m)
          (f := fun x' => ((-EFromToAcc M π term k (m + 1) x' 0) ⊔ 0).toENNReal) (by fun_prop)
        exact this.comp hpm
      unfold erealIntegral
      exact hr.add ((measurable_coe_ennreal_ereal.comp h1).add
        (measurable_coe_ennreal_ereal.comp h2).neg)
    · have k0 := key 0 x
      rw [EReal.coe_zero] at k0
      rw [key, k0, zero_add, EReal.coe_add, add_assoc]

theorem vpi_step (M : MarkovDecisionModel E A N) (π : Policy M) :
    ∀ n < N, ∀ x, Vpi M π n x = Tf M n (Vpi M π (n + 1)) (π.1 n) x := by
  have hg : Measurable (fun x => (M.g x : EReal)) := measurable_coe_real_ereal.comp M.hg_meas
  intro n hn x
  have hk : N - n = (N - (n + 1)) + 1 := by omega
  obtain ⟨_, hlin⟩ := acc_lin M π _ hg (N - (n + 1)) (n + 1) (by omega)
  simp only [Vpi, EFromTo, Tf, L]
  rw [hk]
  simp only [EFromToAcc, zero_add]
  have : (fun x' => EFromToAcc M π (fun x => (M.g x : EReal)) (N - (n + 1)) (n + 1) x'
      (M.r n (x, π.1 n x) : EReal)) = fun x' => ((M.r n (x, π.1 n x) : ℝ) : EReal) +
        ((1 : ℝ) : EReal) * EFromToAcc M π (fun x => (M.g x : EReal)) (N - (n + 1)) (n + 1) x' 0 := by
    funext x'
    rw [hlin, EReal.coe_one, one_mul]
  have hP := M.hQ_prob n hn (x, π.1 n x)
  rw [this, eI_eq, AffineAux.eI_affine _ _ (acc_lin M π _ hg (N - (n + 1)) (n + 1) (by omega)).1
    _ _ one_pos, EReal.coe_one, one_mul, ← eI_eq]
  rfl

theorem vpi_N (M : MarkovDecisionModel E A N) (π : Policy M) (x : E) :
    Vpi M π N x = (M.g x : EReal) := by
  simp [Vpi, EFromTo, EFromToAcc]

theorem eI_mono (μ : Measure E) (v w : E → EReal) (h : ∀ x, v x ≤ w x) :
    erealIntegral μ v ≤ erealIntegral μ w := by
  unfold erealIntegral
  refine add_le_add ?_ (EReal.neg_le_neg_iff.mpr ?_)
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr (lintegral_mono fun x =>
      EReal.toENNReal_le_toENNReal (sup_le_sup_right (h x) _))
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr (lintegral_mono fun x =>
      EReal.toENNReal_le_toENNReal (sup_le_sup_right (EReal.neg_le_neg_iff.mpr (h x)) _))

theorem Tf_mono (M : MarkovDecisionModel E A N) (n : ℕ) (v w : E → EReal) (h : ∀ x, v x ≤ w x)
    (f : E → A) (x : E) : Tf M n v f x ≤ Tf M n w f x :=
  add_le_add le_rfl (eI_mono _ _ _ h)

theorem Tf_le_T (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (f : E → A) (x : E)
    (hf : (x, f x) ∈ M.D n) : Tf M n v f x ≤ T M n v x :=
  le_iSup₂ (f := fun a (_ : a ∈ M.Dx n x) => L M n v (x, a)) (f x) hf

end RewardIterAux

open RewardIterAux in
theorem solution {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M)
    (v : ℕ → E → EReal) (hv_IM : ∀ n, v n ∈ IM E)
    (hv_N : v N = fun x => (M.g x : EReal)) (hv_bellman : ∀ n < N, v n = T M n (v (n + 1))) :
    (∀ n ≤ N, ∀ x, V M n x ≤ v n x) ∧
    (∀ fstar : Policy M, (∀ n < N, IsMaximizer M n (v (n + 1)) (fstar.1 n)) →
        (∀ n ≤ N, v n = V M n) ∧ Vpi M fstar 0 = V M 0) := by
  have upper : ∀ π : Policy M, ∀ k n, N - n = k → n ≤ N → ∀ x, Vpi M π n x ≤ v n x := by
    intro π k
    induction k with
    | zero =>
      intro n hk hn x
      have : n = N := by omega
      subst this
      rw [vpi_N, hv_N]
    | succ k ih =>
      intro n hk hn x
      have hlt : n < N := by omega
      rw [vpi_step M π n hlt x, hv_bellman n hlt]
      exact (Tf_mono M n _ _ (ih (n + 1) (by omega) (by omega)) _ x).trans
        (Tf_le_T M n _ _ x (π.2.2 n hlt x))
  have h1 : ∀ n ≤ N, ∀ x, V M n x ≤ v n x := fun n hn x =>
    iSup_le fun π => upper π _ n rfl hn x
  refine ⟨h1, fun fstar hf => ?_⟩
  have eq : ∀ k n, N - n = k → n ≤ N → ∀ x, Vpi M fstar n x = v n x := by
    intro k
    induction k with
    | zero =>
      intro n hk hn x
      have : n = N := by omega
      subst this
      rw [vpi_N, hv_N]
    | succ k ih =>
      intro n hk hn x
      have hlt : n < N := by omega
      rw [vpi_step M fstar n hlt x, hv_bellman n hlt]
      have e : Vpi M fstar (n + 1) = v (n + 1) := funext (ih (n + 1) (by omega) (by omega))
      rw [e, (hf n hlt).2]
  have h2 : ∀ n ≤ N, v n = V M n := by
    intro n hn
    funext x
    exact le_antisymm ((eq _ n rfl hn x).symm.le.trans (le_iSup (fun π => Vpi M π n x) fstar))
      (h1 n hn x)
  refine ⟨h2, ?_⟩
  funext x
  rw [eq _ 0 rfl (Nat.zero_le _) x, h2 0 (Nat.zero_le _)]

#print axioms solution
