-- Prove2me | solution 1 for KeskinZeevi.SufficientConditions.sq_pricing_error_split
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:32:01.598318+00:00
-- url     : https://prove2.me/submissions/b80c219c-fd57-4779-8f8e-d05eb509ce47

import Mathlib
import Definitions.Def_RobustBooking_Shared_Noise
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
open RobustBooking.Shared
open MeasureTheory ProbabilityTheory

namespace Aux_KZS_split
open KeskinZeevi.SufficientConditions Matrix

lemma priceAux_meas {M : Model} {Ω : Type*} [MeasurableSpace Ω] (π : Policy M) (θ : ℝ × ℝ)
    (ε : ℕ → Ω → ℝ) (hε : ∀ t, Measurable (ε t)) (n : ℕ) :
    Measurable (fun ω => priceAux π θ ε ω n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h : (fun ω => priceAux π θ ε ω n) = fun ω => π.rule n (fun i : Fin n =>
        (θ.1 + θ.2 * priceAux π θ ε ω i + ε ((i : ℕ) + 1) ω, priceAux π θ ε ω i)) := by
      funext ω
      rw [priceAux]
    rw [h]
    refine (π.measurable_rule n).comp (measurable_pi_lambda _ (fun i => ?_))
    have hi := ih i i.isLt
    exact ((measurable_const.add (measurable_const.mul hi)).add (hε _)).prodMk hi

lemma price_mem {M : Model} {Ω : Type*} (π : Policy M) (θ : ℝ × ℝ)
    (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : price π θ ε t ω ∈ Set.Icc M.l M.u := by
  unfold price
  rw [priceAux]
  exact π.rule_mem _ _

lemma inv_mulVec_fin2 (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) :
    (A⁻¹ *ᵥ b) 0 = (A 0 0 * A 1 1 - A 0 1 * A 1 0)⁻¹ * (A 1 1 * b 0 - A 0 1 * b 1) ∧
    (A⁻¹ *ᵥ b) 1 = (A 0 0 * A 1 1 - A 0 1 * A 1 0)⁻¹ * (-A 1 0 * b 0 + A 0 0 * b 1) := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two, Matrix.det_fin_two]
  constructor <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

lemma sq_int {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (h : ∀ ω, |f ω| ≤ C) :
    Integrable (fun ω => f ω ^ 2) P := by
  refine Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (C ^ 2)
    (Filter.Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h ω) 2

end Aux_KZS_split

open KeskinZeevi.SufficientConditions Matrix in
theorem solution (M : Model) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (σ : ℝ)
    (hε : LightTailedNoise P ε σ) (π : Policy M) (θ : ℝ × ℝ) (hθ : θ ∈ M.Theta)
    (t : ℕ) (ht : 2 ≤ t) :
    ∫ ω, (phi θ - price π θ ε (t + 1) ω) ^ 2 ∂P ≤
      2 * ∫ ω, (phi θ - phi (truncEstimate π θ ε t ω)) ^ 2 ∂P +
        2 * ∫ ω, (phi (truncEstimate π θ ε t ω) - price π θ ε (t + 1) ω) ^ 2 ∂P := by
  have hp : ∀ s, Measurable (fun ω => price π θ ε s ω) := fun s =>
    Aux_KZS_split.priceAux_meas π θ ε hε.measurable (s - 1)
  have hd : ∀ s, Measurable (fun ω => demand π θ ε s ω) := fun s =>
    (measurable_const.add (measurable_const.mul (hp s))).add (hε.measurable s)
  have hA : ∀ i j, Measurable (fun ω => (fisherOf (fun s => price π θ ε s ω) t) i j) := by
    intro i j
    simp only [fisherOf, Matrix.sum_apply]
    apply Finset.measurable_sum
    intro s _
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      exact measurable_const
    · simpa using hp s
    · simpa using hp s
    · simpa using (hp s).pow_const 2
  have hb0 : Measurable (fun ω => ∑ s ∈ Finset.Icc 1 t, demand π θ ε s ω) :=
    Finset.measurable_sum _ (fun s _ => hd s)
  have hb1 : Measurable (fun ω => ∑ s ∈ Finset.Icc 1 t, demand π θ ε s ω * price π θ ε s ω) :=
    Finset.measurable_sum _ (fun s _ => (hd s).mul (hp s))
  have hls1 : Measurable (fun ω => (lsEstimate π θ ε t ω).1) := by
    have e : (fun ω => (lsEstimate π θ ε t ω).1) = fun ω =>
        (fisherOf (fun s => price π θ ε s ω) t 0 0 * fisherOf (fun s => price π θ ε s ω) t 1 1 -
          fisherOf (fun s => price π θ ε s ω) t 0 1 * fisherOf (fun s => price π θ ε s ω) t 1 0)⁻¹ *
        (fisherOf (fun s => price π θ ε s ω) t 1 1 * (∑ s ∈ Finset.Icc 1 t, demand π θ ε s ω) -
          fisherOf (fun s => price π θ ε s ω) t 0 1 *
            (∑ s ∈ Finset.Icc 1 t, demand π θ ε s ω * price π θ ε s ω)) := by
      funext ω
      simp only [lsEstimate, lsEstimateOf]
      rw [(Aux_KZS_split.inv_mulVec_fin2 _ _).1]
      simp
    rw [e]
    exact (((hA 0 0).mul (hA 1 1)).sub ((hA 0 1).mul (hA 1 0))).inv.mul
      (((hA 1 1).mul hb0).sub ((hA 0 1).mul hb1))
  have hls2 : Measurable (fun ω => (lsEstimate π θ ε t ω).2) := by
    have e : (fun ω => (lsEstimate π θ ε t ω).2) = fun ω =>
        (fisherOf (fun s => price π θ ε s ω) t 0 0 * fisherOf (fun s => price π θ ε s ω) t 1 1 -
          fisherOf (fun s => price π θ ε s ω) t 0 1 * fisherOf (fun s => price π θ ε s ω) t 1 0)⁻¹ *
        (-fisherOf (fun s => price π θ ε s ω) t 1 0 * (∑ s ∈ Finset.Icc 1 t, demand π θ ε s ω) +
          fisherOf (fun s => price π θ ε s ω) t 0 0 *
            (∑ s ∈ Finset.Icc 1 t, demand π θ ε s ω * price π θ ε s ω)) := by
      funext ω
      simp only [lsEstimate, lsEstimateOf]
      rw [(Aux_KZS_split.inv_mulVec_fin2 _ _).2]
      simp
    rw [e]
    exact (((hA 0 0).mul (hA 1 1)).sub ((hA 0 1).mul (hA 1 0))).inv.mul
      (((hA 1 0).neg.mul hb0).add ((hA 0 0).mul hb1))
  have htr1 : Measurable (fun ω => (truncEstimate π θ ε t ω).1) :=
    measurable_const.max (hls1.min measurable_const)
  have htr2 : Measurable (fun ω => (truncEstimate π θ ε t ω).2) :=
    measurable_const.max (hls2.min measurable_const)
  have hphi : Measurable (fun ω => phi (truncEstimate π θ ε t ω)) :=
    htr1.neg.div (measurable_const.mul htr2)
  -- bounds
  set Ca := |M.aMin| + |M.aMax| with hCa
  set Cφ := Ca / (2 * (-M.bMax)) with hCφ
  have hphi_bd : ∀ x : ℝ × ℝ, M.aMin ≤ x.1 → x.1 ≤ M.aMax → x.2 ≤ M.bMax → |phi x| ≤ Cφ := by
    intro x h1 h2 h3
    have hneg : x.2 < 0 := lt_of_le_of_lt h3 M.bMax_neg
    have hx1 : |x.1| ≤ Ca := by
      rw [abs_le]; constructor <;>
        linarith [neg_abs_le M.aMin, le_abs_self M.aMax, abs_nonneg M.aMin, abs_nonneg M.aMax]
    unfold phi
    rw [abs_div, abs_neg, abs_mul, abs_two, abs_of_neg hneg]
    apply div_le_div₀ (by positivity) hx1 (by linarith [M.bMax_neg])
    linarith
  have htr_mem : ∀ ω, M.aMin ≤ (truncEstimate π θ ε t ω).1 ∧ (truncEstimate π θ ε t ω).1 ≤ M.aMax ∧
      (truncEstimate π θ ε t ω).2 ≤ M.bMax := by
    intro ω
    simp only [truncEstimate, Model.truncate]
    exact ⟨le_max_left _ _, max_le M.aMin_le_aMax (min_le_right _ _),
      max_le M.bMin_le_bMax (min_le_right _ _)⟩
  have hφθ : |phi θ| ≤ Cφ := hphi_bd θ hθ.1.1 hθ.1.2 hθ.2.2
  have hφt : ∀ ω, |phi (truncEstimate π θ ε t ω)| ≤ Cφ := fun ω =>
    hphi_bd _ (htr_mem ω).1 (htr_mem ω).2.1 (htr_mem ω).2.2
  have hpr : ∀ ω, |price π θ ε (t + 1) ω| ≤ M.u := by
    intro ω
    have hm := Aux_KZS_split.price_mem π θ ε (t + 1) ω
    rw [abs_of_nonneg (by linarith [hm.1, M.zero_le_l])]
    exact hm.2
  have i1 : Integrable (fun ω => (phi θ - phi (truncEstimate π θ ε t ω)) ^ 2) P :=
    Aux_KZS_split.sq_int P _ (measurable_const.sub hphi) (Cφ + Cφ) (fun ω =>
      le_trans (abs_sub _ _) (add_le_add hφθ (hφt ω)))
  have i2 : Integrable (fun ω => (phi (truncEstimate π θ ε t ω) - price π θ ε (t + 1) ω) ^ 2) P :=
    Aux_KZS_split.sq_int P _ (hphi.sub (hp _)) (Cφ + M.u) (fun ω =>
      le_trans (abs_sub _ _) (add_le_add (hφt ω) (hpr ω)))
  have i0 : Integrable (fun ω => (phi θ - price π θ ε (t + 1) ω) ^ 2) P :=
    Aux_KZS_split.sq_int P _ (measurable_const.sub (hp _)) (Cφ + M.u) (fun ω =>
      le_trans (abs_sub _ _) (add_le_add hφθ (hpr ω)))
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul 2) (i2.const_mul 2)]
  apply integral_mono i0 ((i1.const_mul 2).add (i2.const_mul 2))
  intro ω
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (phi θ - 2 * phi (truncEstimate π θ ε t ω) + price π θ ε (t + 1) ω)]
