-- Prove2me | solution 1 for KeskinZeevi.SufficientConditions.regret_eq_neg_beta_sum_sqErr
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:52:16.576994+00:00
-- url     : https://prove2.me/submissions/77e5479d-23dc-453c-b3d8-4e5b50ccf9a4

import Mathlib
import Definitions.Def_RobustBooking_Shared_Noise
import Definitions.Def_KeskinZeevi_SufficientConditions_Regret
open RobustBooking.Shared
open MeasureTheory ProbabilityTheory

namespace Aux_KZ_regret
open KeskinZeevi.SufficientConditions

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

end Aux_KZ_regret

open KeskinZeevi.SufficientConditions in
theorem solution (M : Model) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (σ : ℝ)
    (hε : LightTailedNoise P ε σ) (π : Policy M) (θ : ℝ × ℝ) (hθ : θ ∈ M.Theta) (T : ℕ) :
    regret π θ ε P T =
      -θ.2 * ∑ t ∈ Finset.Icc 1 T, ∫ ω, (price π θ ε t ω - phi θ) ^ 2 ∂P := by
  have hb : θ.2 < 0 := lt_of_le_of_lt hθ.2.2 M.bMax_neg
  have hb0 : θ.2 ≠ 0 := hb.ne
  have hpt : ∀ p, revenue θ p = optRevenue θ + θ.2 * (p - phi θ) ^ 2 := by
    intro p
    unfold optRevenue revenue phi
    field_simp
    ring
  have hmeas : ∀ t, Measurable (fun ω => price π θ ε t ω) := fun t =>
    Aux_KZ_regret.priceAux_meas π θ ε hε.measurable (t - 1)
  have hint : ∀ t, Integrable (fun ω => (price π θ ε t ω - phi θ) ^ 2) P := by
    intro t
    refine Integrable.of_bound (((hmeas t).sub measurable_const).pow_const 2).aestronglyMeasurable
      ((M.u + |phi θ|) ^ 2) (Filter.Eventually.of_forall (fun ω => ?_))
    have hm := Aux_KZ_regret.price_mem π θ ε t ω
    have h0 := M.zero_le_l
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : |price π θ ε t ω - phi θ| ≤ M.u + |phi θ| := by
      calc |price π θ ε t ω - phi θ| ≤ |price π θ ε t ω| + |phi θ| := abs_sub _ _
        _ ≤ M.u + |phi θ| := by
          rw [abs_of_nonneg (by linarith [hm.1])]
          linarith [hm.2]
    calc (price π θ ε t ω - phi θ) ^ 2 = |price π θ ε t ω - phi θ| ^ 2 := (sq_abs _).symm
      _ ≤ (M.u + |phi θ|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hid : ∀ ω, ∑ t ∈ Finset.Icc 1 T, revenue θ (price π θ ε t ω) =
      T * optRevenue θ + θ.2 * ∑ t ∈ Finset.Icc 1 T, (price π θ ε t ω - phi θ) ^ 2 := by
    intro ω
    simp only [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Finset.mul_sum]
    simp
  unfold regret
  simp_rw [hid]
  rw [integral_add (integrable_const _)
    ((integrable_finset_sum _ (fun t _ => hint t)).const_mul θ.2)]
  rw [integral_const, probReal_univ, one_smul, integral_const_mul, integral_finset_sum _
    (fun t _ => hint t)]
  ring
