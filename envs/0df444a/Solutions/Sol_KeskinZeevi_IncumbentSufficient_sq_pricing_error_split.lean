-- Prove2me | solution 1 for KeskinZeevi.IncumbentSufficient.sq_pricing_error_split
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:11:02.47762+00:00
-- url     : https://prove2.me/submissions/4141213b-e9ad-4743-8965-e4cb135ff7d4

import Mathlib
import Definitions.Def_RobustBooking_Shared_Noise
import Definitions.Def_KeskinZeevi_IncumbentSufficient_LeastSquares
open RobustBooking.Shared
open MeasureTheory ProbabilityTheory

namespace Aux_KZI_split
open KeskinZeevi.IncumbentSufficient

lemma priceAux_meas {M : Model} {Ω : Type*} [MeasurableSpace Ω] (π : Policy M) (β : ℝ)
    (ε : ℕ → Ω → ℝ) (hε : ∀ t, Measurable (ε t)) (n : ℕ) :
    Measurable (fun ω => priceAux π β ε ω n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h : (fun ω => priceAux π β ε ω n) = fun ω => π.rule n (fun i : Fin n =>
        (M.DHat + β * (priceAux π β ε ω i - M.pHat) + ε ((i : ℕ) + 1) ω, priceAux π β ε ω i)) := by
      funext ω
      rw [priceAux]
    rw [h]
    refine (π.measurable_rule n).comp (measurable_pi_lambda _ (fun i => ?_))
    have hi := ih i i.isLt
    exact ((measurable_const.add (measurable_const.mul (hi.sub_const _))).add (hε _)).prodMk hi

lemma price_mem {M : Model} {Ω : Type*} (π : Policy M) (β : ℝ)
    (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : price π β ε t ω ∈ Set.Icc M.l M.u := by
  unfold price
  rw [priceAux]
  exact π.rule_mem _ _

lemma sq_int {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (h : ∀ ω, |f ω| ≤ C) :
    Integrable (fun ω => f ω ^ 2) P := by
  refine Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (C ^ 2)
    (Filter.Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h ω) 2

end Aux_KZI_split

open KeskinZeevi.IncumbentSufficient in
theorem solution (M : Model) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (σ : ℝ)
    (hε : LightTailedNoise P ε σ) (π : Policy M) (β : ℝ) (hβ : β ∈ M.B)
    (t : ℕ) (ht : 1 ≤ t) :
    ∫ ω, (M.psi β - dev π β ε (t + 1) ω) ^ 2 ∂P ≤
      2 * ∫ ω, (M.psi β - M.psi (truncEst π β ε t ω)) ^ 2 ∂P +
        2 * ∫ ω, (M.psi (truncEst π β ε t ω) - dev π β ε (t + 1) ω) ^ 2 ∂P := by
  have hdev : ∀ s, Measurable (fun ω => dev π β ε s ω) := fun s =>
    (Aux_KZI_split.priceAux_meas π β ε hε.measurable (s - 1)).sub_const _
  have hdem : ∀ s, Measurable (fun ω => demand π β ε s ω) := fun s =>
    (measurable_const.add (measurable_const.mul (hdev s))).add (hε.measurable s)
  have hJ : Measurable (fun ω => Jhat π β ε t ω) :=
    Finset.measurable_sum _ (fun s _ => (hdev s).pow_const 2)
  have hbh : Measurable (fun ω => betaHat π β ε t ω) :=
    (Finset.measurable_sum _ (fun s _ => ((hdem s).sub_const _).mul (hdev s))).div hJ
  have htr : Measurable (fun ω => truncEst π β ε t ω) :=
    measurable_const.max (hbh.min measurable_const)
  have hpsi : Measurable (fun ω => M.psi (truncEst π β ε t ω)) :=
    measurable_const.sub (measurable_const.div (measurable_const.mul htr))
  -- bounds
  have htr_mem : ∀ ω, truncEst π β ε t ω ≤ M.bMax ∧ M.bMin ≤ truncEst π β ε t ω := by
    intro ω
    unfold truncEst Model.truncate
    exact ⟨max_le (le_of_lt M.bMin_lt_bMax) (min_le_right _ _), le_max_left _ _⟩
  set Cψ := |M.pHat| / 2 + |M.DHat| / (2 * (-M.bMax)) with hCψ
  have hpsi_bd : ∀ b, b ≤ M.bMax → |M.psi b| ≤ Cψ := by
    intro b hb
    have hbneg : b < 0 := lt_of_le_of_lt hb M.bMax_neg
    unfold Model.psi psiOf
    have h1 : |-M.pHat / 2 - M.DHat / (2 * b)| ≤ |M.pHat| / 2 + |M.DHat| / (2 * |b|) := by
      calc |-M.pHat / 2 - M.DHat / (2 * b)| ≤ |-M.pHat / 2| + |M.DHat / (2 * b)| := abs_sub _ _
        _ = |M.pHat| / 2 + |M.DHat| / (2 * |b|) := by
          rw [abs_div, abs_div, abs_neg, abs_mul, abs_two]
    have h2 : |M.DHat| / (2 * |b|) ≤ |M.DHat| / (2 * (-M.bMax)) := by
      apply div_le_div_of_nonneg_left (abs_nonneg _)
      · linarith [M.bMax_neg]
      · rw [abs_of_neg hbneg]; linarith
    linarith
  have hdev_bd : ∀ ω, |dev π β ε (t + 1) ω| ≤ M.u + |M.pHat| := by
    intro ω
    have hm := Aux_KZI_split.price_mem π β ε (t + 1) ω
    have h0 := M.zero_le_l
    unfold dev
    calc |price π β ε (t + 1) ω - M.pHat| ≤ |price π β ε (t + 1) ω| + |M.pHat| := abs_sub _ _
      _ ≤ M.u + |M.pHat| := by
        rw [abs_of_nonneg (by linarith [hm.1])]; linarith [hm.2]
  have hpsiβ : |M.psi β| ≤ Cψ := hpsi_bd β hβ.2
  have i1 : Integrable (fun ω => (M.psi β - M.psi (truncEst π β ε t ω)) ^ 2) P :=
    Aux_KZI_split.sq_int P _ (measurable_const.sub hpsi) (Cψ + Cψ) (fun ω => by
      calc |M.psi β - M.psi (truncEst π β ε t ω)| ≤ |M.psi β| + |M.psi (truncEst π β ε t ω)| :=
            abs_sub _ _
        _ ≤ Cψ + Cψ := add_le_add hpsiβ (hpsi_bd _ (htr_mem ω).1))
  have i2 : Integrable (fun ω => (M.psi (truncEst π β ε t ω) - dev π β ε (t + 1) ω) ^ 2) P :=
    Aux_KZI_split.sq_int P _ (hpsi.sub (hdev _)) (Cψ + (M.u + |M.pHat|)) (fun ω => by
      calc |M.psi (truncEst π β ε t ω) - dev π β ε (t + 1) ω|
          ≤ |M.psi (truncEst π β ε t ω)| + |dev π β ε (t + 1) ω| := abs_sub _ _
        _ ≤ Cψ + (M.u + |M.pHat|) := add_le_add (hpsi_bd _ (htr_mem ω).1) (hdev_bd ω))
  have i0 : Integrable (fun ω => (M.psi β - dev π β ε (t + 1) ω) ^ 2) P :=
    Aux_KZI_split.sq_int P _ (measurable_const.sub (hdev _)) (Cψ + (M.u + |M.pHat|)) (fun ω => by
      calc |M.psi β - dev π β ε (t + 1) ω| ≤ |M.psi β| + |dev π β ε (t + 1) ω| := abs_sub _ _
        _ ≤ Cψ + (M.u + |M.pHat|) := add_le_add hpsiβ (hdev_bd ω))
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul 2) (i2.const_mul 2)]
  apply integral_mono i0 ((i1.const_mul 2).add (i2.const_mul 2))
  intro ω
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (M.psi β - 2 * M.psi (truncEst π β ε t ω) + dev π β ε (t + 1) ω)]
