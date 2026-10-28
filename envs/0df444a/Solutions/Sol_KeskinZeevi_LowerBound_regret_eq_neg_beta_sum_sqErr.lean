-- Prove2me | solution 1 for KeskinZeevi.LowerBound.regret_eq_neg_beta_sum_sqErr
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:16:40.666146+00:00
-- url     : https://prove2.me/submissions/916d0b6a-b863-44bd-ab06-0d2e5f6ab832

import Mathlib
import Definitions.Def_KeskinZeevi_LowerBound_Model
import Definitions.Def_KeskinZeevi_LowerBound_Policy
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_KeskinZeevi_LowerBound_Regret

open RobustBooking.Shared
open MeasureTheory

namespace Aux_KZLB_regret
open KeskinZeevi.LowerBound

lemma price_meas {l u : ℝ} {Ω : Type*} [MeasurableSpace Ω] (π : Policy l u) (θ : ℝ × ℝ)
    (ε : ℕ → Ω → ℝ) (hε : ∀ t, Measurable (ε t)) (n : ℕ) :
    Measurable (fun ω => price π θ ε n ω) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h : (fun ω => price π θ ε n ω) = fun ω => π.rule n (fun i : Fin n =>
        (θ.1 + θ.2 * price π θ ε i ω + ε i ω, price π θ ε i ω)) := by
      funext ω
      unfold price
      rw [pricePath]
    rw [h]
    refine (π.measurable_rule n).comp (measurable_pi_lambda _ (fun i => ?_))
    have hi := ih i i.isLt
    exact ((measurable_const.add (measurable_const.mul hi)).add (hε _)).prodMk hi

lemma price_mem {l u : ℝ} {Ω : Type*} (π : Policy l u) (θ : ℝ × ℝ)
    (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : price π θ ε t ω ∈ Set.Icc l u := by
  unfold price
  rw [pricePath]
  exact π.rule_mem _ _

end Aux_KZLB_regret

open Aux_KZLB_regret in
open KeskinZeevi.LowerBound in
theorem solution (M : Model) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (hε : GaussianNoise M.σ P ε)
    (π : Policy M.l M.u) :
    (∀ θ ∈ M.Θ, ∀ T : ℕ,
        regret P ε π θ T = -θ.2 * ∑ t ∈ Finset.range T, sqErr P ε π θ t) ∧
      ∀ T : ℕ,
        |M.bMax| * ⨆ θ : M.Θ, ∑ t ∈ Finset.Ico 1 T, sqErr P ε π (θ : ℝ × ℝ) t
          ≤ worstRegret M P ε π T := by
  have hmeas : ∀ θ t, Measurable (fun ω => price π θ ε t ω) := fun θ t =>
    price_meas π θ ε hε.measurable t
  -- bound on squared error integrand
  have hbound : ∀ θ ∈ M.Θ, ∀ t ω, (price π θ ε t ω - optPrice θ) ^ 2 ≤ (M.u - M.l) ^ 2 := by
    intro θ hθ t ω
    have hm := price_mem π θ ε t ω
    have hi := M.interior θ.1 hθ.1 θ.2 hθ.2
    have h1 : |price π θ ε t ω - optPrice θ| ≤ M.u - M.l := by
      rw [abs_le]; unfold optPrice; constructor <;> linarith [hm.1, hm.2, hi.1, hi.2]
    calc (price π θ ε t ω - optPrice θ) ^ 2 = |price π θ ε t ω - optPrice θ| ^ 2 := (sq_abs _).symm
      _ ≤ (M.u - M.l) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hint : ∀ θ ∈ M.Θ, ∀ t, Integrable (fun ω => (price π θ ε t ω - optPrice θ) ^ 2) P := by
    intro θ hθ t
    refine Integrable.of_bound
      (((hmeas θ t).sub measurable_const).pow_const 2).aestronglyMeasurable
      ((M.u - M.l) ^ 2) (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound θ hθ t ω
  have hsq0 : ∀ θ t, 0 ≤ sqErr P ε π θ t := fun θ t =>
    integral_nonneg (fun ω => sq_nonneg _)
  have hsqle : ∀ θ ∈ M.Θ, ∀ t, sqErr P ε π θ t ≤ (M.u - M.l) ^ 2 := by
    intro θ hθ t
    unfold sqErr
    calc ∫ ω, (price π θ ε t ω - optPrice θ) ^ 2 ∂P ≤ ∫ ω, (M.u - M.l) ^ 2 ∂P :=
          integral_mono (hint θ hθ t) (integrable_const _) (fun ω => hbound θ hθ t ω)
      _ = (M.u - M.l) ^ 2 := by simp
  have part1 : ∀ θ ∈ M.Θ, ∀ T : ℕ,
      regret P ε π θ T = -θ.2 * ∑ t ∈ Finset.range T, sqErr P ε π θ t := by
    intro θ hθ T
    have hb : θ.2 < 0 := lt_of_le_of_lt hθ.2.2 M.bMax_neg
    have hb0 : θ.2 ≠ 0 := hb.ne
    have hpt : ∀ p, revenue θ p = optRevenue θ + θ.2 * (p - optPrice θ) ^ 2 := by
      intro p
      unfold optRevenue revenue optPrice
      field_simp
      ring
    have hid : ∀ ω, ∑ t ∈ Finset.range T, revenue θ (price π θ ε t ω) =
        T * optRevenue θ + θ.2 * ∑ t ∈ Finset.range T, (price π θ ε t ω - optPrice θ) ^ 2 := by
      intro ω
      simp only [hpt]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Finset.mul_sum]
    unfold regret expRevenue sqErr
    simp_rw [hid]
    rw [integral_add (integrable_const _)
      ((integrable_finset_sum _ (fun t _ => hint θ hθ t)).const_mul θ.2)]
    rw [integral_const, probReal_univ, one_smul, integral_const_mul, integral_finset_sum _
      (fun t _ => hint θ hθ t)]
    ring
  refine ⟨part1, fun T => ?_⟩
  unfold worstRegret
  rw [Real.mul_iSup_of_nonneg (abs_nonneg _)]
  apply ciSup_mono
  · refine ⟨-M.bMin * (T * (M.u - M.l) ^ 2), ?_⟩
    rintro _ ⟨θ, rfl⟩
    simp only
    rw [part1 θ.1 θ.2 T]
    have hb1 : 0 ≤ -(θ : ℝ × ℝ).2 := by linarith [θ.2.2.2, M.bMax_neg]
    have hb2 : -(θ : ℝ × ℝ).2 ≤ -M.bMin := by linarith [θ.2.2.1]
    have hs : ∑ t ∈ Finset.range T, sqErr P ε π (θ : ℝ × ℝ) t ≤ T * (M.u - M.l) ^ 2 := by
      calc ∑ t ∈ Finset.range T, sqErr P ε π (θ : ℝ × ℝ) t
          ≤ ∑ _t ∈ Finset.range T, (M.u - M.l) ^ 2 :=
            Finset.sum_le_sum (fun t _ => hsqle θ.1 θ.2 t)
        _ = T * (M.u - M.l) ^ 2 := by simp
    have hs0 : 0 ≤ ∑ t ∈ Finset.range T, sqErr P ε π (θ : ℝ × ℝ) t :=
      Finset.sum_nonneg (fun t _ => hsq0 _ t)
    calc -(θ : ℝ × ℝ).2 * ∑ t ∈ Finset.range T, sqErr P ε π (θ : ℝ × ℝ) t
        ≤ -M.bMin * ∑ t ∈ Finset.range T, sqErr P ε π (θ : ℝ × ℝ) t :=
          mul_le_mul_of_nonneg_right hb2 hs0
      _ ≤ -M.bMin * (T * (M.u - M.l) ^ 2) :=
          mul_le_mul_of_nonneg_left hs (by linarith [hb1, hb2])
  · intro θ
    rw [part1 θ.1 θ.2 T]
    have hab : |M.bMax| = -M.bMax := abs_of_neg M.bMax_neg
    have hb : |M.bMax| ≤ -(θ : ℝ × ℝ).2 := by rw [hab]; linarith [θ.2.2.2]
    have hsub : ∑ t ∈ Finset.Ico 1 T, sqErr P ε π (θ : ℝ × ℝ) t ≤
        ∑ t ∈ Finset.range T, sqErr P ε π (θ : ℝ × ℝ) t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx; simp only [Finset.mem_Ico] at hx; simp only [Finset.mem_range]; omega
      · intro i _ _; exact hsq0 _ i
    have hs0 : 0 ≤ ∑ t ∈ Finset.Ico 1 T, sqErr P ε π (θ : ℝ × ℝ) t :=
      Finset.sum_nonneg (fun t _ => hsq0 _ t)
    calc |M.bMax| * ∑ t ∈ Finset.Ico 1 T, sqErr P ε π (θ : ℝ × ℝ) t
        ≤ -(θ : ℝ × ℝ).2 * ∑ t ∈ Finset.Ico 1 T, sqErr P ε π (θ : ℝ × ℝ) t :=
          mul_le_mul_of_nonneg_right hb hs0
      _ ≤ -(θ : ℝ × ℝ).2 * ∑ t ∈ Finset.range T, sqErr P ε π (θ : ℝ × ℝ) t :=
          mul_le_mul_of_nonneg_left hsub (by linarith [abs_nonneg M.bMax])
