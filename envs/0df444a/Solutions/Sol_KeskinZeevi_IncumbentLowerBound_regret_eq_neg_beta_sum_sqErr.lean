-- Prove2me | solution 1 for KeskinZeevi.IncumbentLowerBound.regret_eq_neg_beta_sum_sqErr
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T08:57:07.118625+00:00
-- url     : https://prove2.me/submissions/734623c3-9a07-4ba9-b124-96ae0afcb9aa

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Model
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Policy
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Regret
import Theorems.Thm_KeskinZeevi_IncumbentLowerBound_cumulative_pricing_error_lower_bound_linear
open RobustBooking.Shared
open MeasureTheory
open KeskinZeevi.IncumbentLowerBound

namespace KZILBRegEq

lemma pricePath_eq (M : Model) (π : Policy M.l M.u) (β : ℝ) (e : ℕ → ℝ) (t : ℕ) :
    pricePath M π β e t = π.rule t (fun i : Fin t =>
      (M.DHat + β * (pricePath M π β e i - M.pHat) + e i, pricePath M π β e i)) := by
  rw [pricePath]

lemma pricePath_mem (M : Model) (π : Policy M.l M.u) (β : ℝ) (e : ℕ → ℝ) (t : ℕ) :
    pricePath M π β e t ∈ Set.Icc M.l M.u := by
  rw [pricePath_eq]; exact π.rule_mem _ _

lemma measurable_pricePath {Ω : Type*} [MeasurableSpace Ω] (M : Model) (π : Policy M.l M.u)
    (β : ℝ) (ε : ℕ → Ω → ℝ) (hε : ∀ t, Measurable (ε t)) :
    ∀ t, Measurable (fun ω => pricePath M π β (fun s => ε s ω) t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    simp_rw [pricePath_eq M π β _ t]
    refine (π.measurable_rule t).comp ?_
    refine measurable_pi_lambda _ fun i => ?_
    have hi := ih i i.isLt
    exact (((measurable_const.add (measurable_const.mul (hi.sub measurable_const))).add
      (hε i))).prodMk hi

lemma measurable_dev {Ω : Type*} [MeasurableSpace Ω] (M : Model) (π : Policy M.l M.u)
    (β : ℝ) (ε : ℕ → Ω → ℝ) (hε : ∀ t, Measurable (ε t)) (t : ℕ) :
    Measurable (dev M π β ε t) :=
  (measurable_pricePath M π β ε hε t).sub measurable_const

lemma dev_mem {Ω : Type*} [MeasurableSpace Ω] (M : Model) (π : Policy M.l M.u)
    (β : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    dev M π β ε t ω ∈ Set.Icc (M.l - M.pHat) (M.u - M.pHat) := by
  have := pricePath_mem M π β (fun s => ε s ω) t
  simp only [dev, Set.mem_Icc] at this ⊢
  constructor <;> linarith [this.1, this.2]

lemma optDev_mem (M : Model) (β : ℝ) (hβ : β ∈ M.B) :
    M.optDev β ∈ Set.Icc (M.l - M.pHat) (M.u - M.pHat) := by
  have := M.interior β hβ
  simp only [Model.optDev, Set.mem_Icc]
  constructor <;> linarith [this.1, this.2]

lemma sq_le_of_mem (M : Model) (a b : ℝ) (ha : a ∈ Set.Icc (M.l - M.pHat) (M.u - M.pHat))
    (hb : b ∈ Set.Icc (M.l - M.pHat) (M.u - M.pHat)) : (a - b) ^ 2 ≤ (M.u - M.l) ^ 2 := by
  obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
  have h1 : |a - b| ≤ M.u - M.l := abs_le.mpr ⟨by linarith, by linarith⟩
  have := sq_le_sq' (neg_le_of_abs_le h1) (le_of_abs_le h1)
  exact this

lemma revenue_gap (M : Model) (β x : ℝ) (hβ : β ≠ 0) :
    M.revenue β (M.optDev β) - M.revenue β x = -β * (x - M.optDev β) ^ 2 := by
  simp only [Model.revenue, Model.optDev]
  field_simp
  ring

lemma regret_eq {Ω : Type*} [MeasurableSpace Ω] (M : Model) (P : Measure Ω)
    [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (hε : ∀ t, Measurable (ε t))
    (π : Policy M.l M.u) (β : ℝ) (hβ : β ∈ M.B) (T : ℕ) :
    regret M P ε π β T = -β * ∑ t ∈ Finset.range T, sqErr M P ε π β t := by
  have hβ0 : β ≠ 0 := by
    have := hβ.2; have := M.bMax_neg; exact (by linarith : β < 0).ne
  have hint : ∀ t, Integrable (fun ω => M.revenue β (dev M π β ε t ω)) P := by
    intro t
    have hm := measurable_dev M π β ε hε t
    have hmeas : Measurable (fun ω => M.revenue β (dev M π β ε t ω)) := by
      simp only [Model.revenue]
      exact (measurable_const.add hm).mul (measurable_const.add (measurable_const.mul hm))
    -- bounded by continuity on a compact set
    obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ Set.Icc (M.l - M.pHat) (M.u - M.pHat),
        ‖M.revenue β x‖ ≤ C := by
      have hc : Continuous (fun x => M.revenue β x) := by
        simp only [Model.revenue]; fun_prop
      obtain ⟨C, hC⟩ := (isCompact_Icc.image hc).isBounded.exists_norm_le
      exact ⟨C, fun x hx => hC _ ⟨x, hx, rfl⟩⟩
    exact Integrable.of_bound hmeas.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => hC _ (dev_mem M π β ε t ω))
  have hint2 : ∀ t, Integrable (fun ω => (dev M π β ε t ω - M.optDev β) ^ 2) P := by
    intro t
    have hm := measurable_dev M π β ε hε t
    refine Integrable.of_bound ((hm.sub measurable_const).pow_const 2).aestronglyMeasurable
      ((M.u - M.l) ^ 2) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_of_mem M _ _ (dev_mem M π β ε t ω) (optDev_mem M β hβ)
  unfold regret expRevenue sqErr
  rw [integral_finsetSum _ (fun t _ => hint t), Finset.mul_sum]
  have : (T : ℝ) * M.revenue β (M.optDev β)
      = ∑ t ∈ Finset.range T, ∫ _ω, M.revenue β (M.optDev β) ∂P := by
    simp
  rw [this, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← integral_sub (integrable_const _) (hint t), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  exact revenue_gap M β _ hβ0

end KZILBRegEq

open KZILBRegEq in
theorem solution (M : Model) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ), GaussianNoise M.σ P ε →
      ∀ (π : Policy M.l M.u) (T : ℕ),
        worstRegret M P ε π T
            = ⨆ β : M.Bexcl, -(β : ℝ) * ∑ t ∈ Finset.range T, sqErr M P ε π (β : ℝ) t ∧
          |M.bMax| * ∑ t ∈ Finset.Ico 1 T, c₀ / (c₁ + (M.u - M.l) ^ 2 * (t : ℝ))
            ≤ worstRegret M P ε π T := by
  obtain ⟨c₀, hc₀, c₁, hc₁, h⟩ := cumulative_pricing_error_lower_bound_linear M
  refine ⟨c₀, hc₀, c₁, hc₁, ?_⟩
  intro Ω _ P _ ε hε π T
  have hlin := h P ε hε π T
  have heq : worstRegret M P ε π T
      = ⨆ β : M.Bexcl, -(β : ℝ) * ∑ t ∈ Finset.range T, sqErr M P ε π (β : ℝ) t := by
    unfold worstRegret
    exact iSup_congr fun β => regret_eq M P ε hε.measurable π β β.2.1 T
  refine ⟨heq, ?_⟩
  rw [heq]
  have hsq : ∀ (β : M.Bexcl) t, 0 ≤ sqErr M P ε π (β : ℝ) t := fun β t =>
    integral_nonneg fun ω => sq_nonneg _
  have hsqle : ∀ (β : M.Bexcl) t, sqErr M P ε π (β : ℝ) t ≤ (M.u - M.l) ^ 2 := by
    intro β t
    have : ∫ ω, (dev M π β ε t ω - M.optDev β) ^ 2 ∂P ≤ ∫ _ω, (M.u - M.l) ^ 2 ∂P := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
        (integrable_const _) (Filter.Eventually.of_forall fun ω => ?_)
      exact sq_le_of_mem M _ _ (dev_mem M π β ε t ω) (optDev_mem M β β.2.1)
    simpa [sqErr] using this
  have hbdd : BddAbove (Set.range fun β : M.Bexcl =>
      -(β : ℝ) * ∑ t ∈ Finset.range T, sqErr M P ε π (β : ℝ) t) := by
    refine ⟨-M.bMin * (T * (M.u - M.l) ^ 2), ?_⟩
    rintro _ ⟨β, rfl⟩
    have hb1 : -(β : ℝ) ≤ -M.bMin := by linarith [β.2.1.1]
    have hb2 : 0 ≤ -(β : ℝ) := by linarith [β.2.1.2, M.bMax_neg]
    have hs : ∑ t ∈ Finset.range T, sqErr M P ε π (β : ℝ) t ≤ T * (M.u - M.l) ^ 2 := by
      calc _ ≤ ∑ t ∈ Finset.range T, (M.u - M.l) ^ 2 := Finset.sum_le_sum fun t _ => hsqle β t
        _ = _ := by simp
    have hs0 : 0 ≤ ∑ t ∈ Finset.range T, sqErr M P ε π (β : ℝ) t :=
      Finset.sum_nonneg fun t _ => hsq β t
    exact mul_le_mul hb1 hs hs0 (by linarith)
  calc |M.bMax| * ∑ t ∈ Finset.Ico 1 T, c₀ / (c₁ + (M.u - M.l) ^ 2 * (t : ℝ))
      ≤ |M.bMax| * ⨆ β : M.Bexcl, ∑ t ∈ Finset.Ico 1 T, sqErr M P ε π (β : ℝ) t :=
        mul_le_mul_of_nonneg_left hlin (abs_nonneg _)
    _ = ⨆ β : M.Bexcl, |M.bMax| * ∑ t ∈ Finset.Ico 1 T, sqErr M P ε π (β : ℝ) t :=
        Real.mul_iSup_of_nonneg (abs_nonneg _) _
    _ ≤ _ := by
      refine ciSup_mono hbdd fun β => ?_
      have hb : |M.bMax| ≤ -(β : ℝ) := by
        rw [abs_of_neg M.bMax_neg]; linarith [β.2.1.2]
      have hsub : ∑ t ∈ Finset.Ico 1 T, sqErr M P ε π (β : ℝ) t
          ≤ ∑ t ∈ Finset.range T, sqErr M P ε π (β : ℝ) t := by
        rw [Finset.range_eq_Ico]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left (by norm_num))
          fun t _ _ => hsq β t
      exact mul_le_mul hb hsub (Finset.sum_nonneg fun t _ => hsq β t)
        (by linarith [β.2.1.2, M.bMax_neg])
