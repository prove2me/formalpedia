-- Prove2me | solution 1 for KeskinZeevi.IncumbentLowerBound.cumulative_pricing_error_lower_bound_linear
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T08:57:07.820084+00:00
-- url     : https://prove2.me/submissions/86169ec3-290e-4e73-8d1a-24cf183a3d00

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Model
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Policy
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Regret
import Theorems.Thm_KeskinZeevi_IncumbentLowerBound_cumulative_pricing_error_lower_bound
open RobustBooking.Shared
open MeasureTheory
open KeskinZeevi.IncumbentLowerBound

namespace KZILBLin

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

end KZILBLin

open KZILBLin in
theorem solution (M : Model) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ), GaussianNoise M.σ P ε →
      ∀ (π : Policy M.l M.u) (T : ℕ),
        ∑ t ∈ Finset.Ico 1 T, c₀ / (c₁ + (M.u - M.l) ^ 2 * (t : ℝ))
          ≤ ⨆ β : M.Bexcl, ∑ t ∈ Finset.Ico 1 T, sqErr M P ε π (β : ℝ) t := by
  obtain ⟨c₀, hc₀, c₁, hc₁, h⟩ := cumulative_pricing_error_lower_bound M
  refine ⟨c₀, hc₀, c₁, hc₁, ?_⟩
  intro Ω _ P _ ε hε π T
  refine le_trans (Finset.sum_le_sum fun t _ => ?_) (h P ε hε π T)
  have hne : Nonempty M.B := ⟨⟨M.bMin, le_refl _, M.bMin_lt_bMax.le⟩⟩
  have hinfo : ∀ β : M.B, expInfo M P ε π (β : ℝ) t ≤ (M.u - M.l) ^ 2 * t := by
    intro β
    have : ∫ ω, ∑ s ∈ Finset.range t, (dev M π β ε s ω) ^ 2 ∂P
        ≤ ∫ _ω, ∑ s ∈ Finset.range t, (M.u - M.l) ^ 2 ∂P := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun s _ => sq_nonneg _)
        (integrable_const _) (Filter.Eventually.of_forall fun ω => ?_)
      refine Finset.sum_le_sum fun s _ => ?_
      have := sq_le_of_mem M _ _ (dev_mem M π β ε s ω) (show (0:ℝ) ∈ _ from
        ⟨by linarith [M.pHat_mem.1], by linarith [M.pHat_mem.2]⟩)
      simpa using this
    simp only [expInfo]
    refine this.trans (le_of_eq ?_)
    simp [mul_comm]
  have hsup : ⨆ β : M.B, expInfo M P ε π (β : ℝ) t ≤ (M.u - M.l) ^ 2 * t :=
    ciSup_le hinfo
  have hsup0 : 0 ≤ ⨆ β : M.B, expInfo M P ε π (β : ℝ) t :=
    Real.iSup_nonneg fun β => integral_nonneg fun ω =>
      Finset.sum_nonneg fun s _ => sq_nonneg _
  exact div_le_div_of_nonneg_left hc₀.le (by positivity) (by linarith)
