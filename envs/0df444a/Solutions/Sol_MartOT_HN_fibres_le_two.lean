-- Prove2me | solution 1 for MartOT.HN.fibres_le_two
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:44:55.580544+00:00
-- url     : https://prove2.me/submissions/7292d6d4-d039-470f-a80a-0d754e855867

import Mathlib
import Definitions.Def_MartOT_Var_Setting

open MeasureTheory

lemma hn73bd_cost_eq (ρ : Measure (ℝ × ℝ)) :
    MartOT.Var.cost (fun x y => -|y - x|) ρ =
      -((∫⁻ p, ENNReal.ofReal |p.2 - p.1| ∂ρ : ENNReal) : EReal) := by
  unfold MartOT.Var.cost MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have h1 : ∀ p : ℝ × ℝ, ((-|p.2 - p.1| : ℝ) : EReal).toENNReal = 0 := by
    intro p
    apply EReal.toENNReal_of_nonpos
    exact_mod_cast neg_nonpos.mpr (abs_nonneg _)
  have h2 : ∀ p : ℝ × ℝ, (-((-|p.2 - p.1| : ℝ) : EReal)).toENNReal =
      ENNReal.ofReal |p.2 - p.1| := fun p => by
    rw [← EReal.coe_neg, neg_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _),
      EReal.toReal_coe]
  simp only [h1, h2, lintegral_zero, EReal.coe_ennreal_zero, zero_sub]

/-- The quadrant `x ≥ 0 ≥ y`, below the diagonal. -/
def hn73bdQ : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.2 ≤ 0}

lemma hn73bdQ_meas : MeasurableSet hn73bdQ :=
  (measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_snd measurable_const)

/-- On the quadrant, `∫ |y - x|` only depends on the two marginals. -/
lemma hn73bd_lint (ρ : Measure (ℝ × ℝ)) (hρ : ρ hn73bdQᶜ = 0) :
    (∫⁻ p, ENNReal.ofReal |p.2 - p.1| ∂ρ) =
      (∫⁻ x, ENNReal.ofReal x ∂(ρ.map Prod.fst)) + ∫⁻ y, ENNReal.ofReal (-y) ∂(ρ.map Prod.snd) := by
  rw [lintegral_map (ENNReal.measurable_ofReal) measurable_fst,
    lintegral_map (f := fun y : ℝ => ENNReal.ofReal (-y)) (by fun_prop) measurable_snd,
    ← lintegral_add_left (f := fun p : ℝ × ℝ => ENNReal.ofReal p.1) (by fun_prop)]
  apply lintegral_congr_ae
  have hae : ∀ᵐ p ∂ρ, p ∈ hn73bdQ := by
    rw [ae_iff]; simpa [Set.compl_def] using hρ
  filter_upwards [hae] with p hp
  obtain ⟨h1, h2⟩ := hp
  rw [abs_of_nonpos (by linarith), ← ENNReal.ofReal_add h1 (by linarith)]
  congr 1; ring

/-- Any set below the diagonal quadrant has the variational property for `-|y - x|`: all
competitors have the same cost. -/
lemma hn73bd_var (Γ : Set (ℝ × ℝ)) (hΓQ : Γ ⊆ hn73bdQ) :
    ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
      ∀ α' : Measure (ℝ × ℝ),
        MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        MartOT.Var.cost (fun x y => -|y - x|) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
          MartOT.Var.cost (fun x y => -|y - x|) α' := by
  intro S w hS α' hc
  set α := ∑ p ∈ S, (w p : ENNReal) • Measure.dirac p with hα
  have hαQ : α hn73bdQᶜ = 0 := by
    rw [hα, Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero (fun p hp => ?_)
    rw [Measure.smul_apply, Measure.dirac_apply' _ hn73bdQ_meas.compl]
    have : p ∈ hn73bdQ := hΓQ (hS hp)
    simp [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr this)]
  obtain ⟨h1, h2, -⟩ := hc
  have hα'Q : α' hn73bdQᶜ = 0 := by
    have hsub : hn73bdQᶜ ⊆ Prod.fst ⁻¹' Set.Iio 0 ∪ Prod.snd ⁻¹' Set.Ioi 0 := by
      intro p hp
      simp only [hn73bdQ, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_le] at hp
      rcases hp with h | h
      · exact Or.inl h
      · exact Or.inr h
    have e1 : α' (Prod.fst ⁻¹' Set.Iio 0) = 0 := by
      rw [← Measure.map_apply measurable_fst measurableSet_Iio, ← h1,
        Measure.map_apply measurable_fst measurableSet_Iio]
      refine measure_mono_null (fun p hp => ?_) hαQ
      exact fun hq => absurd hq.1 (not_le.mpr hp)
    have e2 : α' (Prod.snd ⁻¹' Set.Ioi 0) = 0 := by
      rw [← Measure.map_apply measurable_snd measurableSet_Ioi, ← h2,
        Measure.map_apply measurable_snd measurableSet_Ioi]
      refine measure_mono_null (fun p hp => ?_) hαQ
      exact fun hq => absurd hq.2 (not_le.mpr hp)
    exact measure_mono_null hsub (measure_union_null e1 e2)
  rw [hn73bd_cost_eq, hn73bd_cost_eq, hn73bd_lint α hαQ, hn73bd_lint α' hα'Q, h1, h2]

/-- Disproof of `MartOT.HN.fibres_le_two`. -/
theorem solution : ¬ (∀ (μ : Measure ℝ), (∀ x : ℝ, μ {x} = 0) → ∀ (Γ : Set (ℝ × ℝ)),
    (∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
      ∀ α' : Measure (ℝ × ℝ),
        MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        MartOT.Var.cost (fun x y => -|y - x|) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
          MartOT.Var.cost (fun x y => -|y - x|) α') →
    {a : ℝ | 2 < {y : ℝ | (a, y) ∈ Γ}.encard}.Countable ∧
      μ {a : ℝ | 2 < {y : ℝ | (a, y) ∈ Γ}.encard} = 0) := by
  intro h
  set Γ : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ ({-1, -2, -3} : Set ℝ) with hΓ
  have hQ : Γ ⊆ hn73bdQ := by
    rintro ⟨a, y⟩ ⟨ha, hy⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    refine ⟨ha.1, ?_⟩
    rcases hy with rfl | rfl | rfl <;> norm_num
  have hc := (h 0 (fun _ => rfl) Γ (hn73bd_var Γ hQ)).1
  have h3 : ({-1, -2, -3} : Set ℝ).encard = 3 := by
    rw [Set.encard_insert_of_notMem (by norm_num), Set.encard_pair (by norm_num)]
    rfl
  have hsub : Set.Icc (0:ℝ) 1 ⊆ {a : ℝ | 2 < {y : ℝ | (a, y) ∈ Γ}.encard} := by
    intro a ha
    show 2 < {y : ℝ | (a, y) ∈ Γ}.encard
    have : {y : ℝ | (a, y) ∈ Γ} = ({-1, -2, -3} : Set ℝ) := by
      ext y; simp [hΓ, Set.mem_prod, ha.1, ha.2]
    rw [this, h3]
    decide
  have hz := (hc.mono hsub).measure_zero volume
  rw [Real.volume_Icc] at hz
  norm_num at hz
