-- Prove2me | solution 1 for KuhnWass2019.Reformulation.strong_duality_as_printed
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T12:58:23.698569+00:00
-- url     : https://prove2.me/submissions/4502fb79-b360-4941-b84c-9c82681ed25a

import Mathlib
import Definitions.Def_KuhnWass2019_Reformulation_RegularLoss
import Definitions.Def_KuhnWass2019_Reformulation_worstCaseRisk
import Definitions.Def_KuhnWass2019_Reformulation_moreauYosida

open MeasureTheory Set Filter
open scoped ENNReal Classical Topology
noncomputable section

namespace KuhnWass2019.Reformulation

def ceLoss (z : ℝ) : EReal := if 1 ≤ z then ⊤ else 0

lemma ceLoss_measurable : Measurable ceLoss := by
  change Measurable (fun z : ℝ => if z ∈ Ici (1 : ℝ) then (⊤ : EReal) else 0)
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma ceLoss_usc : UpperSemicontinuous ceLoss := by
  intro x y hxy
  unfold ceLoss at hxy ⊢
  by_cases hx : 1 ≤ x
  · rw [if_pos hx] at hxy
    exact False.elim (not_top_lt hxy)
  · rw [if_neg hx] at hxy
    have hopen : Iio (1 : ℝ) ∈ 𝓝 x := isOpen_Iio.mem_nhds (not_le.mp hx)
    filter_upwards [hopen] with x' hx'
    have hx'le : ¬ (1 ≤ x') := not_le.mpr hx'
    rw [if_neg hx'le]
    exact hxy

lemma ceLoss_regular : RegularLoss (Measure.dirac (0 : ℝ)) ceLoss := by
  refine ⟨ceLoss_measurable, ceLoss_usc, ?_⟩
  rw [lintegral_dirac]
  have h0 : ceLoss 0 = 0 := by
    unfold ceLoss
    norm_num
  rw [h0]
  simp

lemma moreauYosida_ceLoss_eq_top (γ x : ℝ) :
    moreauYosida (Set.univ : Set ℝ) ceLoss 1 γ x = ⊤ := by
  unfold moreauYosida
  rw [eq_top_iff]
  calc (⊤ : EReal)
    _ = ceLoss 1 - ((γ * ‖(1 : ℝ) - x‖ ^ (1 : ℝ) : ℝ) : EReal) := by
      have h1 : ceLoss 1 = ⊤ := by
        unfold ceLoss
        norm_num
      rw [h1]
      rfl
    _ ≤ ⨆ z ∈ (Set.univ : Set ℝ), (ceLoss z - ((γ * ‖z - x‖ ^ (1 : ℝ) : ℝ) : EReal)) := by
      exact le_biSup (fun z => ceLoss z - ((γ * ‖z - x‖ ^ (1 : ℝ) : ℝ) : EReal)) (mem_univ (1 : ℝ))

lemma expect_dirac_moreauYosida_eq_top (γ : ℝ) :
    DupacovaWets.Consistency.expect (Measure.dirac (0 : ℝ))
      (moreauYosida (Set.univ : Set ℝ) ceLoss 1 γ) = ⊤ := by
  unfold DupacovaWets.Consistency.expect
  have htop : (∫⁻ ξ, (moreauYosida (Set.univ : Set ℝ) ceLoss 1 γ ξ).toENNReal ∂Measure.dirac (0 : ℝ)) = ⊤ := by
    rw [lintegral_dirac, moreauYosida_ceLoss_eq_top]
    simp
  rw [if_pos htop]

lemma dual_rhs_eq_top :
    (⨅ (γ : ℝ) (_ : 0 ≤ γ),
      DupacovaWets.Consistency.expect (Measure.dirac (0 : ℝ))
        (moreauYosida (Set.univ : Set ℝ) ceLoss 1 γ) + ((γ * (0 : ℝ) ^ (1 : ℝ) : ℝ) : EReal)) = ⊤ := by
  rw [eq_top_iff]
  refine le_iInf fun γ => le_iInf fun _ => ?_
  rw [expect_dirac_moreauYosida_eq_top]
  rfl

lemma measure_Ici_le_coupling_lintegral {Q : Measure ℝ} {π : Measure (ℝ × ℝ)}
    (h1 : π.map Prod.fst = Q) (h2 : π.map Prod.snd = Measure.dirac (0 : ℝ)) :
    Q (Ici 1) ≤ ∫⁻ x : ℝ × ℝ, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1 : ℝ)) ∂π := by
  have hQ : Q (Ici 1) = π (Prod.fst ⁻¹' Ici 1) := by
    rw [← h1, Measure.map_apply measurable_fst measurableSet_Ici]
  have h0 : π (Prod.snd ⁻¹' ({0} : Set ℝ)ᶜ) = 0 := by
    have hm : MeasurableSet (({0} : Set ℝ)ᶜ) := (measurableSet_singleton 0).compl
    rw [← Measure.map_apply measurable_snd hm, h2, Measure.dirac_apply' 0 hm]
    simp
  let S : Set (ℝ × ℝ) := Prod.fst ⁻¹' Ici 1 ∩ Prod.snd ⁻¹' {0}
  have hS_meas : MeasurableSet S :=
    (measurable_fst measurableSet_Ici).inter (measurable_snd (measurableSet_singleton 0))
  have hsub : Prod.fst ⁻¹' Ici 1 ⊆ S ∪ Prod.snd ⁻¹' ({0} : Set ℝ)ᶜ := by
    intro x hx
    by_cases hx2 : x.2 = 0
    · exact Or.inl ⟨hx, hx2⟩
    · exact Or.inr hx2
  have hle1 : Q (Ici 1) ≤ π S := by
    calc Q (Ici 1) = π (Prod.fst ⁻¹' Ici 1) := hQ
      _ ≤ π (S ∪ Prod.snd ⁻¹' ({0} : Set ℝ)ᶜ) := measure_mono hsub
      _ ≤ π S + π (Prod.snd ⁻¹' ({0} : Set ℝ)ᶜ) := measure_union_le _ _
      _ = π S := by rw [h0, add_zero]
  have hle2 : π S ≤ ∫⁻ x in S, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1 : ℝ)) ∂π := by
    calc π S = ∫⁻ _ in S, (1 : ℝ≥0∞) ∂π := by simp
      _ ≤ ∫⁻ x in S, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1 : ℝ)) ∂π := by
        apply setLIntegral_mono' hS_meas
        intro x ⟨hx1, hx2⟩
        change 1 ≤ x.1 at hx1
        change x.2 = 0 at hx2
        rw [hx2, sub_zero, Real.rpow_one, Real.norm_eq_abs]
        have habs : (1 : ℝ) ≤ |x.1| := hx1.trans (le_abs_self x.1)
        exact ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal habs
  exact hle1.trans (hle2.trans (setLIntegral_le_lintegral S _))

lemma measure_Ici_zero_of_mem_ambiguitySet {Q : Measure ℝ}
    (hQ : Q ∈ WassersteinDRO.Duality.ambiguitySet 0 1 (Set.univ : Set ℝ) (Measure.dirac (0 : ℝ))) :
    Q (Ici 1) = 0 := by
  have hw := hQ.2.2
  unfold WassersteinDRO.Duality.wassersteinDistance at hw
  simp only [div_one, ENNReal.rpow_one, ENNReal.ofReal_zero, nonpos_iff_eq_zero] at hw
  have hle : Q (Ici 1) ≤ ⨅ (π : Measure (ℝ × ℝ))
      (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = Measure.dirac (0 : ℝ)),
      ∫⁻ x : ℝ × ℝ, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1 : ℝ)) ∂π :=
    le_iInf fun π => le_iInf fun hπ => measure_Ici_le_coupling_lintegral hπ.1 hπ.2
  rw [hw] at hle
  exact nonpos_iff_eq_zero.mp hle

lemma expect_ceLoss_zero_of_mem_ambiguitySet {Q : Measure ℝ}
    (hQ : Q ∈ WassersteinDRO.Duality.ambiguitySet 0 1 (Set.univ : Set ℝ) (Measure.dirac (0 : ℝ))) :
    DupacovaWets.Consistency.expect Q ceLoss = 0 := by
  have hnull : Q (Ici 1) = 0 := measure_Ici_zero_of_mem_ambiguitySet hQ
  have hae : ∀ᵐ z ∂Q, ¬ (1 ≤ z) := by
    rw [ae_iff]
    simpa [Ici] using hnull
  have hpos : (∫⁻ z, (ceLoss z).toENNReal ∂Q) = 0 := by
    have hae_pos : (fun z => (ceLoss z).toENNReal) =ᵐ[Q] fun _ => 0 := by
      filter_upwards [hae] with z hz
      unfold ceLoss
      rw [if_neg hz]
      simp
    rw [lintegral_congr_ae hae_pos, lintegral_zero]
  have hneg : (∫⁻ z, (-ceLoss z).toENNReal ∂Q) = 0 := by
    have hae_neg : (fun z => (-ceLoss z).toENNReal) =ᵐ[Q] fun _ => 0 := by
      filter_upwards [hae] with z hz
      unfold ceLoss
      rw [if_neg hz]
      simp
    rw [lintegral_congr_ae hae_neg, lintegral_zero]
  unfold DupacovaWets.Consistency.expect
  rw [hpos, hneg]
  simp

lemma worstCaseRisk_ceLoss_le_zero :
    worstCaseRisk 0 1 (Set.univ : Set ℝ) (Measure.dirac (0 : ℝ)) ceLoss ≤ 0 := by
  unfold worstCaseRisk
  refine iSup_le fun Q => iSup_le fun hQ => ?_
  rw [expect_ceLoss_zero_of_mem_ambiguitySet hQ]

end KuhnWass2019.Reformulation

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ε p : ℝ) (_hε : 0 ≤ ε) (_hp : 1 ≤ p) (Ξ : Set E) (_hΞ : IsClosed Ξ)
    (PN : Measure E) [IsProbabilityMeasure PN] (_hPN : PN Ξᶜ = 0)
    (ℓ : E → EReal) (_hℓ : KuhnWass2019.Reformulation.RegularLoss PN ℓ),
    KuhnWass2019.Reformulation.worstCaseRisk ε p Ξ PN ℓ =
      ⨅ (γ : ℝ) (_ : 0 ≤ γ),
        DupacovaWets.Consistency.expect PN
          (KuhnWass2019.Reformulation.moreauYosida Ξ ℓ p γ)
          + ((γ * ε ^ p : ℝ) : EReal)) := by
  intro hall
  have hce := hall 0 1 (le_refl 0) (le_refl 1) (Set.univ : Set ℝ) isClosed_univ
    (Measure.dirac (0 : ℝ)) (by simp) KuhnWass2019.Reformulation.ceLoss
    KuhnWass2019.Reformulation.ceLoss_regular
  rw [KuhnWass2019.Reformulation.dual_rhs_eq_top] at hce
  have hle := KuhnWass2019.Reformulation.worstCaseRisk_ceLoss_le_zero
  rw [hce] at hle
  exact EReal.top_ne_zero (top_unique hle).symm
