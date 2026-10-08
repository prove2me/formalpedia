-- Prove2me | solution 1 for MultiperiodRisk.Bellman.stable_tfae
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-07T21:18:31.028026+00:00
-- url     : https://prove2.me/submissions/ebc40f9b-de27-4f91-acce-6462d27d0b3f

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_StopOps
import Definitions.Def_MultiperiodRisk_Bellman_TestSet
import Definitions.Def_MultiperiodRisk_Bellman_Psi

set_option autoImplicit false

/- Complete checked body: AttributedRisk -/
section

section
-- Prove2me | solution 1 for MultiperiodRisk.Bellman.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:52:05.353518+00:00
-- url     : https://prove2.me/submissions/e5258489-7203-41dc-8b2c-1677cffd3f66


namespace MultiperiodRisk.Bellman

open MeasureTheory

lemma aux_l31_condExp_pos {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m)
    (f : Ω → ℝ) (hf : Integrable f P₀) (hpos : ∀ᵐ ω ∂P₀, 0 < f ω) (n : ℕ) :
    ∀ᵐ ω ∂P₀, 0 < P₀[f|ℱ n] ω := by
  set h := P₀[f|ℱ n] with hh
  have hsm : StronglyMeasurable[ℱ n] h := stronglyMeasurable_condExp
  set S := {ω | h ω ≤ 0} with hS_def
  have hS : MeasurableSet[ℱ n] S := hsm.measurableSet_le stronglyMeasurable_const
  have hS' : MeasurableSet S := ℱ.le n _ hS
  have h1 : ∫ ω in S, h ω ∂P₀ = ∫ ω in S, f ω ∂P₀ := setIntegral_condExp (ℱ.le n) hf hS
  have h2 : ∫ ω in S, h ω ∂P₀ ≤ 0 := setIntegral_nonpos hS' (fun ω hω => hω)
  have h3 : 0 ≤ ∫ ω in S, f ω ∂P₀ :=
    setIntegral_nonneg_of_ae_restrict (ae_restrict_of_ae (hpos.mono fun ω hω => hω.le))
  have h4 : ∫ ω in S, f ω ∂P₀ = 0 := le_antisymm (h1 ▸ h2) h3
  rw [setIntegral_eq_zero_iff_of_nonneg_ae
    (ae_restrict_of_ae (hpos.mono fun ω hω => hω.le)) hf.integrableOn] at h4
  have h5 : P₀.restrict S = 0 := by
    have : ∀ᵐ ω ∂(P₀.restrict S), False := by
      filter_upwards [h4, ae_restrict_of_ae hpos] with ω h6 h7
      simp [h6] at h7
    simpa using this
  rw [Measure.restrict_eq_zero] at h5
  have := measure_eq_zero_iff_ae_notMem.1 h5
  filter_upwards [this] with ω hω
  simpa [S] using hω

lemma aux_l31_Ioc_indicator {Ω : Type*} (N n : ℕ) (σ : Ω → WithTop ℕ)
    (hσN : ∀ ω, σ ω ≤ (N : WithTop ℕ)) (h : Ω → ℝ) :
    {ω | σ ω ≤ WithTop.some n}ᶜ.indicator h =
      ∑ k ∈ Finset.Ioc n N, {ω | σ ω = WithTop.some k}.indicator h := by
  funext ω
  have hN := hσN ω
  rw [Nat.cast_withTop] at hN
  have hne : σ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hN
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hs, WithTop.coe_le_coe] at hN
  rw [Finset.sum_apply]
  simp only [Set.indicator_apply, Set.mem_compl_iff, Set.mem_ofPred_eq, ← hs,
    WithTop.coe_le_coe, WithTop.coe_eq_coe]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_Ioc, hN]

lemma aux_l31_key {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ)
    (f f' : Ω → ℝ) (hf : Integrable f P₀) (hf' : Integrable f' P₀)
    (hZf'pos : ∀ k, ∀ᵐ ω ∂P₀, 0 < Z P₀ ℱ f' k ω)
    (σ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ)
    (hg : Integrable (pasteDensity P₀ ℱ f f' σ) P₀) (n : ℕ) :
    Z P₀ ℱ (pasteDensity P₀ ℱ f f' σ) n =ᵐ[P₀] fun ω =>
      if σ ω ≤ WithTop.some n then
        stoppedValue (Z P₀ ℱ f) σ ω / stoppedValue (Z P₀ ℱ f') σ ω * Z P₀ ℱ f' n ω
      else Z P₀ ℱ f n ω := by
  set g := pasteDensity P₀ ℱ f f' σ with hg_def
  let E : ℕ → Set Ω := fun k => {ω | σ ω = WithTop.some k}
  have hE : ∀ k, MeasurableSet[ℱ k] (E k) := fun k => hσ.1.measurableSet_eq_of_countable k
  have hEm : ∀ k, MeasurableSet (E k) := fun k => ℱ.le k _ (hE k)
  have hZsm : ∀ (h : Ω → ℝ) k, StronglyMeasurable[ℱ k] (Z P₀ ℱ h k) :=
    fun h k => stronglyMeasurable_condExp
  have hEg : ∀ k, (E k).indicator g = (E k).indicator (Z P₀ ℱ f k / Z P₀ ℱ f' k) * f' := by
    intro k; funext ω
    by_cases hω : ω ∈ E k
    · have hσk : σ ω = WithTop.some k := hω
      simp only [Pi.mul_apply, Set.indicator_of_mem hω, hg_def, pasteDensity, stoppedValue, hσk,
        Pi.div_apply]
      change Z P₀ ℱ f k ω * f' ω / Z P₀ ℱ f' k ω = Z P₀ ℱ f k ω / Z P₀ ℱ f' k ω * f' ω
      ring
    · simp only [Pi.mul_apply, Set.indicator_of_notMem hω, zero_mul]
  have hEg_int : ∀ k, Integrable ((E k).indicator g) P₀ := fun k => hg.indicator (hEm k)
  have hB : ∀ k, n ≤ k → P₀[(E k).indicator g|ℱ n] =ᵐ[P₀] P₀[(E k).indicator f|ℱ n] := by
    intro k hk
    have h1 : P₀[(E k).indicator g|ℱ k] =ᵐ[P₀] P₀[(E k).indicator f|ℱ k] := by
      have hA : P₀[(E k).indicator g|ℱ k] =ᵐ[P₀]
          (E k).indicator (Z P₀ ℱ f k / Z P₀ ℱ f' k) * Z P₀ ℱ f' k := by
        rw [hEg k]
        refine condExp_mul_of_stronglyMeasurable_left ?_ ?_ hf'
        · exact (((hZsm f k).div (hZsm f' k)).indicator (hE k))
        · rw [← hEg k]; exact hEg_int k
      have hC : P₀[(E k).indicator f|ℱ k] =ᵐ[P₀] (E k).indicator (Z P₀ ℱ f k) :=
        condExp_indicator hf (hE k)
      refine hA.trans (Filter.EventuallyEq.trans ?_ hC.symm)
      filter_upwards [hZf'pos k] with ω hω
      by_cases hωE : ω ∈ E k
      · simp only [Pi.mul_apply, Set.indicator_of_mem hωE, Pi.div_apply]
        field_simp
      · simp only [Pi.mul_apply, Set.indicator_of_notMem hωE, zero_mul]
    exact (condExp_condExp_of_le (ℱ.mono hk) (ℱ.le k)).symm.trans
      ((condExp_congr_ae h1).trans (condExp_condExp_of_le (ℱ.mono hk) (ℱ.le k)))
  -- split
  set S := {ω | σ ω ≤ WithTop.some n} with hS_def
  have hS : MeasurableSet[ℱ n] S := hσ.1.measurableSet_le n
  have hSm : MeasurableSet S := ℱ.le n _ hS
  set C : Ω → ℝ := S.indicator (stoppedProcess (Z P₀ ℱ f) σ n / stoppedProcess (Z P₀ ℱ f') σ n)
    with hC_def
  have hZad : ∀ h : Ω → ℝ, StronglyAdapted ℱ (Z P₀ ℱ h) := fun h => (martingale_condExp h ℱ P₀).1
  have hCsm : StronglyMeasurable[ℱ n] C :=
    ((((hZad f).stoppedProcess_of_discrete hσ.1) n).div
      (((hZad f').stoppedProcess_of_discrete hσ.1) n)).indicator hS
  have hSg : S.indicator g = C * f' := by
    funext ω
    by_cases hω : ω ∈ S
    · have hσn : σ ω ≤ WithTop.some n := hω
      simp only [Pi.mul_apply, hC_def, Set.indicator_of_mem hω, hg_def, pasteDensity, Pi.div_apply,
        stoppedProcess, min_eq_right hσn, stoppedValue]
      ring
    · simp only [Pi.mul_apply, hC_def, Set.indicator_of_notMem hω, zero_mul]
  have h1 : P₀[S.indicator g|ℱ n] =ᵐ[P₀] C * Z P₀ ℱ f' n := by
    rw [hSg]
    exact condExp_mul_of_stronglyMeasurable_left hCsm (by rw [← hSg]; exact hg.indicator hSm) hf'
  have h2 : P₀[Sᶜ.indicator g|ℱ n] =ᵐ[P₀] Sᶜ.indicator (Z P₀ ℱ f n) := by
    rw [aux_l31_Ioc_indicator N n σ hσ.2 g]
    refine (condExp_finsetSum (fun k _ => hEg_int k) _).trans ?_
    have h3 : ∀ᵐ ω ∂P₀, ∀ k ∈ Finset.Ioc n N,
        P₀[(E k).indicator g|ℱ n] ω = P₀[(E k).indicator f|ℱ n] ω := by
      rw [Filter.eventually_all_finset]
      intro k hk
      exact hB k (Finset.mem_Ioc.1 hk).1.le
    have h4 : (∑ k ∈ Finset.Ioc n N, P₀[(E k).indicator g|ℱ n]) =ᵐ[P₀]
        ∑ k ∈ Finset.Ioc n N, P₀[(E k).indicator f|ℱ n] := by
      filter_upwards [h3] with ω hω
      simp only [Finset.sum_apply]
      exact Finset.sum_congr rfl hω
    refine h4.trans ?_
    refine (condExp_finsetSum (fun k _ => hf.indicator (hEm k)) _).symm.trans ?_
    rw [← aux_l31_Ioc_indicator N n σ hσ.2 f]
    exact condExp_indicator hf hS.compl
  have h5 : g = S.indicator g + Sᶜ.indicator g := (Set.indicator_self_add_compl S g).symm
  have h6 : Z P₀ ℱ g n =ᵐ[P₀] P₀[S.indicator g|ℱ n] + P₀[Sᶜ.indicator g|ℱ n] := by
    show P₀[g|ℱ n] =ᵐ[P₀] _
    conv_lhs => rw [h5]
    exact condExp_add (hg.indicator hSm) (hg.indicator hSm.compl) _
  refine h6.trans ((h1.add h2).trans ?_)
  refine Filter.Eventually.of_forall (fun ω => ?_)
  by_cases hω : ω ∈ S
  · have hσn : σ ω ≤ WithTop.some n := hω
    simp only [Pi.add_apply, Pi.mul_apply, hC_def, Set.indicator_of_mem hω, Pi.div_apply,
      stoppedProcess, min_eq_right hσn, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω),
      add_zero, if_pos hσn]
    rfl
  · have hσn : ¬ σ ω ≤ WithTop.some n := hω
    simp only [Pi.add_apply, Pi.mul_apply, hC_def, Set.indicator_of_notMem hω, zero_mul, zero_add,
      Set.indicator_of_mem (Set.mem_compl hω), if_neg hσn]

lemma aux_l31_fin {Ω : Type*} (N : ℕ) (τ : Ω → WithTop ℕ) (h : ∀ ω, τ ω ≤ (N : WithTop ℕ))
    (ω : Ω) : ∃ s : ℕ, τ ω = WithTop.some s := by
  have hN := h ω
  rw [Nat.cast_withTop] at hN
  have hne : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hN
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hne
  exact ⟨s, hs.symm⟩

end MultiperiodRisk.Bellman

open MultiperiodRisk.Bellman
open MeasureTheory

theorem checked_lemma_3_1 {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ) (D : TestSet P₀ ℱ N)
    (hstab : IsStable D) (τ σ ν : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ)
    (hσ : IsBddStoppingTime ℱ N σ) (hν : IsBddStoppingTime ℱ N ν)
    (hτσ : ∀ ω, τ ω ≤ σ ω) (hσν : ∀ ω, σ ω ≤ ν ω) :
    (∀ f ∈ Pe D, ∃ g ∈ Pe D, ∃ g' ∈ Pe D,
      (fun ω => stoppedValue (Z P₀ ℱ f) ν ω / stoppedValue (Z P₀ ℱ f) σ ω) =ᵐ[P₀]
        (fun ω => stoppedValue (Z P₀ ℱ g') ν ω / stoppedValue (Z P₀ ℱ g') σ ω) ∧
      (fun ω => stoppedValue (Z P₀ ℱ f) σ ω / stoppedValue (Z P₀ ℱ f) τ ω) =ᵐ[P₀]
        (fun ω => stoppedValue (Z P₀ ℱ g) σ ω / stoppedValue (Z P₀ ℱ g) τ ω)) ∧
    (∀ f ∈ Pe D, ∀ f' ∈ Pe D, ∃ g ∈ Pe D,
      (fun ω => stoppedValue (Z P₀ ℱ g) ν ω / stoppedValue (Z P₀ ℱ g) σ ω) =ᵐ[P₀]
        (fun ω => stoppedValue (Z P₀ ℱ f') ν ω / stoppedValue (Z P₀ ℱ f') σ ω) ∧
      (fun ω => stoppedValue (Z P₀ ℱ g) σ ω / stoppedValue (Z P₀ ℱ g) τ ω) =ᵐ[P₀]
        (fun ω => stoppedValue (Z P₀ ℱ f) σ ω / stoppedValue (Z P₀ ℱ f) τ ω)) := by
  refine ⟨fun f hf => ⟨f, hf, f, hf, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩, ?_⟩
  intro f hf f' hf'
  have hfi : Integrable f P₀ := D.integrable f hf.1
  have hf'i : Integrable f' P₀ := D.integrable f' hf'.1
  have hposf : ∀ k, ∀ᵐ ω ∂P₀, 0 < Z P₀ ℱ f k ω :=
    fun k => aux_l31_condExp_pos P₀ ℱ f hfi hf.2 k
  have hposf' : ∀ k, ∀ᵐ ω ∂P₀, 0 < Z P₀ ℱ f' k ω :=
    fun k => aux_l31_condExp_pos P₀ ℱ f' hf'i hf'.2 k
  have hgD : pasteDensity P₀ ℱ f f' σ ∈ D.set := hstab f hf f' hf' σ hσ
  have hgi : Integrable (pasteDensity P₀ ℱ f f' σ) P₀ := D.integrable _ hgD
  have hall_f := ae_all_iff.2 hposf
  have hall_f' := ae_all_iff.2 hposf'
  have hkey := ae_all_iff.2 (aux_l31_key P₀ ℱ N f f' hfi hf'i hposf' σ hσ hgi)
  have ev : ∀ (ρ : Ω → WithTop ℕ) (u : ℕ → Ω → ℝ) (ω : Ω) (s : ℕ), ρ ω = WithTop.some s →
      stoppedValue u ρ ω = u s ω := by
    intro ρ u ω s hs
    simp only [stoppedValue, hs]
    rfl
  refine ⟨pasteDensity P₀ ℱ f f' σ, ⟨hgD, ?_⟩, ?_, ?_⟩
  · filter_upwards [hall_f, hall_f', hf'.2] with ω h1 h2 h3
    obtain ⟨s, hs⟩ := aux_l31_fin N σ hσ.2 ω
    simp only [pasteDensity, ev σ _ ω s hs]
    exact div_pos (mul_pos (h1 _) h3) (h2 _)
  · filter_upwards [hkey, hall_f, hall_f'] with ω hk h1 h2
    obtain ⟨s, hs⟩ := aux_l31_fin N σ hσ.2 ω
    obtain ⟨t, ht⟩ := aux_l31_fin N ν hν.2 ω
    have hst : s ≤ t := by
      have := hσν ω; rw [hs, ht] at this; exact WithTop.coe_le_coe.1 this
    simp only [ev σ _ ω s hs, ev ν _ ω t ht]
    rw [hk t, hk s]
    simp only [ev σ _ ω s hs, hs, WithTop.coe_le_coe, hst, le_refl, if_true]
    have a1 := (h1 s).ne'
    have a2 := (h2 s).ne'
    have a3 := (h2 t).ne'
    field_simp
  · filter_upwards [hkey, hall_f, hall_f'] with ω hk h1 h2
    obtain ⟨s, hs⟩ := aux_l31_fin N σ hσ.2 ω
    obtain ⟨r, hr⟩ := aux_l31_fin N τ hτ.2 ω
    have hrs : r ≤ s := by
      have := hτσ ω; rw [hr, hs] at this; exact WithTop.coe_le_coe.1 this
    simp only [ev σ _ ω s hs, ev τ _ ω r hr]
    rw [hk s, hk r]
    have a1 := (h1 s).ne'
    have a2 := (h2 s).ne'
    by_cases hsr : s ≤ r
    · have : r = s := le_antisymm hrs hsr
      subst this
      simp only [ev σ _ ω r hs, hs, le_refl, if_true]
      field_simp
    · simp only [ev σ _ ω s hs, hs, WithTop.coe_le_coe, le_refl, if_true, hsr, if_false]
      field_simp
end

section
-- Prove2me | solution 1 for MultiperiodRisk.Bellman.psi_defines_process
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:53:28.961981+00:00
-- url     : https://prove2.me/submissions/6ab9ca5a-ad7f-40d3-8bba-8eb78bffa2bf


namespace MultiperiodRisk.Bellman

open MeasureTheory

theorem aux_pdp_unique {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {m' : MeasurableSpace Ω} {S : Set (Ω → ℝ)} {g₁ g₂ : Ω → ℝ}
    (h₁ : IsEssInf μ m' S g₁) (h₂ : IsEssInf μ m' S g₂) : g₁ =ᵐ[μ] g₂ :=
  (h₂.2.2 g₁ h₁.1 h₁.2.1).antisymm (h₁.2.2 g₂ h₂.1 h₂.2.1)

theorem aux_pdp_essInfFamily_eq {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {m' : MeasurableSpace Ω} {S : Set (Ω → ℝ)} {g : Ω → ℝ}
    (h : IsEssInf μ m' S g) : essInfFamily μ m' S =ᵐ[μ] g := by
  have hex : ∃ g, IsEssInf μ m' S g := ⟨g, h⟩
  unfold essInfFamily
  rw [dif_pos hex]
  exact aux_pdp_unique hex.choose_spec h

theorem aux_pdp_essInfFamily_spec {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {m' : MeasurableSpace Ω} {S : Set (Ω → ℝ)}
    (h : ∃ g, IsEssInf μ m' S g) : IsEssInf μ m' S (essInfFamily μ m' S) := by
  unfold essInfFamily
  rw [dif_pos h]
  exact h.choose_spec

theorem aux_pdp_exists {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {m' : MeasurableSpace Ω} (hm : m' ≤ m)
    {S : Set (Ω → ℝ)} (hne : S.Nonempty) (hmeas : ∀ h ∈ S, StronglyMeasurable[m'] h)
    (c : ℝ) (hc : ∀ h ∈ S, ∀ᵐ ω ∂μ, c ≤ h ω) : ∃ g, IsEssInf μ m' S g := by
  classical
  obtain ⟨h₀, hh₀⟩ := hne
  let G : (ℕ → S) → Ω → ℝ := fun s ω => ⨅ n, max c ((s n : Ω → ℝ) ω)
  have hGmeas : ∀ s, Measurable[m'] (G s) := fun s =>
    Measurable.iInf (fun n => measurable_const.max (hmeas _ (s n).2).measurable)
  have hGbdd : ∀ (s : ℕ → S) ω, BddBelow (Set.range fun n => max c ((s n : Ω → ℝ) ω)) :=
    fun s ω => ⟨c, by rintro _ ⟨n, rfl⟩; exact le_max_left _ _⟩
  have hGle : ∀ s n ω, G s ω ≤ max c ((s n : Ω → ℝ) ω) := fun s n ω => ciInf_le (hGbdd s ω) n
  have hint : ∀ s, Integrable (fun ω => Real.arctan (G s ω)) μ := by
    intro s
    refine Integrable.of_bound ?_ (Real.pi / 2) (Filter.Eventually.of_forall fun ω => ?_)
    · exact (Real.continuous_arctan.measurable.comp ((hGmeas s).mono hm le_rfl)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_le]
      exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  let φ : (ℕ → S) → ℝ := fun s => ∫ ω, Real.arctan (G s ω) ∂μ
  have hφmono : ∀ s s', (∀ ω, G s ω ≤ G s' ω) → φ s ≤ φ s' := fun s s' h =>
    integral_mono (hint s) (hint s') (fun ω => Real.arctan_strictMono.monotone (h ω))
  have hVne : (Set.range φ).Nonempty := ⟨_, ⟨fun _ => ⟨h₀, hh₀⟩, rfl⟩⟩
  have hVbdd : BddBelow (Set.range φ) := by
    refine ⟨∫ _ω, (-(Real.pi / 2)) ∂μ, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact integral_mono (integrable_const _) (hint s)
      (fun ω => (Real.neg_pi_div_two_lt_arctan _).le)
  obtain ⟨u, -, hu_tend, hu_mem⟩ := exists_seq_tendsto_sInf hVne hVbdd
  choose s hs using hu_mem
  let s' : ℕ → S := fun n => s n.unpair.1 n.unpair.2
  have hs'le : ∀ k ω, G s' ω ≤ G (s k) ω := by
    intro k ω
    refine le_ciInf fun j => ?_
    have := hGle s' (Nat.pair k j) ω
    simpa [s', Nat.unpair_pair] using this
  have hφs' : φ s' = sInf (Set.range φ) := by
    refine le_antisymm ?_ (csInf_le hVbdd ⟨s', rfl⟩)
    refine ge_of_tendsto' hu_tend fun k => ?_
    rw [← hs k]
    exact hφmono _ _ (hs'le k)
  refine ⟨G s', (hGmeas s').stronglyMeasurable, ?_, ?_⟩
  · intro h hh
    let s'' : ℕ → S := fun n => if n = 0 then ⟨h, hh⟩ else s' (n - 1)
    have h1 : ∀ ω, G s'' ω ≤ G s' ω := by
      intro ω
      refine le_ciInf fun j => ?_
      have := hGle s'' (j + 1) ω
      simpa [s''] using this
    have h2 : ∀ ω, G s'' ω ≤ max c (h ω) := by
      intro ω
      have := hGle s'' 0 ω
      simpa [s''] using this
    have h3 : φ s' ≤ φ s'' := by
      rw [hφs']
      exact csInf_le hVbdd ⟨s'', rfl⟩
    have h4 : ∫ ω, (Real.arctan (G s' ω) - Real.arctan (G s'' ω)) ∂μ = 0 := by
      rw [integral_sub (hint s') (hint s'')]
      have := hφmono _ _ h1
      simp only [φ] at this h3
      linarith
    have h5 := (integral_eq_zero_iff_of_nonneg (fun ω => sub_nonneg.2
      (Real.arctan_strictMono.monotone (h1 ω))) ((hint s').sub (hint s''))).1 h4
    filter_upwards [h5, hc h hh] with ω hω hcω
    have : G s' ω = G s'' ω := by
      have := sub_eq_zero.1 hω
      exact Real.arctan_injective this
    rw [this]
    exact (h2 ω).trans (max_le hcω le_rfl)
  · intro g' _ hg'
    have : ∀ᵐ ω ∂μ, ∀ n, g' ω ≤ (s' n : Ω → ℝ) ω :=
      ae_all_iff.2 fun n => hg' _ (s' n).2
    filter_upwards [this] with ω hω
    exact le_ciInf fun n => (hω n).trans (le_max_right _ _)

section aux
variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω} {ℱ : Filtration ℕ m} {N : ℕ}

theorem aux_pdp_Qfin (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ D.set) :
    IsFiniteMeasure (Q P₀ f) :=
  isFiniteMeasure_withDensity_ofReal (D.integrable f hf).2

theorem aux_pdp_Qac (f : Ω → ℝ) : Q P₀ f ≪ P₀ := withDensity_absolutelyContinuous _ _

theorem aux_pdp_acQ (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ Pe D) : P₀ ≪ Q P₀ f := by
  refine withDensity_absolutelyContinuous'
    (D.integrable f hf.1).aestronglyMeasurable.aemeasurable.ennreal_ofReal ?_
  filter_upwards [hf.2] with ω hω
  simpa using hω

theorem aux_pdp_exists_k {τ : Ω → WithTop ℕ} (hτ : ∀ ω, τ ω ≤ (N : WithTop ℕ)) (ω : Ω) :
    ∃ k ≤ N, τ ω = (k : WithTop ℕ) := by
  have hne : τ ω ≠ ⊤ := ne_top_of_le_ne_top (WithTop.natCast_ne_top N) (hτ ω)
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hne
  refine ⟨k, ?_, hk.symm⟩
  have := hτ ω
  rw [← hk] at this
  exact WithTop.coe_le_coe.1 this

theorem aux_pdp_sv_of_eq (X : ℕ → Ω → ℝ) {τ : Ω → WithTop ℕ} {ω : Ω} {k : ℕ}
    (h : τ ω = (k : WithTop ℕ)) : stoppedValue X τ ω = X k ω := by
  simp only [stoppedValue, h]
  rfl

theorem aux_pdp_sv_sum (X : ℕ → Ω → ℝ) {τ : Ω → WithTop ℕ} (hτ : ∀ ω, τ ω ≤ (N : WithTop ℕ)) :
    stoppedValue X τ = fun ω => ∑ n ∈ Finset.range (N + 1),
      {ω | τ ω = (n : WithTop ℕ)}.indicator (X n) ω := by
  funext ω
  obtain ⟨k, hk, h⟩ := aux_pdp_exists_k hτ ω
  rw [aux_pdp_sv_of_eq X h]
  rw [Finset.sum_eq_single k]
  · simp [h]
  · intro b _ hb
    simp [h, Ne.symm hb]
  · intro hk'
    exact absurd (Finset.mem_range.2 (by omega)) hk'

theorem aux_pdp_sv_int (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (hX : IsValueProcess P₀ ℱ N X)
    {f : Ω → ℝ} (hf : f ∈ D.set) {τ : Ω → WithTop ℕ} (hτ : IsBddStoppingTime ℱ N τ) :
    Integrable (stoppedValue X τ) (Q P₀ f) := by
  have := aux_pdp_Qfin D hf
  obtain ⟨C, hC⟩ := hX.2
  rw [aux_pdp_sv_sum X hτ.2]
  refine integrable_finsetSum _ fun n hn => ?_
  have hn' : n ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  refine Integrable.indicator ?_ (ℱ.le n _ (hτ.1.measurableSet_eq n))
  refine Integrable.of_bound ((hX.1 n hn').mono (ℱ.le n)).aestronglyMeasurable C ?_
  exact (aux_pdp_Qac f).ae_le (hC n hn')

theorem aux_pdp_lb (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (hX : IsValueProcess P₀ ℱ N X)
    {C : ℝ} (hC : ∀ n ≤ N, ∀ᵐ ω ∂P₀, |X n ω| ≤ C)
    {f : Ω → ℝ} (hf : f ∈ Pe D) {τ : Ω → WithTop ℕ} (hτ : IsBddStoppingTime ℱ N τ)
    {m' : MeasurableSpace Ω} (hm' : m' ≤ m) :
    ∀ᵐ ω ∂P₀, -C ≤ (Q P₀ f)[stoppedValue X τ | m'] ω := by
  have := aux_pdp_Qfin D hf.1
  have hall : ∀ᵐ ω ∂P₀, ∀ n, n ≤ N → |X n ω| ≤ C :=
    ae_all_iff.2 fun n => by
      by_cases hn : n ≤ N
      · filter_upwards [hC n hn] with ω hω using fun _ => hω
      · exact Filter.Eventually.of_forall fun ω h => absurd h hn
  have hY : ∀ᵐ ω ∂(Q P₀ f), (fun _ => -C) ω ≤ stoppedValue X τ ω := by
    refine (aux_pdp_Qac f).ae_le ?_
    filter_upwards [hall] with ω hω
    obtain ⟨k, hk, h⟩ := aux_pdp_exists_k hτ.2 ω
    rw [aux_pdp_sv_of_eq X h]
    exact (abs_le.1 (hω k hk)).1
  have := condExp_mono (m := m') (integrable_const (-C)) (aux_pdp_sv_int D X hX hf.1 hτ) hY
  rw [condExp_const hm'] at this
  exact (aux_pdp_acQ D hf).ae_le this

theorem aux_pdp_loc (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (hX : IsValueProcess P₀ ℱ N X)
    {σ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ) (t : ℕ) {f : Ω → ℝ} (hf : f ∈ Pe D)
    {τ₁ τ₂ : Ω → WithTop ℕ} (h₁ : IsBddStoppingTime ℱ N τ₁) (h₂ : IsBddStoppingTime ℱ N τ₂)
    (heq : ∀ ω, σ ω = (t : WithTop ℕ) → τ₁ ω = τ₂ ω) :
    ∀ᵐ ω ∂P₀, σ ω = (t : WithTop ℕ) →
      (Q P₀ f)[stoppedValue X τ₁ | hσ.measurableSpace] ω =
        (Q P₀ f)[stoppedValue X τ₂ | ℱ t] ω := by
  have := aux_pdp_Qfin D hf.1
  have hi₁ := aux_pdp_sv_int D X hX hf.1 h₁
  have hi₂ := aux_pdp_sv_int D X hX hf.1 h₂
  have hAt : MeasurableSet[ℱ t] {ω | σ ω = (t : WithTop ℕ)} := hσ.measurableSet_eq t
  have hA : MeasurableSet {ω | σ ω = (t : WithTop ℕ)} := ℱ.le t _ hAt
  have step1 := condExp_stopping_time_ae_eq_restrict_eq_of_countable (μ := Q P₀ f)
    (f := stoppedValue X τ₁) hσ t
  have step1' : ∀ᵐ ω ∂(Q P₀ f), σ ω = (t : WithTop ℕ) →
      (Q P₀ f)[stoppedValue X τ₁ | hσ.measurableSpace] ω =
        (Q P₀ f)[stoppedValue X τ₁ | ℱ t] ω := (ae_restrict_iff' hA).1 step1
  have hind : {ω | σ ω = (t : WithTop ℕ)}.indicator (stoppedValue X τ₁) =
      {ω | σ ω = (t : WithTop ℕ)}.indicator (stoppedValue X τ₂) := by
    funext ω
    by_cases hω : σ ω = (t : WithTop ℕ)
    · simp [Set.indicator_of_mem, hω, stoppedValue, heq ω hω]
    · simp [hω]
  have e1 := condExp_indicator hi₁ hAt
  have e2 := condExp_indicator hi₂ hAt
  rw [hind] at e1
  have e3 := e1.symm.trans e2
  have : ∀ᵐ ω ∂(Q P₀ f), σ ω = (t : WithTop ℕ) →
      (Q P₀ f)[stoppedValue X τ₁ | hσ.measurableSpace] ω =
        (Q P₀ f)[stoppedValue X τ₂ | ℱ t] ω := by
    filter_upwards [step1', e3] with ω hω1 hω3 hωt
    rw [hω1 hωt]
    have hmem : ω ∈ {ω | σ ω = (t : WithTop ℕ)} := hωt
    simpa [Set.indicator_of_mem hmem] using hω3
  exact (aux_pdp_acQ D hf).ae_le this

end aux

section aux
variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω} {ℱ : Filtration ℕ m} {N : ℕ}

theorem aux_pdp_piece {σ τ₁ τ₂ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ)
    (hτ₁ : IsStoppingTime ℱ τ₁) (hτ₂ : IsStoppingTime ℱ τ₂) (t : ℕ)
    (h₁ : ∀ ω, σ ω = (t : WithTop ℕ) → (t : WithTop ℕ) ≤ τ₁ ω)
    (h₂ : ∀ ω, σ ω = (t : WithTop ℕ) → (t : WithTop ℕ) ≤ τ₂ ω) :
    IsStoppingTime ℱ (fun ω => if σ ω = (t : WithTop ℕ) then τ₁ ω else τ₂ ω) := by
  classical
  intro i
  show MeasurableSet[ℱ i]
    {ω | (if σ ω = (t : WithTop ℕ) then τ₁ ω else τ₂ ω) ≤ (i : WithTop ℕ)}
  by_cases hi : t ≤ i
  · have hset : {ω | (if σ ω = (t : WithTop ℕ) then τ₁ ω else τ₂ ω) ≤ (i : WithTop ℕ)} =
        ({ω | σ ω = (t : WithTop ℕ)} ∩ {ω | τ₁ ω ≤ (i : WithTop ℕ)}) ∪
          ({ω | σ ω = (t : WithTop ℕ)}ᶜ ∩ {ω | τ₂ ω ≤ (i : WithTop ℕ)}) := by
      ext ω
      by_cases hω : σ ω = (t : WithTop ℕ) <;> simp [hω]
    have hA : MeasurableSet[ℱ i] {ω | σ ω = (t : WithTop ℕ)} :=
      ℱ.mono hi _ (hσ.measurableSet_eq t)
    rw [hset]
    exact (hA.inter (hτ₁ i)).union (hA.compl.inter (hτ₂ i))
  · have hit : (i : WithTop ℕ) < (t : WithTop ℕ) := by exact_mod_cast (not_le.1 hi)
    have hset : {ω | (if σ ω = (t : WithTop ℕ) then τ₁ ω else τ₂ ω) ≤ (i : WithTop ℕ)} =
        {ω | τ₂ ω ≤ (i : WithTop ℕ)} := by
      ext ω
      by_cases hω : σ ω = (t : WithTop ℕ)
      · simp only [hω, if_true, Set.mem_ofPred_eq]
        constructor
        · intro h; exact absurd (lt_of_le_of_lt ((h₁ ω hω).trans h) hit) (lt_irrefl _)
        · intro h; exact absurd (lt_of_le_of_lt ((h₂ ω hω).trans h) hit) (lt_irrefl _)
      · simp [hω]
    rw [hset]
    exact hτ₂ i

theorem aux_pdp_piece_bdd {σ τ₁ τ₂ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ)
    (hτ₁ : IsBddStoppingTime ℱ N τ₁) (hτ₂ : IsBddStoppingTime ℱ N τ₂) (t : ℕ)
    (h₁ : ∀ ω, σ ω = (t : WithTop ℕ) → (t : WithTop ℕ) ≤ τ₁ ω)
    (h₂ : ∀ ω, σ ω = (t : WithTop ℕ) → (t : WithTop ℕ) ≤ τ₂ ω) :
    IsBddStoppingTime ℱ N (fun ω => if σ ω = (t : WithTop ℕ) then τ₁ ω else τ₂ ω) := by
  refine ⟨aux_pdp_piece hσ hτ₁.1 hτ₂.1 t h₁ h₂, fun ω => ?_⟩
  dsimp only
  split_ifs
  · exact hτ₁.2 ω
  · exact hτ₂.2 ω

theorem aux_pdp_ind_meas {σ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ) (t : ℕ) {h : Ω → ℝ}
    (hh : StronglyMeasurable[ℱ t] h) :
    StronglyMeasurable[hσ.measurableSpace] ({ω | σ ω = (t : WithTop ℕ)}.indicator h) := by
  refine Measurable.stronglyMeasurable ?_
  intro B hB
  rw [Set.indicator_preimage, Set.ite]
  refine MeasurableSet.union ?_ ?_
  · exact (hσ.measurableSet_inter_eq_iff _ t).2 ((hh.measurable hB).inter (hσ.measurableSet_eq t))
  · exact (measurable_const hB).diff (hσ.measurableSet_eq' t)

theorem aux_pdp_ind_meas' {σ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ) (t : ℕ) {h : Ω → ℝ}
    (hh : StronglyMeasurable[hσ.measurableSpace] h) :
    StronglyMeasurable[ℱ t] ({ω | σ ω = (t : WithTop ℕ)}.indicator h) := by
  refine Measurable.stronglyMeasurable ?_
  intro B hB
  rw [Set.indicator_preimage, Set.ite]
  refine MeasurableSet.union ?_ ?_
  · exact (hσ.measurableSet_inter_eq_iff _ t).1 ((hh.measurable hB).inter (hσ.measurableSet_eq' t))
  · exact (measurable_const hB).diff (hσ.measurableSet_eq t)

end aux


end MultiperiodRisk.Bellman

open MultiperiodRisk.Bellman
open MeasureTheory

theorem checked_psi_defines_process {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ) (D : TestSet P₀ ℱ N)
    (hPe : (Pe D).Nonempty) (X : ℕ → Ω → ℝ) (hX : IsValueProcess P₀ ℱ N X)
    (σ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ) :
    Psi D X σ hσ.1 =ᵐ[P₀] fun ω =>
      ∑ t ∈ Finset.range (N + 1), if σ ω = (t : WithTop ℕ) then PsiN D X t ω else 0 := by
  classical
  obtain ⟨C, hC⟩ := hX.2
  obtain ⟨f₀, hf₀⟩ := hPe
  let fam : ℕ → Set (Ω → ℝ) := fun t => {h | ∃ τ : Ω → WithTop ℕ, IsBddStoppingTime ℱ N τ ∧
    (∀ ω, (t : WithTop ℕ) ≤ τ ω) ∧ ∃ f ∈ Pe D, h = (Q P₀ f)[stoppedValue X τ | ℱ t]}
  have hPsiN : ∀ t ≤ N, IsEssInf P₀ (ℱ t) (fam t) (PsiN D X t) := by
    intro t ht
    have hconst : IsBddStoppingTime ℱ N (fun _ => (t : WithTop ℕ)) :=
      ⟨isStoppingTime_const ℱ t, fun _ => by
        show (t : WithTop ℕ) ≤ (N : WithTop ℕ)
        exact_mod_cast ht⟩
    have key : IsEssInf P₀ (isStoppingTime_const ℱ t).measurableSpace
        (psiFamily D X (fun _ => (t : WithTop ℕ)) (isStoppingTime_const ℱ t)) (PsiN D X t) := by
      apply aux_pdp_essInfFamily_spec
      refine aux_pdp_exists (isStoppingTime_const ℱ t).measurableSpace_le
        ⟨_, (fun _ => (t : WithTop ℕ)), hconst, fun _ => le_rfl, f₀, hf₀, rfl⟩ ?_ (-C) ?_
      · rintro h ⟨τ, hτ, -, f, hf, rfl⟩
        exact stronglyMeasurable_condExp
      · rintro h ⟨τ, hτ, -, f, hf, rfl⟩
        exact aux_pdp_lb D X hX hC hf hτ (isStoppingTime_const ℱ t).measurableSpace_le
    have e1 : (isStoppingTime_const ℱ t).measurableSpace = ℱ t :=
      IsStoppingTime.measurableSpace_const ℱ t
    have e2 : psiFamily D X (fun _ => (t : WithTop ℕ)) (isStoppingTime_const ℱ t) = fam t := by
      ext h
      simp only [psiFamily, fam, e1]
    rw [e1, e2] at key
    exact key
  have hval : ∀ ω (k : ℕ), σ ω = (k : WithTop ℕ) →
      (∑ t ∈ Finset.range (N + 1), if σ ω = (t : WithTop ℕ) then PsiN D X t ω else 0) =
        PsiN D X k ω := by
    intro ω k hk
    have hkN : k ≤ N := by
      have := hσ.2 ω
      rw [hk] at this
      exact_mod_cast this
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro b _ hb
      simp [hk, Ne.symm hb]
    · intro hk'
      exact absurd (Finset.mem_range.2 (by omega)) hk'
  have key : IsEssInf P₀ hσ.1.measurableSpace (psiFamily D X σ hσ.1) (fun ω =>
      ∑ t ∈ Finset.range (N + 1), if σ ω = (t : WithTop ℕ) then PsiN D X t ω else 0) := by
    refine ⟨?_, ?_, ?_⟩
    · have hfun : (fun ω => ∑ t ∈ Finset.range (N + 1),
          if σ ω = (t : WithTop ℕ) then PsiN D X t ω else 0) = fun ω =>
          ∑ t ∈ Finset.range (N + 1), {ω | σ ω = (t : WithTop ℕ)}.indicator (PsiN D X t) ω := by
        funext ω
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases h : σ ω = (t : WithTop ℕ) <;> simp [h]
      rw [hfun]
      refine Finset.stronglyMeasurable_fun_sum _ fun t ht => ?_
      exact aux_pdp_ind_meas hσ.1 t (hPsiN t (Nat.lt_succ_iff.1 (Finset.mem_range.1 ht))).1
    · rintro h ⟨τ, hτ, hστ, f, hf, rfl⟩
      have hloc : ∀ t, ∀ᵐ ω ∂P₀, t ≤ N → σ ω = (t : WithTop ℕ) →
          PsiN D X t ω ≤ (Q P₀ f)[stoppedValue X τ | hσ.1.measurableSpace] ω := by
        intro t
        by_cases ht : t ≤ N
        · let τ' : Ω → WithTop ℕ := fun ω =>
            if σ ω = (t : WithTop ℕ) then τ ω else (N : WithTop ℕ)
          have hτ' : IsBddStoppingTime ℱ N τ' :=
            aux_pdp_piece_bdd (τ₂ := fun _ => (N : WithTop ℕ)) hσ.1 hτ
              ⟨isStoppingTime_const ℱ N, fun _ => le_rfl⟩ t
              (fun ω hω => by rw [← hω]; exact hστ ω) (fun ω _ => by exact_mod_cast ht)
          have hmem : (Q P₀ f)[stoppedValue X τ' | ℱ t] ∈ fam t := by
            refine ⟨τ', hτ', fun ω => ?_, f, hf, rfl⟩
            show (t : WithTop ℕ) ≤ (if σ ω = (t : WithTop ℕ) then τ ω else (N : WithTop ℕ))
            split_ifs with hω
            · rw [← hω]; exact hστ ω
            · exact_mod_cast ht
          have h1 := (hPsiN t ht).2.1 _ hmem
          have h2 := aux_pdp_loc D X hX hσ.1 t hf hτ hτ' (fun ω hω => by simp [τ', hω])
          filter_upwards [h1, h2] with ω hω1 hω2 _ hωt
          rw [hω2 hωt]
          exact hω1
        · exact Filter.Eventually.of_forall fun ω h => absurd h ht
      filter_upwards [ae_all_iff.2 hloc] with ω hω
      obtain ⟨k, hk, hσk⟩ := aux_pdp_exists_k hσ.2 ω
      rw [hval ω k hσk]
      exact hω k hk hσk
    · intro g' hg'meas hg'le
      have hloc : ∀ t, ∀ᵐ ω ∂P₀, t ≤ N → σ ω = (t : WithTop ℕ) → g' ω ≤ PsiN D X t ω := by
        intro t
        by_cases ht : t ≤ N
        · let g't : Ω → ℝ := fun ω => if σ ω = (t : WithTop ℕ) then g' ω else PsiN D X t ω
          have hg't_eq : g't = {ω | σ ω = (t : WithTop ℕ)}.indicator g' +
              {ω | σ ω = (t : WithTop ℕ)}ᶜ.indicator (PsiN D X t) := by
            funext ω
            by_cases h : σ ω = (t : WithTop ℕ) <;> simp [g't, h]
          have hg't_meas : StronglyMeasurable[ℱ t] g't := by
            rw [hg't_eq]
            exact (aux_pdp_ind_meas' hσ.1 t hg'meas).add
              ((hPsiN t ht).1.indicator (hσ.1.measurableSet_eq t).compl)
          have hg't_le : ∀ h ∈ fam t, g't ≤ᵐ[P₀] h := by
            rintro h ⟨τ, hτ, htτ, f, hf, rfl⟩
            let τ'' : Ω → WithTop ℕ := fun ω => if σ ω = (t : WithTop ℕ) then τ ω else σ ω
            have hτ'' : IsBddStoppingTime ℱ N τ'' :=
              aux_pdp_piece_bdd hσ.1 hτ hσ t (fun ω _ => htτ ω) (fun ω hω => le_of_eq hω.symm)
            have hmem : (Q P₀ f)[stoppedValue X τ'' | hσ.1.measurableSpace] ∈
                psiFamily D X σ hσ.1 := by
              refine ⟨τ'', hτ'', fun ω => ?_, f, hf, rfl⟩
              show σ ω ≤ (if σ ω = (t : WithTop ℕ) then τ ω else σ ω)
              split_ifs with hω
              · rw [hω]; exact htτ ω
              · exact le_rfl
            have h1 := hg'le _ hmem
            have h2 := aux_pdp_loc D X hX hσ.1 t hf hτ'' hτ (fun ω hω => by simp [τ'', hω])
            have h3 := (hPsiN t ht).2.1 _ ⟨τ, hτ, htτ, f, hf, rfl⟩
            filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
            by_cases hωt : σ ω = (t : WithTop ℕ)
            · simp only [g't, hωt, if_true]
              rw [← hω2 hωt]
              exact hω1
            · simp only [g't, hωt, if_false]
              exact hω3
          have := (hPsiN t ht).2.2 g't hg't_meas hg't_le
          filter_upwards [this] with ω hω _ hωt
          simpa [g't, hωt] using hω
        · exact Filter.Eventually.of_forall fun ω h => absurd h ht
      filter_upwards [ae_all_iff.2 hloc] with ω hω
      obtain ⟨k, hk, hσk⟩ := aux_pdp_exists_k hσ.2 ω
      rw [hval ω k hσk]
      exact hω k hk hσk
  exact aux_pdp_essInfFamily_eq key
end

end

/- Complete checked body: DensityBasics -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}

/-- The ordinary integral under a real nonnegative density. -/
theorem integral_Q_eq {f : Ω → ℝ} (hf : Integrable f P₀) (hn : 0 ≤ᵐ[P₀] f)
    (H : Ω → ℝ) : (∫ ω, H ω ∂Q P₀ f) = ∫ ω, f ω * H ω ∂P₀ := by
  rw [Q, integral_withDensity_eq_integral_toReal_smul₀
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [hn] with ω hω
  simp only [ENNReal.toReal_ofReal hω, smul_eq_mul]

theorem integrable_Q_iff {f : Ω → ℝ} (hf : Integrable f P₀) (hn : 0 ≤ᵐ[P₀] f)
    (H : Ω → ℝ) : Integrable H (Q P₀ f) ↔ Integrable (fun ω => f ω * H ω) P₀ := by
  rw [Q, integrable_withDensity_iff_integrable_smul₀'
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)]
  apply integrable_congr
  filter_upwards [hn] with ω hω
  simp only [ENNReal.toReal_ofReal hω, smul_eq_mul]

theorem density_probability {f : Ω → ℝ} (hf : Integrable f P₀)
    (hn : 0 ≤ᵐ[P₀] f) (hi : ∫ ω, f ω ∂P₀ = 1) : IsProbabilityMeasure (Q P₀ f) := by
  constructor
  rw [Q, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hf hn, hi]
  norm_num

theorem Q_eq_of_ae {f g : Ω → ℝ} (h : f =ᵐ[P₀] g) : Q P₀ f = Q P₀ g :=
  withDensity_congr_ae (h.fun_comp ENNReal.ofReal)

theorem density_ac_of_pos {f : Ω → ℝ} (hf : Integrable f P₀)
    (hp : ∀ᵐ ω ∂P₀, 0 < f ω) : P₀ ≪ Q P₀ f := by
  refine withDensity_absolutelyContinuous'
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal ?_
  filter_upwards [hp] with ω hω
  simpa using hω

variable {ℱ : Filtration ℕ m} {N : ℕ}

theorem test_probability (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ D.set) :
    IsProbabilityMeasure (Q P₀ f) :=
  density_probability (D.integrable f hf) (D.nonneg f hf) (D.integral_eq_one f hf)

theorem test_integral_eq (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ D.set)
    (H : Ω → ℝ) : (∫ ω, H ω ∂Q P₀ f) = ∫ ω, f ω * H ω ∂P₀ :=
  integral_Q_eq (D.integrable f hf) (D.nonneg f hf) H

theorem bounded_integrable_Q (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ D.set)
    {H : Ω → ℝ} (hH : AEStronglyMeasurable H P₀) {C : ℝ}
    (hC : ∀ᵐ ω ∂P₀, |H ω| ≤ C) : Integrable H (Q P₀ f) := by
  let := test_probability D hf
  apply Integrable.of_bound (hH.mono_ac (aux_pdp_Qac f)) C
  filter_upwards [(aux_pdp_Qac f).ae_le hC] with ω hω
  simpa only [Real.norm_eq_abs] using hω

theorem bounded_weighted_integrable (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ D.set)
    {H : Ω → ℝ} (hH : AEStronglyMeasurable H P₀) {C : ℝ}
    (hC : ∀ᵐ ω ∂P₀, |H ω| ≤ C) : Integrable (fun ω => f ω * H ω) P₀ :=
  (integrable_Q_iff (D.integrable f hf) (D.nonneg f hf) H).mp
    (bounded_integrable_Q D hf hH hC)

theorem condExp_bounded_Pe (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ Pe D)
    {H : Ω → ℝ} {C : ℝ} (hC : ∀ᵐ ω ∂P₀, |H ω| ≤ C) (m' : MeasurableSpace Ω) :
    ∀ᵐ ω ∂P₀, |(Q P₀ f)[H | m'] ω| ≤ C := by
  let := test_probability D hf.1
  exact (aux_pdp_acQ D hf).ae_le
    (ae_bdd_abs_condExp_of_ae_bdd_abs (m := m') ((aux_pdp_Qac f).ae_le hC))

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: ConditionalDensity -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

lemma Q_apply_eq {f : Ω → ℝ} (hf : Integrable f μ) (hn : 0 ≤ᵐ[μ] f)
    {s : Set Ω} (hs : MeasurableSet s) :
    Q μ f s = ENNReal.ofReal (∫ ω in s, f ω ∂μ) := by
  rw [Q, withDensity_apply _ hs]
  exact (ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_restrict_of_ae hn)).symm

lemma trim_Q_condExp [IsFiniteMeasure μ] {m' : MeasurableSpace Ω} (hm : m' ≤ m)
    {f : Ω → ℝ} (hf : Integrable f μ) (hn : 0 ≤ᵐ[μ] f) :
    (Q μ f).trim hm = (Q μ (μ[f | m'])).trim hm := by
  apply Measure.ext
  intro s hs
  rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs,
    Q_apply_eq hf hn (hm s hs),
    Q_apply_eq integrable_condExp (condExp_nonneg hn) (hm s hs),
    setIntegral_condExp hm hf hs]

lemma integrable_mul_condExp_iff [IsFiniteMeasure μ] {m' : MeasurableSpace Ω}
    (hm : m' ≤ m) {f r : Ω → ℝ} (hf : Integrable f μ) (hn : 0 ≤ᵐ[μ] f)
    (hr : StronglyMeasurable[m'] r) :
    Integrable (fun ω => f ω * r ω) μ ↔
      Integrable (fun ω => μ[f | m'] ω * r ω) μ := by
  rw [← integrable_Q_iff hf hn, ← integrable_Q_iff integrable_condExp (condExp_nonneg hn)]
  have he := trim_Q_condExp hm hf hn
  constructor
  · intro h
    apply integrable_of_integrable_trim hm
    rw [← he]
    exact h.trim hm hr
  · intro h
    apply integrable_of_integrable_trim hm
    rw [he]
    exact h.trim hm hr

lemma integral_mul_condExp [IsFiniteMeasure μ] {m' : MeasurableSpace Ω}
    (hm : m' ≤ m) {f r : Ω → ℝ} (hf : Integrable f μ) (hn : 0 ≤ᵐ[μ] f)
    (hr : StronglyMeasurable[m'] r) :
    (∫ ω, f ω * r ω ∂μ) = ∫ ω, μ[f | m'] ω * r ω ∂μ := by
  rw [← integral_Q_eq hf hn, ← integral_Q_eq integrable_condExp (condExp_nonneg hn)]
  rw [integral_trim hm hr, integral_trim hm hr, trim_Q_condExp hm hf hn]

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: StoppedDensity -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
variable {ℱ : Filtration ℕ m} {N : ℕ}

theorem stopped_stronglyMeasurable {X : ℕ → Ω → ℝ}
    (hX : ∀ n ≤ N, StronglyMeasurable[ℱ n] (X n))
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    StronglyMeasurable[hτ.1.measurableSpace] (stoppedValue X τ) := by
  rw [aux_pdp_sv_sum X hτ.2]
  apply Finset.stronglyMeasurable_fun_sum
  intro n hn
  exact aux_pdp_ind_meas hτ.1 n (hX n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)))

theorem stopped_Z_measurable (f : Ω → ℝ) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) :
    StronglyMeasurable[hτ.1.measurableSpace] (stoppedValue (Z P₀ ℱ f) τ) :=
  stopped_stronglyMeasurable (fun _ _ => stronglyMeasurable_condExp) τ hτ

noncomputable def pasteRatio (P₀ : Measure Ω) (ℱ : Filtration ℕ m)
    (f₀ f : Ω → ℝ) (τ : Ω → WithTop ℕ) : Ω → ℝ :=
  fun ω => stoppedValue (Z P₀ ℱ f₀) τ ω / stoppedValue (Z P₀ ℱ f) τ ω

theorem paste_eq_mul_ratio (f₀ f : Ω → ℝ) (τ : Ω → WithTop ℕ) :
    pasteDensity P₀ ℱ f₀ f τ = fun ω => f ω * pasteRatio P₀ ℱ f₀ f τ ω := by
  funext ω
  dsimp [pasteDensity, pasteRatio]
  ring

theorem pasteRatio_measurable (f₀ f : Ω → ℝ) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) :
    StronglyMeasurable[hτ.1.measurableSpace] (pasteRatio P₀ ℱ f₀ f τ) :=
  (stopped_Z_measurable f₀ τ hτ).div (stopped_Z_measurable f τ hτ)

variable [IsProbabilityMeasure P₀]

theorem stopped_Z_eq_condExp (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ D.set)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    stoppedValue (Z P₀ ℱ f) τ =ᵐ[P₀] P₀[f | hτ.1.measurableSpace] := by
  have h := (martingale_condExp f ℱ P₀).stoppedValue_ae_eq_condExp_of_le_const
    (n := N) hτ.1 hτ.2
  have he : Z P₀ ℱ f N = f :=
    condExp_of_stronglyMeasurable (ℱ.le N) (D.stronglyMeasurable f hf) (D.integrable f hf)
  change stoppedValue (Z P₀ ℱ f) τ =ᵐ[P₀] P₀[Z P₀ ℱ f N | hτ.1.measurableSpace] at h
  rwa [he] at h

theorem stopped_Z_integrable (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ D.set)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    Integrable (stoppedValue (Z P₀ ℱ f) τ) P₀ :=
  integrable_condExp.congr (stopped_Z_eq_condExp D hf τ hτ).symm

theorem stopped_Z_integral (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ D.set)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    (∫ ω, stoppedValue (Z P₀ ℱ f) τ ω ∂P₀) = 1 := by
  rw [integral_congr_ae (stopped_Z_eq_condExp D hf τ hτ),
    integral_condExp hτ.1.measurableSpace_le, D.integral_eq_one f hf]

theorem stopped_Z_pos (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ Pe D)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    ∀ᵐ ω ∂P₀, 0 < stoppedValue (Z P₀ ℱ f) τ ω := by
  have h := ae_all_iff.mpr (fun n => aux_l31_condExp_pos P₀ ℱ f (D.integrable f hf.1) hf.2 n)
  filter_upwards [h] with ω hω
  obtain ⟨k, _hk, he⟩ := aux_pdp_exists_k hτ.2 ω
  rw [aux_pdp_sv_of_eq _ he]
  exact hω k

theorem pasteRatio_mul_condExp (D : TestSet P₀ ℱ N) (f₀ : Ω → ℝ)
    {f : Ω → ℝ} (hf : f ∈ Pe D) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) :
    (fun ω => P₀[f | hτ.1.measurableSpace] ω * pasteRatio P₀ ℱ f₀ f τ ω) =ᵐ[P₀]
      stoppedValue (Z P₀ ℱ f₀) τ := by
  filter_upwards [stopped_Z_eq_condExp D hf.1 τ hτ, stopped_Z_pos D hf τ hτ] with ω he hp
  dsimp [pasteRatio]
  rw [← he]
  field_simp [hp.ne']

theorem paste_integrable (D : TestSet P₀ ℱ N) {f₀ f : Ω → ℝ}
    (hf₀ : f₀ ∈ D.set) (hf : f ∈ Pe D) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) : Integrable (pasteDensity P₀ ℱ f₀ f τ) P₀ := by
  rw [paste_eq_mul_ratio]
  apply (integrable_mul_condExp_iff hτ.1.measurableSpace_le (D.integrable f hf.1)
    (D.nonneg f hf.1) (pasteRatio_measurable f₀ f τ hτ)).mpr
  exact (stopped_Z_integrable D hf₀ τ hτ).congr (pasteRatio_mul_condExp D f₀ hf τ hτ).symm

theorem paste_integral (D : TestSet P₀ ℱ N) {f₀ f : Ω → ℝ}
    (hf₀ : f₀ ∈ D.set) (hf : f ∈ Pe D) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) : (∫ ω, pasteDensity P₀ ℱ f₀ f τ ω ∂P₀) = 1 := by
  rw [paste_eq_mul_ratio, integral_mul_condExp hτ.1.measurableSpace_le
    (D.integrable f hf.1) (D.nonneg f hf.1) (pasteRatio_measurable f₀ f τ hτ),
    integral_congr_ae (pasteRatio_mul_condExp D f₀ hf τ hτ), stopped_Z_integral D hf₀ τ hτ]

theorem paste_pos (D : TestSet P₀ ℱ N) {f₀ f : Ω → ℝ}
    (hf₀ : f₀ ∈ Pe D) (hf : f ∈ Pe D) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) : ∀ᵐ ω ∂P₀, 0 < pasteDensity P₀ ℱ f₀ f τ ω := by
  filter_upwards [stopped_Z_pos D hf₀ τ hτ, stopped_Z_pos D hf τ hτ, hf.2] with ω h₀ h hterm
  exact div_pos (mul_pos h₀ hterm) h

omit [IsProbabilityMeasure P₀] in
theorem paste_measurable (D : TestSet P₀ ℱ N) {f₀ f : Ω → ℝ}
    (hf : f ∈ D.set) (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    StronglyMeasurable[ℱ N] (pasteDensity P₀ ℱ f₀ f τ) := by
  rw [paste_eq_mul_ratio]
  exact (D.stronglyMeasurable f hf).mul
    ((pasteRatio_measurable f₀ f τ hτ).mono (hτ.1.measurableSpace_le_of_le_const hτ.2))

theorem paste_probability (D : TestSet P₀ ℱ N) {f₀ f : Ω → ℝ}
    (hf₀ : f₀ ∈ Pe D) (hf : f ∈ Pe D) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) : IsProbabilityMeasure (Q P₀ (pasteDensity P₀ ℱ f₀ f τ)) :=
  density_probability (paste_integrable D hf₀.1 hf τ hτ)
    ((paste_pos D hf₀ hf τ hτ).mono fun _ h => h.le) (paste_integral D hf₀.1 hf τ hτ)

theorem paste_mem_Pe (D : TestSet P₀ ℱ N) (hs : IsStable D) {f₀ f : Ω → ℝ}
    (hf₀ : f₀ ∈ Pe D) (hf : f ∈ Pe D) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) : pasteDensity P₀ ℱ f₀ f τ ∈ Pe D :=
  ⟨hs f₀ hf₀ f hf τ hτ, paste_pos D hf₀ hf τ hτ⟩

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: PastingExpectation -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω} [IsProbabilityMeasure P₀]
variable {ℱ : Filtration ℕ m} {N : ℕ}

theorem paste_claim_integrable (D : TestSet P₀ ℱ N) {f₀ f : Ω → ℝ}
    (hf₀ : f₀ ∈ Pe D) (hf : f ∈ Pe D) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) {H : Ω → ℝ}
    (hH : AEStronglyMeasurable H P₀) {C : ℝ} (hC : ∀ᵐ ω ∂P₀, |H ω| ≤ C) :
    Integrable H (Q P₀ (pasteDensity P₀ ℱ f₀ f τ)) := by
  let := paste_probability D hf₀ hf τ hτ
  apply Integrable.of_bound (hH.mono_ac (aux_pdp_Qac _)) C
  filter_upwards [(aux_pdp_Qac _).ae_le hC] with ω hω
  simpa only [Real.norm_eq_abs] using hω

theorem paste_expectation (D : TestSet P₀ ℱ N) {f₀ f : Ω → ℝ}
    (hf₀ : f₀ ∈ Pe D) (hf : f ∈ Pe D) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) {H : Ω → ℝ}
    (hH : AEStronglyMeasurable H P₀) {C : ℝ} (hC : ∀ᵐ ω ∂P₀, |H ω| ≤ C) :
    (∫ ω, H ω ∂Q P₀ (pasteDensity P₀ ℱ f₀ f τ)) =
      ∫ ω, (Q P₀ f)[H | hτ.1.measurableSpace] ω ∂Q P₀ f₀ := by
  let := test_probability D hf.1
  let g := pasteDensity P₀ ℱ f₀ f τ
  let R := pasteRatio P₀ ℱ f₀ f τ
  let V := (Q P₀ f)[H | hτ.1.measurableSpace]
  have hg : Integrable g P₀ := paste_integrable D hf₀.1 hf τ hτ
  have hgn : 0 ≤ᵐ[P₀] g := (paste_pos D hf₀ hf τ hτ).mono fun _ h => h.le
  have hr : StronglyMeasurable[hτ.1.measurableSpace] R := pasteRatio_measurable f₀ f τ hτ
  have hv : StronglyMeasurable[hτ.1.measurableSpace] V := stronglyMeasurable_condExp
  have hHf : Integrable H (Q P₀ f) := bounded_integrable_Q D hf.1 hH hC
  have hHg : Integrable H (Q P₀ g) := paste_claim_integrable D hf₀ hf τ hτ hH hC
  have he : g = fun ω => f ω * R ω := paste_eq_mul_ratio f₀ f τ
  have hRH : Integrable (fun ω => R ω * H ω) (Q P₀ f) := by
    apply (integrable_Q_iff (D.integrable f hf.1) (D.nonneg f hf.1) _).mpr
    have h := (integrable_Q_iff hg hgn H).mp hHg
    simpa only [he, mul_assoc] using h
  have hce := condExp_mul_of_stronglyMeasurable_left (μ := Q P₀ f) hr hRH hHf
  calc
    (∫ ω, H ω ∂Q P₀ g) = ∫ ω, g ω * H ω ∂P₀ := integral_Q_eq hg hgn H
    _ = ∫ ω, f ω * (R ω * H ω) ∂P₀ := by simp only [he, mul_assoc]
    _ = ∫ ω, R ω * H ω ∂Q P₀ f := (test_integral_eq D hf.1 _).symm
    _ = ∫ ω, R ω * V ω ∂Q P₀ f := by
      rw [← integral_condExp hτ.1.measurableSpace_le]
      exact integral_congr_ae hce
    _ = ∫ ω, f ω * (R ω * V ω) ∂P₀ := test_integral_eq D hf.1 _
    _ = ∫ ω, P₀[f | hτ.1.measurableSpace] ω * (R ω * V ω) ∂P₀ :=
      integral_mul_condExp hτ.1.measurableSpace_le (D.integrable f hf.1) (D.nonneg f hf.1) (hr.mul hv)
    _ = ∫ ω, stoppedValue (Z P₀ ℱ f₀) τ ω * V ω ∂P₀ := by
      apply integral_congr_ae
      filter_upwards [pasteRatio_mul_condExp D f₀ hf τ hτ] with ω hω
      rw [← mul_assoc]
      exact congrArg (fun z => z * V ω) hω
    _ = ∫ ω, P₀[f₀ | hτ.1.measurableSpace] ω * V ω ∂P₀ := by
      apply integral_congr_ae
      filter_upwards [stopped_Z_eq_condExp D hf₀.1 τ hτ] with ω hω
      exact congrArg (fun z => z * V ω) hω
    _ = ∫ ω, f₀ ω * V ω ∂P₀ :=
      (integral_mul_condExp hτ.1.measurableSpace_le (D.integrable f₀ hf₀.1)
        (D.nonneg f₀ hf₀.1) hv).symm
    _ = ∫ ω, V ω ∂Q P₀ f₀ := (test_integral_eq D hf₀.1 V).symm

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: PastingConditional -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
variable {ℱ : Filtration ℕ m} {N : ℕ}

theorem claim_indicator_bound {H : Ω → ℝ} {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ᵐ ω ∂P₀, |H ω| ≤ C) (A : Set Ω) :
    ∀ᵐ ω ∂P₀, |A.indicator H ω| ≤ C := by
  filter_upwards [hC] with ω hω
  by_cases h : ω ∈ A
  · simpa only [Set.indicator_of_mem h] using hω
  · simpa only [Set.indicator_of_notMem h, abs_zero] using h0

variable [IsProbabilityMeasure P₀]

theorem paste_condExp_at_stop (D : TestSet P₀ ℱ N) {f₀ f : Ω → ℝ}
    (hf₀ : f₀ ∈ Pe D) (hf : f ∈ Pe D) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) {H : Ω → ℝ}
    (hH : AEStronglyMeasurable H P₀) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ᵐ ω ∂P₀, |H ω| ≤ C) :
    (Q P₀ (pasteDensity P₀ ℱ f₀ f τ))[H | hτ.1.measurableSpace] =ᵐ[P₀]
      (Q P₀ f)[H | hτ.1.measurableSpace] := by
  let g := pasteDensity P₀ ℱ f₀ f τ
  let V := (Q P₀ f)[H | hτ.1.measurableSpace]
  let := test_probability D hf.1
  let := paste_probability D hf₀ hf τ hτ
  have hvm : StronglyMeasurable[hτ.1.measurableSpace] V := stronglyMeasurable_condExp
  have hva : AEStronglyMeasurable V P₀ := (hvm.mono hτ.1.measurableSpace_le).aestronglyMeasurable
  have hvb : ∀ᵐ ω ∂P₀, |V ω| ≤ C := condExp_bounded_Pe D hf hC _
  have hvi : Integrable V (Q P₀ g) := paste_claim_integrable D hf₀ hf τ hτ hva hvb
  have hHi : Integrable H (Q P₀ g) := paste_claim_integrable D hf₀ hf τ hτ hH hC
  have hac : P₀ ≪ Q P₀ g := density_ac_of_pos
    (paste_integrable D hf₀.1 hf τ hτ) (paste_pos D hf₀ hf τ hτ)
  apply hac.ae_le
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hτ.1.measurableSpace_le hHi
  · intro A _ _
    exact hvi.integrableOn
  · intro A hA _
    have hAm : MeasurableSet A := hτ.1.measurableSpace_le A hA
    rw [← integral_indicator hAm, ← integral_indicator hAm]
    rw [paste_expectation D hf₀ hf τ hτ (hva.indicator hAm) (claim_indicator_bound h0 hvb A),
      paste_expectation D hf₀ hf τ hτ (hH.indicator hAm) (claim_indicator_bound h0 hC A)]
    have hVf : Integrable V (Q P₀ f) := bounded_integrable_Q D hf.1 hva hvb
    rw [condExp_of_stronglyMeasurable hτ.1.measurableSpace_le (hvm.indicator hA)
      (hVf.indicator hAm)]
    have he := condExp_indicator (m := hτ.1.measurableSpace)
      (bounded_integrable_Q D hf.1 hH hC) hA
    apply integral_congr_ae
    exact Filter.EventuallyEq.symm ((aux_pdp_Qac f₀).ae_le ((aux_pdp_acQ D hf).ae_le he))
  · exact hvm.aestronglyMeasurable

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: ConditionalFork -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω} [IsProbabilityMeasure P₀]
variable {ℱ : Filtration ℕ m} {N : ℕ}

omit [IsProbabilityMeasure P₀] in
theorem test_condExp_eq_on (D : TestSet P₀ ℱ N) {f g : Ω → ℝ}
    (hf : f ∈ Pe D) (hg : g ∈ Pe D) {m' : MeasurableSpace Ω} (hm : m' ≤ m)
    {A : Set Ω} (hA : MeasurableSet[m'] A)
    (he : ∀ᵐ ω ∂P₀, ω ∈ A → f ω = g ω) {H : Ω → ℝ}
    (hH : AEStronglyMeasurable[m] H P₀) {C : ℝ} (hC : ∀ᵐ ω ∂P₀, |H ω| ≤ C) :
    ∀ᵐ ω ∂P₀, ω ∈ A → (Q P₀ f)[H | m'] ω = (Q P₀ g)[H | m'] ω := by
  let := test_probability D hf.1
  let := test_probability D hg.1
  have hAm := hm A hA
  have hmeasure : (Q P₀ f).restrict A = (Q P₀ g).restrict A := by
    rw [Q, Q, restrict_withDensity hAm, restrict_withDensity hAm]
    apply withDensity_congr_ae
    apply (ae_restrict_iff' hAm).mpr
    filter_upwards [he] with ω hω hωA
    rw [hω hωA]
  have hl := condExp_restrict_ae_eq_restrict (μ := Q P₀ f) hm hA (bounded_integrable_Q D hf.1 hH hC)
  have hr := condExp_restrict_ae_eq_restrict (μ := Q P₀ g) hm hA (bounded_integrable_Q D hg.1 hH hC)
  rw [← hmeasure] at hr
  exact (aux_pdp_acQ D hf).ae_le ((ae_restrict_iff' hAm).mp (hl.symm.trans hr))

noncomputable def forkTime (N n : ℕ) (A : Set Ω) : Ω → WithTop ℕ :=
  by
    classical
    exact fun ω => if ω ∈ A then N else n

theorem forkTime_bounded (n : ℕ) (hn : n ≤ N) (A : Set Ω) (hA : MeasurableSet[ℱ n] A) :
    IsBddStoppingTime ℱ N (forkTime N n A) := by
  classical
  constructor
  · intro k
    change MeasurableSet[ℱ k] {ω | forkTime N n A ω ≤ (k : WithTop ℕ)}
    by_cases hNk : N ≤ k
    · have he : {ω | forkTime N n A ω ≤ (k : WithTop ℕ)} = Set.univ := by
        ext ω
        by_cases hω : ω ∈ A <;> simp [forkTime, hω, hNk, hn.trans hNk]
      rw [he]
      exact MeasurableSet.univ
    · by_cases hnk : n ≤ k
      · have he : {ω | forkTime N n A ω ≤ (k : WithTop ℕ)} = Aᶜ := by
          ext ω
          by_cases hω : ω ∈ A <;> simp [forkTime, hω, hNk, hnk]
        rw [he]
        exact (ℱ.mono hnk A hA).compl
      · have he : {ω | forkTime N n A ω ≤ (k : WithTop ℕ)} = ∅ := by
          ext ω
          by_cases hω : ω ∈ A <;> simp [forkTime, hω, hNk, hnk]
        rw [he]
        exact @MeasurableSet.empty Ω (ℱ k)
  · intro ω
    by_cases hω : ω ∈ A <;> simp [forkTime, hω, hn]

omit [IsProbabilityMeasure P₀] in
theorem test_condExp_stopping_local (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ Pe D)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) (n : ℕ) (H : Ω → ℝ) :
    ∀ᵐ ω ∂P₀, τ ω = (n : WithTop ℕ) →
      (Q P₀ f)[H | hτ.measurableSpace] ω = (Q P₀ f)[H | ℱ n] ω := by
  let := test_probability D hf.1
  have hloc := condExp_stopping_time_ae_eq_restrict_eq_of_countable (μ := Q P₀ f) (f := H) hτ n
  have hA : MeasurableSet {ω | τ ω = (n : WithTop ℕ)} := ℱ.le n _ (hτ.measurableSet_eq n)
  exact (aux_pdp_acQ D hf).ae_le ((ae_restrict_iff' hA).mp hloc)

open Classical in
theorem exists_conditional_fork (D : TestSet P₀ ℱ N) (hs : IsStable D)
    {f₁ f₂ : Ω → ℝ} (hf₁ : f₁ ∈ Pe D) (hf₂ : f₂ ∈ Pe D)
    (n : ℕ) (hn : n ≤ N) (A : Set Ω) (hA : MeasurableSet[ℱ n] A) :
    ∃ g ∈ Pe D, ∀ (H : Ω → ℝ), AEStronglyMeasurable H P₀ →
      ∀ C : ℝ, 0 ≤ C → (∀ᵐ ω ∂P₀, |H ω| ≤ C) →
      (Q P₀ g)[H | ℱ n] =ᵐ[P₀]
        fun ω => if ω ∈ A then (Q P₀ f₁)[H | ℱ n] ω else (Q P₀ f₂)[H | ℱ n] ω := by
  classical
  let τ := forkTime N n A
  have hτ : IsBddStoppingTime ℱ N τ := forkTime_bounded n hn A hA
  let g := pasteDensity P₀ ℱ f₁ f₂ τ
  have hg : g ∈ Pe D := paste_mem_Pe D hs hf₁ hf₂ τ hτ
  have heA : ∀ᵐ ω ∂P₀, ω ∈ A → g ω = f₁ ω := by
    have h₁ : Z P₀ ℱ f₁ N = f₁ :=
      condExp_of_stronglyMeasurable (ℱ.le N) (D.stronglyMeasurable f₁ hf₁.1) (D.integrable f₁ hf₁.1)
    have h₂ : Z P₀ ℱ f₂ N = f₂ :=
      condExp_of_stronglyMeasurable (ℱ.le N) (D.stronglyMeasurable f₂ hf₂.1) (D.integrable f₂ hf₂.1)
    filter_upwards [hf₂.2] with ω hpos hωA
    have heτ : τ ω = (N : WithTop ℕ) := by simp [τ, forkTime, hωA]
    change stoppedValue (Z P₀ ℱ f₁) τ ω * f₂ ω / stoppedValue (Z P₀ ℱ f₂) τ ω = f₁ ω
    rw [aux_pdp_sv_of_eq _ heτ, aux_pdp_sv_of_eq _ heτ, h₁, h₂]
    exact mul_div_cancel_right₀ _ hpos.ne'
  refine ⟨g, hg, ?_⟩
  intro H hH C h0 hC
  have hon := test_condExp_eq_on D hg hf₁ (ℱ.le n) hA heA hH hC
  have hstop := paste_condExp_at_stop D hf₁ hf₂ τ hτ hH h0 hC
  have hlocg := test_condExp_stopping_local D hg hτ.1 n H
  have hloc₂ := test_condExp_stopping_local D hf₂ hτ.1 n H
  filter_upwards [hon, hstop, hlocg, hloc₂] with ω hAω hstopω hlg hl₂
  by_cases hω : ω ∈ A
  · rw [if_pos hω]
    exact hAω hω
  · rw [if_neg hω]
    have heτ : τ ω = (n : WithTop ℕ) := by simp [τ, forkTime, hω]
    exact (hlg heτ).symm.trans (hstopω.trans (hl₂ heτ))

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: EssentialInfimumProperties -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {m' : MeasurableSpace Ω} {S T : Set (Ω → ℝ)} {f g k : Ω → ℝ}

theorem isEssInf_bounded [IsFiniteMeasure μ] (hm : m' ≤ m)
    (hne : S.Nonempty) (hsm : ∀ h ∈ S, StronglyMeasurable[m'] h) (C : ℝ)
    (hb : ∀ h ∈ S, ∀ᵐ ω ∂μ, |h ω| ≤ C) :
    IsEssInf μ m' S (essInfFamily μ m' S) :=
  aux_pdp_essInfFamily_spec (aux_pdp_exists hm hne hsm (-C)
    (fun h hh => (hb h hh).mono fun _ hω => (abs_le.mp hω).1))

theorem isEssInf_abs_le (hf : IsEssInf μ m' S f) (hne : S.Nonempty) (C : ℝ)
    (hb : ∀ h ∈ S, ∀ᵐ ω ∂μ, |h ω| ≤ C) : ∀ᵐ ω ∂μ, |f ω| ≤ C := by
  obtain ⟨h, hh⟩ := hne
  have hl : (fun _ => -C) ≤ᵐ[μ] f := hf.2.2 _ stronglyMeasurable_const
    (fun h hh => (hb h hh).mono fun _ hω => (abs_le.mp hω).1)
  filter_upwards [hl, hf.2.1 h hh, hb h hh] with ω hlo hle hbo
  exact abs_le.mpr ⟨hlo, hle.trans (abs_le.mp hbo).2⟩

theorem isEssInf_mono_family (hf : IsEssInf μ m' S f) (hg : IsEssInf μ m' T g)
    (hST : ∀ t ∈ T, ∃ s ∈ S, s ≤ᵐ[μ] t) : f ≤ᵐ[μ] g := by
  apply hg.2.2 _ hf.1
  intro t ht
  obtain ⟨s, hs, hst⟩ := hST t ht
  exact (hf.2.1 s hs).trans hst

theorem isEssInf_congr_family (hf : IsEssInf μ m' S f) (hg : IsEssInf μ m' T g)
    (hST : ∀ t ∈ T, ∃ s ∈ S, s =ᵐ[μ] t)
    (hTS : ∀ s ∈ S, ∃ t ∈ T, t =ᵐ[μ] s) : f =ᵐ[μ] g :=
  (isEssInf_mono_family hf hg (fun t ht => by
    obtain ⟨s, hs, h⟩ := hST t ht
    exact ⟨s, hs, h.le⟩)).antisymm
  (isEssInf_mono_family hg hf (fun s hs => by
    obtain ⟨t, ht, h⟩ := hTS s hs
    exact ⟨t, ht, h.le⟩))

theorem isEssInf_local_le (hf : IsEssInf μ m' S f) (hg : IsEssInf μ m' T g)
    {A : Set Ω} (hA : MeasurableSet[m'] A)
    (hST : ∀ t ∈ T, ∃ s ∈ S, ∀ᵐ ω ∂μ, ω ∈ A → s ω ≤ t ω) :
    ∀ᵐ ω ∂μ, ω ∈ A → f ω ≤ g ω := by
  classical
  let z := A.piecewise f g
  have hz : StronglyMeasurable[m'] z := hf.1.piecewise hA hg.1
  have hle : z ≤ᵐ[μ] g := hg.2.2 z hz (by
    intro t ht
    obtain ⟨s, hs, hst⟩ := hST t ht
    filter_upwards [hf.2.1 s hs, hg.2.1 t ht, hst] with ω hfs hgt hstω
    by_cases hω : ω ∈ A
    · simpa [z, Set.piecewise, hω] using hfs.trans (hstω hω)
    · simpa [z, Set.piecewise, hω] using hgt)
  filter_upwards [hle] with ω hω hmem
  simpa [z, Set.piecewise, hmem] using hω

theorem isEssInf_translate (hf : IsEssInf μ m' S f) (hk : StronglyMeasurable[m'] k)
    (hST : ∀ t ∈ T, ∃ s ∈ S, t =ᵐ[μ] fun ω => s ω + k ω)
    (hTS : ∀ s ∈ S, ∃ t ∈ T, t =ᵐ[μ] fun ω => s ω + k ω) :
    IsEssInf μ m' T (fun ω => f ω + k ω) := by
  refine ⟨hf.1.add hk, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, he⟩ := hST t ht
    filter_upwards [hf.2.1 s hs, he] with ω hω heω
    rw [heω]
    linarith
  · intro z hz hzt
    have hzf : (fun ω => z ω - k ω) ≤ᵐ[μ] f := hf.2.2 _ (hz.sub hk) (by
      intro s hs
      obtain ⟨t, ht, he⟩ := hTS s hs
      filter_upwards [hzt t ht, he] with ω hω heω
      rw [heω] at hω
      linarith)
    filter_upwards [hzf] with ω hω
    linarith

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: RiskOperator -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
  {ℱ : Filtration ℕ m} {N : ℕ}

def condFamily (D : TestSet P₀ ℱ N) (H : Ω → ℝ) (m' : MeasurableSpace Ω) :
    Set (Ω → ℝ) := {h | ∃ f ∈ Pe D, h = (Q P₀ f)[H | m']}

noncomputable def lowerCond (D : TestSet P₀ ℱ N) (H : Ω → ℝ)
    (m' : MeasurableSpace Ω) : Ω → ℝ := essInfFamily P₀ m' (condFamily D H m')

theorem condFamily_nonempty (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    (H : Ω → ℝ) (m' : MeasurableSpace Ω) : (condFamily D H m').Nonempty := by
  obtain ⟨f, hf⟩ := hPe
  exact ⟨_, f, hf, rfl⟩

theorem condFamily_measurable (D : TestSet P₀ ℱ N) (H : Ω → ℝ)
    (m' : MeasurableSpace Ω) : ∀ h ∈ condFamily D H m', StronglyMeasurable[m'] h := by
  rintro h ⟨f, hf, rfl⟩
  exact stronglyMeasurable_condExp

theorem condFamily_bounded (D : TestSet P₀ ℱ N) {H : Ω → ℝ} {C : ℝ}
    (hH : ∀ᵐ ω ∂P₀, |H ω| ≤ C) (m' : MeasurableSpace Ω) :
    ∀ h ∈ condFamily D H m', ∀ᵐ ω ∂P₀, |h ω| ≤ C := by
  rintro h ⟨f, hf, rfl⟩
  exact condExp_bounded_Pe D hf hH m'

variable [IsProbabilityMeasure P₀]

theorem lowerCond_spec (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {H : Ω → ℝ} {C : ℝ} (hH : ∀ᵐ ω ∂P₀, |H ω| ≤ C)
    {m' : MeasurableSpace Ω} (hm : m' ≤ m) :
    IsEssInf P₀ m' (condFamily D H m') (lowerCond D H m') :=
  isEssInf_bounded hm (condFamily_nonempty D hPe H m')
    (condFamily_measurable D H m') C (condFamily_bounded D hH m')

theorem lowerCond_measurable (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {H : Ω → ℝ} {C : ℝ} (hH : ∀ᵐ ω ∂P₀, |H ω| ≤ C)
    {m' : MeasurableSpace Ω} (hm : m' ≤ m) : StronglyMeasurable[m'] (lowerCond D H m') :=
  (lowerCond_spec D hPe hH hm).1

theorem lowerCond_bounded (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {H : Ω → ℝ} {C : ℝ} (hH : ∀ᵐ ω ∂P₀, |H ω| ≤ C)
    {m' : MeasurableSpace Ω} (hm : m' ≤ m) :
    ∀ᵐ ω ∂P₀, |lowerCond D H m' ω| ≤ C :=
  isEssInf_abs_le (lowerCond_spec D hPe hH hm) (condFamily_nonempty D hPe H m')
    C (condFamily_bounded D hH m')

theorem lowerCond_le (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {H f : Ω → ℝ} {C : ℝ} (hH : ∀ᵐ ω ∂P₀, |H ω| ≤ C)
    {m' : MeasurableSpace Ω} (hm : m' ≤ m) (hf : f ∈ Pe D) :
    lowerCond D H m' ≤ᵐ[P₀] (Q P₀ f)[H | m'] :=
  (lowerCond_spec D hPe hH hm).2.1 _ ⟨f, hf, rfl⟩

theorem lowerCond_greatest (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {H g : Ω → ℝ} {C : ℝ} (hH : ∀ᵐ ω ∂P₀, |H ω| ≤ C)
    {m' : MeasurableSpace Ω} (hm : m' ≤ m) (hg : StronglyMeasurable[m'] g)
    (hle : ∀ f ∈ Pe D, g ≤ᵐ[P₀] (Q P₀ f)[H | m']) : g ≤ᵐ[P₀] lowerCond D H m' :=
  (lowerCond_spec D hPe hH hm).2.2 g hg (by
    rintro h ⟨f, hf, rfl⟩
    exact hle f hf)

theorem lowerCond_of_measurable (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {H : Ω → ℝ} {C : ℝ} (hH : ∀ᵐ ω ∂P₀, |H ω| ≤ C)
    {m' : MeasurableSpace Ω} (hm : m' ≤ m) (hsm : StronglyMeasurable[m'] H) :
    lowerCond D H m' =ᵐ[P₀] H := by
  have hce (f : Ω → ℝ) (hf : f ∈ Pe D) : (Q P₀ f)[H | m'] = H := by
    let := test_probability D hf.1
    exact condExp_of_stronglyMeasurable hm hsm
      (bounded_integrable_Q D hf.1 (hsm.mono hm).aestronglyMeasurable hH)
  obtain ⟨f, hf⟩ := hPe
  have hlo := lowerCond_le D ⟨f, hf⟩ hH hm hf
  rw [hce f hf] at hlo
  apply hlo.antisymm
  apply lowerCond_greatest D ⟨f, hf⟩ hH hm hsm
  intro g hg
  rw [hce g hg]

theorem lowerCond_mono (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {H K : Ω → ℝ} {C B : ℝ} (hH : ∀ᵐ ω ∂P₀, |H ω| ≤ C)
    (hK : ∀ᵐ ω ∂P₀, |K ω| ≤ B) (hsmH : AEStronglyMeasurable H P₀)
    (hsmK : AEStronglyMeasurable K P₀) (hle : H ≤ᵐ[P₀] K)
    {m' : MeasurableSpace Ω} (hm : m' ≤ m) :
    lowerCond D H m' ≤ᵐ[P₀] lowerCond D K m' := by
  apply isEssInf_mono_family (lowerCond_spec D hPe hH hm) (lowerCond_spec D hPe hK hm)
  rintro h ⟨f, hf, rfl⟩
  refine ⟨(Q P₀ f)[H | m'], ⟨f, hf, rfl⟩, ?_⟩
  exact (aux_pdp_acQ D hf).ae_le (condExp_mono
    (bounded_integrable_Q D hf.1 hsmH hH) (bounded_integrable_Q D hf.1 hsmK hK)
    ((aux_pdp_Qac f).ae_le hle))

theorem lowerCond_congr (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {H K : Ω → ℝ} {C B : ℝ} (hH : ∀ᵐ ω ∂P₀, |H ω| ≤ C)
    (hK : ∀ᵐ ω ∂P₀, |K ω| ≤ B) (he : H =ᵐ[P₀] K)
    {m' : MeasurableSpace Ω} (hm : m' ≤ m) :
    lowerCond D H m' =ᵐ[P₀] lowerCond D K m' := by
  apply isEssInf_congr_family (lowerCond_spec D hPe hH hm) (lowerCond_spec D hPe hK hm)
  · rintro h ⟨f, hf, rfl⟩
    exact ⟨_, ⟨f, hf, rfl⟩, (aux_pdp_acQ D hf).ae_le
      (condExp_congr_ae ((aux_pdp_Qac f).ae_le he))⟩
  · rintro h ⟨f, hf, rfl⟩
    exact ⟨_, ⟨f, hf, rfl⟩, (aux_pdp_acQ D hf).ae_le
      (condExp_congr_ae ((aux_pdp_Qac f).ae_le he.symm))⟩

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: RiskLocality -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

theorem condExp_local_eq {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {m' : MeasurableSpace Ω} {A : Set Ω} (hA : MeasurableSet[m'] A)
    {H K : Ω → ℝ} (hH : Integrable H μ) (hK : Integrable K μ)
    (he : ∀ᵐ ω ∂μ, ω ∈ A → H ω = K ω) :
    ∀ᵐ ω ∂μ, ω ∈ A → μ[H | m'] ω = μ[K | m'] ω := by
  classical
  have hind : A.indicator H =ᵐ[μ] A.indicator K := by
    filter_upwards [he] with ω hω
    by_cases ha : ω ∈ A
    · simp only [Set.indicator_of_mem ha, hω ha]
    · simp only [Set.indicator_of_notMem ha]
  have hc := (condExp_indicator hH hA).symm.trans
    ((condExp_congr_ae hind).trans (condExp_indicator hK hA))
  filter_upwards [hc] with ω hω ha
  simpa only [Set.indicator_of_mem ha] using hω

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
  {ℱ : Filtration ℕ m} {N : ℕ} [IsProbabilityMeasure P₀]

theorem lowerCond_local_eq (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {H K : Ω → ℝ} {C B : ℝ} (hH : ∀ᵐ ω ∂P₀, |H ω| ≤ C)
    (hK : ∀ᵐ ω ∂P₀, |K ω| ≤ B) (hsmH : AEStronglyMeasurable H P₀)
    (hsmK : AEStronglyMeasurable K P₀)
    {m' : MeasurableSpace Ω} (hm : m' ≤ m) {A : Set Ω} (hA : MeasurableSet[m'] A)
    (he : ∀ᵐ ω ∂P₀, ω ∈ A → H ω = K ω) :
    ∀ᵐ ω ∂P₀, ω ∈ A → lowerCond D H m' ω = lowerCond D K m' ω := by
  have hce (f : Ω → ℝ) (hf : f ∈ Pe D) :
      ∀ᵐ ω ∂P₀, ω ∈ A → (Q P₀ f)[H | m'] ω = (Q P₀ f)[K | m'] ω :=
    (aux_pdp_acQ D hf).ae_le (condExp_local_eq hA
      (bounded_integrable_Q D hf.1 hsmH hH) (bounded_integrable_Q D hf.1 hsmK hK)
      ((aux_pdp_Qac f).ae_le he))
  have hl := isEssInf_local_le (lowerCond_spec D hPe hH hm) (lowerCond_spec D hPe hK hm)
    hA (by
      rintro h ⟨f, hf, rfl⟩
      exact ⟨_, ⟨f, hf, rfl⟩, (hce f hf).mono fun _ h ha => (h ha).le⟩)
  have hr := isEssInf_local_le (lowerCond_spec D hPe hK hm) (lowerCond_spec D hPe hH hm)
    hA (by
      rintro h ⟨f, hf, rfl⟩
      exact ⟨_, ⟨f, hf, rfl⟩, (hce f hf).mono fun _ h ha => (h ha).ge⟩)
  filter_upwards [hl, hr] with ω hlω hrω ha
  exact (hlω ha).antisymm (hrω ha)

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: PsiProperties -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
  {ℱ : Filtration ℕ m} {N : ℕ}

theorem value_bound_stopped {X : ℕ → Ω → ℝ} {C : ℝ}
    (hC : ∀ n ≤ N, ∀ᵐ ω ∂P₀, |X n ω| ≤ C)
    {τ : Ω → WithTop ℕ} (hτ : ∀ ω, τ ω ≤ (N : WithTop ℕ)) :
    ∀ᵐ ω ∂P₀, |stoppedValue X τ ω| ≤ C := by
  have hall : ∀ᵐ ω ∂P₀, ∀ n, n ≤ N → |X n ω| ≤ C := ae_all_iff.mpr fun n => by
    by_cases hn : n ≤ N
    · exact (hC n hn).mono fun _ h _ => h
    · exact Filter.Eventually.of_forall fun _ h => (hn h).elim
  filter_upwards [hall] with ω hω
  obtain ⟨n, hn, he⟩ := aux_pdp_exists_k hτ ω
  rw [aux_pdp_sv_of_eq X he]
  exact hω n hn

theorem bounded_const_stop (n : ℕ) (hn : n ≤ N) :
    IsBddStoppingTime ℱ N (fun _ => (n : WithTop ℕ)) :=
  ⟨isStoppingTime_const ℱ n, fun _ => by
    show (n : WithTop ℕ) ≤ (N : WithTop ℕ)
    exact_mod_cast hn⟩

theorem stoppedValue_const_nat (X : ℕ → Ω → ℝ) (n : ℕ) :
    stoppedValue X (fun _ => (n : WithTop ℕ)) = X n := by
  funext ω
  exact aux_pdp_sv_of_eq X rfl

theorem psiFamily_nonempty (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    (X : ℕ → Ω → ℝ) (σ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ) :
    (psiFamily D X σ hσ.1).Nonempty := by
  obtain ⟨f, hf⟩ := hPe
  exact ⟨_, σ, hσ, fun _ => le_rfl, f, hf, rfl⟩

theorem psiFamily_bounded (D : TestSet P₀ ℱ N) {X : ℕ → Ω → ℝ} {C : ℝ}
    (hC : ∀ n ≤ N, ∀ᵐ ω ∂P₀, |X n ω| ≤ C)
    (σ : Ω → WithTop ℕ) (hσ : IsStoppingTime ℱ σ) :
    ∀ h ∈ psiFamily D X σ hσ, ∀ᵐ ω ∂P₀, |h ω| ≤ C := by
  rintro h ⟨τ, hτ, -, f, hf, rfl⟩
  exact condExp_bounded_Pe D hf (value_bound_stopped hC hτ.2) _

variable [IsProbabilityMeasure P₀]

theorem psi_spec (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    (σ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ) :
    IsEssInf P₀ hσ.1.measurableSpace (psiFamily D X σ hσ.1) (Psi D X σ hσ.1) := by
  obtain ⟨C, hC⟩ := hX.2
  exact isEssInf_bounded hσ.1.measurableSpace_le (psiFamily_nonempty D hPe X σ hσ)
    (by rintro h ⟨τ, hτ, -, f, hf, rfl⟩; exact stronglyMeasurable_condExp)
    C (psiFamily_bounded D hC σ hσ.1)

theorem psi_bounded (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X) {C : ℝ}
    (hC : ∀ n ≤ N, ∀ᵐ ω ∂P₀, |X n ω| ≤ C)
    (σ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ) :
    ∀ᵐ ω ∂P₀, |Psi D X σ hσ.1 ω| ≤ C :=
  isEssInf_abs_le (psi_spec D hPe hX σ hσ) (psiFamily_nonempty D hPe X σ hσ)
    C (psiFamily_bounded D hC σ hσ.1)

theorem psi_le_condExp (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    (σ τ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ)
    (hτ : IsBddStoppingTime ℱ N τ) (hστ : ∀ ω, σ ω ≤ τ ω)
    {f : Ω → ℝ} (hf : f ∈ Pe D) :
    Psi D X σ hσ.1 ≤ᵐ[P₀] (Q P₀ f)[stoppedValue X τ | hσ.1.measurableSpace] :=
  (psi_spec D hPe hX σ hσ).2.1 _ ⟨τ, hτ, hστ, f, hf, rfl⟩

theorem psi_le_stopped (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    (σ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ) :
    Psi D X σ hσ.1 ≤ᵐ[P₀] stoppedValue X σ := by
  obtain ⟨f, hf⟩ := hPe
  let := test_probability D hf.1
  have h := psi_le_condExp D ⟨f, hf⟩ hX σ σ hσ hσ (fun _ => le_rfl) hf
  rwa [condExp_of_stronglyMeasurable hσ.1.measurableSpace_le
    (stopped_stronglyMeasurable hX.1 σ hσ) (aux_pdp_sv_int D X hX hf.1 hσ)] at h

theorem psiN_measurable (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X) {n : ℕ} (hn : n ≤ N) :
    StronglyMeasurable[ℱ n] (PsiN D X n) := by
  have h := (psi_spec D hPe hX _ (bounded_const_stop n hn)).1
  have he : (bounded_const_stop (ℱ := ℱ) n hn).1.measurableSpace = ℱ n :=
    IsStoppingTime.measurableSpace_const ℱ n
  exact he ▸ h

theorem psiN_bounded (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X) {C : ℝ}
    (hC : ∀ n ≤ N, ∀ᵐ ω ∂P₀, |X n ω| ≤ C) {n : ℕ} (hn : n ≤ N) :
    ∀ᵐ ω ∂P₀, |PsiN D X n ω| ≤ C :=
  psi_bounded D hPe hX hC _ (bounded_const_stop n hn)

theorem psi_valueProcess (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X) :
    IsValueProcess P₀ ℱ N (PsiN D X) := by
  refine ⟨fun _ hn => psiN_measurable D hPe hX hn, ?_⟩
  obtain ⟨C, hC⟩ := hX.2
  exact ⟨C, fun _ hn => psiN_bounded D hPe hX hC hn⟩

theorem psiN_le_X (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X) {n : ℕ} (hn : n ≤ N) :
    PsiN D X n ≤ᵐ[P₀] X n := by
  have h := psi_le_stopped D hPe hX _ (bounded_const_stop n hn)
  simpa only [PsiN, stoppedValue_const_nat] using h

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: StoppingProcesses -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
  {ℱ : Filtration ℕ m} {N : ℕ}

theorem value_nonneg_bound {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≤ N, ∀ᵐ ω ∂P₀, |X n ω| ≤ C := by
  obtain ⟨C, hC⟩ := hX.2
  exact ⟨|C|, abs_nonneg C, fun n hn => (hC n hn).mono fun _ h => h.trans (le_abs_self C)⟩

def prevProcess (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ := if n=0 then 0 else X (n-1)

theorem prevProcess_measurable {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    {n : ℕ} (hn : n ≤ N) : StronglyMeasurable[ℱ n] (prevProcess X n) := by
  classical
  by_cases h0 : n=0
  · simp only [prevProcess, if_pos h0]
    exact stronglyMeasurable_zero
  · rw [prevProcess, if_neg h0]
    exact (hX.1 (n-1) (by omega)).mono (ℱ.mono (by omega))

theorem prevProcess_bound {X : ℕ → Ω → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ n ≤ N, ∀ᵐ ω ∂P₀, |X n ω| ≤ C) {n : ℕ} (hn : n ≤ N) :
    ∀ᵐ ω ∂P₀, |prevProcess X n ω| ≤ C := by
  classical
  by_cases h0 : n=0
  · simpa only [prevProcess, if_pos h0, Pi.zero_apply, abs_zero] using
      (Filter.Eventually.of_forall fun _ : Ω => hC0 : ∀ᵐ _ω ∂P₀, 0 ≤ C)
  · simpa only [prevProcess, if_neg h0] using hC (n-1) (by omega)

theorem Xprev_eq_stopped (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) : Xprev X τ = stoppedValue (prevProcess X) τ := by
  classical
  funext ω
  obtain ⟨k, hk, he⟩ := aux_pdp_exists_k hτ.2 ω
  rw [aux_pdp_sv_of_eq (prevProcess X) he]
  simp [Xprev, prevProcess, he, WithTop.untopA]
  split_ifs <;> rfl

theorem Xprev_measurable {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    StronglyMeasurable[hτ.1.measurableSpace] (Xprev X τ) := by
  rw [Xprev_eq_stopped X τ hτ]
  exact stopped_stronglyMeasurable (fun _ hn => prevProcess_measurable hX hn) τ hτ

theorem Xprev_bound {X : ℕ → Ω → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ n ≤ N, ∀ᵐ ω ∂P₀, |X n ω| ≤ C)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    ∀ᵐ ω ∂P₀, |Xprev X τ ω| ≤ C := by
  rw [Xprev_eq_stopped X τ hτ]
  exact value_bound_stopped (fun _ hn => prevProcess_bound hC0 hC hn) hτ.2

theorem stopping_indicator_le_measurable {τ : Ω → WithTop ℕ}
    (hτ : IsBddStoppingTime ℱ N τ) {H : Ω → ℝ}
    (hH : StronglyMeasurable[hτ.1.measurableSpace] H) (n : ℕ) :
    StronglyMeasurable[ℱ n] ({ω | τ ω ≤ (n : WithTop ℕ)}.indicator H) := by
  classical
  have he : {ω | τ ω ≤ (n : WithTop ℕ)}.indicator H =
      fun ω => ∑ k ∈ Finset.range (n+1), {ω | τ ω=(k:WithTop ℕ)}.indicator H ω := by
    funext ω
    obtain ⟨k, hk, he⟩ := aux_pdp_exists_k hτ.2 ω
    by_cases hkn : k ≤ n
    · rw [Finset.sum_eq_single k]
      · simp [he, hkn]
      · intro j _ hj
        simp [he, Ne.symm hj]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr (by omega))).elim
    · have hz : ∑ j ∈ Finset.range (n+1), {ω | τ ω=(j:WithTop ℕ)}.indicator H ω = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hjn := Finset.mem_range.mp hj
        have hkj : k ≠ j := by omega
        simp [he, hkj]
      rw [hz]
      simp [he, hkn]
  rw [he]
  apply Finset.stronglyMeasurable_fun_sum
  intro k hk
  exact (aux_pdp_ind_meas' hτ.1 k hH).mono (ℱ.mono (by
    have := Finset.mem_range.mp hk
    omega))

theorem fromStop_bound {X : ℕ → Ω → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ n ≤ N, ∀ᵐ ω ∂P₀, |X n ω| ≤ C)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) {n : ℕ} (hn : n ≤ N) :
    ∀ᵐ ω ∂P₀, |fromStop X τ n ω| ≤ 2*C := by
  classical
  filter_upwards [hC n hn, Xprev_bound hC0 hC τ hτ] with ω hx hp
  dsimp [fromStop]
  split_ifs
  · exact (abs_sub _ _).trans (by linarith)
  · simpa only [abs_zero] using mul_nonneg (by norm_num : (0:ℝ)≤2) hC0

theorem fromStop_valueProcess {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    IsValueProcess P₀ ℱ N (fromStop X τ) := by
  classical
  refine ⟨?_, ?_⟩
  · intro n hn
    have he : fromStop X τ n = {ω | τ ω ≤ (n:WithTop ℕ)}.indicator (X n) -
        {ω | τ ω ≤ (n:WithTop ℕ)}.indicator (Xprev X τ) := by
      funext ω
      by_cases hω : τ ω ≤ (n:WithTop ℕ) <;> simp [fromStop, hω]
    rw [he]
    exact ((hX.1 n hn).indicator (hτ.1.measurableSet_le n)).sub
      (stopping_indicator_le_measurable hτ (Xprev_measurable hX τ hτ) n)
  · obtain ⟨C, hC0, hC⟩ := value_nonneg_bound hX
    exact ⟨2*C, fun _ hn => fromStop_bound hC0 hC τ hτ hn⟩

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: EssentialInfimumBasis -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

/- This strengthened witness export follows the complete accepted @mrfancypants
   aux_pdp_exists proof, whose unchanged original and full attributed body are preserved.
   Only the returned existential witness is exposed as its countable family. -/
theorem essInf_countable_basis {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {m' : MeasurableSpace Ω} (hm : m' ≤ m)
    {S : Set (Ω → ℝ)} (hne : S.Nonempty) (hmeas : ∀ h ∈ S, StronglyMeasurable[m'] h)
    (c : ℝ) (hc : ∀ h ∈ S, ∀ᵐ ω ∂μ, c ≤ h ω) : ∃ s : ℕ → S, IsEssInf μ m' S (fun ω => ⨅ n, max c ((s n : Ω → ℝ) ω)) := by
  classical
  obtain ⟨h₀, hh₀⟩ := hne
  let G : (ℕ → S) → Ω → ℝ := fun s ω => ⨅ n, max c ((s n : Ω → ℝ) ω)
  have hGmeas : ∀ s, Measurable[m'] (G s) := fun s =>
    Measurable.iInf (fun n => measurable_const.max (hmeas _ (s n).2).measurable)
  have hGbdd : ∀ (s : ℕ → S) ω, BddBelow (Set.range fun n => max c ((s n : Ω → ℝ) ω)) :=
    fun s ω => ⟨c, by rintro _ ⟨n, rfl⟩; exact le_max_left _ _⟩
  have hGle : ∀ s n ω, G s ω ≤ max c ((s n : Ω → ℝ) ω) := fun s n ω => ciInf_le (hGbdd s ω) n
  have hint : ∀ s, Integrable (fun ω => Real.arctan (G s ω)) μ := by
    intro s
    refine Integrable.of_bound ?_ (Real.pi / 2) (Filter.Eventually.of_forall fun ω => ?_)
    · exact (Real.continuous_arctan.measurable.comp ((hGmeas s).mono hm le_rfl)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_le]
      exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  let φ : (ℕ → S) → ℝ := fun s => ∫ ω, Real.arctan (G s ω) ∂μ
  have hφmono : ∀ s s', (∀ ω, G s ω ≤ G s' ω) → φ s ≤ φ s' := fun s s' h =>
    integral_mono (hint s) (hint s') (fun ω => Real.arctan_strictMono.monotone (h ω))
  have hVne : (Set.range φ).Nonempty := ⟨_, ⟨fun _ => ⟨h₀, hh₀⟩, rfl⟩⟩
  have hVbdd : BddBelow (Set.range φ) := by
    refine ⟨∫ _ω, (-(Real.pi / 2)) ∂μ, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact integral_mono (integrable_const _) (hint s)
      (fun ω => (Real.neg_pi_div_two_lt_arctan _).le)
  obtain ⟨u, -, hu_tend, hu_mem⟩ := exists_seq_tendsto_sInf hVne hVbdd
  choose s hs using hu_mem
  let s' : ℕ → S := fun n => s n.unpair.1 n.unpair.2
  have hs'le : ∀ k ω, G s' ω ≤ G (s k) ω := by
    intro k ω
    refine le_ciInf fun j => ?_
    have := hGle s' (Nat.pair k j) ω
    simpa [s', Nat.unpair_pair] using this
  have hφs' : φ s' = sInf (Set.range φ) := by
    refine le_antisymm ?_ (csInf_le hVbdd ⟨s', rfl⟩)
    refine ge_of_tendsto' hu_tend fun k => ?_
    rw [← hs k]
    exact hφmono _ _ (hs'le k)
  refine ⟨s', (hGmeas s').stronglyMeasurable, ?_, ?_⟩
  · intro h hh
    let s'' : ℕ → S := fun n => if n = 0 then ⟨h, hh⟩ else s' (n - 1)
    have h1 : ∀ ω, G s'' ω ≤ G s' ω := by
      intro ω
      refine le_ciInf fun j => ?_
      have := hGle s'' (j + 1) ω
      simpa [s''] using this
    have h2 : ∀ ω, G s'' ω ≤ max c (h ω) := by
      intro ω
      have := hGle s'' 0 ω
      simpa [s''] using this
    have h3 : φ s' ≤ φ s'' := by
      rw [hφs']
      exact csInf_le hVbdd ⟨s'', rfl⟩
    have h4 : ∫ ω, (Real.arctan (G s' ω) - Real.arctan (G s'' ω)) ∂μ = 0 := by
      rw [integral_sub (hint s') (hint s'')]
      have := hφmono _ _ h1
      simp only [φ] at this h3
      linarith
    have h5 := (integral_eq_zero_iff_of_nonneg (fun ω => sub_nonneg.2
      (Real.arctan_strictMono.monotone (h1 ω))) ((hint s').sub (hint s''))).1 h4
    filter_upwards [h5, hc h hh] with ω hω hcω
    have : G s' ω = G s'' ω := by
      have := sub_eq_zero.1 hω
      exact Real.arctan_injective this
    change G s' ω ≤ h ω
    rw [this]
    exact (h2 ω).trans (max_le hcω le_rfl)
  · intro g' _ hg'
    have : ∀ᵐ ω ∂μ, ∀ n, g' ω ≤ (s' n : Ω → ℝ) ω :=
      ae_all_iff.2 fun n => hg' _ (s' n).2
    filter_upwards [this] with ω hω
    exact le_ciInf fun n => (hω n).trans (le_max_right _ _)

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: EssentialInfimumApprox -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

/-- A bounded family closed under minima up to null sets admits decreasing
    approximants from the family itself. The underlying measurable space is arbitrary. -/
theorem essInf_decreasing_sequence {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ] {m' : MeasurableSpace Ω} (hm : m' ≤ m)
    (S : Set (Ω → ℝ)) (hne : S.Nonempty)
    (hsm : ∀ h ∈ S, StronglyMeasurable[m'] h) (C : ℝ)
    (hb : ∀ h ∈ S, ∀ᵐ ω ∂μ, |h ω| ≤ C)
    (hmin : ∀ f ∈ S, ∀ g ∈ S, ∃ h ∈ S, h =ᵐ[μ] fun ω => min (f ω) (g ω)) :
    ∃ u : ℕ → Ω → ℝ, (∀ n, u n ∈ S) ∧
      (∀ n, u (n + 1) ≤ᵐ[μ] u n) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => u n ω) atTop (𝓝 (essInfFamily μ m' S ω)) := by
  classical
  obtain ⟨s, hs⟩ := essInf_countable_basis hm hne hsm (-C) (fun h hh =>
    (hb h hh).mono fun ω hω => (abs_le.mp hω).1)
  let merge (f g : S) : S := ⟨(hmin f f.2 g g.2).choose,
    (hmin f f.2 g g.2).choose_spec.1⟩
  have hmerge (f g : S) : (merge f g : Ω → ℝ) =ᵐ[μ]
      fun ω => min ((f : Ω → ℝ) ω) ((g : Ω → ℝ) ω) := (hmin f f.2 g g.2).choose_spec.2
  let u : ℕ → S := Nat.rec (s 0) (fun n prev => merge prev (s (n + 1)))
  have hu (n : ℕ) : (u (n + 1)).1 =ᵐ[μ]
      fun ω => min ((u n).1 ω) ((s (n + 1)).1 ω) := by
    exact hmerge (u n) (s (n + 1))
  have hmono (n : ℕ) : (u (n + 1)).1 ≤ᵐ[μ] (u n).1 :=
    (hu n).mono fun ω hω => hω.le.trans (min_le_left _ _)
  refine ⟨fun n => (u n).1, fun n => (u n).2, hmono, ?_⟩
  have heq := aux_pdp_essInfFamily_eq hs
  have hba : ∀ᵐ ω ∂μ, ∀ n, |(u n).1 ω| ≤ C :=
    ae_all_iff.mpr fun n => hb _ (u n).2
  have hbs : ∀ᵐ ω ∂μ, ∀ n, |(s n).1 ω| ≤ C :=
    ae_all_iff.mpr fun n => hb _ (s n).2
  have hua : ∀ᵐ ω ∂μ, ∀ n, (u (n+1)).1 ω =
      min ((u n).1 ω) ((s (n+1)).1 ω) := ae_all_iff.mpr hu
  filter_upwards [heq, hba, hbs, hua] with ω heqω hbaω hbsω huaω
  let v : ℕ → ℝ := fun n => (u n).1 ω
  let g : ℝ := ⨅ n, max (-C) ((s n).1 ω)
  have hbv : BddBelow (Set.range v) := ⟨-C, by
    rintro _ ⟨n, rfl⟩
    exact (abs_le.mp (hbaω n)).1⟩
  have hbg : BddBelow (Set.range fun n => max (-C) ((s n).1 ω)) :=
    ⟨-C, by rintro _ ⟨n, rfl⟩; exact le_max_left _ _⟩
  have hvs : ∀ n, v n ≤ (s n).1 ω := by
    intro n
    cases n with
    | zero => exact le_rfl
    | succ n => exact (huaω n).le.trans (min_le_right _ _)
  have hgs : ∀ n, g ≤ (s n).1 ω := by
    intro n
    have h := ciInf_le hbg n
    simpa only [max_eq_right (abs_le.mp (hbsω n)).1] using h
  have hgv : ∀ n, g ≤ v n := by
    intro n
    induction n with
    | zero => exact hgs 0
    | succ n ih =>
      change g ≤ (u (n+1)).1 ω
      rw [huaω n]
      exact le_min ih (hgs (n+1))
  have hvanti : Antitone v := antitone_nat_of_succ_le fun n =>
    (huaω n).le.trans (min_le_left _ _)
  have hinf : (⨅ n, v n) = g := le_antisymm
    (le_ciInf fun n => (ciInf_le hbv n).trans ((hvs n).trans (le_max_right _ _)))
    (le_ciInf hgv)
  have ht := tendsto_atTop_ciInf hvanti hbv
  rw [hinf] at ht
  simpa only [heqω] using ht

/-- Bounded a.e. convergence transfers to every absolutely continuous finite measure. -/
theorem integral_tendsto_of_bounded_ae {Ω : Type*} {m : MeasurableSpace Ω}
    {μ ν : Measure Ω} [IsFiniteMeasure ν] (hν : ν ≪ μ)
    {u : ℕ → Ω → ℝ} {g : Ω → ℝ} (C : ℝ)
    (hsm : ∀ n, AEStronglyMeasurable (u n) μ)
    (hb : ∀ n, ∀ᵐ ω ∂μ, |u n ω| ≤ C)
    (ht : ∀ᵐ ω ∂μ, Tendsto (fun n => u n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n => ∫ ω, u n ω ∂ν) atTop (𝓝 (∫ ω, g ω ∂ν)) := by
  apply tendsto_integral_of_dominated_convergence (F := u) (f := g) (μ := ν) (fun _ => C)
    (fun n => (hsm n).mono_ac hν) (integrable_const C)
  · intro n
    filter_upwards [hν.ae_le (hb n)] with ω hω
    simpa only [Real.norm_eq_abs] using hω
  · exact hν.ae_le ht

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: PsiApproximation -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
  {ℱ : Filtration ℕ m} {N : ℕ} [IsProbabilityMeasure P₀]

def timePsiFamily (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (n : ℕ) : Set (Ω → ℝ) :=
  {h | ∃ τ : Ω → WithTop ℕ, IsBddStoppingTime ℱ N τ ∧
    (∀ ω, (n : WithTop ℕ) ≤ τ ω) ∧ ∃ f ∈ Pe D, h = (Q P₀ f)[stoppedValue X τ | ℱ n]}

theorem psiN_spec_time (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X) {n : ℕ} (hn : n ≤ N) :
    IsEssInf P₀ (ℱ n) (timePsiFamily D X n) (PsiN D X n) := by
  let hσ := bounded_const_stop (ℱ := ℱ) n hn
  have e1 : hσ.1.measurableSpace = ℱ n := IsStoppingTime.measurableSpace_const ℱ n
  have e2 : psiFamily D X (fun _ => (n : WithTop ℕ)) hσ.1 = timePsiFamily D X n := by
    ext h
    simp only [psiFamily, timePsiFamily, e1]
  have h := psi_spec D hPe hX (fun _ => (n : WithTop ℕ)) hσ
  rw [e1, e2] at h
  exact h

omit [IsProbabilityMeasure P₀] in
theorem timePsiFamily_nonempty (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    (X : ℕ → Ω → ℝ) {n : ℕ} (hn : n ≤ N) : (timePsiFamily D X n).Nonempty := by
  obtain ⟨f, hf⟩ := hPe
  exact ⟨_, (fun _ => (n : WithTop ℕ)), bounded_const_stop n hn, fun _ => le_rfl, f, hf, rfl⟩

omit [IsProbabilityMeasure P₀] in
theorem timePsiFamily_measurable (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (n : ℕ) :
    ∀ h ∈ timePsiFamily D X n, StronglyMeasurable[ℱ n] h := by
  rintro h ⟨τ, hτ, -, f, hf, rfl⟩
  exact stronglyMeasurable_condExp

omit [IsProbabilityMeasure P₀] in
theorem timePsiFamily_bounded (D : TestSet P₀ ℱ N) {X : ℕ → Ω → ℝ} {C : ℝ}
    (hC : ∀ n ≤ N, ∀ᵐ ω ∂P₀, |X n ω| ≤ C) (n : ℕ) :
    ∀ h ∈ timePsiFamily D X n, ∀ᵐ ω ∂P₀, |h ω| ≤ C := by
  rintro h ⟨τ, hτ, -, f, hf, rfl⟩
  exact condExp_bounded_Pe D hf (value_bound_stopped hC hτ.2) _

noncomputable def eventStop (A : Set Ω) (τ₁ τ₂ : Ω → WithTop ℕ) : Ω → WithTop ℕ :=
  by
    classical
    exact A.piecewise τ₁ τ₂

theorem eventStop_bounded {n : ℕ} {A : Set Ω} (hA : MeasurableSet[ℱ n] A)
    {τ₁ τ₂ : Ω → WithTop ℕ} (hτ₁ : IsBddStoppingTime ℱ N τ₁)
    (hτ₂ : IsBddStoppingTime ℱ N τ₂) (hl₁ : ∀ ω, (n:WithTop ℕ) ≤ τ₁ ω)
    (hl₂ : ∀ ω, (n:WithTop ℕ) ≤ τ₂ ω) :
    IsBddStoppingTime ℱ N (eventStop A τ₁ τ₂) ∧
      ∀ ω, (n:WithTop ℕ) ≤ eventStop A τ₁ τ₂ ω := by
  classical
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro k
    change MeasurableSet[ℱ k] {ω | eventStop A τ₁ τ₂ ω ≤ (k : WithTop ℕ)}
    by_cases hnk : n ≤ k
    · have he : {ω | eventStop A τ₁ τ₂ ω ≤ (k:WithTop ℕ)} =
          (A ∩ {ω | τ₁ ω ≤ (k:WithTop ℕ)}) ∪ (Aᶜ ∩ {ω | τ₂ ω ≤ (k:WithTop ℕ)}) := by
        ext ω
        by_cases hω : ω ∈ A <;> simp [eventStop, Set.piecewise, hω]
      rw [he]
      exact ((ℱ.mono hnk A hA).inter (hτ₁.1 k)).union
        ((ℱ.mono hnk A hA).compl.inter (hτ₂.1 k))
    · have hkn : (k:WithTop ℕ) < (n:WithTop ℕ) := by exact_mod_cast (not_le.mp hnk)
      have he : {ω | eventStop A τ₁ τ₂ ω ≤ (k:WithTop ℕ)} = ∅ := by
        ext ω
        have h1 : ¬τ₁ ω ≤ (k:WithTop ℕ) := not_le.mpr (hkn.trans_le (hl₁ ω))
        have h2 : ¬τ₂ ω ≤ (k:WithTop ℕ) := not_le.mpr (hkn.trans_le (hl₂ ω))
        by_cases hω : ω ∈ A <;> simp [eventStop, Set.piecewise, hω, h1, h2]
      rw [he]
      exact @MeasurableSet.empty Ω (ℱ k)
  · intro ω
    by_cases hω : ω ∈ A
    · simpa only [eventStop, Set.piecewise, if_pos hω] using hτ₁.2 ω
    · simpa only [eventStop, Set.piecewise, if_neg hω] using hτ₂.2 ω
  · intro ω
    by_cases hω : ω ∈ A
    · simpa only [eventStop, Set.piecewise, if_pos hω] using hl₁ ω
    · simpa only [eventStop, Set.piecewise, if_neg hω] using hl₂ ω

theorem timePsiFamily_min (D : TestSet P₀ ℱ N) (hs : IsStable D)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X) {n : ℕ} (hn : n ≤ N) :
    ∀ h₁ ∈ timePsiFamily D X n, ∀ h₂ ∈ timePsiFamily D X n,
      ∃ h ∈ timePsiFamily D X n, h =ᵐ[P₀] fun ω => min (h₁ ω) (h₂ ω) := by
  classical
  rintro h₁ ⟨τ₁, hτ₁, hl₁, f₁, hf₁, rfl⟩ h₂ ⟨τ₂, hτ₂, hl₂, f₂, hf₂, rfl⟩
  let := test_probability D hf₁.1
  let := test_probability D hf₂.1
  let A : Set Ω := {ω | (Q P₀ f₁)[stoppedValue X τ₁ | ℱ n] ω ≤
    (Q P₀ f₂)[stoppedValue X τ₂ | ℱ n] ω}
  have hA : MeasurableSet[ℱ n] A :=
    stronglyMeasurable_condExp.measurableSet_le stronglyMeasurable_condExp
  let τ := eventStop A τ₁ τ₂
  obtain ⟨hτ, hl⟩ := eventStop_bounded hA hτ₁ hτ₂ hl₁ hl₂
  obtain ⟨g, hg, hfork⟩ := exists_conditional_fork D hs hf₁ hf₂ n hn A hA
  obtain ⟨C, hC0, hC⟩ := value_nonneg_bound hX
  have hHsm : AEStronglyMeasurable (stoppedValue X τ) P₀ :=
    ((stopped_stronglyMeasurable hX.1 τ hτ).mono hτ.1.measurableSpace_le).aestronglyMeasurable
  have he₁ : ∀ ω, ω ∈ A → stoppedValue X τ ω = stoppedValue X τ₁ ω := by
    intro ω hω
    simp [stoppedValue, τ, eventStop, hω]
  have he₂ : ∀ ω, ω ∈ Aᶜ → stoppedValue X τ ω = stoppedValue X τ₂ ω := by
    intro ω hω
    have hnot : ω ∉ A := hω
    simp [stoppedValue, τ, eventStop, hnot]
  have hc₁ := (aux_pdp_acQ D hf₁).ae_le (condExp_local_eq hA
    (aux_pdp_sv_int D X hX hf₁.1 hτ) (aux_pdp_sv_int D X hX hf₁.1 hτ₁)
    (Filter.Eventually.of_forall he₁))
  have hc₂ := (aux_pdp_acQ D hf₂).ae_le (condExp_local_eq hA.compl
    (aux_pdp_sv_int D X hX hf₂.1 hτ) (aux_pdp_sv_int D X hX hf₂.1 hτ₂)
    (Filter.Eventually.of_forall he₂))
  refine ⟨_, ⟨τ, hτ, hl, g, hg, rfl⟩, ?_⟩
  filter_upwards [hfork _ hHsm C hC0 (value_bound_stopped hC hτ.2), hc₁, hc₂] with ω hforkω hc₁ω hc₂ω
  by_cases hω : ω ∈ A
  · rw [hforkω, if_pos hω, hc₁ω hω]
    exact (min_eq_left (show (Q P₀ f₁)[stoppedValue X τ₁ | ℱ n] ω ≤
      (Q P₀ f₂)[stoppedValue X τ₂ | ℱ n] ω from hω)).symm
  · rw [hforkω, if_neg hω, hc₂ω hω]
    exact (min_eq_right (le_of_lt (not_le.mp hω))).symm

theorem psiN_decreasing_approximation (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    (hs : IsStable D) {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    {n : ℕ} (hn : n ≤ N) :
    ∃ u : ℕ → Ω → ℝ, (∀ k, u k ∈ timePsiFamily D X n) ∧
      (∀ k, u (k+1) ≤ᵐ[P₀] u k) ∧
      ∀ᵐ ω ∂P₀, Tendsto (fun k => u k ω) atTop (𝓝 (PsiN D X n ω)) := by
  obtain ⟨C, hC⟩ := hX.2
  have hne := timePsiFamily_nonempty D hPe X hn
  have hsm := timePsiFamily_measurable D X n
  have hb := timePsiFamily_bounded D hC n
  obtain ⟨u, hu, hanti, ht⟩ := essInf_decreasing_sequence P₀ (ℱ.le n)
    (timePsiFamily D X n) hne hsm C hb (timePsiFamily_min D hs hX hn)
  have he := aux_pdp_unique (isEssInf_bounded (ℱ.le n) hne hsm C hb) (psiN_spec_time D hPe hX hn)
  refine ⟨u, hu, hanti, ?_⟩
  filter_upwards [ht, he] with ω htω heω
  simpa only [heω] using htω

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: PastingTests -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω} [IsProbabilityMeasure P₀]
variable {ℱ : Filtration ℕ m} {N : ℕ}

theorem paste_integral_of_measurable (D : TestSet P₀ ℱ N) {f₀ f : Ω → ℝ}
    (hf₀ : f₀ ∈ Pe D) (hf : f ∈ Pe D) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) {H : Ω → ℝ}
    (hH : StronglyMeasurable[hτ.1.measurableSpace] H)
    {C : ℝ} (hC : ∀ᵐ ω ∂P₀, |H ω| ≤ C) :
    (∫ ω, H ω ∂Q P₀ (pasteDensity P₀ ℱ f₀ f τ)) = ∫ ω, H ω ∂Q P₀ f₀ := by
  let := test_probability D hf.1
  have hsm : AEStronglyMeasurable H P₀ := (hH.mono hτ.1.measurableSpace_le).aestronglyMeasurable
  rw [paste_expectation D hf₀ hf τ hτ hsm hC,
    condExp_of_stronglyMeasurable hτ.1.measurableSpace_le hH (bounded_integrable_Q D hf.1 hsm hC)]

theorem paste_setIntegral_expectation (D : TestSet P₀ ℱ N) {f₀ f : Ω → ℝ}
    (hf₀ : f₀ ∈ Pe D) (hf : f ∈ Pe D) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) {H : Ω → ℝ}
    (hH : AEStronglyMeasurable H P₀) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ᵐ ω ∂P₀, |H ω| ≤ C) {A : Set Ω}
    (hA : MeasurableSet[hτ.1.measurableSpace] A) :
    (∫ ω in A, H ω ∂Q P₀ (pasteDensity P₀ ℱ f₀ f τ)) =
      ∫ ω in A, (Q P₀ f)[H | hτ.1.measurableSpace] ω ∂Q P₀ f₀ := by
  have hAm := hτ.1.measurableSpace_le A hA
  rw [← integral_indicator hAm, ← integral_indicator hAm,
    paste_expectation D hf₀ hf τ hτ (hH.indicator hAm) (claim_indicator_bound h0 hC A)]
  apply integral_congr_ae
  exact (aux_pdp_Qac f₀).ae_le ((aux_pdp_acQ D hf).ae_le
    (condExp_indicator (bounded_integrable_Q D hf.1 hH hC) hA))

theorem paste_setIntegral_past (D : TestSet P₀ ℱ N) {f₀ f : Ω → ℝ}
    (hf₀ : f₀ ∈ Pe D) (hf : f ∈ Pe D) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) {H : Ω → ℝ}
    (hH : StronglyMeasurable[hτ.1.measurableSpace] H)
    {C : ℝ} (h0 : 0 ≤ C) (hC : ∀ᵐ ω ∂P₀, |H ω| ≤ C) {A : Set Ω}
    (hA : MeasurableSet[hτ.1.measurableSpace] A) :
    (∫ ω in A, H ω ∂Q P₀ (pasteDensity P₀ ℱ f₀ f τ)) = ∫ ω in A, H ω ∂Q P₀ f₀ := by
  let := test_probability D hf.1
  have hsm : AEStronglyMeasurable H P₀ := (hH.mono hτ.1.measurableSpace_le).aestronglyMeasurable
  rw [paste_setIntegral_expectation D hf₀ hf τ hτ hsm h0 hC hA,
    condExp_of_stronglyMeasurable hτ.1.measurableSpace_le hH (bounded_integrable_Q D hf.1 hsm hC)]

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: SnellRegular -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
  {ℱ : Filtration ℕ m} {N : ℕ} [IsProbabilityMeasure P₀]

omit [IsProbabilityMeasure P₀] in
theorem psiBarAux_succ (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) (k : ℕ) :
    psiBarAux D X (k+1) = fun ω => min (X (N-(k+1)) ω)
      (lowerCond D (psiBarAux D X k) (ℱ (N-(k+1))) ω) := rfl

theorem snell_aux_regular (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X) {C : ℝ}
    (hC : ∀ n ≤ N, ∀ᵐ ω ∂P₀, |X n ω| ≤ C) :
    ∀ k ≤ N, StronglyMeasurable[ℱ (N-k)] (psiBarAux D X k) ∧
      ∀ᵐ ω ∂P₀, |psiBarAux D X k ω| ≤ C := by
  intro k
  induction k with
  | zero =>
    intro _
    simpa only [Nat.sub_zero, psiBarAux] using And.intro (hX.1 N le_rfl) (hC N le_rfl)
  | succ k ih =>
    intro hk
    have hp := ih (by omega)
    have hn : N-(k+1) ≤ N := Nat.sub_le _ _
    rw [psiBarAux_succ]
    refine ⟨((hX.1 _ hn).measurable.min (lowerCond_measurable D hPe hp.2 (ℱ.le _)).measurable).stronglyMeasurable, ?_⟩
    filter_upwards [hC _ hn, lowerCond_bounded D hPe hp.2 (ℱ.le (N-(k+1)))] with ω hx hh
    obtain ⟨hxl, hxu⟩ := abs_le.mp hx
    obtain ⟨hhl, hhu⟩ := abs_le.mp hh
    exact abs_le.mpr ⟨le_min hxl hhl, (min_le_left _ _).trans hxu⟩

theorem psiBar_regular (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X) {C : ℝ}
    (hC : ∀ n ≤ N, ∀ᵐ ω ∂P₀, |X n ω| ≤ C) {n : ℕ} (hn : n ≤ N) :
    StronglyMeasurable[ℱ n] (PsiBar D X n) ∧ ∀ᵐ ω ∂P₀, |PsiBar D X n ω| ≤ C := by
  have h := snell_aux_regular D hPe hX hC (N-n) (Nat.sub_le _ _)
  have he : N-(N-n)=n := by omega
  rw [PsiBar, if_pos hn]
  have hsm : StronglyMeasurable[ℱ n] (psiBarAux D X (N-n)) := (congrArg ℱ he) ▸ h.1
  exact ⟨hsm, h.2⟩

theorem psiBar_valueProcess (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X) :
    IsValueProcess P₀ ℱ N (PsiBar D X) := by
  obtain ⟨C, hC⟩ := hX.2
  exact ⟨fun n hn => (psiBar_regular D hPe hX hC hn).1,
    C, fun n hn => (psiBar_regular D hPe hX hC hn).2⟩

omit [IsProbabilityMeasure P₀] in
theorem psiBar_terminal (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) :
    PsiBar D X N = X N := by simp only [PsiBar, le_refl, if_true, Nat.sub_self, psiBarAux]

omit [IsProbabilityMeasure P₀] in
theorem psiBar_rec (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) {n : ℕ} (hn : n < N) :
    PsiBar D X n = fun ω => min (X n ω)
      (lowerCond D (PsiBar D X (n+1)) (ℱ n) ω) := by
  have hn' : n+1 ≤ N := by omega
  have hk : N-n = (N-(n+1))+1 := by omega
  have he : N-((N-(n+1))+1)=n := by omega
  simp only [PsiBar, if_pos hn.le, if_pos hn', hk, psiBarAux_succ, he]

omit [IsProbabilityMeasure P₀] in
theorem psiBar_le_X (D : TestSet P₀ ℱ N) (X : ℕ → Ω → ℝ) {n : ℕ} (hn : n ≤ N) :
    ∀ ω, PsiBar D X n ω ≤ X n ω := by
  by_cases he : n=N
  · subst n
    rw [psiBar_terminal]
    exact fun _ => le_rfl
  · rw [psiBar_rec D X (by omega)]
    exact fun _ => min_le_left _ _

theorem psiBar_le_condExp (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X) {n : ℕ} (hn : n < N)
    {f : Ω → ℝ} (hf : f ∈ Pe D) :
    PsiBar D X n ≤ᵐ[P₀] (Q P₀ f)[PsiBar D X (n+1) | ℱ n] := by
  obtain ⟨C, hC⟩ := hX.2
  have hb := (psiBar_regular D hPe hX hC (show n+1≤N by omega)).2
  have hl := lowerCond_le D hPe hb (ℱ.le n) hf
  filter_upwards [hl] with ω hω
  rw [psiBar_rec D X hn]
  exact (min_le_right _ _).trans hω

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: DensityMixtures -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
  {ℱ : Filtration ℕ m} {N : ℕ}

def densityMix (t : ℝ) (f g : Ω → ℝ) : Ω → ℝ := fun ω => (1-t)*f ω+t*g ω

theorem densityMix_mem (D : TestSet P₀ ℱ N) {f g : Ω → ℝ}
    (hf : f ∈ D.set) (hg : g ∈ D.set) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    densityMix t f g ∈ D.set := by
  exact D.convex hf hg (sub_nonneg.mpr ht1) ht (by ring)

theorem densityMix_mem_Pe (D : TestSet P₀ ℱ N) {f g : Ω → ℝ}
    (hf : f ∈ D.set) (hg : g ∈ Pe D) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    densityMix t f g ∈ Pe D := by
  refine ⟨densityMix_mem D hf hg.1 ht.le ht1, ?_⟩
  filter_upwards [D.nonneg f hf, hg.2] with ω hfω hgω
  have h1 : 0 ≤ (1-t)*f ω := mul_nonneg (sub_nonneg.mpr ht1) hfω
  have h2 : 0 < t*g ω := mul_pos ht hgω
  exact add_pos_of_nonneg_of_pos h1 h2

theorem integral_densityMix (D : TestSet P₀ ℱ N) {f g H : Ω → ℝ}
    (hf : f ∈ D.set) (hg : g ∈ D.set) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hsm : AEStronglyMeasurable H P₀) {C : ℝ} (hb : ∀ᵐ ω ∂P₀, |H ω| ≤ C) :
    (∫ ω, H ω ∂Q P₀ (densityMix t f g)) =
      (1-t)*(∫ ω, H ω ∂Q P₀ f)+t*(∫ ω, H ω ∂Q P₀ g) := by
  rw [test_integral_eq D (densityMix_mem D hf hg ht ht1), test_integral_eq D hf,
    test_integral_eq D hg]
  have he : (fun ω => densityMix t f g ω * H ω) =
      fun ω => (1-t)*(f ω*H ω)+t*(g ω*H ω) := by
    funext ω
    dsimp [densityMix]
    ring
  rw [he, integral_add ((bounded_weighted_integrable D hf hsm hb).const_mul _)
    ((bounded_weighted_integrable D hg hsm hb).const_mul _), integral_const_mul,
    integral_const_mul]

theorem integral_nonneg_of_Pe (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {H : Ω → ℝ} (hsm : AEStronglyMeasurable H P₀) {C : ℝ}
    (hb : ∀ᵐ ω ∂P₀, |H ω| ≤ C)
    (hpos : ∀ f ∈ Pe D, 0 ≤ ∫ ω, H ω ∂Q P₀ f) {f : Ω → ℝ} (hf : f ∈ D.set) :
    0 ≤ ∫ ω, H ω ∂Q P₀ f := by
  obtain ⟨g, hg⟩ := hPe
  let t : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have ht1 (n : ℕ) : t n ≤ 1 := by
    dsimp [t]
    apply (div_le_one (by positivity)).mpr
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  have hlim : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hl' : Tendsto (fun n => (1-t n)*(∫ ω, H ω ∂Q P₀ f)+
      t n*(∫ ω, H ω ∂Q P₀ g)) atTop (𝓝 (∫ ω, H ω ∂Q P₀ f)) := by
    simpa only [sub_zero, one_mul, zero_mul, add_zero] using
      (((tendsto_const_nhds (x := (1 : ℝ))).sub hlim).mul
        (tendsto_const_nhds (x := ∫ ω, H ω ∂Q P₀ f))).add
          (hlim.mul (tendsto_const_nhds (x := ∫ ω, H ω ∂Q P₀ g)))
  apply ge_of_tendsto' hl'
  intro n
  rw [← integral_densityMix D hf hg.1 (ht n).le (ht1 n) hsm hb]
  exact hpos _ (densityMix_mem_Pe D hf hg (ht n) (ht1 n))

theorem setIntegral_nonneg_of_Pe (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {H : Ω → ℝ} (hsm : AEStronglyMeasurable H P₀) {C : ℝ}
    (hb : ∀ᵐ ω ∂P₀, |H ω| ≤ C) {A : Set Ω} (hA : MeasurableSet A)
    (hpos : ∀ f ∈ Pe D, 0 ≤ ∫ ω in A, H ω ∂Q P₀ f)
    {f : Ω → ℝ} (hf : f ∈ D.set) : 0 ≤ ∫ ω in A, H ω ∂Q P₀ f := by
  classical
  have hb' : ∀ᵐ ω ∂P₀, |A.indicator H ω| ≤ |C| := by
    filter_upwards [hb] with ω hω
    by_cases ha : ω ∈ A
    · simpa only [Set.indicator_of_mem ha] using hω.trans (le_abs_self C)
    · simp only [Set.indicator_of_notMem ha, abs_zero, abs_nonneg]
  have h := integral_nonneg_of_Pe D hPe (hsm.indicator hA) hb'
    (fun g hg => by simpa only [integral_indicator hA] using hpos g hg) hf
  simpa only [integral_indicator hA] using h

theorem setIntegral_le_of_Pe (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {H K : Ω → ℝ} (hsmH : AEStronglyMeasurable H P₀)
    (hsmK : AEStronglyMeasurable K P₀) {C : ℝ}
    (hbH : ∀ᵐ ω ∂P₀, |H ω| ≤ C) (hbK : ∀ᵐ ω ∂P₀, |K ω| ≤ C)
    {A : Set Ω} (hA : MeasurableSet A)
    (hle : ∀ f ∈ Pe D, (∫ ω in A, H ω ∂Q P₀ f) ≤ ∫ ω in A, K ω ∂Q P₀ f)
    {f : Ω → ℝ} (hf : f ∈ D.set) :
    (∫ ω in A, H ω ∂Q P₀ f) ≤ ∫ ω in A, K ω ∂Q P₀ f := by
  have hb : ∀ᵐ ω ∂P₀, |K ω-H ω| ≤ 2*C := by
    filter_upwards [hbH, hbK] with ω hh hk
    exact (abs_sub _ _).trans (by linarith)
  have hiH (g : Ω → ℝ) (hg : g ∈ D.set) :=
    (bounded_integrable_Q D hg hsmH hbH).integrableOn (s := A)
  have hiK (g : Ω → ℝ) (hg : g ∈ D.set) :=
    (bounded_integrable_Q D hg hsmK hbK).integrableOn (s := A)
  have h := setIntegral_nonneg_of_Pe D hPe (hsmK.sub hsmH) hb hA (fun g hg => by
    simp only [Pi.sub_apply]
    rw [integral_sub (hiK g hg.1) (hiH g hg.1)]
    exact sub_nonneg.mpr (hle g hg)) hf
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hiK f hf) (hiH f hf)] at h
  exact sub_nonneg.mp h

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: SnellSubmartingale -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
  {ℱ : Filtration ℕ m} {N : ℕ}

theorem value_frozen_adapted {Y : ℕ → Ω → ℝ} (hY : IsValueProcess P₀ ℱ N Y) :
    StronglyAdapted ℱ (fun n => Y (min n N)) := fun _ =>
  (hY.1 _ (min_le_right _ _)).mono (ℱ.mono (min_le_left _ _))

theorem value_frozen_integrable (D : TestSet P₀ ℱ N) {Y : ℕ → Ω → ℝ}
    (hY : IsValueProcess P₀ ℱ N Y) {f : Ω → ℝ} (hf : f ∈ D.set) (n : ℕ) :
    Integrable (Y (min n N)) (Q P₀ f) := by
  obtain ⟨C, hC⟩ := hY.2
  exact bounded_integrable_Q D hf ((value_frozen_adapted hY n).mono (ℱ.le n)).aestronglyMeasurable
    (hC _ (min_le_right _ _))

theorem frozen_submartingale_all (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {Y : ℕ → Ω → ℝ} (hY : IsValueProcess P₀ ℱ N Y)
    (hsub : ∀ g ∈ Pe D, Submartingale (fun n => Y (min n N)) ℱ (Q P₀ g))
    {f : Ω → ℝ} (hf : f ∈ D.set) :
    Submartingale (fun n => Y (min n N)) ℱ (Q P₀ f) := by
  let := test_probability D hf
  apply submartingale_of_setIntegral_le_succ (value_frozen_adapted hY)
    (value_frozen_integrable D hY hf)
  intro n A hA
  obtain ⟨C, hC⟩ := hY.2
  apply setIntegral_le_of_Pe D hPe
    ((value_frozen_adapted hY n).mono (ℱ.le n)).aestronglyMeasurable
    ((value_frozen_adapted hY (n+1)).mono (ℱ.le (n+1))).aestronglyMeasurable
    (hC _ (min_le_right _ _)) (hC _ (min_le_right _ _)) (ℱ.le n _ hA) ?_ hf
  intro g hg
  let := test_probability D hg.1
  exact (hsub g hg).setIntegral_le (Nat.le_succ n) hA

variable [IsProbabilityMeasure P₀]

theorem psiBar_submartingale_Pe (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    {f : Ω → ℝ} (hf : f ∈ Pe D) :
    Submartingale (fun n => PsiBar D X (min n N)) ℱ (Q P₀ f) := by
  let := test_probability D hf.1
  have hY := psiBar_valueProcess D hPe hX
  have hint := value_frozen_integrable D hY hf.1
  apply submartingale_of_setIntegral_le_succ (value_frozen_adapted hY) hint
  intro n A hA
  by_cases hn : n < N
  · have hn' : n+1 ≤ N := by omega
    simp only [min_eq_left hn.le, min_eq_left hn']
    have hi : Integrable (PsiBar D X (n+1)) (Q P₀ f) := by
      simpa only [min_eq_left hn'] using hint (n+1)
    have hi0 : Integrable (PsiBar D X n) (Q P₀ f) := by
      simpa only [min_eq_left hn.le] using hint n
    have hle := (aux_pdp_Qac f).ae_le (psiBar_le_condExp D hPe hX hn hf)
    calc
      (∫ ω in A, PsiBar D X n ω ∂Q P₀ f) ≤
          ∫ ω in A, (Q P₀ f)[PsiBar D X (n+1) | ℱ n] ω ∂Q P₀ f :=
        integral_mono_ae hi0.integrableOn integrable_condExp.integrableOn
          (ae_restrict_of_ae hle)
      _ = ∫ ω in A, PsiBar D X (n+1) ω ∂Q P₀ f := setIntegral_condExp (ℱ.le n) hi hA
  · have hN : N ≤ n := by omega
    have hN' : N ≤ n+1 := by omega
    simp only [min_eq_right hN, min_eq_right hN', le_refl]

theorem psiBar_submartingale (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    {f : Ω → ℝ} (hf : f ∈ D.set) :
    Submartingale (fun n => PsiBar D X (min n N)) ℱ (Q P₀ f) :=
  frozen_submartingale_all D hPe (psiBar_valueProcess D hPe hX)
    (fun _ hg => psiBar_submartingale_Pe D hPe hX hg) hf

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: ForwardSubmartingale -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
  {ℱ : Filtration ℕ m} {N : ℕ} [IsProbabilityMeasure P₀]

theorem psi_step_family_integral (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    (hs : IsStable D) {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    {f₀ : Ω → ℝ} (hf₀ : f₀ ∈ Pe D) {n : ℕ} (hn : n<N)
    {A : Set Ω} (hA : MeasurableSet[ℱ n] A) :
    ∀ h ∈ timePsiFamily D X (n+1),
      (∫ ω in A, PsiN D X n ω ∂Q P₀ f₀) ≤ ∫ ω in A, h ω ∂Q P₀ f₀ := by
  rintro h ⟨ν, hν, hnν, f, hf, rfl⟩
  let τ : Ω → WithTop ℕ := fun _ => (n+1 : ℕ)
  have hτ : IsBddStoppingTime ℱ N τ := bounded_const_stop (n+1) (by omega)
  have eτ : hτ.1.measurableSpace = ℱ (n+1) := IsStoppingTime.measurableSpace_const ℱ (n+1)
  let g := pasteDensity P₀ ℱ f₀ f τ
  have hg : g ∈ Pe D := paste_mem_Pe D hs hf₀ hf τ hτ
  let := test_probability D hg.1
  obtain ⟨C, hC0, hC⟩ := value_nonneg_bound hX
  have hpb := psiN_bounded D hPe hX hC hn.le
  have hpm := psiN_measurable D hPe hX hn.le
  have hpτ : StronglyMeasurable[hτ.1.measurableSpace] (PsiN D X n) := by
    exact eτ.symm ▸ hpm.mono (ℱ.mono (Nat.le_succ n))
  have hAτ : MeasurableSet[hτ.1.measurableSpace] A := by
    exact eτ.symm ▸ ℱ.mono (Nat.le_succ n) A hA
  have hprior : (∫ ω in A, PsiN D X n ω ∂Q P₀ g) =
      ∫ ω in A, PsiN D X n ω ∂Q P₀ f₀ :=
    paste_setIntegral_past D hf₀ hf τ hτ hpτ hC0 hpb hAτ
  have hfuture : (∫ ω in A, stoppedValue X ν ω ∂Q P₀ g) =
      ∫ ω in A, (Q P₀ f)[stoppedValue X ν | ℱ (n+1)] ω ∂Q P₀ f₀ := by
    have h := paste_setIntegral_expectation D hf₀ hf τ hτ
      ((stopped_stronglyMeasurable hX.1 ν hν).mono hν.1.measurableSpace_le).aestronglyMeasurable
      hC0 (value_bound_stopped hC hν.2) hAτ
    rw [eτ] at h
    exact h
  have hlow : PsiN D X n ≤ᵐ[P₀] (Q P₀ g)[stoppedValue X ν | ℱ n] :=
    (psiN_spec_time D hPe hX hn.le).2.1 _
      ⟨ν, hν, fun ω => (show (n:WithTop ℕ) ≤ (n+1:ℕ) by exact_mod_cast Nat.le_succ n).trans (hnν ω),
        g, hg, rfl⟩
  have hip := bounded_integrable_Q D hg.1 (hpm.mono (ℱ.le n)).aestronglyMeasurable hpb
  have hiX := aux_pdp_sv_int D X hX hg.1 hν
  calc
    (∫ ω in A, PsiN D X n ω ∂Q P₀ f₀) = ∫ ω in A, PsiN D X n ω ∂Q P₀ g := hprior.symm
    _ ≤ ∫ ω in A, (Q P₀ g)[stoppedValue X ν | ℱ n] ω ∂Q P₀ g :=
      integral_mono_ae hip.integrableOn integrable_condExp.integrableOn
        (ae_restrict_of_ae ((aux_pdp_Qac g).ae_le hlow))
    _ = ∫ ω in A, stoppedValue X ν ω ∂Q P₀ g := setIntegral_condExp (ℱ.le n) hiX hA
    _ = ∫ ω in A, (Q P₀ f)[stoppedValue X ν | ℱ (n+1)] ω ∂Q P₀ f₀ := hfuture

theorem psi_step_integral (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    (hs : IsStable D) {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    {f₀ : Ω → ℝ} (hf₀ : f₀ ∈ Pe D) {n : ℕ} (hn : n<N)
    {A : Set Ω} (hA : MeasurableSet[ℱ n] A) :
    (∫ ω in A, PsiN D X n ω ∂Q P₀ f₀) ≤ ∫ ω in A, PsiN D X (n+1) ω ∂Q P₀ f₀ := by
  let := test_probability D hf₀.1
  obtain ⟨u, hu, -, ht⟩ := psiN_decreasing_approximation D hPe hs hX (show n+1≤N by omega)
  obtain ⟨C, hC⟩ := hX.2
  have hν : (Q P₀ f₀).restrict A ≪ P₀ := Measure.absolutelyContinuous_restrict.trans (aux_pdp_Qac f₀)
  have hi := integral_tendsto_of_bounded_ae hν C
    (fun k => ((timePsiFamily_measurable D X (n+1) _ (hu k)).mono (ℱ.le (n+1))).aestronglyMeasurable)
    (fun k => timePsiFamily_bounded D hC (n+1) _ (hu k)) ht
  exact ge_of_tendsto' hi (fun k => psi_step_family_integral D hPe hs hX hf₀ hn hA (u k) (hu k))

theorem psi_submartingale_Pe_of_stable (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    (hs : IsStable D) {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    {f : Ω → ℝ} (hf : f ∈ Pe D) :
    Submartingale (fun n => PsiN D X (min n N)) ℱ (Q P₀ f) := by
  let := test_probability D hf.1
  have hY := psi_valueProcess D hPe hX
  apply submartingale_of_setIntegral_le_succ (value_frozen_adapted hY)
    (value_frozen_integrable D hY hf.1)
  intro n A hA
  by_cases hn : n<N
  · simpa only [min_eq_left hn.le, min_eq_left (show n+1≤N by omega)] using
      psi_step_integral D hPe hs hX hf hn hA
  · simp only [min_eq_right (show N≤n by omega), min_eq_right (show N≤n+1 by omega), le_refl]

theorem psi_submartingale_of_stable (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    (hs : IsStable D) {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    {f : Ω → ℝ} (hf : f ∈ D.set) :
    Submartingale (fun n => PsiN D X (min n N)) ℱ (Q P₀ f) :=
  frozen_submartingale_all D hPe (psi_valueProcess D hPe hX)
    (fun _ hg => psi_submartingale_Pe_of_stable D hPe hs hX hg) hf

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: SubmartingaleStopping -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
  {ℱ : Filtration ℕ m} {N : ℕ} [IsProbabilityMeasure P₀]

theorem stoppedValue_freeze (Y : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (hτ : ∀ ω, τ ω ≤ (N:WithTop ℕ)) :
    stoppedValue (fun n => Y (min n N)) τ = stoppedValue Y τ := by
  funext ω
  obtain ⟨k, hk, he⟩ := aux_pdp_exists_k hτ ω
  rw [aux_pdp_sv_of_eq _ he, aux_pdp_sv_of_eq _ he, min_eq_left hk]

omit [IsProbabilityMeasure P₀] in
theorem stopped_le_of_value_le {Y X : ℕ → Ω → ℝ}
    (hle : ∀ n ≤ N, Y n ≤ᵐ[P₀] X n) (τ : Ω → WithTop ℕ)
    (hτ : ∀ ω, τ ω ≤ (N:WithTop ℕ)) : stoppedValue Y τ ≤ᵐ[P₀] stoppedValue X τ := by
  have hall : ∀ᵐ ω ∂P₀, ∀ n, n ≤ N → Y n ω ≤ X n ω := ae_all_iff.mpr fun n => by
    by_cases hn : n≤N
    · exact (hle n hn).mono fun _ h _ => h
    · exact Filter.Eventually.of_forall fun _ h => (hn h).elim
  filter_upwards [hall] with ω hω
  obtain ⟨k, hk, he⟩ := aux_pdp_exists_k hτ ω
  rw [aux_pdp_sv_of_eq _ he, aux_pdp_sv_of_eq _ he]
  exact hω k hk

omit [IsProbabilityMeasure P₀] in
theorem frozen_submartingale_stop_le (D : TestSet P₀ ℱ N)
    {Y : ℕ → Ω → ℝ} {f : Ω → ℝ} (hf : f ∈ Pe D)
    (hsub : Submartingale (fun n => Y (min n N)) ℱ (Q P₀ f))
    {n : ℕ} (hn : n≤N) (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ)
    (hnτ : ∀ ω, (n:WithTop ℕ) ≤ τ ω) :
    Y n ≤ᵐ[P₀] (Q P₀ f)[stoppedValue Y τ | ℱ n] := by
  let := test_probability D hf.1
  have hs := hsub.stoppedProcess hτ.1
  have hl : stoppedProcess (fun k => Y (min k N)) τ n = Y n := by
    funext ω
    change Y (min ((min (n : WithTop ℕ) (τ ω)).untopA) N) ω = Y n ω
    rw [min_eq_left (hnτ ω)]
    change Y (min n N) ω = Y n ω
    rw [min_eq_left hn]
  have hr : stoppedProcess (fun k => Y (min k N)) τ N = stoppedValue Y τ := by
    have he : stoppedProcess (fun k => Y (min k N)) τ N =
        stoppedValue (fun k => Y (min k N)) τ := by
      funext ω
      change Y (min ((min (N : WithTop ℕ) (τ ω)).untopA) N) ω =
        Y (min (τ ω).untopA N) ω
      rw [min_eq_right (hτ.2 ω)]
    rw [he, stoppedValue_freeze Y τ hτ.2]
  have h := hs.2.1 n N hn
  rw [hl, hr] at h
  exact (aux_pdp_acQ D hf).ae_le h

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: SnellLowerComparison -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
  {ℱ : Filtration ℕ m} {N : ℕ} [IsProbabilityMeasure P₀]

theorem submartingale_below_psiN (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {Y X : ℕ → Ω → ℝ} (hY : IsValueProcess P₀ ℱ N Y) (hX : IsValueProcess P₀ ℱ N X)
    (hle : ∀ n ≤ N, Y n ≤ᵐ[P₀] X n)
    (hsub : ∀ f ∈ Pe D, Submartingale (fun n => Y (min n N)) ℱ (Q P₀ f))
    {n : ℕ} (hn : n≤N) : Y n ≤ᵐ[P₀] PsiN D X n := by
  apply (psiN_spec_time D hPe hX hn).2.2 _ (hY.1 n hn)
  rintro h ⟨τ, hτ, hnτ, f, hf, rfl⟩
  have h1 := frozen_submartingale_stop_le D hf (hsub f hf) hn τ hτ hnτ
  have h2 := condExp_mono (m := ℱ n) (aux_pdp_sv_int D Y hY hf.1 hτ)
    (aux_pdp_sv_int D X hX hf.1 hτ)
    ((aux_pdp_Qac f).ae_le (stopped_le_of_value_le hle τ hτ.2))
  exact h1.trans ((aux_pdp_acQ D hf).ae_le h2)

theorem psiBar_le_psiN (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X) {n : ℕ} (hn : n≤N) :
    PsiBar D X n ≤ᵐ[P₀] PsiN D X n :=
  submartingale_below_psiN D hPe (psiBar_valueProcess D hPe hX) hX
    (fun _ hn => Filter.Eventually.of_forall (psiBar_le_X D X hn))
    (fun _ hf => psiBar_submartingale_Pe D hPe hX hf) hn

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: SnellUpperComparison -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
  {ℱ : Filtration ℕ m} {N : ℕ} [IsProbabilityMeasure P₀]

theorem submartingale_below_snell (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {Y X : ℕ → Ω → ℝ} (hY : IsValueProcess P₀ ℱ N Y) (hX : IsValueProcess P₀ ℱ N X)
    (hle : ∀ n ≤ N, Y n ≤ᵐ[P₀] X n)
    (hsub : ∀ f ∈ Pe D, Submartingale (fun n => Y (min n N)) ℱ (Q P₀ f)) :
    ∀ n ≤ N, Y n ≤ᵐ[P₀] PsiBar D X n := by
  obtain ⟨C, hC⟩ := hX.2
  obtain ⟨B, hB⟩ := hY.2
  have aux : ∀ k ≤ N, Y (N-k) ≤ᵐ[P₀] PsiBar D X (N-k) := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa only [Nat.sub_zero, psiBar_terminal] using hle N le_rfl
    | succ k ih =>
      intro hk
      let n := N-(k+1)
      have hn : n<N := by dsimp [n]; omega
      have hnp : n+1=N-k := by dsimp [n]; omega
      have ih' : Y (n+1) ≤ᵐ[P₀] PsiBar D X (n+1) := by
        simpa only [hnp] using ih (show k≤N by omega)
      have hbar := psiBar_regular D hPe hX hC (show n+1≤N by omega)
      have hlo : Y n ≤ᵐ[P₀] lowerCond D (PsiBar D X (n+1)) (ℱ n) := by
        apply lowerCond_greatest D hPe hbar.2 (ℱ.le n) (hY.1 n hn.le)
        intro f hf
        have hsn := (hsub f hf).2.1 n (n+1) (Nat.le_succ n)
        have hsn' : Y n ≤ᵐ[Q P₀ f] (Q P₀ f)[Y (n+1) | ℱ n] := by
          simpa only [min_eq_left hn.le, min_eq_left (show n+1≤N by omega)] using hsn
        have hiY := bounded_integrable_Q D hf.1
          ((hY.1 (n+1) (by omega)).mono (ℱ.le (n+1))).aestronglyMeasurable
          (hB (n+1) (by omega))
        have hiS := bounded_integrable_Q D hf.1 (hbar.1.mono (ℱ.le (n+1))).aestronglyMeasurable hbar.2
        have hc := condExp_mono (m := ℱ n) hiY hiS ((aux_pdp_Qac f).ae_le ih')
        exact (aux_pdp_acQ D hf).ae_le (hsn'.trans hc)
      have hxn := hle n hn.le
      change Y n ≤ᵐ[P₀] PsiBar D X n
      filter_upwards [hxn, hlo] with ω hx hl
      rw [psiBar_rec D X hn]
      exact le_min hx hl
  intro n hn
  have he : N-(N-n)=n := by omega
  simpa only [he] using aux (N-n) (Nat.sub_le _ _)

theorem psi_eq_snell_of_submartingale (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    (hsub : ∀ f ∈ D.set, Submartingale (fun n => PsiN D X (min n N)) ℱ (Q P₀ f)) :
    ∀ n ≤ N, PsiN D X n =ᵐ[P₀] PsiBar D X n := by
  intro n hn
  exact (submartingale_below_snell D hPe (psi_valueProcess D hPe hX) hX
    (fun _ hn => psiN_le_X D hPe hX hn) (fun _ hf => hsub _ hf.1) n hn).antisymm
    (psiBar_le_psiN D hPe hX hn)

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: TerminalL1 -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
variable {ℱ : Filtration ℕ m} {N : ℕ}

noncomputable abbrev TerminalL1 (P₀ : Measure Ω) (ℱ : Filtration ℕ m) (N : ℕ) :=
  Lp ℝ 1 (P₀.trim (ℱ.le N))

noncomputable def terminalClass (f : Ω → ℝ) (hfm : StronglyMeasurable[ℱ N] f)
    (hfi : Integrable f P₀) : TerminalL1 P₀ ℱ N :=
  (memLp_one_iff_integrable.mpr (hfi.trim (ℱ.le N) hfm)).toLp f

theorem terminalClass_coe_trim (f : Ω → ℝ) (hfm : StronglyMeasurable[ℱ N] f)
    (hfi : Integrable f P₀) : terminalClass f hfm hfi =ᵐ[P₀.trim (ℱ.le N)] f :=
  MemLp.coeFn_toLp _

theorem terminalClass_coe (f : Ω → ℝ) (hfm : StronglyMeasurable[ℱ N] f)
    (hfi : Integrable f P₀) : terminalClass f hfm hfi =ᵐ[P₀] f :=
  ae_eq_of_ae_eq_trim (terminalClass_coe_trim f hfm hfi)

def terminalDensitySet (D : TestSet P₀ ℱ N) : Set (TerminalL1 P₀ ℱ N) :=
  {u | (fun ω => u ω) ∈ D.set}

theorem terminalClass_mem (D : TestSet P₀ ℱ N) {f : Ω → ℝ} (hf : f ∈ D.set) :
    terminalClass f (D.stronglyMeasurable f hf) (D.integrable f hf) ∈ terminalDensitySet D :=
  D.ae_saturated f hf _ (Lp.stronglyMeasurable _)
    (terminalClass_coe f (D.stronglyMeasurable f hf) (D.integrable f hf))

theorem terminalClass_mem_iff (D : TestSet P₀ ℱ N) (f : Ω → ℝ)
    (hfm : StronglyMeasurable[ℱ N] f) (hfi : Integrable f P₀) :
    terminalClass f hfm hfi ∈ terminalDensitySet D ↔ f ∈ D.set := by
  constructor
  · intro h
    exact D.ae_saturated _ h f hfm (terminalClass_coe f hfm hfi).symm
  · intro h
    exact D.ae_saturated f h _ (Lp.stronglyMeasurable _) (terminalClass_coe f hfm hfi)

theorem terminalDensitySet_closed (D : TestSet P₀ ℱ N) : IsClosed (terminalDensitySet D) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u z hu hz
  change (fun ω => z ω) ∈ D.set
  apply D.closed (fun n ω => u n ω) (fun ω => z ω) hu (Lp.stronglyMeasurable z)
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' u z).mp hz
  have he : (fun n => eLpNorm (⇑(u n) - ⇑z) 1 (P₀.trim (ℱ.le N))) =
      (fun n => eLpNorm (⇑(u n) - ⇑z) 1 P₀) := by
    funext n
    exact eLpNorm_trim (ℱ.le N) ((Lp.stronglyMeasurable (u n)).sub (Lp.stronglyMeasurable z))
  rwa [he] at ht

theorem terminalDensitySet_convex (D : TestSet P₀ ℱ N) : Convex ℝ (terminalDensitySet D) := by
  intro u hu v hv a b ha hb hab
  change (fun ω => u ω) ∈ D.set at hu
  change (fun ω => v ω) ∈ D.set at hv
  have hmem := D.convex hu hv ha hb hab
  apply D.ae_saturated _ hmem (fun ω => (a • u + b • v) ω) (Lp.stronglyMeasurable _)
  apply ae_eq_of_ae_eq_trim (hm := ℱ.le N)
  filter_upwards [Lp.coeFn_add (a • u) (b • v), Lp.coeFn_smul a u, Lp.coeFn_smul b v]
    with ω hadd haω hbω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hadd haω hbω ⊢
  rw [hadd, haω, hbω]

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: L2Inclusion -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def l2L1 (u : Lp ℝ 2 μ) : Lp ℝ 1 μ :=
  ((Lp.memLp u).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).toLp u

theorem l2L1_coe (u : Lp ℝ 2 μ) : l2L1 μ u =ᵐ[μ] u :=
  MemLp.coeFn_toLp _

theorem l2L1_norm (u : Lp ℝ 2 μ) : ‖l2L1 μ u‖ ≤ ‖u‖ := by
  rw [l2L1, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp u).2.ne
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Lp.aestronglyMeasurable u))

noncomputable def l2ToL1Linear : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 1 μ where
  toFun := l2L1 μ
  map_add' u v := by
    apply Lp.ext
    filter_upwards [l2L1_coe μ (u+v), Lp.coeFn_add u v,
      Lp.coeFn_add (l2L1 μ u) (l2L1 μ v), l2L1_coe μ u, l2L1_coe μ v] with ω h₁ h₂ h₃ h₄ h₅
    simp only [Pi.add_apply] at h₂ h₃
    exact h₁.trans (h₂.trans ((congrArg₂ (· + ·) h₄ h₅).symm.trans h₃.symm))
  map_smul' c u := by
    change l2L1 μ (c • u) = c • l2L1 μ u
    apply Lp.ext
    filter_upwards [l2L1_coe μ (c • u), Lp.coeFn_smul c u,
      Lp.coeFn_smul c (l2L1 μ u), l2L1_coe μ u] with ω h₁ h₂ h₃ h₄
    simp only [Pi.smul_apply, smul_eq_mul] at h₂ h₃
    exact h₁.trans (h₂.trans ((congrArg (fun z => c * z) h₄).symm.trans h₃.symm))

noncomputable def l2ToL1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 1 μ :=
  (l2ToL1Linear μ).mkContinuous 1 (fun u => by
    change ‖l2L1 μ u‖ ≤ 1 * ‖u‖
    simpa only [one_mul] using l2L1_norm μ u)

theorem l2ToL1_coe (u : Lp ℝ 2 μ) : l2ToL1 μ u =ᵐ[μ] u := l2L1_coe μ u

theorem l2ToL1_toLp {u : Ω → ℝ} (hu : MemLp u 2 μ) :
    l2ToL1 μ (hu.toLp u) = (hu.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).toLp u := by
  apply Lp.ext
  exact (l2ToL1_coe μ (hu.toLp u)).trans (hu.coeFn_toLp.trans (MemLp.coeFn_toLp _).symm)

theorem l2_representation (T : StrongDual ℝ (Lp ℝ 1 μ)) :
    ∃ h : Lp ℝ 2 μ, ∀ u : Lp ℝ 2 μ,
      T (l2ToL1 μ u) = ∫ ω, h ω * u ω ∂μ := by
  let h := (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm (T.comp (l2ToL1 μ))
  refine ⟨h, ?_⟩
  intro u
  have he := InnerProductSpace.toDual_symm_apply (x := u) (y := T.comp (l2ToL1 μ))
  simpa only [h, ContinuousLinearMap.comp_apply, L2.inner_def, Real.inner_apply] using he.symm

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: L1BoundedDual -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem l2ToL1_indicator {s : Set Ω} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) :
    l2ToL1 μ (indicatorConstLp 2 hs hμs c) = indicatorConstLp 1 hs hμs c := by
  apply Lp.ext
  exact (l2ToL1_coe μ _).trans (indicatorConstLp_coeFn.trans indicatorConstLp_coeFn.symm)

theorem clm_eq_of_l2 (T S : StrongDual ℝ (Lp ℝ 1 μ))
    (h : ∀ u : Lp ℝ 2 μ, T (l2ToL1 μ u) = S (l2ToL1 μ u)) : T = S := by
  apply ContinuousLinearMap.ext
  intro u
  refine Lp.induction (by simp) (fun v : Lp ℝ 1 μ => T v = S v) ?_ ?_ ?_ u
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst, ← l2ToL1_indicator μ hs hμs.ne c]
    exact h _
  · intro f g hf hg _ hTf hTg
    simp only [map_add, hTf, hTg]
  · exact isClosed_eq T.continuous S.continuous

theorem l2_representer_bounded (T : StrongDual ℝ (Lp ℝ 1 μ)) (h : Lp ℝ 2 μ)
    (hrep : ∀ u : Lp ℝ 2 μ, T (l2ToL1 μ u) = ∫ ω, h ω * u ω ∂μ) :
    ∀ᵐ ω ∂μ, |h ω| ≤ ‖T‖ := by
  have hint : Integrable h μ := MemLp.integrable (by norm_num) (Lp.memLp h)
  have htest : ∀ s, MeasurableSet s → |∫ ω in s, h ω ∂μ| ≤ ‖T‖ * μ.real s := by
    intro s hs
    let u : Lp ℝ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) 1
    let v : Lp ℝ 1 μ := indicatorConstLp 1 hs (measure_ne_top μ s) 1
    have huv : l2ToL1 μ u = v := l2ToL1_indicator μ hs (measure_ne_top μ s) 1
    have hv : ‖v‖ = μ.real s := by
      simpa [v] using (norm_indicatorConstLp (p := (1 : ℝ≥0∞)) (hs := hs)
        (hμs := measure_ne_top μ s) (c := (1 : ℝ)) (by simp) (by simp))
    have hTv : T v = ∫ ω in s, h ω ∂μ := by
      rw [← huv, hrep u, ← integral_indicator hs]
      apply integral_congr_ae
      filter_upwards [show u =ᵐ[μ] s.indicator (fun _ => (1 : ℝ)) from indicatorConstLp_coeFn] with ω hω
      by_cases hωs : ω ∈ s <;> simp [hω, hωs]
    have hh := T.le_opNorm v
    rw [hTv, hv, Real.norm_eq_abs] at hh
    exact hh
  have hupper : (fun ω => h ω) ≤ᵐ[μ] fun _ => ‖T‖ := by
    apply ae_le_of_forall_setIntegral_le hint (integrable_const _)
    intro s hs _
    calc
      (∫ ω in s, h ω ∂μ) ≤ |∫ ω in s, h ω ∂μ| := le_abs_self _
      _ ≤ ‖T‖ * μ.real s := htest s hs
      _ = ∫ _ω in s, ‖T‖ ∂μ := by simp [smul_eq_mul, mul_comm]
  have hlower : (fun _ => -‖T‖) ≤ᵐ[μ] fun ω => h ω := by
    apply ae_le_of_forall_setIntegral_le (integrable_const _) hint
    intro s hs _
    have hh := (abs_le.mp (htest s hs)).1
    simpa [setIntegral_const, smul_eq_mul, mul_comm] using hh
  filter_upwards [hupper, hlower] with ω hu hl
  exact abs_le.mpr ⟨hl, hu⟩

noncomputable def boundedIntegralCLM (H : Ω → ℝ) (hH : StronglyMeasurable H)
    (C : ℝ) (hC : ∀ᵐ ω ∂μ, |H ω| ≤ C) : StrongDual ℝ (Lp ℝ 1 μ) :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ ∞ 1
    ((memLp_top_of_bound hH.aestronglyMeasurable C (by simpa only [Real.norm_eq_abs] using hC)).toLp H)

omit [IsProbabilityMeasure μ] in
theorem boundedIntegralCLM_apply (H : Ω → ℝ) (hH : StronglyMeasurable H)
    (C : ℝ) (hC : ∀ᵐ ω ∂μ, |H ω| ≤ C) (u : Lp ℝ 1 μ) :
    boundedIntegralCLM μ H hH C hC u = ∫ ω, H ω * u ω ∂μ := by
  rw [boundedIntegralCLM, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp
    (memLp_top_of_bound hH.aestronglyMeasurable C (by simpa only [Real.norm_eq_abs] using hC))] with ω hω
  simp only [ContinuousLinearMap.mul_apply', hω]

theorem exists_L1_bounded_representer (T : StrongDual ℝ (Lp ℝ 1 μ)) :
    ∃ H : Ω → ℝ, StronglyMeasurable H ∧ (∀ᵐ ω ∂μ, |H ω| ≤ ‖T‖) ∧
      ∀ u : Lp ℝ 1 μ, T u = ∫ ω, H ω * u ω ∂μ := by
  obtain ⟨h, hrep⟩ := l2_representation μ T
  have hb := l2_representer_bounded μ T h hrep
  let S := boundedIntegralCLM μ h (Lp.stronglyMeasurable h) ‖T‖ hb
  have hTS : T = S := by
    apply clm_eq_of_l2 μ
    intro u
    rw [hrep u]
    change (∫ ω, h ω * u ω ∂μ) = boundedIntegralCLM μ h (Lp.stronglyMeasurable h) ‖T‖ hb (l2ToL1 μ u)
    rw [boundedIntegralCLM_apply]
    apply integral_congr_ae
    filter_upwards [l2ToL1_coe μ u] with ω hω
    rw [hω]
  refine ⟨h, Lp.stronglyMeasurable h, hb, ?_⟩
  intro u
  rw [hTS]
  exact boundedIntegralCLM_apply μ h (Lp.stronglyMeasurable h) ‖T‖ hb u

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: BoundedClaimSeparation -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω} [IsProbabilityMeasure P₀]
variable {ℱ : Filtration ℕ m} {N : ℕ}

theorem mem_of_bounded_claim_lower_bounds (D : TestSet P₀ ℱ N) (g : Ω → ℝ)
    (hgm : StronglyMeasurable[ℱ N] g) (hgi : Integrable g P₀)
    (h : ∀ (H : Ω → ℝ), StronglyMeasurable[ℱ N] H →
      ∀ C : ℝ, 0 ≤ C → (∀ᵐ ω ∂P₀, |H ω| ≤ C) →
      ∀ a : ℝ, (∀ f ∈ D.set, a ≤ ∫ ω, H ω * f ω ∂P₀) →
        a ≤ ∫ ω, H ω * g ω ∂P₀) : g ∈ D.set := by
  by_contra hnot
  let u := terminalClass g hgm hgi
  have hu : u ∉ terminalDensitySet D := fun hh => hnot ((terminalClass_mem_iff D g hgm hgi).mp hh)
  obtain ⟨T, a, hTa, hAll⟩ := geometric_hahn_banach_point_closed
    (terminalDensitySet_convex D) (terminalDensitySet_closed D) hu
  let htrim : @IsProbabilityMeasure Ω (ℱ N) (P₀.trim (ℱ.le N)) := ⟨by
    rw [trim_measurableSet_eq (ℱ.le N) MeasurableSet.univ, measure_univ]⟩
  obtain ⟨H, hH, hB, hrep⟩ := @exists_L1_bounded_representer Ω (ℱ N) (P₀.trim (ℱ.le N)) htrim T
  have hclass : ∀ (f : Ω → ℝ) (hfm : StronglyMeasurable[ℱ N] f) (hfi : Integrable f P₀),
      T (terminalClass f hfm hfi) = ∫ ω, H ω * f ω ∂P₀ := by
    intro f hfm hfi
    calc
      T (terminalClass f hfm hfi) =
          ∫ ω, H ω * terminalClass f hfm hfi ω ∂P₀.trim (ℱ.le N) := hrep _
      _ = ∫ ω, H ω * f ω ∂P₀.trim (ℱ.le N) := by
        apply integral_congr_ae
        filter_upwards [terminalClass_coe_trim f hfm hfi] with ω hω
        rw [hω]
      _ = ∫ ω, H ω * f ω ∂P₀ := (integral_trim (ℱ.le N) (hH.mul hfm)).symm
  have hba : ∀ᵐ ω ∂P₀, |H ω| ≤ ‖T‖ := ae_of_ae_trim (ℱ.le N) hB
  have hlow := h H hH ‖T‖ (norm_nonneg _) hba a (by
    intro f hf
    rw [← hclass f (D.stronglyMeasurable f hf) (D.integrable f hf)]
    exact (hAll _ (terminalClass_mem D hf)).le)
  change T (terminalClass g hgm hgi) < a at hTa
  rw [hclass g hgm hgi] at hTa
  exact (not_le_of_gt hTa) hlow

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: InitialTriviality -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω} [IsProbabilityMeasure P₀]
variable {ℱ : Filtration ℕ m} {N : ℕ}

theorem condExp_of_trivial (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m' : MeasurableSpace Ω} (hm : m' ≤ m)
    (htr : ∀ A, MeasurableSet[m'] A → μ A = 0 ∨ μ A = 1)
    {H : Ω → ℝ} (hH : Integrable H μ) :
    μ[H | m'] =ᵐ[μ] fun _ => ∫ ω, H ω ∂μ := by
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hH
  · intro A _ _
    exact (integrable_const _).integrableOn
  · intro A hA _
    rcases htr A hA with hzero | hone
    · rw [Measure.restrict_eq_zero.mpr hzero]
      simp
    · have hc : μ Aᶜ = 0 := by
        rw [measure_compl (hm A hA) (by rw [hone]; exact ENNReal.one_ne_top),
          measure_univ, hone, tsub_self]
      rw [Measure.restrict_eq_self_of_ae_mem (show ∀ᵐ ω ∂μ, ω ∈ A from hc)]
      simp
  · exact stronglyMeasurable_const.aestronglyMeasurable

theorem test_initial_condExp (D : TestSet P₀ ℱ N)
    (hℱ₀ : ∀ A, MeasurableSet[ℱ 0] A → P₀ A = 0 ∨ P₀ A = 1)
    {f : Ω → ℝ} (hf : f ∈ Pe D) {H : Ω → ℝ} (hH : Integrable H (Q P₀ f)) :
    (Q P₀ f)[H | ℱ 0] =ᵐ[P₀] fun _ => ∫ ω, H ω ∂Q P₀ f := by
  let := test_probability D hf.1
  apply (aux_pdp_acQ D hf).ae_le
  apply condExp_of_trivial (Q P₀ f) (ℱ.le 0) ?_ hH
  intro A hA
  rcases hℱ₀ A hA with hzero | hone
  · exact Or.inl ((aux_pdp_Qac f) hzero)
  · right
    have hc : P₀ Aᶜ = 0 := by
      rw [measure_compl (ℱ.le 0 A hA) (by rw [hone]; exact ENNReal.one_ne_top),
        measure_univ, hone, tsub_self]
    simpa only [measure_univ] using measure_of_measure_compl_eq_zero ((aux_pdp_Qac f) hc)

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: TerminalTests -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω} [IsProbabilityMeasure P₀]
variable {ℱ : Filtration ℕ m} {N : ℕ}

def terminalTest (N : ℕ) (H : Ω → ℝ) (C : ℝ) (n : ℕ) : Ω → ℝ :=
  if n = N then H else fun _ => C

omit [IsProbabilityMeasure P₀] in
theorem terminalTest_bound {H : Ω → ℝ} {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ᵐ ω ∂P₀, |H ω| ≤ C) (n : ℕ) :
    ∀ᵐ ω ∂P₀, |terminalTest N H C n ω| ≤ C := by
  by_cases hn : n = N
  · simpa [terminalTest, hn] using hC
  · simp [terminalTest, hn, abs_of_nonneg h0]

omit [IsProbabilityMeasure P₀] in
theorem terminalTest_valueProcess {H : Ω → ℝ} (hH : StronglyMeasurable[ℱ N] H)
    {C : ℝ} (h0 : 0 ≤ C) (hC : ∀ᵐ ω ∂P₀, |H ω| ≤ C) :
    IsValueProcess P₀ ℱ N (terminalTest N H C) := by
  refine ⟨?_, C, fun n _ => terminalTest_bound h0 hC n⟩
  intro n _
  by_cases hn : n = N
  · subst n
    simpa [terminalTest] using hH
  · simpa [terminalTest, hn] using (stronglyMeasurable_const : StronglyMeasurable[ℱ n] (fun _ : Ω => C))

omit [IsProbabilityMeasure P₀] in
theorem terminalTest_stopped_ge {H : Ω → ℝ} {C : ℝ}
    (hC : ∀ᵐ ω ∂P₀, |H ω| ≤ C) {τ : Ω → WithTop ℕ}
    (hτ : ∀ ω, τ ω ≤ (N : WithTop ℕ)) :
    H ≤ᵐ[P₀] stoppedValue (terminalTest N H C) τ := by
  filter_upwards [hC] with ω hω
  obtain ⟨k, _, hk⟩ := aux_pdp_exists_k hτ ω
  rw [aux_pdp_sv_of_eq _ hk]
  by_cases he : k = N
  · simp [terminalTest, he]
  · simpa [terminalTest, he] using (le_abs_self (H ω)).trans hω

theorem terminalTest_at_N (H : Ω → ℝ) (C : ℝ) :
    stoppedValue (terminalTest N H C) (fun _ => (N : WithTop ℕ)) = H := by
  rw [stoppedValue_const_nat]
  simp [terminalTest]

theorem lower_bound_psi_terminalTest (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    (hℱ₀ : ∀ A, MeasurableSet[ℱ 0] A → P₀ A = 0 ∨ P₀ A = 1)
    {H : Ω → ℝ} (hH : StronglyMeasurable[ℱ N] H) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ᵐ ω ∂P₀, |H ω| ≤ C) (a : ℝ)
    (ha : ∀ f ∈ D.set, a ≤ ∫ ω, H ω * f ω ∂P₀) :
    (fun _ => a) ≤ᵐ[P₀] PsiN D (terminalTest N H C) 0 := by
  have hX := terminalTest_valueProcess hH h0 hC
  apply (psi_spec D hPe hX _ (bounded_const_stop 0 (Nat.zero_le N))).2.2
    _ stronglyMeasurable_const
  rintro Y ⟨τ, hτ, _, f, hf, rfl⟩
  have hspace : (bounded_const_stop (ℱ := ℱ) 0 (Nat.zero_le N)).1.measurableSpace = ℱ 0 :=
    IsStoppingTime.measurableSpace_const ℱ 0
  rw [hspace]
  have hHi := bounded_integrable_Q D hf.1 (hH.mono (ℱ.le N)).aestronglyMeasurable hC
  have hlo := condExp_mono (m := ℱ 0) hHi (aux_pdp_sv_int D _ hX hf.1 hτ)
    ((aux_pdp_Qac f).ae_le (terminalTest_stopped_ge hC hτ.2))
  have he := test_initial_condExp D hℱ₀ hf hHi
  have hval : a ≤ ∫ ω, H ω ∂Q P₀ f := by
    rw [test_integral_eq D hf.1]
    simpa only [mul_comm] using ha f hf.1
  filter_upwards [he, (aux_pdp_acQ D hf).ae_le hlo] with ω heω hloω
  exact hval.trans (heω ▸ hloω)

theorem psi_terminalTest_le (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {H : Ω → ℝ} (hH : StronglyMeasurable[ℱ N] H) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ᵐ ω ∂P₀, |H ω| ≤ C) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) {f : Ω → ℝ} (hf : f ∈ Pe D) :
    Psi D (terminalTest N H C) τ hτ.1 ≤ᵐ[P₀]
      (Q P₀ f)[H | hτ.1.measurableSpace] := by
  have hh := psi_le_condExp D hPe (terminalTest_valueProcess hH h0 hC) τ
    (fun _ => (N : WithTop ℕ)) hτ (bounded_const_stop N le_rfl) hτ.2 hf
  rwa [terminalTest_at_N] at hh

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: BellmanCash -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
  {ℱ : Filtration ℕ m} {N : ℕ} [IsProbabilityMeasure P₀]

omit [IsProbabilityMeasure P₀] in
theorem condExp_stop_decomposition (D : TestSet P₀ ℱ N)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    (σ ν : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ)
    (hν : IsBddStoppingTime ℱ N ν) (hσν : ∀ ω, σ ω ≤ ν ω)
    {f : Ω → ℝ} (hf : f ∈ Pe D) :
    (Q P₀ f)[stoppedValue X ν | hσ.1.measurableSpace] =ᵐ[P₀]
      fun ω => (Q P₀ f)[stoppedValue (fromStop X σ) ν | hσ.1.measurableSpace] ω +
        Xprev X σ ω := by
  let := test_probability D hf.1
  have hfrom := fromStop_valueProcess hX σ hσ
  have hprev := Xprev_measurable hX σ hσ
  obtain ⟨C, hC0, hC⟩ := value_nonneg_bound hX
  have hiprev := bounded_integrable_Q D hf.1
    (hprev.mono hσ.1.measurableSpace_le).aestronglyMeasurable (Xprev_bound hC0 hC σ hσ)
  have he : stoppedValue X ν = stoppedValue (fromStop X σ) ν + Xprev X σ := by
    funext ω
    obtain ⟨k, hk, hνk⟩ := aux_pdp_exists_k hν.2 ω
    have hσk : σ ω ≤ (k : WithTop ℕ) := (hσν ω).trans_eq hνk
    simp only [Pi.add_apply, aux_pdp_sv_of_eq X hνk,
      aux_pdp_sv_of_eq (fromStop X σ) hνk, fromStop, if_pos hσk, sub_add_cancel]
  have h := condExp_add (aux_pdp_sv_int D _ hfrom hf.1 hν) hiprev hσ.1.measurableSpace
  rw [condExp_of_stronglyMeasurable hσ.1.measurableSpace_le hprev hiprev] at h
  rw [he]
  exact (aux_pdp_acQ D hf).ae_le h

theorem psi_fromStop_add_prev (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    Psi D X τ hτ.1 =ᵐ[P₀] fun ω =>
      Psi D (fromStop X τ) τ hτ.1 ω + Xprev X τ ω := by
  have hfrom := fromStop_valueProcess hX τ hτ
  have hs := psi_spec D hPe hfrom τ hτ
  have ht := psi_spec D hPe hX τ hτ
  apply aux_pdp_unique ht
  apply isEssInf_translate hs (Xprev_measurable hX τ hτ)
  · rintro t ⟨ν, hν, hτν, f, hf, rfl⟩
    refine ⟨_, ⟨ν, hν, hτν, f, hf, rfl⟩, ?_⟩
    exact condExp_stop_decomposition D hX τ ν hτ hν hτν hf
  · rintro s ⟨ν, hν, hτν, f, hf, rfl⟩
    refine ⟨_, ⟨ν, hν, hτν, f, hf, rfl⟩, ?_⟩
    exact condExp_stop_decomposition D hX τ ν hτ hν hτν hf

theorem bellman_valueProcess (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    IsValueProcess P₀ ℱ N (bellmanProcess D X τ hτ.1) := by
  classical
  have hfrom := fromStop_valueProcess hX τ hτ
  have hprev := Xprev_measurable hX τ hτ
  have hpsi := (psi_spec D hPe hfrom τ hτ).1
  have he (n : ℕ) : bellmanProcess D X τ hτ.1 n =
      {ω | τ ω ≤ (n:WithTop ℕ)}ᶜ.indicator (X n) +
      {ω | τ ω ≤ (n:WithTop ℕ)}.indicator
        (fun ω => Xprev X τ ω + Psi D (fromStop X τ) τ hτ.1 ω) := by
    funext ω
    by_cases hω : τ ω ≤ (n:WithTop ℕ)
    · simp [bellmanProcess, preStop, hω, not_lt.mpr hω]
    · simp [bellmanProcess, preStop, hω, not_le.mp hω]
  refine ⟨?_, ?_⟩
  · intro n hn
    rw [he]
    exact ((hX.1 n hn).indicator (hτ.1.measurableSet_le n).compl).add
      (stopping_indicator_le_measurable hτ (hprev.add hpsi) n)
  · obtain ⟨C, hC0, hC⟩ := value_nonneg_bound hX
    have hbpsi := psi_bounded D hPe hfrom (fun _ hn => fromStop_bound hC0 hC τ hτ hn) τ hτ
    refine ⟨3*C, fun n hn => ?_⟩
    filter_upwards [hC n hn, Xprev_bound hC0 hC τ hτ, hbpsi] with ω hx hp hv
    by_cases hω : τ ω ≤ (n:WithTop ℕ)
    · simp only [bellmanProcess, preStop, if_neg (not_lt.mpr hω), if_pos hω]
      exact (abs_add_le _ _).trans (by linarith)
    · simp only [bellmanProcess, preStop, if_pos (not_le.mp hω), if_neg hω, add_zero]
      exact hx.trans (show C ≤ 3*C by linarith)

theorem bellman_stoppedValue (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    stoppedValue (bellmanProcess D X τ hτ.1) τ =ᵐ[P₀] Psi D X τ hτ.1 := by
  have he : stoppedValue (bellmanProcess D X τ hτ.1) τ =
      fun ω => Xprev X τ ω + Psi D (fromStop X τ) τ hτ.1 ω := by
    funext ω
    obtain ⟨k, hk, hτk⟩ := aux_pdp_exists_k hτ.2 ω
    rw [aux_pdp_sv_of_eq _ hτk]
    simp [bellmanProcess, preStop, hτk]
  rw [he]
  filter_upwards [psi_fromStop_add_prev D hPe hX τ hτ] with ω hω
  linarith

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: ReverseStability -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω} [IsProbabilityMeasure P₀]
variable {ℱ : Filtration ℕ m} {N : ℕ}

theorem stable_of_bellman (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    (hℱ₀ : ∀ A, MeasurableSet[ℱ 0] A → P₀ A = 0 ∨ P₀ A = 1)
    (hBell : ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
      ∀ σ τ : Ω → WithTop ℕ, ∀ hσ : IsBddStoppingTime ℱ N σ,
      ∀ hτ : IsBddStoppingTime ℱ N τ, (∀ ω, σ ω ≤ τ ω) →
      Psi D X σ hσ.1 =ᵐ[P₀] Psi D (bellmanProcess D X τ hτ.1) σ hσ.1) :
    IsStable D := by
  intro f₀ hf₀ f hf τ hτ
  apply mem_of_bounded_claim_lower_bounds D _ (paste_measurable D hf.1 τ hτ)
    (paste_integrable D hf₀.1 hf τ hτ)
  intro H hH C h0 hC a ha
  let X := terminalTest N H C
  have hX : IsValueProcess P₀ ℱ N X := terminalTest_valueProcess hH h0 hC
  let σ : Ω → WithTop ℕ := fun _ => 0
  have hσ : IsBddStoppingTime ℱ N σ := bounded_const_stop 0 (Nat.zero_le N)
  have hσspace : hσ.1.measurableSpace = ℱ 0 := IsStoppingTime.measurableSpace_const ℱ 0
  have hστ : ∀ ω, σ ω ≤ τ ω := fun _ => bot_le
  let Y := bellmanProcess D X τ hτ.1
  have hY : IsValueProcess P₀ ℱ N Y := bellman_valueProcess D hPe hX τ hτ
  have hinit : (fun _ => a) ≤ᵐ[P₀] Psi D X σ hσ.1 :=
    lower_bound_psi_terminalTest D hPe hℱ₀ hH h0 hC a ha
  have hbell := hBell X hX σ τ hσ hτ hστ
  have hle := psi_le_condExp D hPe hY σ τ hσ hτ hστ hf₀
  have hconst := test_initial_condExp D hℱ₀ hf₀ (aux_pdp_sv_int D Y hY hf₀.1 hτ)
  have htotal : a ≤ ∫ ω, stoppedValue Y τ ω ∂Q P₀ f₀ := by
    have hle' : Psi D Y σ hσ.1 ≤ᵐ[P₀] (Q P₀ f₀)[stoppedValue Y τ | ℱ 0] := by
      simpa only [hσspace] using hle
    have hall : ∀ᵐ ω ∂P₀, a ≤ ∫ ω, stoppedValue Y τ ω ∂Q P₀ f₀ := by
      filter_upwards [hinit, hbell, hle', hconst] with ω hi hb hl hc
      exact (hi.trans_eq hb).trans (hl.trans_eq hc)
    exact hall.exists.choose_spec
  have hstopped := bellman_stoppedValue D hPe hX τ hτ
  have hpsi : a ≤ ∫ ω, Psi D X τ hτ.1 ω ∂Q P₀ f₀ := by
    rwa [integral_congr_ae ((aux_pdp_Qac f₀).ae_le hstopped)] at htotal
  have hpm := (psi_spec D hPe hX τ hτ).1
  have hpb : ∀ᵐ ω ∂P₀, |Psi D X τ hτ.1 ω| ≤ C :=
    psi_bounded D hPe hX (fun n _ => terminalTest_bound h0 hC n) τ hτ
  have hcm : AEStronglyMeasurable ((Q P₀ f)[H | hτ.1.measurableSpace]) P₀ :=
    (stronglyMeasurable_condExp.mono hτ.1.measurableSpace_le).aestronglyMeasurable
  have hci := bounded_integrable_Q D hf₀.1 hcm (condExp_bounded_Pe D hf hC _)
  have hpi := bounded_integrable_Q D hf₀.1
    (hpm.mono hτ.1.measurableSpace_le).aestronglyMeasurable hpb
  have hbound := integral_mono_ae hpi hci
    ((aux_pdp_Qac f₀).ae_le (psi_terminalTest_le D hPe hH h0 hC τ hτ hf))
  have hfinal := hpsi.trans hbound
  rw [← paste_expectation D hf₀ hf τ hτ (hH.mono (ℱ.le N)).aestronglyMeasurable hC] at hfinal
  rw [integral_Q_eq (paste_integrable D hf₀.1 hf τ hτ)
    ((paste_pos D hf₀ hf τ hτ).mono fun _ h => h.le)] at hfinal
  simpa only [mul_comm] using hfinal

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: SnellUniqueness -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
  {ℱ : Filtration ℕ m} {N : ℕ} [IsProbabilityMeasure P₀]

theorem snell_unique_recursion (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {B K : ℕ → Ω → ℝ} (hB : IsValueProcess P₀ ℱ N B) (hK : IsValueProcess P₀ ℱ N K)
    (hterm : K N =ᵐ[P₀] B N)
    (hrec : ∀ n<N, K n =ᵐ[P₀] fun ω => min (B n ω) (lowerCond D (K (n+1)) (ℱ n) ω)) :
    ∀ n≤N, PsiBar D B n =ᵐ[P₀] K n := by
  obtain ⟨C, hC⟩ := hB.2
  obtain ⟨E, hE⟩ := hK.2
  have aux : ∀ k≤N, PsiBar D B (N-k) =ᵐ[P₀] K (N-k) := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa only [Nat.sub_zero, psiBar_terminal] using hterm.symm
    | succ k ih =>
      intro hk
      let n := N-(k+1)
      have hn : n<N := by dsimp [n]; omega
      have hnp : n+1=N-k := by dsimp [n]; omega
      have ih' : PsiBar D B (n+1) =ᵐ[P₀] K (n+1) := by
        simpa only [hnp] using ih (show k≤N by omega)
      have hb := (psiBar_regular D hPe hB hC (show n+1≤N by omega)).2
      have hc := lowerCond_congr D hPe hb (hE (n+1) (by omega)) ih' (ℱ.le n)
      change PsiBar D B n =ᵐ[P₀] K n
      filter_upwards [hc, hrec n hn] with ω hcω hrω
      rw [psiBar_rec D B hn]
      change min (B n ω) (lowerCond D (PsiBar D B (n+1)) (ℱ n) ω) = K n ω
      rw [hcω, hrω]
  intro n hn
  have he : N-(N-n)=n := by omega
  simpa only [he] using aux (N-n) (Nat.sub_le _ _)

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: StoppingEvaluation -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
  {ℱ : Filtration ℕ m} {N : ℕ} [IsProbabilityMeasure P₀]

omit [IsProbabilityMeasure P₀] in
theorem stopped_eq_of_value_eq {X Y : ℕ → Ω → ℝ}
    (he : ∀ n≤N, X n =ᵐ[P₀] Y n) (τ : Ω → WithTop ℕ)
    (hτ : ∀ ω, τ ω ≤ (N:WithTop ℕ)) : stoppedValue X τ =ᵐ[P₀] stoppedValue Y τ :=
  (stopped_le_of_value_le (fun n hn => (he n hn).le) τ hτ).antisymm
    (stopped_le_of_value_le (fun n hn => (he n hn).ge) τ hτ)

theorem psi_eq_stopped_psiN (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    Psi D X τ hτ.1 =ᵐ[P₀] stoppedValue (PsiN D X) τ := by
  classical
  have h := checked_psi_defines_process P₀ ℱ N D hPe X hX τ hτ
  rw [aux_pdp_sv_sum (PsiN D X) hτ.2]
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using h

theorem psi_eq_stopped_snell (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    (he : ∀ n≤N, PsiN D X n =ᵐ[P₀] PsiBar D X n)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    Psi D X τ hτ.1 =ᵐ[P₀] stoppedValue (PsiBar D X) τ :=
  (psi_eq_stopped_psiN D hPe hX τ hτ).trans (stopped_eq_of_value_eq he τ hτ.2)

theorem bellman_replacement_eq (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) (n : ℕ) :
    bellmanProcess D X τ hτ.1 n =ᵐ[P₀]
      fun ω => if τ ω ≤ (n:WithTop ℕ) then Psi D X τ hτ.1 ω else X n ω := by
  classical
  filter_upwards [psi_fromStop_add_prev D hPe hX τ hτ] with ω hω
  by_cases hn : τ ω ≤ (n:WithTop ℕ)
  · simp only [bellmanProcess, preStop, if_neg (not_lt.mpr hn), if_pos hn]
    linarith
  · simp only [bellmanProcess, preStop, if_pos (not_le.mp hn), if_neg hn, add_zero]

theorem bellman_replacement_snell (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    (he : ∀ n≤N, PsiN D X n =ᵐ[P₀] PsiBar D X n)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) (n : ℕ) :
    bellmanProcess D X τ hτ.1 n =ᵐ[P₀]
      fun ω => if τ ω ≤ (n:WithTop ℕ) then stoppedValue (PsiBar D X) τ ω else X n ω := by
  classical
  filter_upwards [bellman_replacement_eq D hPe hX τ hτ n,
    psi_eq_stopped_snell D hPe hX he τ hτ] with ω hb heω
  simpa only [heω] using hb

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: FrozenProcess -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
variable {ℱ : Filtration ℕ m} {N : ℕ}

noncomputable def freezeAtStop (Y : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (n : ℕ) : Ω → ℝ := by
  classical
  exact fun ω => if τ ω ≤ (n : WithTop ℕ) then stoppedValue Y τ ω else Y n ω

theorem freezeAtStop_bound {Y : ℕ → Ω → ℝ} {C : ℝ}
    (hC : ∀ n ≤ N, ∀ᵐ ω ∂P₀, |Y n ω| ≤ C) (τ : Ω → WithTop ℕ)
    (hτ : IsBddStoppingTime ℱ N τ) {n : ℕ} (hn : n ≤ N) :
    ∀ᵐ ω ∂P₀, |freezeAtStop Y τ n ω| ≤ C := by
  filter_upwards [value_bound_stopped hC hτ.2, hC n hn] with ω hs hnω
  by_cases h : τ ω ≤ (n : WithTop ℕ)
  · simpa only [freezeAtStop, if_pos h] using hs
  · simpa only [freezeAtStop, if_neg h] using hnω

theorem freezeAtStop_valueProcess {Y : ℕ → Ω → ℝ} (hY : IsValueProcess P₀ ℱ N Y)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    IsValueProcess P₀ ℱ N (freezeAtStop Y τ) := by
  classical
  refine ⟨?_, ?_⟩
  · intro n hn
    have he : freezeAtStop Y τ n =
        {ω | τ ω ≤ (n : WithTop ℕ)}.indicator (stoppedValue Y τ) +
        {ω | τ ω ≤ (n : WithTop ℕ)}ᶜ.indicator (Y n) := by
      funext ω
      by_cases h : τ ω ≤ (n : WithTop ℕ) <;> simp [freezeAtStop, h]
    rw [he]
    exact (stopping_indicator_le_measurable hτ (stopped_stronglyMeasurable hY.1 τ hτ) n).add
      ((hY.1 n hn).indicator (hτ.1.measurableSet_le n).compl)
  · obtain ⟨C, hC⟩ := hY.2
    exact ⟨C, fun _ hn => freezeAtStop_bound hC τ hτ hn⟩

theorem freezeAtStop_succ_on (Y : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ) (n : ℕ)
    (ω : Ω) (h : τ ω ≤ (n : WithTop ℕ)) :
    freezeAtStop Y τ (n+1) ω = freezeAtStop Y τ n ω := by
  have hn : (n : WithTop ℕ) ≤ (n+1 : ℕ) := by exact_mod_cast Nat.le_succ n
  simp only [freezeAtStop, if_pos h, if_pos (h.trans hn)]

theorem freezeAtStop_succ_off (Y : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (hτ : ∀ ω, τ ω ≤ (N : WithTop ℕ)) (n : ℕ) (ω : Ω)
    (h : ¬τ ω ≤ (n : WithTop ℕ)) : freezeAtStop Y τ (n+1) ω = Y (n+1) ω := by
  obtain ⟨k, _, hk⟩ := aux_pdp_exists_k hτ ω
  have hnk : n < k := by
    rw [hk] at h
    exact_mod_cast not_le.mp h
  by_cases he : k = n+1
  · rw [freezeAtStop, hk, he, if_pos le_rfl, aux_pdp_sv_of_eq _ (hk.trans (congrArg (fun j : ℕ => (j : WithTop ℕ)) he))]
  · have hnot : ¬τ ω ≤ (n+1 : ℕ) := by
      rw [hk]
      exact_mod_cast (show ¬k ≤ n+1 by omega)
    simp only [freezeAtStop, if_neg hnot]

theorem freezeAtStop_stopped (Y : ℕ → Ω → ℝ) (σ τ : Ω → WithTop ℕ)
    (hσ : ∀ ω, σ ω ≤ (N : WithTop ℕ)) (hτ : ∀ ω, τ ω ≤ (N : WithTop ℕ))
    (hστ : ∀ ω, σ ω ≤ τ ω) :
    stoppedValue (freezeAtStop Y τ) σ = stoppedValue Y σ := by
  funext ω
  obtain ⟨k, _, hk⟩ := aux_pdp_exists_k hσ ω
  obtain ⟨j, _, hj⟩ := aux_pdp_exists_k hτ ω
  rw [aux_pdp_sv_of_eq _ hk, aux_pdp_sv_of_eq _ hk]
  by_cases h : τ ω ≤ (k : WithTop ℕ)
  · have he : τ ω = σ ω := h.trans_eq hk.symm |>.antisymm (hστ ω)
    rw [freezeAtStop, if_pos h, aux_pdp_sv_of_eq _ (he.trans hk)]
  · simp only [freezeAtStop, if_neg h]

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: StoppedSnell -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω}
variable {ℱ : Filtration ℕ m} {N : ℕ}

variable [IsProbabilityMeasure P₀]

theorem snell_bellman_stopped (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    {X : ℕ → Ω → ℝ} (hX : IsValueProcess P₀ ℱ N X)
    (he : ∀ n ≤ N, PsiN D X n =ᵐ[P₀] PsiBar D X n)
    (τ : Ω → WithTop ℕ) (hτ : IsBddStoppingTime ℱ N τ) :
    ∀ n ≤ N, PsiBar D (bellmanProcess D X τ hτ.1) n =ᵐ[P₀]
      freezeAtStop (PsiBar D X) τ n := by
  let Y := PsiBar D X
  let K := freezeAtStop Y τ
  let B := bellmanProcess D X τ hτ.1
  have hY : IsValueProcess P₀ ℱ N Y := psiBar_valueProcess D hPe hX
  have hK : IsValueProcess P₀ ℱ N K := freezeAtStop_valueProcess hY τ hτ
  have hB : IsValueProcess P₀ ℱ N B := bellman_valueProcess D hPe hX τ hτ
  obtain ⟨C, hC⟩ := hX.2
  have hbY (n : ℕ) (hn : n ≤ N) : ∀ᵐ ω ∂P₀, |Y n ω| ≤ C :=
    (psiBar_regular D hPe hX hC hn).2
  have hbK (n : ℕ) (hn : n ≤ N) : ∀ᵐ ω ∂P₀, |K n ω| ≤ C :=
    freezeAtStop_bound hbY τ hτ hn
  apply snell_unique_recursion D hPe hB hK
  · filter_upwards [bellman_replacement_snell D hPe hX he τ hτ N] with ω hω
    simpa only [B, K, freezeAtStop, if_pos (hτ.2 ω)] using hω.symm
  · intro n hn
    have hn' : n+1 ≤ N := by omega
    let A := {ω | τ ω ≤ (n : WithTop ℕ)}
    have hA : MeasurableSet[ℱ n] A := hτ.1.measurableSet_le n
    have hsmK (j : ℕ) (hj : j ≤ N) : AEStronglyMeasurable (K j) P₀ :=
      ((hK.1 j hj).mono (ℱ.le j)).aestronglyMeasurable
    have hsmY : AEStronglyMeasurable (Y (n+1)) P₀ :=
      ((hY.1 (n+1) hn').mono (ℱ.le (n+1))).aestronglyMeasurable
    have hon := lowerCond_local_eq D hPe (hbK (n+1) hn') (hbK n hn.le)
      (hsmK (n+1) hn') (hsmK n hn.le) (ℱ.le n) hA
      (Filter.Eventually.of_forall fun ω hω => freezeAtStop_succ_on Y τ n ω hω)
    have hoff := lowerCond_local_eq D hPe (hbK (n+1) hn') (hbY (n+1) hn')
      (hsmK (n+1) hn') hsmY (ℱ.le n) hA.compl
      (Filter.Eventually.of_forall fun ω hω => freezeAtStop_succ_off Y τ hτ.2 n ω hω)
    have hmeas := lowerCond_of_measurable D hPe (hbK n hn.le) (ℱ.le n) (hK.1 n hn.le)
    filter_upwards [hon, hoff, hmeas, bellman_replacement_snell D hPe hX he τ hτ n]
      with ω honω hoffω hmω hbω
    by_cases hω : τ ω ≤ (n : WithTop ℕ)
    · have hlc : lowerCond D (K (n+1)) (ℱ n) ω = K n ω := (honω hω).trans hmω
      rw [hlc]
      have hb : B n ω = K n ω := by
        simpa only [K, freezeAtStop, if_pos hω] using hbω
      rw [hb, min_self]
    · have hlc : lowerCond D (K (n+1)) (ℱ n) ω = lowerCond D (Y (n+1)) (ℱ n) ω := hoffω hω
      rw [hlc]
      have hb : B n ω = X n ω := by simpa only [if_neg hω] using hbω
      rw [hb]
      simpa only [K, freezeAtStop, if_neg hω] using congrFun (psiBar_rec D X hn) ω

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: BellmanPrinciple -/
section

namespace MultiperiodRisk.Bellman.Proof

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω} {P₀ : Measure Ω} [IsProbabilityMeasure P₀]
variable {ℱ : Filtration ℕ m} {N : ℕ}

theorem bellman_of_snell_equality (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty)
    (hEq : ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
      ∀ n ≤ N, PsiN D X n =ᵐ[P₀] PsiBar D X n) :
    ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
      ∀ σ τ : Ω → WithTop ℕ, ∀ hσ : IsBddStoppingTime ℱ N σ,
      ∀ hτ : IsBddStoppingTime ℱ N τ, (∀ ω, σ ω ≤ τ ω) →
      Psi D X σ hσ.1 =ᵐ[P₀] Psi D (bellmanProcess D X τ hτ.1) σ hσ.1 := by
  intro X hX σ τ hσ hτ hστ
  let B := bellmanProcess D X τ hτ.1
  have hB : IsValueProcess P₀ ℱ N B := bellman_valueProcess D hPe hX τ hτ
  have hleft := psi_eq_stopped_snell D hPe hX (hEq X hX) σ hσ
  have hright := psi_eq_stopped_snell D hPe hB (hEq B hB) σ hσ
  have hstop := stopped_eq_of_value_eq (snell_bellman_stopped D hPe hX (hEq X hX) τ hτ) σ hσ.2
  have he := freezeAtStop_stopped (PsiBar D X) σ τ hσ.2 hτ.2 hστ
  exact hleft.trans (hright.trans (hstop.trans (Filter.EventuallyEq.of_eq he))).symm

end MultiperiodRisk.Bellman.Proof

end

/- Complete checked body: RiskRoot -/
section

namespace MultiperiodRisk.Bellman

open MeasureTheory

/-- Theorem 4.2: for a closed convex set of test probabilities with `𝒫ᵉ ≠ ∅` and an initial
σ-algebra `ℱ_0` that is trivial under `P₀`, stability is equivalent to each of
(i) `Ψ(X)` is a `ℚ`-submartingale for every `ℚ ∈ 𝒫` and every value process `X`;
(ii) `Ψ = Ψ̄` on value processes;
(iii) Bellman's principle `Ψ_σ(X) = Ψ_σ(X^{τ-} + Ψ_τ(^τX) 1_{[τ,N]})` for stopping times `σ ≤ τ`. -/
theorem solution {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ)
    (hℱ₀ : ∀ s, MeasurableSet[ℱ 0] s → P₀ s = 0 ∨ P₀ s = 1)
    (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty) :
    List.TFAE
      [ IsStable D,
        ∀ f ∈ D.set, ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
          Submartingale (fun n => PsiN D X (min n N)) ℱ (Q P₀ f),
        ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
          ∀ n ≤ N, PsiN D X n =ᵐ[P₀] PsiBar D X n,
        ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
          ∀ (σ τ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ)
            (hτ : IsBddStoppingTime ℱ N τ), (∀ ω, σ ω ≤ τ ω) →
            Psi D X σ hσ.1 =ᵐ[P₀] Psi D (bellmanProcess D X τ hτ.1) σ hσ.1 ] := by
  classical
  tfae_have 1 → 2 := by
    intro hs f hf X hX
    exact Proof.psi_submartingale_of_stable D hPe hs hX hf
  tfae_have 2 → 3 := by
    intro hsub X hX n hn
    exact Proof.psi_eq_snell_of_submartingale D hPe hX (fun f hf => hsub f hf X hX) n hn
  tfae_have 3 → 4 := by
    intro heq
    exact Proof.bellman_of_snell_equality D hPe heq
  tfae_have 4 → 1 := by
    intro hbell
    exact Proof.stable_of_bellman D hPe hℱ₀ hbell
  tfae_finish

end MultiperiodRisk.Bellman

end

open MultiperiodRisk.Bellman
open MeasureTheory

theorem solution {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ)
    (hℱ₀ : ∀ s, MeasurableSet[ℱ 0] s → P₀ s = 0 ∨ P₀ s = 1)
    (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty) :
    List.TFAE
      [ IsStable D,
        ∀ f ∈ D.set, ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
          Submartingale (fun n => PsiN D X (min n N)) ℱ (Q P₀ f),
        ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
          ∀ n ≤ N, PsiN D X n =ᵐ[P₀] PsiBar D X n,
        ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
          ∀ (σ τ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ)
            (hτ : IsBddStoppingTime ℱ N τ), (∀ ω, σ ω ≤ τ ω) →
            Psi D X σ hσ.1 =ᵐ[P₀] Psi D (bellmanProcess D X τ hτ.1) σ hσ.1 ] := by
  exact MultiperiodRisk.Bellman.solution P₀ ℱ N hℱ₀ D hPe

#print axioms MultiperiodRisk.Bellman.solution
#print axioms _root_.solution
