-- Prove2me | solution 1 for MultiperiodRisk.Bellman.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:52:05.353518+00:00
-- url     : https://prove2.me/submissions/e5258489-7203-41dc-8b2c-1677cffd3f66

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_TestSet

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

theorem solution {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
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
