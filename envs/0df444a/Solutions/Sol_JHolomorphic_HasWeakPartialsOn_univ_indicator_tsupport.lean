-- Prove2me | solution 1 for JHolomorphic.HasWeakPartialsOn.univ_indicator_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T17:31:14.806994+00:00
-- url     : https://prove2.me/submissions/fc8c416e-c2b5-4c12-9be4-035ebd0a85f0

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_local
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_ae_eq
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_congr_ae
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension



namespace JHolomorphic

open MeasureTheory Filter Metric ContinuousLinearMap
open scoped ContDiff Convolution ENNReal

/-- A map with compact support `K ⊆ U` whose weak partials on the open set `U` lie in `L^p(U)`
(`1 ≤ p`) has, on all of `ℂ`, the weak partials obtained by restricting them to `K` and extending
by zero; moreover the given partials vanish almost everywhere on `U \ K`. -/
theorem HasWeakPartialsOn.univ_indicator_tsupport_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {p : ℝ≥0∞}
    (hp : 1 ≤ p) {ξ ξs ξt : ℂ → E} (hξ : Continuous ξ) (hc : HasCompactSupport ξ)
    (hsub : tsupport ξ ⊆ U) (h : HasWeakPartialsOn U ξ ξs ξt)
    (hs : MemLp ξs p (volume.restrict U)) (ht : MemLp ξt p (volume.restrict U)) :
    HasWeakPartialsOn Set.univ ξ ((tsupport ξ).indicator ξs) ((tsupport ξ).indicator ξt) ∧
      ∀ᵐ z ∂(volume.restrict U),
        ξs z = (tsupport ξ).indicator ξs z ∧ ξt z = (tsupport ξ).indicator ξt z := by
  set K := tsupport ξ with hK
  have hKc : IsClosed K := isClosed_tsupport ξ
  have hKo : IsOpen Kᶜ := hKc.isOpen_compl
  -- `L^p` on a compact set gives integrability there
  have hint : ∀ {f : ℂ → E} {K' : Set ℂ}, IsCompact K' → MemLp f p (volume.restrict K') →
      IntegrableOn f K' := by
    intro f K' hK' hf
    haveI : IsFiniteMeasure (volume.restrict K') :=
      isFiniteMeasure_restrict.2 hK'.measure_lt_top.ne
    exact hf.integrable hp
  have hmonoU : ∀ {f : ℂ → E} {K' : Set ℂ}, K' ⊆ U → MemLp f p (volume.restrict U) →
      MemLp f p (volume.restrict K') := fun hK'U hf => hf.mono_measure (Measure.restrict_mono hK'U le_rfl)
  -- off the support, `ξ` has zero weak partials
  have hzero : HasWeakPartialsOn Kᶜ ξ 0 0 := by
    intro φ _ _ hφK
    have hvan : ∀ v : ℂ, (fun z => fderiv ℝ φ z v • ξ z) = 0 := by
      intro v; funext z
      by_cases hz : z ∈ K
      · have hz' : z ∉ tsupport φ := fun hz' => hφK hz' hz
        have : fderiv ℝ φ z = 0 := by
          by_contra hne
          exact hz' (support_fderiv_subset ℝ hne)
        simp [this]
      · simp [image_eq_zero_of_notMem_tsupport hz]
    refine ⟨?_, ?_⟩
    · rw [hvan 1]; simp
    · rw [hvan Complex.I]; simp
  -- glue
  obtain ⟨gs, gt, hW, hloc⟩ := HasWeakPartialsOn.of_local isOpen_univ hp
    (fun K' _ hK' => hξ.continuousOn.integrableOn_compact hK')
    (fun z _ => by
      by_cases hz : z ∈ U
      · exact ⟨U, hU, hz, Set.subset_univ _, ξs, ξt, h, hs, ht⟩
      · exact ⟨Kᶜ, hKo, fun hzK => hz (hsub hzK), Set.subset_univ _, 0, 0, hzero,
          MemLp.zero, MemLp.zero⟩)
  have hWon : ∀ V : Set ℂ, HasWeakPartialsOn V ξ gs gt := fun V φ h1 h2 _ =>
    hW φ h1 h2 (Set.subset_univ _)
  have hsU := HasWeakPartialsOn.ae_eq hU (hWon U) h (fun K' hK'U hK' =>
    ⟨hint hK' (hloc K' (Set.subset_univ _) hK').1, hint hK' (hloc K' (Set.subset_univ _) hK').2,
      hint hK' (hmonoU hK'U hs), hint hK' (hmonoU hK'U ht)⟩)
  have hsK := HasWeakPartialsOn.ae_eq hKo (hWon Kᶜ) hzero (fun K' _ hK' =>
    ⟨hint hK' (hloc K' (Set.subset_univ _) hK').1, hint hK' (hloc K' (Set.subset_univ _) hK').2,
      integrableOn_zero, integrableOn_zero⟩)
  have hsU' := (ae_restrict_iff' hU.measurableSet).1 hsU
  have hsK' := (ae_restrict_iff' hKo.measurableSet).1 hsK
  have hind : ∀ᵐ z ∂(volume : Measure ℂ), gs z = K.indicator ξs z ∧ gt z = K.indicator ξt z := by
    filter_upwards [hsU', hsK'] with z h1 h2
    by_cases hz : z ∈ K
    · simp only [Set.indicator_of_mem hz]
      exact h1 (hsub hz)
    · simp only [Set.indicator_of_notMem hz]
      exact h2 hz
  refine ⟨?_, ?_⟩
  · refine HasWeakPartialsOn.congr_ae isOpen_univ hW (Eventually.of_forall fun _ => rfl) ?_ ?_
    · rw [Measure.restrict_univ]; filter_upwards [hind] with z hz using hz.1
    · rw [Measure.restrict_univ]; filter_upwards [hind] with z hz using hz.2
  · filter_upwards [hsU, ae_restrict_of_ae hind] with z h1 h2
    exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩

end JHolomorphic

open JHolomorphic JHolomorphic.HasWeakPartialsOn

open MeasureTheory Filter
open scoped ContDiff ENNReal

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {p : ℝ≥0∞}
    (hp : 1 ≤ p) {ξ ξs ξt : ℂ → E} (hξ : Continuous ξ) (hc : HasCompactSupport ξ)
    (hsub : tsupport ξ ⊆ U) (h : HasWeakPartialsOn U ξ ξs ξt)
    (hs : MemLp ξs p (volume.restrict U)) (ht : MemLp ξt p (volume.restrict U)) :
    HasWeakPartialsOn Set.univ ξ ((tsupport ξ).indicator ξs) ((tsupport ξ).indicator ξt) ∧
      ∀ᵐ z ∂(volume.restrict U),
        ξs z = (tsupport ξ).indicator ξs z ∧ ξt z = (tsupport ξ).indicator ξt z :=
  JHolomorphic.HasWeakPartialsOn.univ_indicator_tsupport_aux hU hp hξ hc hsub h hs ht
