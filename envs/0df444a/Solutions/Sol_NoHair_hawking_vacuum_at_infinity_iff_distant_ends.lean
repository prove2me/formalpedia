-- Prove2me | solution 1 for NoHair.hawking_vacuum_at_infinity_iff_distant_ends
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:29:07.65779+00:00
-- url     : https://prove2.me/submissions/90037b12-ea27-48c8-931f-e3a41dc85e66

import Theorems.Thm_NoHair_asymptoticallyFlatEnd_chronology_stabilizes
import Theorems.Thm_NoHair_asymptoticallyFlatEnd_timelike_restriction
import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold BigOperators

theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ,E4) ∞ M] [IsManifold 𝓘(ℝ,E4) ω M]
    (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (hl : IsLorentzian g) (hsm : IsSmoothBilinField g) (hsF : IsSmoothBilinField F)
    (h2 : IsTwoForm F) (hT : IsTimeOrientation g T) (hem : IsElectrovac g F)
    (hφ : IsSymmetryFlow g F φ) (hvac : ∀ x, F x = 0) (han : IsAnalyticBilinField g) :
    (∀ E : AsymptoticallyFlatEnd g F φ,
      let A := fun R : ℝ => E.ψ '' exteriorRegion R
      let D := domainOfOuterCommunicationsAtInfinity g T A E.R
      let H := futureEventHorizonAtInfinity g T A E.R
      IsGloballyHyperbolicOn g T D → (chronoPastAtInfinity g T A E.R)ᶜ.Nonempty →
      IsConnected H → IsNondegenerateHorizon g F H D →
      ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧ IsKerrNewmanDOC g F D m a 0) ↔
    (∀ E : AsymptoticallyFlatEnd g F φ, 16 * |E.C| ≤ E.R → IsStationaryBlackHole g F T φ E →
      IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
        (domainOfOuterCommunications g T E.region) →
      ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧
        IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m a 0) := by
  constructor
  · intro classify E hR bh hn
    obtain ⟨hp,_,hd,hh⟩ := asymptoticallyFlatEnd_chronology_stabilizes E hl hsm T hT E.R le_rfl hR
    let A := fun R : ℝ => E.ψ '' exteriorRegion R
    change chronoPastAtInfinity g T A E.R = chronoPastSet g T E.region at hp
    change domainOfOuterCommunicationsAtInfinity g T A E.R = domainOfOuterCommunications g T E.region at hd
    change futureEventHorizonAtInfinity g T A E.R = futureEventHorizon g T E.region at hh
    have hg' : IsGloballyHyperbolicOn g T (domainOfOuterCommunicationsAtInfinity g T A E.R) := hd.symm ▸ bh.globallyHyperbolic
    have hb' : (chronoPastAtInfinity g T A E.R)ᶜ.Nonempty := by rw [hp]; exact bh.blackHole_nonempty
    have hc' : IsConnected (futureEventHorizonAtInfinity g T A E.R) := hh.symm ▸ bh.horizon_connected
    have hn' : IsNondegenerateHorizon g F (futureEventHorizonAtInfinity g T A E.R)
        (domainOfOuterCommunicationsAtInfinity g T A E.R) := by rwa [hh,hd]
    obtain ⟨m,a,hm,hiso⟩ := classify E hg' hb' hc' hn'
    exact ⟨m,a,hm,hd ▸ hiso⟩
  · intro classify E
    let A := fun R : ℝ => E.ψ '' exteriorRegion R
    change IsGloballyHyperbolicOn g T (domainOfOuterCommunicationsAtInfinity g T A E.R) →
      (chronoPastAtInfinity g T A E.R)ᶜ.Nonempty → IsConnected (futureEventHorizonAtInfinity g T A E.R) →
      IsNondegenerateHorizon g F (futureEventHorizonAtInfinity g T A E.R) (domainOfOuterCommunicationsAtInfinity g T A E.R) →
      ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧ IsKerrNewmanDOC g F (domainOfOuterCommunicationsAtInfinity g T A E.R) m a 0
    intro hglob hblack hconn hn
    let R₀ := max E.R (16 * |E.C|)
    have hR : E.R ≤ R₀ := le_max_left _ _
    have hC : 16 * |E.C| ≤ R₀ := le_max_right _ _
    have hc : E.C ≤ R₀ := by linarith [le_abs_self E.C,abs_nonneg E.C]
    obtain ⟨E',hr,_,heC,him,_⟩ := asymptoticallyFlatEnd_timelike_restriction g F φ E R₀ hR hc
    have far : 16 * |E'.C| ≤ E'.R := by rwa [heC,hr]
    obtain ⟨hp,_,hd,hh⟩ := asymptoticallyFlatEnd_chronology_stabilizes E hl hsm T hT R₀ hR hC
    change chronoPastAtInfinity g T A E.R = chronoPastSet g T (A R₀) at hp
    change domainOfOuterCommunicationsAtInfinity g T A E.R = domainOfOuterCommunications g T (A R₀) at hd
    change futureEventHorizonAtInfinity g T A E.R = futureEventHorizon g T (A R₀) at hh
    change E'.region = A R₀ at him
    rw [←him] at hp hd hh
    have bh : IsStationaryBlackHole g F T φ E' :=
      { lorentzian := hl, smooth_metric := hsm, smooth_field := hsF, twoForm := h2,
        timeOrientation := hT, electrovac := hem, stationary := hφ,
        globallyHyperbolic := hd ▸ hglob,
        blackHole_nonempty := by change (chronoPastSet g T E'.region)ᶜ.Nonempty; rwa [←hp],
        horizon_connected := hh ▸ hconn }
    have hn' : IsNondegenerateHorizon g F (futureEventHorizon g T E'.region)
        (domainOfOuterCommunications g T E'.region) := by rwa [←hh,←hd]
    obtain ⟨m,a,hm,hiso⟩ := classify E' far bh hn'
    exact ⟨m,a,hm,hd.symm ▸ hiso⟩
