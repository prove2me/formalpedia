-- Prove2me | solution 1 for NoHair.israel_static_vacuum_regular_slice
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T07:13:44.203412+00:00
-- url     : https://prove2.me/submissions/0c1120c5-a2a0-43ce-9635-4707d1532c25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_regular_static_vacuum_euclidean_double
import Theorems.Thm_NoHair_schwarzschild_of_positive_harmonic_double

open NoHair Set InnerProductSpace
open scoped ContDiff Manifold

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0)
    (hstatic : IsStaticOn g φ (domainOfOuterCommunications g T E.region))
    (htime : ∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0)
    (hslice : HasRegularStaticVacuumSlice g φ (domainOfOuterCommunications g T E.region)) :
    ∃ m : ℝ, 0 < m ∧ IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m 0 0 := by
  obtain ⟨U, p, hc, hh, hn, hfar, hp, hlevel⟩ :=
    regular_static_vacuum_euclidean_double g φ _ hslice
  exact ⟨2 * ‖p‖, schwarzschild_of_positive_harmonic_double g F _ (fun x _ => hvac x)
    U hc hh hn hfar p hp hlevel⟩
