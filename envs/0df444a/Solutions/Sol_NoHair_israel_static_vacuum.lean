-- Prove2me | solution 1 for NoHair.israel_static_vacuum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:35:28.30994+00:00
-- url     : https://prove2.me/submissions/7b892105-61e8-4bc2-9cb7-0e2a2091df13
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_israel_static_electrovac
import Theorems.Thm_NoHair_reissnerNordstrom_charge_eq_zero

open scoped ContDiff Manifold
open NoHair

theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0)
    (hstatic : IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ m : ℝ, 0 < m ∧
      IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m 0 0 := by
  obtain ⟨m, e, hp, hRN⟩ := israel_static_electrovac g F T φ E h hstatic
  obtain ⟨β, Ψ, hΨ, hmatch⟩ := hRN
  have he : e = 0 := by
    apply reissnerNordstrom_charge_eq_zero m e β hp
    intro y hy
    rw [← (hmatch y hy).2]
    ext i j
    simp [pullbackCoeffs, hvac]
  subst e
  exact ⟨m, hp.1, β, Ψ, hΨ, hmatch⟩
