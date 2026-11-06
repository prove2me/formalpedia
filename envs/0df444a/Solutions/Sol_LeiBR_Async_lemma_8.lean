-- Prove2me | solution 1 for LeiBR.Async.lemma_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T10:53:40.716623+00:00
-- url     : https://prove2.me/submissions/71a2a8c8-d058-48ff-9b50-06613f934b13
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model
import Definitions.Def_LeiBR_Async_Algorithm
import Theorems.Thm_LeiBR_Async_lemma_8_upto

open MeasureTheory

open LeiBR.Async in
theorem solution {Ω : Type*} (Fk : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N d : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i)) (f : Fin N → LeiBR.Sync.Profile n → ℝ)
    (hA1 : Assumption1ab X f) (μ : ℝ) (hμ : 0 < μ) (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n)
    (hxhat : LeiBR.Sync.IsProxBR X f μ xhat) (M : Fin N → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i)
    (hgψ : ∀ i, Measurable (Function.uncurry (gψ i)))
    (proj : ∀ i, LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i)
    (hproj : ∀ i, SpectralProjGrad.Shared.IsProjOnto (X i) (proj i))
    (i : Fin N) (hFk : Fk ≤ mΩ) (G : ℕ → MeasurableSpace Ω)
    (hG : ∀ t, G t ≤ mΩ) (hFG : Fk ≤ G 1) (hGmono : ∀ t, G t ≤ G (t + 1))
    (y : Ω → LeiBR.Sync.Profile n) (hy : Measurable[Fk] y) (hyX : ∀ ω, y ω ∈ profileSet X)
    (ξ : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hξ : ∀ t, Measurable[G (t + 1)] (ξ t)) (j : ℕ)
    (horacle : IsSAOracle P f gψ proj μ M i y ξ G j) :
    ∀ t, 1 ≤ t → t ≤ j →
      P[fun ω => ‖saPath proj gψ μ i (y ω) (fun s => ξ s ω) t - xhat (y ω) i‖ ^ 2 | Fk]
        ≤ᵐ[P] fun _ => LeiBR.Sync.Qconst X M μ i / ((t : ℝ) + 1) :=
  lemma_8_upto Fk P X f hA1 μ hμ xhat hxhat M gψ hgψ proj hproj i j hFk G (fun t _ => hG t) hFG
    hGmono y hy hyX ξ (fun t _ => hξ t) horacle
