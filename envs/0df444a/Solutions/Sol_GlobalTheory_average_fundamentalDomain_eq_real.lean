-- Prove2me | solution 1 for GlobalTheory.average_fundamentalDomain_eq_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:45:27.609391+00:00
-- url     : https://prove2.me/submissions/be6ccdd4-2a7c-41ad-9cb5-60daa9ef1583

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Theorems.Thm_GlobalTheory_setIntegral_fundamentalDomain_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_tile_average


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MeasureTheory
namespace GlobalTheory
theorem _root_.solution {V κ κ' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [Fintype κ] [Fintype κ'] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (b : Module.Basis κ ℝ V) (b' : Module.Basis κ' ℝ V)
    (f : V → ℝ) (hf : Continuous f)
    (hb : ∀ γ ∈ Submodule.span ℤ (Set.range b), ∀ v, f (v + γ) = f v)
    (hle : Submodule.span ℤ (Set.range b') ≤ Submodule.span ℤ (Set.range b)) (a : V) :
    ⨍ v in ZSpan.fundamentalDomain b', f (v + a) ∂μ =
      ⨍ v in ZSpan.fundamentalDomain b, f v ∂μ := by
  have h1 : ⨍ v in ZSpan.fundamentalDomain b', f (v + a) ∂μ =
      ⨍ v in ZSpan.fundamentalDomain b', f v ∂μ := by
    rw [setAverage_eq, setAverage_eq,
      setIntegral_fundamentalDomain_add_right μ b' f (fun γ hγ => hb γ (hle hγ)) a]
  rw [h1, ← ZSpan.fundamentalDomain_reindex b' (b'.indexEquiv b)]
  refine ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.tile_average μ _ b ?_ f hf hb
  rwa [Module.Basis.range_reindex]
end GlobalTheory
