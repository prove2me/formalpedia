-- Prove2me | solution 1 for KStar.Choice.adeleMap_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:50:24.96406+00:00
-- url     : https://prove2.me/submissions/2f6ce421-7511-4849-87fe-e73cdd502e0c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_HeckeCharacterChoice_TendstoUnderCofinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open KStar KStar.Choice
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (K L)
namespace KStar.Choice
theorem _root_.solution :
    Continuous (adeleMap K L) ∧ Function.Injective (adeleMap K L) ∧
      Continuous (infAdeleMap K L) ∧
      (∀ x : K, adeleMap K L (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧
      ∀ x : K, infAdeleMap K L (algebraMap K _ x) = algebraMap L _ (algebraMap K L x) := by
  have hinf : Continuous (infAdeleMap K L) :=
    continuous_pi fun w => LiesOver.continuous_completionMap.comp (continuous_apply _)
  have hfin : Continuous (finAdeleMap K L) :=
    RestrictedProduct.mapAlong_continuous
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (A₁ := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      (A₂ := fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L)))
      (fun w => w.under (𝓞 K)) (tendsto_under_cofinite K L)
      (fun w => complMap (w.under (𝓞 K)) w)
      (Filter.Eventually.of_forall fun w x (hx : x ∈ (w.under (𝓞 K)).adicCompletionIntegers K) =>
        (complMap_mem _ w hx : _ ∈ w.adicCompletionIntegers L))
      (fun w => continuous_complMap _ w)
  have iinf : Function.Injective (infAdeleMap K L) := by
    intro x y h
    funext v
    obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (K := L) v
    exact (LiesOver.completionMap (v := w.comap (algebraMap K L)) (w := w)).injective
      (congrFun h w)
  have ifin : Function.Injective (finAdeleMap K L) := by
    intro x y h
    refine FiniteAdeleRing.ext _ fun v => ?_
    obtain ⟨w, rfl⟩ : ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) = v := by
      have := v.isMaximal
      obtain ⟨Q, hQ, hQv⟩ :=
        Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
      exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
        HeightOneSpectrum.ext hQv.over.symm⟩
    exact (complMap (w.under (𝓞 K)) w).injective (DFunLike.congr_fun h w)
  have ainf : ∀ x : K,
      infAdeleMap K L (algebraMap K _ x) = algebraMap L _ (algebraMap K L x) := by
    intro x
    funext w
    exact (LiesOver.completionMap_coe (v := w.comap (algebraMap K L)) (w := w)
      (WithAbs.toAbs _ x)).trans rfl
  refine ⟨hinf.prodMap hfin, iinf.prodMap ifin, hinf, fun x => Prod.ext (ainf x) ?_, ainf⟩
  exact FiniteAdeleRing.ext _ fun w => complMap_algebraMap _ w x
end KStar.Choice
