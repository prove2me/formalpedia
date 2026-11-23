-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:12.662646+00:00
-- url     : https://prove2.me/submissions/21ed7cf0-b536-4456-8060-d58aa1d95cdd

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodInt_valued_algebraMap
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodInt_eventually_le_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodInt_eventually_eq_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodInt_repr_inclR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodInt
namespace GlobalTheory.CompanionTheory.SW.GoodInt
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ x : E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) x) k ∈ v.adicCompletionIntegers F) ∧ ∀ x : F, x ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (algebraMap F (Fv F v) x) = 1 := by
  intro F E _ _ _ _ _ σ _ d b
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · have h : ∀ k : Fin d, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        v.valuation F (b.repr x k) ≤ 1 := fun k => eventually_le_one _
    filter_upwards [Filter.eventually_all.mpr h] with v hv k
    rw [repr_inclR, HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]
    exact hv k
  · filter_upwards [eventually_eq_one x hx] with v hv
    rw [valued_algebraMap, hv]
end GlobalTheory.CompanionTheory.SW.GoodInt
