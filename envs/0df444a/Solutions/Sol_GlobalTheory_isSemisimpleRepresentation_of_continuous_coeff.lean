-- Prove2me | solution 1 for GlobalTheory.isSemisimpleRepresentation_of_continuous_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:25:42.901484+00:00
-- url     : https://prove2.me/submissions/8e5fbd58-1e79-4ca0-8930-8908135164ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Theorems.Thm_GlobalTheory_isSemisimpleRepresentation_of_invariant_core
import Theorems.Thm_GlobalTheory_exists_invariant_core_of_continuous_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace ComplexConjugate
open GlobalTheory
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
namespace GlobalTheory
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V] (ρ : Representation 𝕜 K V)
    (hρc : ∀ (l : Module.Dual 𝕜 V) (v : V), Continuous fun k => l (ρ k v)) :
    ρ.IsSemisimpleRepresentation := by
  obtain ⟨c, hc⟩ := exists_invariant_core_of_continuous_coeff ρ hρc
  exact isSemisimpleRepresentation_of_invariant_core ρ c hc
end GlobalTheory
