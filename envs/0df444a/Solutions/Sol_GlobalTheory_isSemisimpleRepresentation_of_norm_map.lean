-- Prove2me | solution 1 for GlobalTheory.isSemisimpleRepresentation_of_norm_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:11:29.990806+00:00
-- url     : https://prove2.me/submissions/1d52e43d-6716-4de6-9682-f16f66a9ad4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv

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
namespace GlobalTheory
theorem _root_.solution {G V : Type*} [Group G] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V] (ρ : Representation 𝕜 G V)
    (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖) : ρ.IsSemisimpleRepresentation := by
  refine ⟨fun U => ⟨orthogonalSubrepresentation hρu U, ?_⟩⟩
  have h := U.toSubmodule.isCompl_orthogonal
  constructor
  · rw [disjoint_iff]
    exact Subrepresentation.toSubmodule_injective h.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subrepresentation.toSubmodule_injective h.sup_eq_top
end GlobalTheory
