-- Prove2me | solution 1 for GlobalTheory.SmGL.IndDual.dual_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:27:47.693322+00:00
-- url     : https://prove2.me/submissions/9e6a761b-6233-4756-b506-9e288df911a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviIntegralFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralIntegralGLMulRightComplexProductSigma
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_exists_fixed_map_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IndDual
variable {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W'] {P : Subgroup G}
namespace GlobalTheory.SmGL.IndDual
theorem _root_.solution {σ : Representation ℂ G W} (hσ : IsSmooth σ) {H : Subgroup G} (hH : IsCompact (H : Set G))
    {l l' : Module.Dual ℂ W} (hl : ∀ h ∈ H, ∀ w, l (σ h w) = l w) (hl' : ∀ h ∈ H, ∀ w, l' (σ h w) = l' w)
    (h : ∀ w ∈ fixed σ H, l w = l' w) : l = l' := by
  ext u
  obtain ⟨v, hv, e⟩ := IwahoriOnto.exists_fixed_map_eq hσ hH (l - l') u fun g hg => by
    simp [hl g hg, hl' g hg]
  simp only [LinearMap.sub_apply, h v hv, sub_self] at e
  exact sub_eq_zero.1 e.symm
end GlobalTheory.SmGL.IndDual
