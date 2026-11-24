-- Prove2me | solution 1 for GlobalTheory.SmGL.IndDual.smInd_bump
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:43:35.236339+00:00
-- url     : https://prove2.me/submissions/819c9dfc-0379-481b-b2dd-ad0c38eb87e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviIntegralFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralIntegralGLMulRightComplexProductSigma
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Theorems.Thm_GlobalTheory_SmGL_IndDual_bump_mul
import Theorems.Thm_GlobalTheory_SmGL_IndDual_bump_zero
import Theorems.Thm_GlobalTheory_SmGL_IndDual_smInd_apply

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
theorem _root_.solution (σ : Representation ℂ P W) {J : Subgroup G} (hJ : IsOpen (J : Set G)) (q : P)
    (hq : ∀ j ∈ J, (q : G) * j * (q : G)⁻¹ ∈ J) (hq' : ∀ j ∈ J, (q : G)⁻¹ * j * q ∈ J)
    (w v : fixed σ (J.subgroupOf P)) (hv : v.1 = σ q w) : smInd P σ q (bump σ hJ w) = bump σ hJ v := by
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  rw [smInd_apply]
  rcases cell_cases (P := P) J g with h | ⟨p, j, hj, rfl⟩
  · rw [bump_zero _ _ _ h, bump_zero]
    rintro ⟨p, hp⟩
    exact h ⟨p * q⁻¹, by simpa [mul_assoc] using hq _ hp⟩
  · have : (p : G) * j * q = (p * q : P) * ((q : G)⁻¹ * j * q) := by simp [mul_assoc]
    rw [this, bump_mul _ _ _ _ (hq' j hj), bump_mul _ _ _ _ hj, hv, map_mul, Module.End.mul_apply]
end GlobalTheory.SmGL.IndDual
