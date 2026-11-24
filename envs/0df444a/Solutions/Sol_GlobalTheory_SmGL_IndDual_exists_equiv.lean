-- Prove2me | solution 1 for GlobalTheory.SmGL.IndDual.exists_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:28:46.714153+00:00
-- url     : https://prove2.me/submissions/5d5421ca-9106-4cc2-b61b-d1f0bcc85eb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviIntegralFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralIntegralGLMulRightComplexProductSigma
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_smoothRep


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
variable [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] {K : Subgroup G}
  (hK : IsCompact (K : Set G)) (σ : Representation ℂ P W) (τ : Representation ℂ P W')
  (B : W' →ₗ[ℂ] Module.Dual ℂ W)
namespace GlobalTheory.SmGL.IndDual
theorem _root_.solution
    (hinv : ∀ g f' f, pair μ hK σ τ B (smInd P τ g f') (smInd P σ g f) = pair μ hK σ τ B f' f)
    (hi : Function.Injective (pair μ hK σ τ B))
    (hs : ∀ l ∈ smoothPart (smInd P σ).dual, l ∈ LinearMap.range (pair μ hK σ τ B)) :
    ∃ Φ : (smInd P τ).Equiv (contra (smInd P σ)), ∀ f' f,
      (Φ f' : Module.Dual ℂ (smoothPart (ind P σ))) f = ∫ x in (K : Set G), B (f'.1.1 x) (f.1.1 x) ∂μ := by
  have hact : ∀ g f', pair μ hK σ τ B (smInd P τ g f') =
      (smInd P σ).dual g (pair μ hK σ τ B f') := fun g f' => LinearMap.ext fun f => by
    show _ = pair μ hK σ τ B f' (smInd P σ g⁻¹ f)
    rw [← hinv g f', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hsm : ∀ f', pair μ hK σ τ B f' ∈ smoothPart (smInd P σ).dual := fun f' =>
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      (IsOpen.mem_nhds (isSmooth_smoothRep _ f') (by
        rw [Set.mem_ofPred_eq, map_one, Module.End.one_apply])) fun g hg => by
        have hg' : smInd P τ g f' = f' := hg
        rw [Set.mem_ofPred_eq, ← hact, hg'])
  refine ⟨.mk (LinearEquiv.ofBijective ((pair μ hK σ τ B).codRestrict _ hsm)
    ⟨fun a b h => hi (congrArg Subtype.val h), fun l => ?_⟩) fun g => ?_, fun f' f => rfl⟩
  · obtain ⟨f', hf'⟩ := hs l.1 l.2
    exact ⟨f', Subtype.ext hf'⟩
  · exact LinearMap.ext fun f' => Subtype.ext (hact g f')
end GlobalTheory.SmGL.IndDual
