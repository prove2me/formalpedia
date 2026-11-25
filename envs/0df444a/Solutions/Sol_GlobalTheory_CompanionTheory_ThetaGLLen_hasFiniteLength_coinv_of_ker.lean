-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:46:25.9666+00:00
-- url     : https://prove2.me/submissions/1513edbd-5a23-4567-9c29-b21e1071add0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviIntegralFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoinvariantsFiniteOfSmoothLevi
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GroundTheory_Automorphic_hasFiniteLength_of_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen
namespace GlobalTheory.CompanionTheory.ThetaGLLen
theorem _root_.solution {Γ G V U : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup U] [Module ℂ U] (τ : Representation ℂ (Γ × G) V) (ψ : Γ →* ℂˣ)
    (π : Representation ℂ G U) (Φ : V →ₗ[ℂ] U) (hint : ∀ g v, Φ (τ (1, g) v) = π g (Φ v))
    (hker : LinearMap.ker Φ = twRel (τ.comp (MonoidHom.inl Γ G)) ψ) (hπ : HasFiniteLength π) :
    HasFiniteLength (coinv τ ψ) := by
  have hle : twRel (τ.comp (MonoidHom.inl Γ G)) ψ ≤ LinearMap.ker Φ := hker.ge
  have hinj : Function.Injective ((twRel (τ.comp (MonoidHom.inl Γ G)) ψ).liftQ Φ hle) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    rw [← hker]
    exact hx
  let Ψ : (coinv τ ψ).IntertwiningMap π :=
    { toLinearMap := (twRel (τ.comp (MonoidHom.inl Γ G)) ψ).liftQ Φ hle
      isIntertwining' := fun g => LinearMap.ext fun x => by
        obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        exact hint g f }
  exact GroundTheory.Automorphic.hasFiniteLength_of_injective Ψ hinj hπ
end GlobalTheory.CompanionTheory.ThetaGLLen
