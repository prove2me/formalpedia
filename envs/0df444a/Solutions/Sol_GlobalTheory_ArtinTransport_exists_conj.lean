-- Prove2me | solution 1 for GlobalTheory.ArtinTransport.exists_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:58:59.870822+00:00
-- url     : https://prove2.me/submissions/e36d94a8-2706-466e-9749-62eccd7b1f19

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FrobeniusRestrictScalarsPowModInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ArtinTransportAlgClosureEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
noncomputable section
open GlobalTheory GlobalTheory.ArtinTransport
open scoped Pointwise
variable {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω'] [Algebra E E']
namespace GlobalTheory.ArtinTransport
theorem _root_.solution (φ : Ω ≃+* Ω') (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x))
    (τ : G E' Ω') : ∃ σ : G E Ω, ∀ z, φ (σ z) = τ (φ z) := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (φ.trans τ.toRingEquiv).trans φ.symm) fun x => ?_, fun z => ?_⟩
  · show φ.symm (τ (φ (algebraMap E Ω x))) = algebraMap E Ω x
    rw [hφ, AlgEquiv.commutes, ← hφ, φ.symm_apply_apply]
  · show φ (φ.symm (τ (φ z))) = τ (φ z)
    exact φ.apply_symm_apply _
end GlobalTheory.ArtinTransport
