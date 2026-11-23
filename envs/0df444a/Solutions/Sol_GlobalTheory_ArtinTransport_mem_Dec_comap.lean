-- Prove2me | solution 1 for GlobalTheory.ArtinTransport.mem_Dec_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:02.540722+00:00
-- url     : https://prove2.me/submissions/c6a1a3b1-4c53-4c3a-af5c-75de27bcc5b6

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
variable {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω']
variable [NumberField E] [NumberField E'] (A' : ValuationSubring Ω') (φ : Ω ≃+* Ω') {σ : G E Ω} {τ : G E' Ω'}
namespace GlobalTheory.ArtinTransport
theorem _root_.solution (h : ∀ z, φ (σ z) = τ (φ z)) (hτ : τ ∈ Dec (F := E') A') :
    σ ∈ Dec (F := E) (A'.comap φ.toRingHom) := by
  have hx : ∀ x, σ x ∈ A'.comap φ.toRingHom ↔ x ∈ A'.comap φ.toRingHom := by
    intro x
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap]
    show φ (σ x) ∈ A' ↔ φ x ∈ A'
    rw [h]
    exact apply_mem_iff_of_mem_Dec hτ (φ x)
  show σ • A'.comap φ.toRingHom = A'.comap φ.toRingHom
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hx, mul_inv_apply]
end GlobalTheory.ArtinTransport
