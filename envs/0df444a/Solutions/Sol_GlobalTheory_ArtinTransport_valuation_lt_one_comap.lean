-- Prove2me | solution 1 for GlobalTheory.ArtinTransport.valuation_lt_one_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:02.416366+00:00
-- url     : https://prove2.me/submissions/3f5c553e-9d6d-4884-861a-9cf4dc948c26

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
namespace GlobalTheory.ArtinTransport
theorem _root_.solution (A' : ValuationSubring Ω') (φ : Ω ≃+* Ω') (y : Ω) :
    (A'.comap φ.toRingHom).valuation y < 1 ↔ A'.valuation (φ y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    map_eq_zero_iff _ φ.injective]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀]
end GlobalTheory.ArtinTransport
