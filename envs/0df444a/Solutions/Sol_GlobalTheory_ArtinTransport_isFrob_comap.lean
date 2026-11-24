-- Prove2me | solution 1 for GlobalTheory.ArtinTransport.isFrob_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:59:00.809884+00:00
-- url     : https://prove2.me/submissions/dab950e8-c4d7-4929-a397-c7d900c1c6f8

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FrobeniusRestrictScalarsPowModInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ArtinTransportAlgClosureEquiv
import Theorems.Thm_GlobalTheory_ArtinTransport_valuation_le_one_comap
import Theorems.Thm_GlobalTheory_ArtinTransport_valuation_lt_one_comap
import Theorems.Thm_GlobalTheory_ArtinTransport_mem_Dec_comap

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
theorem _root_.solution (h : ∀ z, φ (σ z) = τ (φ z)) {q : ℕ} (hτ : IsFrob (F := E') A' q τ) :
    IsFrob (F := E) (A'.comap φ.toRingHom) q σ := by
  refine ⟨mem_Dec_comap A' φ h hτ.1, fun x hx => ?_⟩
  rw [valuation_lt_one_comap, map_sub, map_pow, h]
  exact hτ.2 _ ((valuation_le_one_comap A' φ x).mp hx)
end GlobalTheory.ArtinTransport
