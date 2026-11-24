-- Prove2me | solution 1 for GlobalTheory.ArtinTransport.isPlaceOver_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:59:01.955817+00:00
-- url     : https://prove2.me/submissions/346c79ac-429c-4fd3-98f4-b2e9ebe562ea

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FrobeniusRestrictScalarsPowModInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ArtinTransportAlgClosureEquiv
import Theorems.Thm_GlobalTheory_ArtinTransport_valuation_lt_one_comap

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
theorem _root_.solution [NumberField E] [NumberField E'] (φ : Ω ≃+* Ω')
    (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x))
    {v : HeightOneSpectrum (𝓞 E)} {w : HeightOneSpectrum (𝓞 E')}
    (hwv : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = v.asIdeal) {A' : ValuationSubring Ω'}
    (hA : IsPlaceOver A' w) : IsPlaceOver (A'.comap φ.toRingHom) v := by
  intro x
  rw [valuation_lt_one_comap, hφ, ← hwv, Ideal.mem_comap, ← hA (algebraMap (𝓞 E) (𝓞 E') x)]
  rfl
end GlobalTheory.ArtinTransport
