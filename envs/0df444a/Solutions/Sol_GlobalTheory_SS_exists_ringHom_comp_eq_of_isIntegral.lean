-- Prove2me | solution 1 for GlobalTheory.SS.exists_ringHom_comp_eq_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:11:50.616255+00:00
-- url     : https://prove2.me/submissions/a22e2a1e-6042-4a45-ac3f-372c300d6cd9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution {W k Ω : Type} [CommRing W] [IsLocalRing W] [Field k] [Field Ω]
    [IsAlgClosed Ω] (ρ : W →+* k) (hρ : RingHom.ker ρ = IsLocalRing.maximalIdeal W) (hi : ρ.IsIntegral)
    (φ : W →+* Ω) (hφ : RingHom.ker φ = IsLocalRing.maximalIdeal W) : ∃ ψ : k →+* Ω, ψ.comp ρ = φ := by
  let ρ' : IsLocalRing.ResidueField W →+* k :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) ρ fun a ha => (RingHom.mem_ker).1 (hρ ▸ ha)
  let φ' : IsLocalRing.ResidueField W →+* Ω :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) φ fun a ha => (RingHom.mem_ker).1 (hφ ▸ ha)
  letI := ρ'.toAlgebra
  letI := φ'.toAlgebra
  have hi' : ρ'.IsIntegral := RingHom.IsIntegral.tower_top (IsLocalRing.residue W) ρ' hi
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField W) k := ⟨hi'⟩
  let ψ : k →ₐ[IsLocalRing.ResidueField W] Ω := IsAlgClosed.lift
  refine ⟨ψ.toRingHom, RingHom.ext fun x => ?_⟩
  exact ψ.commutes (IsLocalRing.residue W x)
end GlobalTheory.SS
