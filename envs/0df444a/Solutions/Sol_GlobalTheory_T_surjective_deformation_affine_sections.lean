-- Prove2me | solution 1 for GlobalTheory.T.surjective_deformation_affine_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:11:44.2138+00:00
-- url     : https://prove2.me/submissions/e4448a82-55be-4ad7-864e-105f8944a85a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveDeformationAffineSections
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveDeformationAffineSectionsStatement
import Theorems.Thm_P2M_GlobalTheory_AbCoh_pre__surjective_and_ker_5a1e5300be4a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) [IsAffineHom φ] [IsAffineHom φ₀], SmallExt t σ σ₀ → Flat s → ∀ U : AffOp X, Function.Surjective (preα φ s s' U) ∧ (∀ b, preα φ s s' U b = 0 ↔ ∃ c, b = t • c) ∧ Function.Surjective (preα φ₀ s s₀ U) ∧ ∀ b : (OAff s).obj U, preα φ₀ s s₀ U b = 0 ↔ t • b = 0 := by
  first | exact @GlobalTheory.AbCoh.preα_surjective_and_ker | exact GlobalTheory.AbCoh.preα_surjective_and_ker | (intros; apply GlobalTheory.AbCoh.preα_surjective_and_ker <;> assumption)
end _root_.GlobalTheory.T
