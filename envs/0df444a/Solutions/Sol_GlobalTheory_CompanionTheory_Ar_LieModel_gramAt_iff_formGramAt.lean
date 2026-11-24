-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.LieModel.gramAt_iff_formGramAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:18:34.80408+00:00
-- url     : https://prove2.me/submissions/e7493ad3-89f3-4132-83fc-dff0c4b2dc46

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_hodgeInnerProduct_iff_hodgeForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
variable {L : LB G.left} {z : Spec (CommRingCat.of ℂ) ⟶ X} {v w : epsAt z ⟶ G} {c : ℂ}
namespace GlobalTheory.CompanionTheory.Ar
namespace LieModel
theorem _root_.solution (M : LieModel G ξ E) {r : ℕ} {b : Fin r → E} {Γ : Matrix (Fin r) (Fin r) ℂ} :
    M.GramAt L z b Γ ↔ M.FormGramAt L z b Γ.transpose :=
  ⟨fun ⟨v, hv, h⟩ => ⟨v, hv, fun p q => hodgeInnerProduct_iff_hodgeForm.1 (h q p)⟩,
    fun ⟨v, hv, h⟩ => ⟨v, hv, fun p q => hodgeInnerProduct_iff_hodgeForm.2 (h q p)⟩⟩
end LieModel
end GlobalTheory.CompanionTheory.Ar
