-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.LieModel.mem_eigSp_of_mem_htDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:32:44.182881+00:00
-- url     : https://prove2.me/submissions/a5c32950-ef23-45a8-802a-5ff45a3c76a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_MemEigSpOfMemHtDual
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_LieModel_mem_htDual_iff

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
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
open GlobalTheory.CompanionTheory.Ar.LieModel
variable (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
  (σ : O →+* Ω)
namespace GlobalTheory.CompanionTheory.Ar.LieModel
theorem _root_.solution {q : Cpt ξ} {e : E} (he : e ∈ M.htDual L n ρ σ q) : e ∈ eigSp ρ σ :=
  ((M.mem_htDual_iff L n ρ σ q e).1 he).1
end GlobalTheory.CompanionTheory.Ar.LieModel
