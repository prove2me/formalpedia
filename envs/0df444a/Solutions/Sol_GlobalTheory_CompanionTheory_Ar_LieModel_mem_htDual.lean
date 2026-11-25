-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.LieModel.mem_htDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:40:44.02748+00:00
-- url     : https://prove2.me/submissions/edb5e6da-cbc8-4a71-ac98-8e5621f6d644

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
theorem _root_.solution (q : Cpt ξ) (e : eigSp ρ σ) :
    (e : E) ∈ M.htDual L n ρ σ q ↔ ∀ u ∈ M.htOmEig L n ρ σ q, u e ∈ regAt ξ q := by
  rw [mem_htDual_iff]
  constructor
  · rintro ⟨-, h⟩ u hu
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hu
    exact h w hw
  · intro h
    refine ⟨e.2, fun w hw => ?_⟩
    exact h _ (Submodule.mem_map.2 ⟨w, hw, rfl⟩)
end GlobalTheory.CompanionTheory.Ar.LieModel
