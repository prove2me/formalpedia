-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.LieModel.mem_eigSp_of_mem_htW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:32:48.381763+00:00
-- url     : https://prove2.me/submissions/f25a588c-aa02-4ec7-a4ee-0fcb2161ef6c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_MemEigSpOfMemHtDual

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
theorem _root_.solution (𝔡 : Ideal O) {q : Cpt ξ} {e : E} (he : e ∈ M.htW L n ρ σ 𝔡 q) :
    e ∈ eigSp ρ σ := by
  induction he using Submodule.span_induction with
  | mem x hx => exact hx.1
  | zero => exact (eigSp ρ σ).zero_mem
  | add x y _ _ hx hy => exact (eigSp ρ σ).add_mem hx hy
  | smul c x _ hx => exact (eigSp ρ σ).smul_mem (c : Ω) hx
end GlobalTheory.CompanionTheory.Ar.LieModel
