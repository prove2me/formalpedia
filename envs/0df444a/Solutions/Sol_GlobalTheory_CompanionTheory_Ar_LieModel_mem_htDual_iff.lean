-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.LieModel.mem_htDual_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:24.767597+00:00
-- url     : https://prove2.me/submissions/51e75faa-a1f3-4914-845c-3b8219eaadb3

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
theorem _root_.solution (q : Cpt ξ) (e : E) :
    e ∈ M.htDual L n ρ σ q ↔ e ∈ eigSp ρ σ ∧ ∀ w ∈ M.htOm L n q, w e ∈ regAt ξ q := by
  constructor
  · intro he
    induction he using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨(eigSp ρ σ).zero_mem, fun w _ => by simpa using (regAt ξ q).zero_mem⟩
    | add x y _ _ hx hy =>
      exact ⟨(eigSp ρ σ).add_mem hx.1 hy.1, fun w hw => by
        simpa using (regAt ξ q).add_mem (hx.2 w hw) (hy.2 w hw)⟩
    | smul c x _ hx =>
      refine ⟨(eigSp ρ σ).smul_mem (c : Ω) hx.1, fun w hw => ?_⟩
      have : w (c • x) = (c : Ω) * w x := by
        show w ((c : Ω) • x) = _
        rw [map_smul, smul_eq_mul]
      rw [this]
      exact (regAt ξ q).mul_mem c.2 (hx.2 w hw)
  · exact fun h => Submodule.subset_span h
end GlobalTheory.CompanionTheory.Ar.LieModel
