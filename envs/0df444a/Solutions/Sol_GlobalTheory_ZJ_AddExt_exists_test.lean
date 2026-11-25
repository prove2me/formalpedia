-- Prove2me | solution 1 for GlobalTheory.ZJ.AddExt.exists_test
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:30:25.226547+00:00
-- url     : https://prove2.me/submissions/202f7e31-952d-41a0-b59c-24d0244e129e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddExtension
import Theorems.Thm_GlobalTheory_ZJ_AddExt_eq_mul_of_generic
import Theorems.Thm_GlobalTheory_ZJ_AddExt_isPullback_square

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
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.AddExt
namespace GlobalTheory.ZJ.AddExt
theorem _root_.solution (C : Core) (hT : C.HasTests) (hC : C.TestCart)
    (φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left) (h : IsSquare C.a φ₂) {p : ℕ} [Fact p.Prime]
    (a : Sp (OO p) ⟶ (C.GG ⊗ C.GG).left) (a₀ : Sp (PadicAlgCl p) ⟶ (C.A ⊗ C.A).left)
    (ha : a₀ ≫ φ₂ = gPt p ≫ a) (b : Sp (OO p) ⟶ C.P.left)
    (hb : gPt p ≫ b = a₀ ≫ (μ[C.A]).left ≫ C.a ≫ C.G.ι) (hb' : b ≫ C.P.hom = a ≫ (C.GG ⊗ C.GG).hom) :
    ∃ (τ : C.Test (a ≫ (C.GG ⊗ C.GG).hom)) (c d : Over.mk (spMap τ.j) ⟶ τ.H),
      c.left ≫ τ.f = a ≫ (fst C.GG C.GG).left ∧ d.left ≫ τ.f = a ≫ (snd C.GG C.GG).left ∧
      b = (c * d).left ≫ τ.f ≫ C.G.ι := by
  have hp := isPullback_square C φ₂ h
  have w₁ : (fst C.GG C.GG).left ≫ C.GG.hom = (C.GG ⊗ C.GG).hom := Over.w _
  have w₂ : (snd C.GG C.GG).left ≫ C.GG.hom = (C.GG ⊗ C.GG).hom := Over.w _
  have hcl : C.Cl (a ≫ (C.GG ⊗ C.GG).hom) := by
    rintro _ ⟨x, rfl⟩
    rw [← reassoc_of% ha, hp.w, ← Category.assoc, Scheme.Hom.comp_apply]
    exact Subtype.property _
  obtain ⟨τ⟩ := hT p _ hcl
  have hτ := hC p _ τ
  let c : Over.mk (spMap τ.j) ⟶ τ.H := Over.homMk
    (hτ.lift (a ≫ (fst C.GG C.GG).left) (spMap τ.j) (by rw [Category.assoc, w₁, τ.fac])) (hτ.lift_snd _ _ _)
  let d : Over.mk (spMap τ.j) ⟶ τ.H := Over.homMk
    (hτ.lift (a ≫ (snd C.GG C.GG).left) (spMap τ.j) (by rw [Category.assoc, w₂, τ.fac])) (hτ.lift_snd _ _ _)
  have hc : c.left ≫ τ.f = a ≫ (fst C.GG C.GG).left := hτ.lift_fst _ _ _
  have hd : d.left ≫ τ.f = a ≫ (snd C.GG C.GG).left := hτ.lift_fst _ _ _
  refine ⟨τ, c, d, hc, hd, eq_mul_of_generic C τ c d a₀ ?_ ?_ b hb hb'⟩
  · rw [hc, ← reassoc_of% ha, h.1]
  · rw [hd, ← reassoc_of% ha, h.2]
end GlobalTheory.ZJ.AddExt
