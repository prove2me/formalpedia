-- Prove2me | solution 1 for GlobalTheory.InvExt.exists_test
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:08:01.817008+00:00
-- url     : https://prove2.me/submissions/211b38e9-0560-475b-a70d-e79a0cc26390

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsInverseExtensionProperClosure
import Theorems.Thm_GlobalTheory_InvExt_isDominant_gPt
import Theorems.Thm_GlobalTheory_InvExt_generic_inv

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
open GlobalTheory GlobalTheory.InvExt
variable (C : Core)
variable {C}
namespace GlobalTheory.InvExt
theorem _root_.solution (hT : C.HasTests) {p : ℕ} [Fact p.Prime] (α : Sp (OO p) ⟶ C.G.toScheme)
    (a₀ : Sp (PadicAlgCl p) ⟶ C.A.left) (b : Sp (OO p) ⟶ C.P.left) (ha : a₀ ≫ C.a = gPt p ≫ α)
    (hb : gPt p ≫ b = a₀ ≫ (ι[C.A]).left ≫ C.a ≫ C.G.ι) (hb' : b ≫ C.P.hom = α ≫ C.GG.hom) :
    ∃ (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y) (c : Sp (OO p) ⟶ τ.H.left),
      c ≫ τ.H.hom = spMap τ.j ∧ c ≫ τ.f = α ∧ b = (c ≫ (ι[τ.H]).left ≫ τ.f) ≫ C.G.ι := by
  have hw : C.a ≫ C.GG.hom = C.A.hom ≫ C.U.ι := by simpa using C.cart.w
  have hcl : C.Cl (α ≫ C.GG.hom) := by
    rintro _ ⟨x, rfl⟩
    rw [← reassoc_of% ha, hw, ← Category.assoc, Scheme.Hom.comp_apply]
    exact Subtype.property _
  obtain ⟨τ⟩ := hT p _ hcl
  obtain ⟨c, hc, hcf⟩ := τ.lift α rfl
  refine ⟨_, τ, c, hc, hcf, ?_⟩
  have := C.proper
  have := isDominant_gPt p
  refine ext_of_isDominant_of_isSeparated C.P.hom ?_ (gPt p) ?_
  · have h1 : τ.f ≫ C.G.ι ≫ C.P.hom = τ.H.hom ≫ τ.y₀ := τ.f_over
    simp only [Category.assoc]
    rw [hb', h1, Over.w_assoc, reassoc_of% hc, τ.fac]
  · rw [hb, ← Category.assoc (gPt p), generic_inv τ c hc a₀ (by rw [hcf, ha])]
    simp only [Category.assoc]
end GlobalTheory.InvExt
