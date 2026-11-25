-- Prove2me | solution 1 for GlobalTheory.ZJ.AddExt.centre_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:51:20.271975+00:00
-- url     : https://prove2.me/submissions/f415027e-d0d0-4f55-99c0-cbae8aca6794

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddExtension
import Theorems.Thm_GlobalTheory_ZJ_AddExt_exists_common_geometric_point
import Theorems.Thm_GlobalTheory_ZJ_AddExt_prime_eq
import Theorems.Thm_GlobalTheory_ZJ_AddExt_exists_test
import Theorems.Thm_GlobalTheory_ZJ_AddExt_range_comp_test

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
theorem _root_.solution (C : Core) (hT : C.HasTests) (hC : C.TestCart) (hF : C.FibLaw)
    (φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left) (h : IsSquare C.a φ₂) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (a : Sp (OO p) ⟶ (C.GG ⊗ C.GG).left) (a₀ : Sp (PadicAlgCl p) ⟶ (C.A ⊗ C.A).left)
    (ha : a₀ ≫ φ₂ = gPt p ≫ a) (b : Sp (OO p) ⟶ C.P.left)
    (hb : gPt p ≫ b = a₀ ≫ (μ[C.A]).left ≫ C.a ≫ C.G.ι) (hb' : b ≫ C.P.hom = a ≫ (C.GG ⊗ C.GG).hom)
    (a' : Sp (OO q) ⟶ (C.GG ⊗ C.GG).left) (a₁ : Sp (PadicAlgCl q) ⟶ (C.A ⊗ C.A).left)
    (ha' : a₁ ≫ φ₂ = gPt q ≫ a') (b' : Sp (OO q) ⟶ C.P.left)
    (hb₁ : gPt q ≫ b' = a₁ ≫ (μ[C.A]).left ≫ C.a ≫ C.G.ι) (hb₁' : b' ≫ C.P.hom = a' ≫ (C.GG ⊗ C.GG).hom)
    (e : a (cPt p) = a' (cPt q)) : b (cPt p) = b' (cPt q) := by
  obtain ⟨K, _, _, u, u', hu, h1, h2⟩ := exists_common_geometric_point a a' _ _ e
  obtain rfl := prime_eq p q u u' h1 h2
  obtain ⟨τ, c, d, hc, hd, rfl⟩ := exists_test C hT hC φ₂ h a a₀ ha b hb hb'
  obtain ⟨τ', c', d', hc', hd', rfl⟩ := exists_test C hT hC φ₂ h a' a₁ ha' b' hb₁ hb₁'
  let v : Over.mk (u ≫ spMap τ.j) ⟶ Over.mk (spMap τ.j) := Over.homMk u
  let v' : Over.mk (u' ≫ spMap τ'.j) ⟶ Over.mk (spMap τ'.j) := Over.homMk u'
  have key := (hF p _ _ τ τ' K (u ≫ spMap τ.j) (u' ≫ spMap τ'.j) (range_comp_test τ u h1)
    (range_comp_test τ' u' h2) (by rw [Category.assoc, Category.assoc, τ.fac, τ'.fac, reassoc_of% hu])
    (v ≫ c) (v ≫ d) (v' ≫ c') (v' ≫ d')
    (by
      change (u ≫ c.left) ≫ _ = (u' ≫ c'.left) ≫ _
      rw [Category.assoc, Category.assoc, hc, hc', reassoc_of% hu])
    (by
      change (u ≫ d.left) ≫ _ = (u' ≫ d'.left) ≫ _
      rw [Category.assoc, Category.assoc, hd, hd', reassoc_of% hu])).1
  rw [← MonObj.comp_mul, ← MonObj.comp_mul] at key
  have key' : u ≫ (c * d).left ≫ τ.f ≫ C.G.ι = u' ≫ (c' * d').left ≫ τ'.f ≫ C.G.ι := by
    have : (u ≫ (c * d).left) ≫ τ.f = (u' ≫ (c' * d').left) ≫ τ'.f := key
    simpa only [Category.assoc] using congrArg (· ≫ C.G.ι) this
  obtain ⟨x⟩ : Nonempty (Sp K) := inferInstance
  have := congrArg (fun g : Sp K ⟶ C.P.left => g x) key'
  beta_reduce at this
  rwa [Scheme.Hom.comp_apply u, Scheme.Hom.comp_apply u', h1, h2] at this
end GlobalTheory.ZJ.AddExt
