-- Prove2me | solution 1 for GlobalTheory.Frames.openChart_factor_near_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:50:25.43757+00:00
-- url     : https://prove2.me/submissions/fe6b93b3-cf93-42c4-a34a-7227e3b15505

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFactorOpenImmersion
import Theorems.Thm_GlobalTheory_Frames_exists_factor_openImmersion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Frames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
namespace GlobalTheory.Frames
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [Algebra c.F R] (j : Sp R ⟶ Xo.XF c) (y₀ : FrPt Xo c R), OpenChart j y₀ → ∀ (S : Type) [CommRing S] [Algebra c.F S] (xF : Sp S ⟶ Xo.XF c), xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) → ∀ p : Sp S, xF p ∈ Set.range j → ∃ g : S, g ∉ p.asIdeal ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (lam : S →ₐ[c.F] T), IsUnit (lam g) → ∃ ψ : R →ₐ[c.F] T, spMap lam.toRingHom ≫ xF = spMap ψ.toRingHom ≫ j := by
  intro E _ _ _ H Dw l Xo c R _ _ j y₀ hj S _ _ xF hx p hp
  haveI := hj.1
  obtain ⟨g, hg, h⟩ := exists_factor_openImmersion j xF p hp
  refine ⟨g, hg, fun T _ _ lam hu => ?_⟩
  obtain ⟨ψ, hψ⟩ := h T lam.toRingHom hu
  have h2 := congrArg (· ≫ pullback.snd _ _) hψ
  simp only [Category.assoc] at h2
  rw [hx, hj.2.2, ← Spec.map_comp, ← Spec.map_comp] at h2
  have h3 := congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  refine ⟨{ ψ with commutes' := fun a => ?_ }, hψ⟩
  have h4 := RingHom.congr_fun h3 a
  exact h4.symm.trans (lam.commutes a)
end GlobalTheory.Frames
