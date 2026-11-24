-- Prove2me | solution 1 for GlobalTheory.UnifParts.cls_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:01:43.165639+00:00
-- url     : https://prove2.me/submissions/9dabe0ea-3ddd-4cc8-aee3-6e91e72d6452

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FamilyUnifOfParts
import Theorems.Thm_GlobalTheory_UnifParts_isPeriod_transport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.UnifParts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  (perObj : ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)), InGenus D l σ D' t →
    IsPeriod D' ty P → ∃ y e, Unif Xo σ ty D' t P y e)
  (upUniq : ∀ (D' D'' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (t' : D.La →ₗ[𝓞 E] D''.La) (P : D'.La →+ (Fin g → ℂ))
    (P' : D''.La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ Xo.X) e e', Unif Xo σ ty D' t P y e → Unif Xo σ ty D'' t' P' y' e' →
    (y = y' ↔ ∃ (gam : D'.La ≃ₗ[𝓞 E] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, D''.EF (gam a) (gam b) = D'.EF a b) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ x, gam (t a) = t' a + l.M • x) ∧
      (∀ a, ∃ x, gam (t a) = t' a + l.A • x) ∧ ∀ a, P' (gam a) = h (P a)))
include perObj upUniq
namespace GlobalTheory.UnifParts
theorem _root_.solution {y y' : Sp ℂ ⟶ Xo.X} {x} (hx : x ∈ cls Xo σ ty y) (hx' : x ∈ cls Xo σ ty y') :
    cls Xo σ ty y ⊆ cls Xo σ ty y' := by
  rintro x' ⟨hg', P', e', hu'⟩
  obtain ⟨-, P, e, hu⟩ := hx
  obtain ⟨-, P₂, e₂, hu₂⟩ := hx'
  obtain ⟨gam, h, h1, h2, h3, -⟩ := (upUniq _ _ _ _ _ _ _ _ _ _ hu hu').mp rfl
  obtain ⟨y'', e'', hu''⟩ := perObj _ _ _ hg' (isPeriod_transport gam h1 hu₂.2.1)
  have : y' = y'' := (upUniq _ _ _ _ _ _ _ _ _ _ hu₂ hu'').mpr
    ⟨gam, LinearEquiv.refl _ _, h1, h2, h3, fun a => by simp⟩
  subst this
  exact ⟨hg', _, _, hu''⟩
end GlobalTheory.UnifParts
