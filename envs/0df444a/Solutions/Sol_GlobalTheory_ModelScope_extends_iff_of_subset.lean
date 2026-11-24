-- Prove2me | solution 1 for GlobalTheory.ModelScope.extends_iff_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:25:03.685881+00:00
-- url     : https://prove2.me/submissions/438177e1-0103-4339-b336-f45310ea1d7f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_RangeJSubsetAbLocus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ModelScope
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
namespace GlobalTheory.ModelScope
theorem _root_.solution (Y : Model Xo c β) (U : Y.X.Opens) (hU : Set.range Y.j ⊆ (U : Set Y.X))
    (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) :
    Y.Extends U σ ↔ ∃ (j' : Xo.XF c ⟶ U.toScheme) (σ' : U.toScheme ⟶ Y.t.G.left),
      j' ≫ U.ι = Y.j ∧ σ' ≫ Y.t.G.hom = U.ι ∧ j' ≫ σ' = σ.left ≫ Y.m.φ := by
  have hU' : Set.range Y.j ⊆ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
  constructor
  · rintro ⟨σ', h₁, h₂⟩
    exact ⟨IsOpenImmersion.lift U.ι Y.j hU', σ', IsOpenImmersion.lift_fac _ _ _, h₁,
      h₂ _ (IsOpenImmersion.lift_fac _ _ _)⟩
  · rintro ⟨j', σ', h₀, h₁, h₂⟩
    refine ⟨σ', h₁, fun j'' h => ?_⟩
    obtain rfl : j'' = j' := by rw [← cancel_mono U.ι, h, h₀]
    exact h₂
end GlobalTheory.ModelScope
