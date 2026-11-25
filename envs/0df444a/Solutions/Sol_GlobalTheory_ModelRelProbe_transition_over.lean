-- Prove2me | solution 1 for GlobalTheory.ModelRelProbe.transition_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:04:34.848863+00:00
-- url     : https://prove2.me/submissions/78a3da21-2309-4569-9687-546b19f0e52f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_DominatesLiftUnique
import Theorems.Thm_GlobalTheory_ModelRelProbe_j_over
import Theorems.Thm_GlobalTheory_ModelRelProbe_spMap_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ModelRelProbe
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}
namespace GlobalTheory.ModelRelProbe
theorem _root_.solution {l₂ : Level H} {Xo₂ : Moduli D l₂} {c₂ : Coeff l₂} {O O₂ : Type} [CommRing O] [CommRing O₂]
    {β : O →+* c.F} {β₂ : O₂ →+* c₂.F} (Y : Model Xo c β) (Y₂ : Model Xo₂ c₂ β₂) (b : O →+* O₂) (π : Y₂.X ⟶ Y.X)
    (h : IsTransition Y Y₂ b π) [Mono (spMap β)] (σ : c.F →+* c₂.F) (hσ : σ.comp β = β₂.comp b) :
    π ≫ Y.s = Y₂.s ≫ spMap b ∧ ∃ r : Xo₂.XF c₂ ⟶ Xo.XF c, Y₂.j ≫ π = r ≫ Y.j ∧
      r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap σ := by
  obtain ⟨π', -, r, h₁, h₂, -, h₃, -⟩ := h
  have e : π ≫ Y.s = Y₂.s ≫ spMap b := by
    rw [← h₁, ← h₂, Category.assoc, Category.assoc, pullback.condition]
  refine ⟨e, r, h₃, ?_⟩
  rw [← cancel_mono (spMap β), Category.assoc, Category.assoc, ← j_over, ← Category.assoc, ← h₃, Category.assoc, e,
    ← Category.assoc, j_over, Category.assoc, spMap_comp, spMap_comp, hσ]
end GlobalTheory.ModelRelProbe
