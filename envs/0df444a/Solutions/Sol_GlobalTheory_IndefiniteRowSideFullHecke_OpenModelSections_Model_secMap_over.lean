-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections.Model.secMap_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:01:01.470104+00:00
-- url     : https://prove2.me/submissions/b9acef96-3274-44dc-be8b-ff9e16f86599

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoefficientFieldBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_OpenModelSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
open GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections.Model
variable {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
  {univ : Obj D l (baseKA l) str} {F₀ : IntermediateField ℚ ℂ} {h : IsCoeffField l F₀}
  {O : Type} [CommRing O] {φ : O →+* F₀} (m : Model univ h φ)
namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections.Model
theorem _root_.solution (σ : Over.mk (baseChangeFst str h) ⟶ univ.t.G) : m.secMap σ ≫ m.t.G.hom = m.incl := by
  rw [secMap, Category.assoc, m.toModel.cart.1.w, ← Category.assoc, liftSec, IsPullback.lift_snd, Category.id_comp, incl]
end GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections.Model
