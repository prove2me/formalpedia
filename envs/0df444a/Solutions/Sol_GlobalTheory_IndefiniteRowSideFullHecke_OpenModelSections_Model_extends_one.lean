-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections.Model.extends_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:52:15.135797+00:00
-- url     : https://prove2.me/submissions/08b47c3d-39e9-41fc-a6ba-d4359c5d02af

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
theorem _root_.solution (U : m.X.Opens) : m.Extends (toUnit _ ≫ MonObj.one) U := by
  have h1 : m.liftSec (toUnit _ ≫ MonObj.one) = eSec m.t₀.G := by
    apply m.toUniv.cart.1.hom_ext
    · rw [liftSec, IsPullback.lift_fst, m.toUniv.cm.e_comm, m.toUniv.base]; rfl
    · rw [liftSec, IsPullback.lift_snd]; exact (Over.w (MonObj.one (X := m.t₀.G))).symm
  refine ⟨toUnit _ ≫ MonObj.one, ?_⟩
  have h2 : m.secMap (toUnit _ ≫ MonObj.one) = m.incl ≫ eSec m.t.G := by
    rw [secMap, h1]
    have := m.toModel.cm.e_comm
    rw [m.toModel.base] at this
    exact this
  rw [h2, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  rfl
end GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections.Model
