-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections.Model.incl_mem_abLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:54:17.606204+00:00
-- url     : https://prove2.me/submissions/60cec10f-902b-4b23-82b1-076641c7f2d4

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
theorem _root_.solution (y : ↥(baseChange str h)) : m.incl y ∈ abLocus m.t.G := by
  have := (m.ab (m.j y)).mpr ⟨y, rfl⟩
  simpa [incl] using this
end GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections.Model
