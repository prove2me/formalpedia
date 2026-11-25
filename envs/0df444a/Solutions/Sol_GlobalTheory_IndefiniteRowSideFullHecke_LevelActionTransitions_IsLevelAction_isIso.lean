-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions.IsLevelAction.isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:59:31.004003+00:00
-- url     : https://prove2.me/submissions/8d1938ed-3e38-41df-9543-59d1b683a8c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_OpenModelSections
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LevelActionTransitions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
  {univ : Obj D l (baseKA l) str} {F₀ : IntermediateField ℚ ℂ} {h : IsCoeffField l F₀}
  {O : Type} [CommRing O] {φ : O →+* F₀}
namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
namespace IsLevelAction
theorem _root_.solution {m : Model univ h φ} {act lift act₀} (ρ : IsLevelAction m act lift act₀) (g : KMax D) :
    IsIso (act g) :=
  ⟨act g⁻¹, by rw [← ρ.act_mul, mul_inv_cancel, ρ.act_one], by rw [← ρ.act_mul, inv_mul_cancel, ρ.act_one]⟩
end IsLevelAction
end GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
