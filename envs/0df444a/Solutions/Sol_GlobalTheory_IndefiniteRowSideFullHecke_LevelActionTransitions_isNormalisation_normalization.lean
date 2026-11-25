-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions.isNormalisation_normalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:00:10.779796+00:00
-- url     : https://prove2.me/submissions/5ca6a369-dc69-4211-9b4a-e8a332ec722c

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
theorem _root_.solution {U Y : Scheme.{0}} (f : U ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    IsNormalisation f.toNormalization f.fromNormalization := by
  have key : ∀ g : U ⟶ Y, g = f → ∃ (_ : QuasiCompact g) (_ : QuasiSeparated g) (e : f.normalization ≅ g.normalization),
      f.toNormalization ≫ e.hom = g.toNormalization ∧ e.hom ≫ g.fromNormalization = f.fromNormalization := by
    rintro g rfl
    exact ⟨inferInstance, inferInstance, Iso.refl _, by simp, by simp⟩
  exact key _ f.toNormalization_fromNormalization
end GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
