-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.indCoeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:40:24.485263+00:00
-- url     : https://prove2.me/submissions/29167af4-eeda-4ee0-8417-7377db11b825

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable (D : Datum H) (l : Level H)
variable {l}
variable {D}
namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
theorem _root_.solution (c : Coeff l) {n : ℕ} (x₀ : Fin n → ConjCl D l) (t : Fin n → NamedCl D l) :
    indCoeff c x₀ t = (Nat.card (Fin n → NamedCl D l) : c.F)⁻¹ * (zetaM c ^ (pairing D l x₀ t).val)⁻¹ := by
  rw [indCoeff, fourier, Finset.sum_eq_single x₀]
  · simp [indicatorCl, eChar]
  · intro b _ hb; simp [indicatorCl, hb]
  · intro h; simp at h
end GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
