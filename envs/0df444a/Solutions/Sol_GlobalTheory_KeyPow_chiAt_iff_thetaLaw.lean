-- Prove2me | solution 1 for GlobalTheory.KeyPow.chiAt_iff_thetaLaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:42:36.485478+00:00
-- url     : https://prove2.me/submissions/3fdfa09a-10d6-4f40-a04b-5ad7517bec6d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.KeyPow
open ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace GlobalTheory.KeyPow
theorem _root_.solution (g : ℕ) (sp : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    ChiAt g sp ↔ ∀ n n' : Fin g → ℤ, ∃ k k' : Fin g → ℤ,
      (∀ i, k i = 0 ∨ k i = 1) ∧ (∀ i, k' i = 0 ∨ k' i = 1) ∧ ThetaLaw g sp n n' k k' := by
  constructor
  · intro h n n'
    obtain ⟨k, k', c, hk, hk', hc, hl⟩ := h n n'
    exact ⟨k, k', hk, hk', c, hc, hl⟩
  · intro h n n'
    obtain ⟨k, k', hk, hk', c, hc, hl⟩ := h n n'
    exact ⟨k, k', c, hk, hk', hc, hl⟩
end GlobalTheory.KeyPow
