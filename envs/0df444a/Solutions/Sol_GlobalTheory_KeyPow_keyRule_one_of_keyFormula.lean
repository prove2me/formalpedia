-- Prove2me | solution 1 for GlobalTheory.KeyPow.keyRule_one_of_keyFormula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:56:59.37435+00:00
-- url     : https://prove2.me/submissions/60147e4f-3db1-47e2-8d26-c60eb7d80e2c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Theorems.Thm_GlobalTheory_KeyPow_normalAt_one_iff

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
namespace GlobalTheory.KeyPow
theorem _root_.solution (h : KeyFormula) : KeyRule (fun _ => 1) 1 charHalf := by
  obtain ⟨κ, h1, h2, h3, h4, -⟩ := h
  refine ⟨κ, ?_, ?_, ?_, ?_⟩
  · intro K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M _ hs hM
    simpa only [mul_one] using h1 K P hg rig hr th hth v hv th' hth' v' hv' a M hs hM
  · intro K K' _ _ _ _ f x x' _ hpb
    exact h2 K K' f x x' hpb
  · intro R K _ _ _ _ _ _ _ x xK _ hpb
    exact h3 R K x xK hpb
  · intro x τ a b _ hS hN
    obtain ⟨u, hs, hp, hΛ, hr, hf, hd⟩ := (normalAt_one_iff x τ a b).1 hN
    exact h4 x u τ a b hs hp hS.1 hS.2 hΛ hr hf hd
end GlobalTheory.KeyPow
