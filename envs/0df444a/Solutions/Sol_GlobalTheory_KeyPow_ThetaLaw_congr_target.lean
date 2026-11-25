-- Prove2me | solution 1 for GlobalTheory.KeyPow.ThetaLaw.congr_target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:36:31.891857+00:00
-- url     : https://prove2.me/submissions/e7661aa1-556d-44ae-ad87-f40769347816

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaSqCongrModTwo
import Theorems.Thm_GlobalTheory_KeyPow_theta_sq_congr_mod_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open GlobalTheory GlobalTheory.KeyPow
namespace GlobalTheory.KeyPow
namespace ThetaLaw
theorem _root_.solution {g : ℕ} {sp : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    {n n' k k' m m' : Fin g → ℤ} (hl : ThetaLaw g sp n n' k k') (h : ∀ i, m i % 2 = k i % 2)
    (h' : ∀ i, m' i % 2 = k' i % 2) : ThetaLaw g sp n n' m m' := by
  obtain ⟨c, hc, hlaw⟩ := hl
  exact ⟨c, hc, fun τ hτ z => by rw [theta_sq_congr_mod_two h h']; exact hlaw τ hτ z⟩
end ThetaLaw
end GlobalTheory.KeyPow
