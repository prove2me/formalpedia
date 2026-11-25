-- Prove2me | solution 1 for GlobalTheory.KeyPow.thetaLaw_generators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:47:34.51599+00:00
-- url     : https://prove2.me/submissions/8741989b-2f27-4ae9-acf5-df7ef7d8acb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaSqCongrModTwo
import Theorems.Thm_GlobalTheory_KeyPow_ThetaLaw_congr_target
import Theorems.Thm_GlobalTheory_KeyPow_thetaLaw_spTransl
import Theorems.Thm_GlobalTheory_KeyPow_thetaLaw_J

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
theorem _root_.solution (hInv : InversionStatement) (g : ℕ) (k k' : Fin g → ℤ) :
    (∀ (S : Matrix (Fin g) (Fin g) ℤ) (n' : Fin g → ℤ), S.IsSymm →
      (∀ i, (2 : ℤ) ∣ (S.mulVec k) i + S i i + k' i - n' i) → ThetaLaw g (spTransl S) k n' k k') ∧
    ThetaLaw g (Matrix.J (Fin g) ℤ) k' k k k' := by
  refine ⟨fun S n' hS hd => (thetaLaw_spTransl S hS k n').congr_target (fun _ => rfl) fun i => ?_,
    (thetaLaw_J hInv k' k).congr_target (fun i => ?_) fun _ => rfl⟩
  · have := hd i
    simp only [Pi.sub_apply]
    omega
  · simp only [Pi.neg_apply]
    omega
end GlobalTheory.KeyPow
