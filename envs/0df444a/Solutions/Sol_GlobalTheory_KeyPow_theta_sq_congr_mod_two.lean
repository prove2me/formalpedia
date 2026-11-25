-- Prove2me | solution 1 for GlobalTheory.KeyPow.theta_sq_congr_mod_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:23:12.590921+00:00
-- url     : https://prove2.me/submissions/505c0b07-62ac-42dd-bf21-94f2dea9a023

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaSqCongrModTwo
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_theta_sq_red


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
theorem _root_.solution {g : ℕ} {k k' m m' : Fin g → ℤ} (h : ∀ i, k i % 2 = m i % 2)
    (h' : ∀ i, k' i % 2 = m' i % 2) (z : Fin g → ℂ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    theta (halfVec k) (halfVec k') z τ ^ 2 = theta (halfVec m) (halfVec m') z τ ^ 2 := by
  rw [theta_sq_red k k', theta_sq_red m m', funext h, funext h']
end GlobalTheory.KeyPow
