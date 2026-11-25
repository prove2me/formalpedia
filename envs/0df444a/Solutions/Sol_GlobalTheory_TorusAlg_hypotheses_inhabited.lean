-- Prove2me | solution 1 for GlobalTheory.TorusAlg.hypotheses_inhabited
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:27:25.968801+00:00
-- url     : https://prove2.me/submissions/d426cab6-4203-4d02-b1a6-387affc3a474

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Theorems.Thm_GlobalTheory_IsSiegel_smul
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusAlg
open ReciprocityTheory.PTheta
namespace GlobalTheory.TorusAlg
theorem _root_.solution :
    (∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.IsSymm →
      (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ) + B.map Complex.ofReal).IsSymm ∧
      ((Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ) + B.map Complex.ofReal).map Complex.im).PosDef) ∧
    ((!![Complex.I, 1 / 3; 1 / 3, Complex.I] : Matrix (Fin 2) (Fin 2) ℂ).IsSymm ∧
      ((!![Complex.I, 1 / 3; 1 / 3, Complex.I] : Matrix (Fin 2) (Fin 2) ℂ).map Complex.im).PosDef ∧
      (∀ i, (![1 / 2, 0] : Fin 2 → ℂ) i = 0 ∨ (![1 / 2, 0] : Fin 2 → ℂ) i = 1 / 2) ∧
      ∀ i, (![1 / 2, 1 / 2] : Fin 2 → ℂ) i = 0 ∨ (![1 / 2, 1 / 2] : Fin 2 → ℂ) i = 1 / 2) := by
  refine ⟨fun g B hB => ⟨(Matrix.isSymm_one.smul _).add (hB.map _), ?_⟩, ?_, ?_, ?_, ?_⟩
  · convert (Matrix.PosDef.one : (1 : Matrix (Fin g) (Fin g) ℝ).PosDef) using 1
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · convert (Matrix.PosDef.one : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef) using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro i; fin_cases i <;> simp
  · intro i; fin_cases i <;> simp
end GlobalTheory.TorusAlg
