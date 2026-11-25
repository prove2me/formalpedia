-- Prove2me | solution 1 for GlobalTheory.TorusAlg.thetaChar_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:08:31.40696+00:00
-- url     : https://prove2.me/submissions/affeec5a-e68e-4f60-a9d8-180b78aa1264

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Theorems.Thm_GlobalTheory_TorusAlg_thetaChar_eq_theta
import Theorems.Thm_GlobalTheory_thetaLevelChar_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusAlg
open ReciprocityTheory.PTheta
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}
namespace GlobalTheory.TorusAlg
theorem _root_.solution (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (ha : ∀ i, a i = 0 ∨ a i = 1 / 2)
    (hb : ∀ i, b i = 0 ∨ b i = 1 / 2) :
    thetaChar τ a b ≠ 0 ∧
    thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) 1 τ = Submodule.span ℂ {thetaChar τ a b} ∧
    ∀ n : ℕ, 0 < n → Module.finrank ℂ (thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) n τ) = n ^ g := by
  rw [thetaChar_eq_theta τ ha hb]
  refine ⟨theta_ne_zero ⟨hs, hp⟩ _ _, thetaLevelChar_one ⟨hs, hp⟩, fun n hn => ?_⟩
  rw [finrank_thetaLevelChar ⟨hs, hp⟩ hn, Fintype.card_fin]
end GlobalTheory.TorusAlg
