-- Prove2me | solution 1 for GlobalTheory.ThetaFn.existsUnique_sec_isFnT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:09:36.285301+00:00
-- url     : https://prove2.me/submissions/25c5ed67-2378-40c1-9eb0-c51e669db6bf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_GlobalTheory_ThetaFn_existsUnique_sec_isFnAt

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
variable {u}
variable (u)
namespace GlobalTheory.ThetaFn
theorem _root_.solution {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} {n : ℕ}
    (hsec : ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ) {θ : (Fin g → ℂ) → ℂ}
    (hθ : u.IsThetaFn Hm χ n θ) :
    ∃! s : LB.Sec (LPow A L n (baseOver (Sp ℂ))), IsFnT u n s θ :=
  existsUnique_sec_isFnAt u basePt (hsec θ hθ)
end GlobalTheory.ThetaFn
