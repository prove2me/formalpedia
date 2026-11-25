-- Prove2me | solution 1 for GlobalTheory.ThetaFn.IsFnT.sec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:25:38.730934+00:00
-- url     : https://prove2.me/submissions/134e35dc-7669-481b-8d5f-b18525b18f4a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_GlobalTheory_ThetaFn_IsFnAt_isThetaFn
import Theorems.Thm_GlobalTheory_ThetaFn_IsFnT_isThetaFn
import Theorems.Thm_GlobalTheory_ThetaFn_existsUnique_sec_isFnT

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
namespace IsFnT
theorem _root_.solution (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hAH : u.IsAH Hm χ) {n : ℕ} (hsec : ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ)
    {s s' : LB.Sec (LPow A L n (baseOver (Sp ℂ)))} {θ : (Fin g → ℂ) → ℂ} (h : IsFnT u n s θ)
    (h' : IsFnT u n s' θ) : s = s' :=
  (existsUnique_sec_isFnT u hsec (h.isThetaFn hL hAH)).unique h h'
end IsFnT
end GlobalTheory.ThetaFn
