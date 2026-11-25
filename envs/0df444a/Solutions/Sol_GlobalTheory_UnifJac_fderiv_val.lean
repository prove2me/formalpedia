-- Prove2me | solution 1 for GlobalTheory.UnifJac.fderiv_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:46:04.789867+00:00
-- url     : https://prove2.me/submissions/21b33d1f-68cd-4002-a9c9-de144d4a7eb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_UnifValueJacZeros
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.UnifJac
variable {A : Over (Sp ℂ)} [GrpObj A]
variable {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.UnifJac
theorem _root_.solution (c : L.ι) (f : Γ(A.left, L.U c)) (F : (Fin g → ℂ) → ℂ) (hF : Differentiable ℂ F) (n : ℕ)
    (hf : ∀ y, ⊤ ≤ (u.ex y).left ⁻¹ᵁ L.U c → valAt' (u.ex y).left (L.U c) f = F y * u.fr c y ^ n)
    (z : Fin g → ℂ) (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U c) (h0 : F z = 0) (w : Fin g → ℂ) :
    fderiv ℂ (fun y => valAt' (u.ex y).left (L.U c) f) z w = u.fr c z ^ n * fderiv ℂ F z w := by
  have hn := (u.hol (L.U c) f).1.mem_nhds hz
  have e : (fun y => valAt' (u.ex y).left (L.U c) f) =ᶠ[nhds z] fun y => F y * u.fr c y ^ n :=
    Filter.eventually_of_mem hn hf
  have hd : DifferentiableAt ℂ (fun y => u.fr c y ^ n) z := ((u.fr_hol c).differentiableAt hn).pow n
  rw [e.fderiv_eq, fderiv_fun_mul (hF z) hd, h0]
  simp
end GlobalTheory.UnifJac
