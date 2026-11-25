-- Prove2me | solution 1 for GlobalTheory.PrimitiveRegular.mem_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:22:56.146334+00:00
-- url     : https://prove2.me/submissions/e078fad8-a790-4597-a62b-db380149a6ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowEqThetaLevelChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PrimitiveRegularOnSectionNonzeroLocus
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.PrimitiveRegular
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
namespace GlobalTheory.PrimitiveRegular
theorem _root_.solution (u : HolUnif A L g) {n : ℕ} {σ : (lbPow L n).Sec} {θ : (Fin g → ℂ) → ℂ}
    (hθ : u.IsFnPow n σ θ) (k : (lbPow L n).ι) (z : Fin g → ℂ) (hk : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U k)
    (hz : θ z ≠ 0) : valAt' (u.ex z).left ((lbPow L n).U k) (σ.f k) ≠ 0 := by
  rw [hθ k z hk]
  refine mul_ne_zero hz (pow_ne_zero _ (u.11 _ z ?_))
  have hU : (lbPow L n).U k ≤ L.U (k PUnit.unit) := by
    intro p hp
    have hp' := Set.mem_iInter.mp hp PUnit.unit
    simpa using hp'
  exact fun q hq => hU (hk hq)
end GlobalTheory.PrimitiveRegular
