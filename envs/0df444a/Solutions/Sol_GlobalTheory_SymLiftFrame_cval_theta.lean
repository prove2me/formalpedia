-- Prove2me | solution 1 for GlobalTheory.SymLiftFrame.cval_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:20:39.006666+00:00
-- url     : https://prove2.me/submissions/1ed6a1cb-2c0f-48c9-afa1-ef07cc7a0464

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymmetricLiftTorsionPointActionOnTheta
import Theorems.Thm_GlobalTheory_SymLiftFrame_cval_of
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_translPt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.SymLiftFrame
open ThetaFn CubeValues SymmetricSemicharacter AppellHumbertTrivial ReciprocityTheory.ChartRestriction.G.Out
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {T : Over (Sp ℂ)} {p : 𝟙_ (Over (Sp ℂ)) ⟶ T} {J : (Sp ℂ ⟶ A.left) → L.ι}
  (hJ : ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
variable {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ} {c : ℂ}
include hJ
namespace GlobalTheory.SymLiftFrame
theorem _root_.solution (hc : HasAnConst u p Hm Θ x c) (z : Fin g → ℂ) :
    cval (L := L) Θ.φ (exAt u p z) J * u.fr (J (u.ex (z + x)).left) (z + x) ^ k =
      c * fockFactor Hm k x z * u.fr (J (u.ex z).left) z ^ k := by
  rw [cval_of Θ.φ (exAt u p z) J ![J (u.ex z).left, J (u.ex (z + x)).left] (fun i => ?_)]
  · exact hc.2 _ z (hJ _) (hJ _)
  · fin_cases i
    · show J ((lift p (u.ex z)).left ≫ (snd T A).left) = J (u.ex z).left
      rw [← Over.comp_left, lift_snd]
    · exact congrArg J (exAt_translPt u hc.1 z)
end GlobalTheory.SymLiftFrame
