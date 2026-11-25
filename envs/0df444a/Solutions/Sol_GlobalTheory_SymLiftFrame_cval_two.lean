-- Prove2me | solution 1 for GlobalTheory.SymLiftFrame.cval_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:13:37.863632+00:00
-- url     : https://prove2.me/submissions/8f1ae933-5739-45ec-b08e-caf223d1b078

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymmetricLiftTorsionPointActionOnTheta
import Theorems.Thm_GlobalTheory_SymLiftFrame_cval_of

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
namespace GlobalTheory.SymLiftFrame
theorem _root_.solution {m : T ⊗ A ⟶ A} {ε : Fin 2 → ℤ}
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ε)) {z w : Fin g → ℂ}
    (h : exAt u p z ≫ m.left = (u.ex w).left) :
    cval α (exAt u p z) J = valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left]
      ![J (u.ex z).left, J (u.ex w).left]) (α.s ![J (u.ex z).left, J (u.ex w).left]).val := by
  refine cval_of α _ J _ fun i => ?_
  fin_cases i
  · show J ((lift p (u.ex z)).left ≫ (snd T A).left) = J (u.ex z).left
    rw [← Over.comp_left, lift_snd]
  · exact congrArg J h
end GlobalTheory.SymLiftFrame
