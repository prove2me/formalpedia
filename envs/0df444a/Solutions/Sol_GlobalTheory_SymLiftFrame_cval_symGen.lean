-- Prove2me | solution 1 for GlobalTheory.SymLiftFrame.cval_symGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:15:00.960744+00:00
-- url     : https://prove2.me/submissions/40fda41c-c11c-478d-b360-051449474634

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymmetricLiftTorsionPointActionOnTheta
import Theorems.Thm_GlobalTheory_SymLiftFrame_cval_mul
import Theorems.Thm_GlobalTheory_SymLiftFrame_cval_inv
import Theorems.Thm_GlobalTheory_SymLiftFrame_cval_pull

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
include hJ
namespace GlobalTheory.SymLiftFrame
theorem _root_.solution {k : ℤ} (θ : ThetaGrp A L k T) (nu : LB.Gen (negLB A L k T))
    (r : Sp ℂ ⟶ (T ⊗ A).left) :
    cval (symGen A L k θ nu) r J =
      cval (L := L) θ.φ (r ≫ (translT A θ.pt⁻¹).left) J * cval (L := L) nu r J *
        (cval (L := L) θ.φ (r ≫ (negT A T).left) J *
          (cval (L := L) nu (r ≫ (translT A θ.pt⁻¹).left) J)⁻¹) := by
  unfold symGen
  rw [cval_mul hJ, cval_mul hJ, cval_mul hJ _ nu, cval_pull hJ θ.φ, cval_pull hJ θ.φ, cval_inv hJ,
    cval_pull hJ nu]
end GlobalTheory.SymLiftFrame
