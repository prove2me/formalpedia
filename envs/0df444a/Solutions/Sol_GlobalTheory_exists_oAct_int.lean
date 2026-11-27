-- Prove2me | solution 1 for GlobalTheory.exists_oAct_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:37:18.65098+00:00
-- url     : https://prove2.me/submissions/f5cc7d9e-a37e-4fda-8f88-3e96fd094da0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RosatiAdjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RosatiAdjOfPoints
import Theorems.Thm_GlobalTheory_IntAct_rosatiAdj_zpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Out.CubeSt → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S),
    ∃ ρ : P.OAct ℤ, ∀ a : ℤ, ρ.act a = (𝟙 P.A : P.A ⟶ P.A) ^ a := by
  intro hC S _ P
  obtain ⟨r, hr⟩ := P.rigid
  obtain ⟨c⟩ := (hC S P ⟨P.L, r, P.isLB, hr⟩ rfl).1
  exact ⟨⟨IntAct.intRingAct P.A, fun a => IntAct.rosatiAdj_zpow ⟨P.L, r, P.isLB, hr⟩ c P.sym a⟩, fun _ => rfl⟩
end GlobalTheory
