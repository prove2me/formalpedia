-- Prove2me | solution 1 for GlobalTheory.FormalChartOf.tsze_nil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:48:02.066642+00:00
-- url     : https://prove2.me/submissions/5591aef5-0bd9-491d-8bbf-8bad6bb89668

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.FormalChartOf
variable {R₀ : Type} [CommRing R₀]
namespace GlobalTheory.FormalChartOf
theorem _root_.solution {M : Type} [AddCommGroup M] [Module R₀ M] [Module R₀ᵐᵒᵖ M] [IsCentralScalar R₀ M]
    (a : TrivSqZeroExt R₀ M) (h : a.fst = 0) : IsNilpotent a := by
  refine ⟨2, ?_⟩
  have : a = TrivSqZeroExt.inr a.snd := by ext <;> simp [h]
  rw [this, pow_two, TrivSqZeroExt.inr_mul_inr]
end GlobalTheory.FormalChartOf
