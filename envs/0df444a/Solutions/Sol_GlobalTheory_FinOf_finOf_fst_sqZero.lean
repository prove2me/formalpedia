-- Prove2me | solution 1 for GlobalTheory.FinOf.finOf_fst_sqZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:46:54.119571+00:00
-- url     : https://prove2.me/submissions/70f37a4a-16bc-4d56-8d49-c49c2131334f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FinOf
variable {R₀ : Type} [CommRing R₀]
namespace GlobalTheory.FinOf
theorem _root_.solution (C : Type) [Field C] [Algebra R₀ C] : (finOf_fst (R₀ := R₀) C).SqZero := by
  refine ⟨fun c => ⟨TrivSqZeroExt.inl c, rfl⟩, ?_⟩
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  have ha' : TrivSqZeroExt.fst (a : DualNumber C) = 0 := ha
  have hb' : TrivSqZeroExt.fst (b : DualNumber C) = 0 := hb
  change (a * b : DualNumber C) = 0
  ext
  · simp [ha']
  · simp [ha', hb']
end GlobalTheory.FinOf
