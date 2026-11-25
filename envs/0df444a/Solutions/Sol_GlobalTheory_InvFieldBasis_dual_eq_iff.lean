-- Prove2me | solution 1 for GlobalTheory.InvFieldBasis.dual_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:35:18.702388+00:00
-- url     : https://prove2.me/submissions/72e2c825-3b2d-416c-8344-7b2c6624f1c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningFieldStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PreimageTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivations
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS GlobalTheory.TangentOrigin GlobalTheory.SqZero GlobalTheory.LieBaseChange
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD pushR pullR fB)
open TrivSqZeroExt (inl inr)
noncomputable section
open GlobalTheory GlobalTheory.InvFieldBasis
variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] {n : ℕ}
variable {C : Type} [CommRing C] [Algebra K C] {B : Type} [CommRing B] [Algebra K B]
namespace GlobalTheory.InvFieldBasis
theorem _root_.solution {C : Type} [CommRing C] (a b : C) (c d : Fin n → C) :
    (inl a + inr b : DualNumber C) = inl a + ∑ i, inr (c i) * inl (d i) ↔ b = ∑ i, c i * d i := by
  rw [add_right_inj]
  have hs : ∑ i, (inr (c i) : DualNumber C) * inl (d i) = inr (∑ i, c i * d i) := by
    ext <;> simp [TrivSqZeroExt.fst_sum, TrivSqZeroExt.snd_sum]
  rw [hs]
  exact TrivSqZeroExt.inr_injective.eq_iff
end GlobalTheory.InvFieldBasis
