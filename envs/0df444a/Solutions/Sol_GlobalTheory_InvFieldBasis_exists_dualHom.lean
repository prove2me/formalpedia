-- Prove2me | solution 1 for GlobalTheory.InvFieldBasis.exists_dualHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:47:21.660029+00:00
-- url     : https://prove2.me/submissions/9b812a20-3a89-4acd-b84c-a99c22fb239f

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
theorem _root_.solution {A C : Type} [CommRing A] [CommRing C] (φ : A →+* C) (δ : A → C)
    (hadd : ∀ f f', δ (f + f') = δ f + δ f') (hmul : ∀ f f', δ (f * f') = φ f * δ f' + φ f' * δ f) :
    ∃ ψ : A →+* DualNumber C, ∀ f, ψ f = inl (φ f) + inr (δ f) := by
  have h0 : δ 0 = 0 := by
    have h := hadd 0 0
    simp only [add_zero] at h
    exact left_eq_add.mp h
  have h1 : δ 1 = 0 := by
    have h := hmul 1 1
    simp at h
    linear_combination h
  refine ⟨{ toFun := fun f => inl (φ f) + inr (δ f)
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun _ => rfl⟩
  · simp [h1]
  · intro f f'
    ext <;> simp [hmul, TrivSqZeroExt.snd_mul, mul_comm]
  · simp [h0]
  · intro f f'
    ext <;> simp [hadd]
end GlobalTheory.InvFieldBasis
