-- Prove2me | solution 1 for GlobalTheory.StepData.TypeDatum.ofResidue_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:52:01.919496+00:00
-- url     : https://prove2.me/submissions/d787b742-191a-4577-965b-5a33a6bf5dbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
open GlobalTheory.StepData.TypeDatum
namespace GlobalTheory.StepData.TypeDatum
theorem _root_.solution (H : Subgroup (GL a 𝓀[k])) (χ : H →* ℂˣ) (u : GL a 𝒪[k])
    (hu : Matrix.GeneralLinearGroup.map (n := a) (IsLocalRing.residue 𝒪[k]) u ∈ H) :
    (ofResidue H χ).lam ⟨Matrix.GeneralLinearGroup.map (n := a) (algebraMap 𝒪[k] k) u, u, hu, rfl⟩ = χ ⟨_, hu⟩ := by
  have inj : Function.Injective (Matrix.GeneralLinearGroup.map (n := a) (algebraMap 𝒪[k] k)) :=
    Units.map_injective (Matrix.map_injective (FaithfulSMul.algebraMap_injective 𝒪[k] k))
  have h1 : (Subgroup.equivMapOfInjective
      (H.comap (Matrix.GeneralLinearGroup.map (n := a) (IsLocalRing.residue 𝒪[k]))) _ inj).symm ⟨_, u, hu, rfl⟩ =
      ⟨u, hu⟩ := (MulEquiv.symm_apply_eq _).2 rfl
  change χ ((Matrix.GeneralLinearGroup.map (n := a) (IsLocalRing.residue 𝒪[k])).subgroupComap H
    ((Subgroup.equivMapOfInjective _ _ inj).symm ⟨_, u, hu, rfl⟩)) = _
  rw [h1]; rfl
end GlobalTheory.StepData.TypeDatum
