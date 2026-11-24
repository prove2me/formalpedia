-- Prove2me | solution 1 for GlobalTheory.IdealChain.sph_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:36.046194+00:00
-- url     : https://prove2.me/submissions/ced69f9e-c10c-4fdf-8ac0-3eecb1f0db31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_HalfPowerSpherical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical GlobalTheory.LatPair GlobalTheory.StepData
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.IdealChain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype ι] [DecidableEq ι] [DecidableEq ι']
open Classical
namespace GlobalTheory.IdealChain
theorem _root_.solution (α : kˣ) (L' : Submodule 𝒪[k] (ι' → k)) (L : Submodule 𝒪[k] (ι → k)) (x : Matrix ι ι' k) :
    sph α L' L x = if ∀ v ∈ L', (((α⁻¹ : kˣ) : k) • x) *ᵥ v ∈ L then 1 else 0 := by
  unfold sph
  refine if_congr (forall₂_congr fun v _ => ?_) rfl rfl
  rw [Matrix.smul_mulVec]
  constructor
  · rintro ⟨w, hw, e⟩
    rw [e, smul_smul]
    simpa using hw
  · exact fun h => ⟨_, h, by simp [smul_smul]⟩
end GlobalTheory.IdealChain
