-- Prove2me | solution 1 for GlobalTheory.LastSteps.exists_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:46.997408+00:00
-- url     : https://prove2.me/submissions/20fc4c07-1e8c-4305-ae53-bf7b5427877f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData
noncomputable section
open GlobalTheory GlobalTheory.LastSteps
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type}
namespace GlobalTheory.LastSteps
theorem _root_.solution (L : Submodule 𝒪[k] (n → k)) (F : L →ₗ[𝒪[k]] 𝓀[k]) :
    ∃ f : Module.Dual 𝓀[k] (Red L), ∀ z, f (Red.mk L z) = F z := by
  let f : Red L →ₗ[𝒪[k]] 𝓀[k] :=
    (maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] L).liftQ F (Submodule.smul_le.2 fun s hs x _ => by
      rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, ResidueField.algebraMap_eq,
        (residue_eq_zero_iff s).2 hs, zero_mul])
  exact ⟨f.extendScalarsOfSurjective residue_surjective, fun _ => rfl⟩
end GlobalTheory.LastSteps
