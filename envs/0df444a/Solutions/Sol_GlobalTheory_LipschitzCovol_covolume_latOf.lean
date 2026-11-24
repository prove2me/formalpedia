-- Prove2me | solution 1 for GlobalTheory.LipschitzCovol.covolume_latOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:24:35.841856+00:00
-- url     : https://prove2.me/submissions/8f463071-132e-44db-84f6-db94b2965d28

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImage
import Theorems.Thm_GlobalTheory_LipschitzCovol_toMixed_remb
import Theorems.Thm_GlobalTheory_LipschitzCovol_measurePreserving_toMixed
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TraceDualDifferent_covol_eq_covolume
import Theorems.Thm_GlobalTheory_LipschitzTR_mem_latOf
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open scoped Classical
open GlobalTheory.LipschitzCovol
namespace GlobalTheory.LipschitzCovol
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)] [IsZLattice ℝ (latOf N)],
    ZLattice.covolume (latOf N) = covol N := by
  intro F _ _ _ N hN _ _
  have hmem : ∀ x : RSp F, x ∈ latOf N ↔
      toMixed x ∈ mixedEmbedding.idealLattice F (Units.mk0 N hN) := by
    intro x
    rw [mem_latOf, mixedEmbedding.mem_idealLattice]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, by simpa using ha, (toMixed_remb a).symm⟩
    · rintro ⟨a, ha, h⟩
      refine ⟨a, by simpa using ha, toMixed.injective ?_⟩
      rw [toMixed_remb, h]
  have hL : latOf N = ZLattice.comap ℝ (mixedEmbedding.idealLattice F (Units.mk0 N hN))
      (toMixed (F := F)).toContinuousLinearEquiv.toLinearMap :=
    Submodule.ext fun x => hmem x
  have key := ZLattice.covolume_comap (mixedEmbedding.idealLattice F (Units.mk0 N hN)) volume volume
    (measurePreserving_toMixed (F := F))
  have hc := covol_eq_covolume (Units.mk0 N hN)
  rw [Units.val_mk0] at hc
  rw [hc, ← key]
  congr 1
end GlobalTheory.LipschitzCovol
