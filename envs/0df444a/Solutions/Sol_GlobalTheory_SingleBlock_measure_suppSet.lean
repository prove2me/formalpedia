-- Prove2me | solution 1 for GlobalTheory.SingleBlock.measure_suppSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:18.604418+00:00
-- url     : https://prove2.me/submissions/95d62c02-dc10-4103-9972-ba9f6402c4c5

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Theorems.Thm_GlobalTheory_SingleBlock_measurableSet_Jset
import Theorems.Thm_P2M_GlobalTheory_SingleBlock_measurable_toRows__1516c29dbd57
import Theorems.Thm_P2M_GlobalTheory_SingleBlock_measurable_toRows__be0362a1a7c9
import Theorems.Thm_GlobalTheory_SingleBlock_measurableSet_intMat
import Theorems.Thm_GlobalTheory_SingleBlock_invariant_top
import Theorems.Thm_GlobalTheory_SingleBlock_invariant_bot
import Theorems.Thm_Formalism_DoubleCosetMeasures_Final_volII
import Theorems.Thm_Formalism_DoubleCosetMeasures_Final_volJadd
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_meas_ii
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_volII
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_volJadd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {r t : ℕ}
  {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}
variable [MeasurableSpace F] [BorelSpace F]
namespace GlobalTheory.SingleBlock
theorem _root_.solution (hO : IsOpen (O : Set F)) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    (hloc : IsLocalAt O ϖ) [Finite (kF O ϖ hϖ)] (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r)
    (ν : Measure (Matrix (Fin r ⊕ Fin t) (Fin r) F)) [ν.IsAddLeftInvariant] :
    ν (suppSet t O ϖ P) * (Nat.card (kF O ϖ hϖ) : ENNReal) ^ (r * r) *
        (Nat.card (kF O ϖ hϖ) : ENNReal) ^ (t * r) =
      (Nat.card (P ⧸ (congSub O ϖ r).subgroupOf P) : ENNReal) *
        ν (intMatrices O (Fin r ⊕ Fin t) (Fin r)) := by
  have i1 := invariant_top ν (IIset O ϖ)
  have i2 := invariant_bot ν (intMat O r r)
  have h1 := volJadd F O hO ϖ hϖ hϖ0 hloc inferInstance r
    ((ν.restrict (toRows₂ ⁻¹' IIset O ϖ)).map toRows₁) P hKP hP
  have h2 := volII F O hO ϖ hϖ hϖ0 inferInstance t r
    ((ν.restrict (toRows₁ ⁻¹' intMat O r r)).map toRows₂)
  have mJ := measurableSet_Jset hO hϖ hϖ0 hloc hKP hP
  have mI := Vol.meas_ii O hO ϖ hϖ0 t r
  rw [Measure.map_apply measurable_toRows₁ mJ,
    Measure.map_apply measurable_toRows₁ (measurableSet_intMat hO r r),
    Measure.restrict_apply (measurable_toRows₁ mJ),
    Measure.restrict_apply (measurable_toRows₁ (measurableSet_intMat hO r r))] at h1
  rw [Measure.map_apply measurable_toRows₂ mI,
    Measure.map_apply measurable_toRows₂ (measurableSet_intMat hO t r),
    Measure.restrict_apply (measurable_toRows₂ mI),
    Measure.restrict_apply (measurable_toRows₂ (measurableSet_intMat hO t r)),
    Set.inter_comm] at h2
  have e : intMatrices O (Fin r ⊕ Fin t) (Fin r) =
      toRows₂ ⁻¹' intMat O t r ∩ toRows₁ ⁻¹' intMat O r r := by
    ext x
    exact ⟨fun h => ⟨fun i j => h _ _, fun i j => h _ _⟩,
      fun h i j => by rcases i with i | i; exacts [h.2 i j, h.1 i j]⟩
  rw [e, ← h2, ← mul_assoc]
  congr 1
end GlobalTheory.SingleBlock
