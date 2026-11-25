-- Prove2me | solution 1 for GlobalTheory.SingleBlock.weilPairing_self_eq_measure_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:37.12485+00:00
-- url     : https://prove2.me/submissions/aa5ea9c2-cda6-4b67-b614-0115e6add1f6

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Theorems.Thm_GlobalTheory_SingleBlock_phiU_of_mem
import Theorems.Thm_GlobalTheory_SingleBlock_phiU_of_notMem
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {r t : ℕ}
  {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}
variable [MeasurableSpace F] [BorelSpace F]
namespace GlobalTheory.SingleBlock
theorem _root_.solution (hS : MeasurableSet (suppSet t O ϖ P)) (ρ : P →* ℂˣ)
    (hρ : ∀ k, ‖((ρ k : ℂˣ) : ℂ)‖ = 1) (ν : Measure (Matrix (Fin r ⊕ Fin t) (Fin r) F)) :
    weilIP ν (phiU O ϖ P ρ) (phiU O ϖ P ρ) = ((ν (suppSet t O ϖ P)).toReal : ℂ) := by
  have hpt : ∀ x, phiU O ϖ P ρ x * conj (phiU O ϖ P ρ x) =
      (suppSet t O ϖ P).indicator (fun _ => (1 : ℂ)) x := by
    intro x
    by_cases hx : x ∈ suppSet t O ϖ P
    · rw [Set.indicator_of_mem hx]
      obtain ⟨⟨k, hk, ek⟩, h2⟩ := hx
      rw [phiU_of_mem ρ ⟨k, hk⟩ ek h2, Complex.mul_conj, Complex.normSq_eq_norm_sq, hρ]
      simp
    · rw [Set.indicator_of_notMem hx, phiU_of_notMem ρ hx, zero_mul]
  unfold weilIP
  simp_rw [hpt]
  rw [integral_indicator_const _ hS]
  simp [Measure.real]
end GlobalTheory.SingleBlock
