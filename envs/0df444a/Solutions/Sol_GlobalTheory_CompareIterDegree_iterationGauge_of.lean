-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.iterationGauge_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:06.159646+00:00
-- url     : https://prove2.me/submissions/3ac82a43-b568-46f2-831f-fc2f688700fd

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CompareIterDegree
open Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.ExpansionTerms GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords
namespace GlobalTheory.CompareIterDegree
theorem _root_.solution (h : Iteration) : IterationGauge := by
  intro A V ι _ _ _ N M j D w lam R Γ p K hN hM hΓ hone hadd hsm hK L μ hμ
  obtain ⟨a, ha, hs, hl⟩ := h A V ι N M j D w lam R Γ hN hM hΓ hone L μ hμ
  have hp0 : p 0 = 0 := by simpa using hsm 0 0
  have h1 : p (comb j μ a) ≤ ∑ ν ∈ a.support, p (a ν • j (μ + ν)) :=
    Finset.le_sum_of_subadditive p hp0.le hadd _ _
  rw [ha]
  refine h1.trans (le_trans (sum_le_sum (g := fun ν => ‖a ν‖ₑ * K) fun ν hν => ?_) ?_)
  · rw [hsm]
    refine mul_le_mul' le_rfl (hK _ ?_)
    have h2 := hN.2 (μ - lam) ν
    rw [show μ - lam + ν = μ + ν - lam by abel] at h2
    linarith [(hs ν hν).1]
  · rw [← sum_mul]
    refine mul_le_mul' (le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hl)) le_rfl
    rw [l1, ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _]
    simp
end GlobalTheory.CompareIterDegree
