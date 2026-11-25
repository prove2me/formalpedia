-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.inj_add_of_gapTwo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:12:03.72704+00:00
-- url     : https://prove2.me/submissions/cd7e2ae7-a3ac-41bd-99be-5c42982eb75f

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
theorem _root_.solution {n : ℕ} {μ e : Fin n → ℝ} (h : GapTwo μ) (he : ∀ a b, |e a - e b| ≤ 1) :
    Function.Injective (μ + e) := fun a b hab => by
  by_contra hne
  have h1 := h a b hne
  have h2 := he b a
  rw [show μ a - μ b = e b - e a by simp only [Pi.add_apply] at hab; linarith] at h1
  linarith
end GlobalTheory.CompareIterDegree
