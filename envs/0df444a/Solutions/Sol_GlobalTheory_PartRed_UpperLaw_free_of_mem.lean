-- Prove2me | solution 1 for GlobalTheory.PartRed.UpperLaw.free_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:55:29.280829+00:00
-- url     : https://prove2.me/submissions/709c31bc-4da3-45bc-bc18-1c3162aed794

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralCoordinateShearHaarLocalFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionUpperFreeEntryTranslationLaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.UpperLaw
open GlobalTheory.PartRed
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {ρ : ℕ} {I : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))}
namespace GlobalTheory.PartRed.UpperLaw
theorem _root_.solution (hI : I ⊆ transSet ρ ∪ upSet ρ) {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} (he : e ∈ I) :
    Free (ρ + 1) e := by
  rcases Finset.mem_union.1 (hI he) with h | h
  · simp only [transSet, Finset.mem_filter] at h
    exact h.2.1
  · simp only [upSet, Finset.mem_filter] at h
    obtain ⟨-, l, i, rfl, h1, -⟩ := h
    exact h1
end GlobalTheory.PartRed.UpperLaw
