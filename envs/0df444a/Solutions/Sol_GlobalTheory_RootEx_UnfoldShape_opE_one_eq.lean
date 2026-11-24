-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.opE_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:35:46.188462+00:00
-- url     : https://prove2.me/submissions/bf64e598-9fae-4b7d-9a85-c3303a282576

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_affPt_eq_pt
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_ch_pt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
variable {k : Type} [Field k] [ValuativeRel k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
open Classical
namespace GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution (ψ : AddChar k Circle) (ν : Measure k) (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x₀ : Matrix n n' k) :
    opE ψ ν 1 Ψ x₀ = ∫ e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k,
      Ψ (pt x₀ (col e)) * (ψ (-∑ i, col e i (Sum.inr i)) : ℂ) ∂(Measure.pi fun _ => ν) := by
  simp only [opE, affPt_eq_pt, ch_pt]
end GlobalTheory.RootEx.UnfoldShape
