-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.mem_chainLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:52.694807+00:00
-- url     : https://prove2.me/submissions/9465c2f4-d587-41d0-a224-620f2e4fbc53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice

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
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n]
namespace GlobalTheory.RootEx.UnfoldShape
namespace _root_.GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution {ϖ : 𝒪[k]} {L : Submodule 𝒪[k] (n → k)} {v : n ⊕ Fin c → k} :
    v ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.chainLat ϖ c L ↔
      (fun r => v (Sum.inl r)) ∈ L ∧ ∀ i : Fin c, ∃ a : 𝒪[k], v (Sum.inr i) = a * (ϖ : k) ^ (i.val + 1) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.chainLat
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
    refine ⟨?_, fun i => ⟨a i, ?_⟩⟩
    · simpa [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX, _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux, Finset.sum_apply,
        Pi.single_apply] using hw
    · simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX, _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux, Finset.sum_apply,
        Pi.single_apply, Subring.smul_def]
  · rintro ⟨hL, ha⟩
    choose a ha using ha
    refine ⟨_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX k n c (fun r => v (Sum.inl r)),
      Submodule.mem_map_of_mem hL,
      ∑ i, a i • ((ϖ : k) ^ (i.val + 1) • _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux k n i),
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
    funext r
    rcases r with r | i
    · simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX, _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux, Finset.sum_apply,
        Pi.single_apply]
    · simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.inX, _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.aux, Finset.sum_apply,
        Pi.single_apply, Subring.smul_def, ha i]
end _root_.GlobalTheory.RootEx.UnfoldShape
end GlobalTheory.RootEx.UnfoldShape
