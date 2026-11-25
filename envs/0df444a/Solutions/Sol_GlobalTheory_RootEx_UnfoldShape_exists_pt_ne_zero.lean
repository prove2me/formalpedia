-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.exists_pt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:06:27.688996+00:00
-- url     : https://prove2.me/submissions/c45d1322-3457-42db-b82b-bc18616db21a

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
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
namespace GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
variable {k : Type} [Field k] [ValuativeRel k]
section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
section
omit [ValuativeRel k] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
end
section
omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
end
section
omit [ValuativeRel k] [Fintype n] [DecidableEq n] [DecidableEq n']
end
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [ValuativeRel k] in
private theorem affPt_eq_pt_col (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // _root_.GlobalTheory.RootEx.Free 1 rs} → k) :
    _root_.GlobalTheory.RootEx.affPt 1 x₀ e = _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.pt x₀ (_root_.GlobalTheory.RootEx.UnfoldShape.col e) := by
  unfold _root_.GlobalTheory.RootEx.affPt _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.pt
  congr 1
  ext r s
  rcases s with s | j
  · rcases r with r | l <;> simp [_root_.GlobalTheory.RootEx.Free]
  · refine Fin.cases ?_ (fun i => ?_) j
    · rcases r with r | l <;> simp [_root_.GlobalTheory.RootEx.Free]
    · by_cases h : _root_.GlobalTheory.RootEx.Free (n' := n') 1 (r, Sum.inr i.succ) <;>
        simp [_root_.GlobalTheory.RootEx.UnfoldShape.col, h]
open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [ValuativeRel k] in
private theorem col_mem_Yle' [ValuativeRel k]
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // _root_.GlobalTheory.RootEx.Free 1 rs} → k) (i : Fin c) :
    _root_.GlobalTheory.RootEx.UnfoldShape.col e i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Yle k n c (i.val + 1) := by
  intro l hl
  simp only [_root_.GlobalTheory.RootEx.UnfoldShape.col]
  rw [dif_neg]
  simp only [_root_.GlobalTheory.RootEx.Free, Fin.val_succ]
  omega
end GlobalTheory.RootEx.UnfoldShape
end
end

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
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.RootEx.UnfoldShape
namespace _root_.GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution {ψ : AddChar k Circle} {ν : Measure k}
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {x₀ : Matrix n n' k} (h : _root_.GlobalTheory.RootEx.opE ψ ν 1 Ψ x₀ ≠ 0) :
    ∃ y : Fin c → (n ⊕ Fin c → k), (∀ i, y i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Yle k n c (i.val + 1)) ∧
      Ψ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.pt x₀ y) ≠ 0 := by
  by_contra hne
  push_neg at hne
  apply h
  have hzero : ∀ e, Ψ (_root_.GlobalTheory.RootEx.affPt 1 x₀ e) = 0 := fun e => by
    rw [affPt_eq_pt_col]
    exact hne _ fun i => col_mem_Yle' e i
  unfold _root_.GlobalTheory.RootEx.opE
  simp [hzero]
end _root_.GlobalTheory.RootEx.UnfoldShape
end GlobalTheory.RootEx.UnfoldShape
