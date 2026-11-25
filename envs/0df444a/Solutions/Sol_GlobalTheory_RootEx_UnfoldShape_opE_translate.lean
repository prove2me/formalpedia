-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.opE_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:08:29.518774+00:00
-- url     : https://prove2.me/submissions/64f38c57-1663-4370-984e-d8b6dbc0567f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable

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
private theorem colMat_eq_zero_of_not_free [ValuativeRel k] {y : Fin c → (n ⊕ Fin c → k)}
    (hy : ∀ i, y i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Yle k n c (i.val + 1)) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (h : ¬ _root_.GlobalTheory.RootEx.Free 1 (r, s)) : _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y r s = 0 := by
  rcases s with s | j
  · simp [_root_.GlobalTheory.RootEx.UnfoldShape.colMat]
  · induction j using Fin.cases with
    | zero => simp [_root_.GlobalTheory.RootEx.UnfoldShape.colMat]
    | succ i =>
      simp only [_root_.GlobalTheory.RootEx.UnfoldShape.colMat, Matrix.of_apply, Sum.elim_inr, Fin.cases_succ]
      rcases r with r | l
      · exact absurd (by simp [_root_.GlobalTheory.RootEx.Free]) h
      · apply hy i l
        simp only [_root_.GlobalTheory.RootEx.Free, Fin.val_succ] at h
        omega
open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [ValuativeRel k] in
private theorem affPt_add_uncol [ValuativeRel k] (x₀ : Matrix n n' k) {y : Fin c → (n ⊕ Fin c → k)}
    (hy : ∀ i, y i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Yle k n c (i.val + 1))
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // _root_.GlobalTheory.RootEx.Free 1 rs} → k) :
    _root_.GlobalTheory.RootEx.affPt 1 x₀ (e + _root_.GlobalTheory.RootEx.UnfoldShape.uncol n' y) =
      _root_.GlobalTheory.RootEx.affPt 1 x₀ e + _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y := by
  unfold _root_.GlobalTheory.RootEx.affPt
  rw [add_assoc]
  congr 1
  ext r s
  by_cases h : _root_.GlobalTheory.RootEx.Free 1 (r, s)
  · simp [h, _root_.GlobalTheory.RootEx.UnfoldShape.uncol]
  · simp [h, colMat_eq_zero_of_not_free hy h]
open MeasureTheory ValuativeRel Matrix in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [ValuativeRel k] in
private theorem ch_add_colMat (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (y : Fin c → (n ⊕ Fin c → k)) :
    _root_.GlobalTheory.RootEx.ch (x + _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y) =
      _root_.GlobalTheory.RootEx.ch x + ∑ i, y i (Sum.inr i) := by
  simp [_root_.GlobalTheory.RootEx.ch, Finset.sum_add_distrib, _root_.GlobalTheory.RootEx.UnfoldShape.colMat]
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
theorem _root_.solution (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {y : Fin c → (n ⊕ Fin c → k)}
    (hy : ∀ i, y i ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Yle k n c (i.val + 1)) (hΨ : ∀ x, Ψ (x + _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y) = Ψ x)
    (x₀ : Matrix n n' k) :
    _root_.GlobalTheory.RootEx.opE ψ ν 1 Ψ x₀ = (ψ (-∑ i, y i (Sum.inr i)) : ℂ) * _root_.GlobalTheory.RootEx.opE ψ ν 1 Ψ x₀ := by
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  unfold _root_.GlobalTheory.RootEx.opE
  conv_lhs => rw [← integral_add_right_eq_self _ (_root_.GlobalTheory.RootEx.UnfoldShape.uncol n' y)]
  rw [← integral_const_mul]
  congr 1
  funext e
  rw [affPt_add_uncol x₀ hy, hΨ, ch_add_colMat, neg_add, AddChar.map_add_eq_mul,
    Circle.coe_mul]
  ring
end _root_.GlobalTheory.RootEx.UnfoldShape
end GlobalTheory.RootEx.UnfoldShape
