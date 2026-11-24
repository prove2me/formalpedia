-- Prove2me | solution 1 for GlobalTheory.RootEx.RowSign.opE_om_rowE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:31:17.652917+00:00
-- url     : https://prove2.me/submissions/30da79e4-34a4-4dfe-be2c-2b6e123e3be0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeOperatorWeilRowUnipotent
import Theorems.Thm_GlobalTheory_RootEx_RowSign_mat_add_gRow
import Theorems.Thm_GlobalTheory_RootEx_Exchange_affPt_eq
import Theorems.Thm_GlobalTheory_RootEx_Exchange_affPt_mul_rowE
import Theorems.Thm_GlobalTheory_RootEx_Exchange_continuous_mat
import Theorems.Thm_GlobalTheory_RootEx_Exchange_continuous_wittExtendByZero
import Theorems.Thm_GlobalTheory_RootEx_Exchange_integral_shear
import Theorems.Thm_GlobalTheory_RootEx_Exchange_om_rowE
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
namespace GlobalTheory.RootEx.RowSign
open GlobalTheory.RootEx.Exchange
private theorem ch_affPt_add_sRow {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] {c : ℕ} (q : Fin c) (u : n' → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    ch (affPt (q.val + 1) x₀ (e + sRow q u e)) = ch (affPt (q.val + 1) x₀ e) := by
  unfold ch
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [affPt, sRow]
end GlobalTheory.RootEx.RowSign
end
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.RowSign
open GlobalTheory.RootEx.Exchange
namespace GlobalTheory.RootEx.RowSign
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (u : n' → k) (x₀ : Matrix n n' k), opE ψ ν p (om μ (rowE (c + 1) p u) 1 Φ.1) x₀ = opE ψ ν p (fun x => Φ.1 (x + rowM n c p u)) x₀ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ hψ ν _ μ Φ u x₀
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨q, rfl⟩ : ∃ q : Fin c, q.val + 1 = p := ⟨⟨p - 1, by omega⟩, by show p - 1 + 1 = p; omega⟩
  have hΦ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  have hA : Continuous fun e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k =>
      affPt (q.val + 1) x₀ e :=
    ((continuous_mat x₀).comp (continuous_wittExtendByZero _)).congr fun e => (affPt_eq _ x₀ e).symm
  have hch : Continuous fun x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => ch x :=
    continuous_finsetSum _ fun i _ => continuous_id.matrix_elem _ _
  set f : ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) → ℂ := fun e =>
    Φ.1 (affPt (q.val + 1) x₀ e + rowM n c (q.val + 1) u) * (ψ (-ch (affPt (q.val + 1) x₀ e)) : ℂ) with hf_def
  have hf : Continuous f := by
    refine (hΦ.1.continuous.comp (hA.add continuous_const)).mul ?_
    exact continuous_subtype_val.comp (hψ.comp (hch.comp hA).neg)
  have hS : Continuous (sRow (n := n) (n' := n') q u) := by
    refine continuous_pi fun i => ?_
    rcases i with ⟨⟨r, s | s⟩, hi⟩
    · exact ((continuous_apply _).comp (continuous_wittExtendByZero _)).mul continuous_const
    · exact continuous_const
  have h0 : ∀ e (i : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs}),
      ¬ (∃ s, i.1.2 = Sum.inl s) → sRow q u e i = 0 := by
    rintro e ⟨⟨r, s | s⟩, hi⟩ h
    · exact absurd ⟨s, rfl⟩ h
    · rfl
  have h1 : ∀ e e' : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k,
      (∀ i, ¬ (∃ s, i.1.2 = Sum.inl s) → e i = e' i) → sRow q u e = sRow q u e' := by
    intro e e' he
    funext i
    rcases i with ⟨⟨r, s | s⟩, hi⟩
    · simp only [sRow, Sum.elim_inl]
      congr 1
      simp only [ext0]
      split_ifs with h
      · exact he _ (by simp)
      · rfl
    · rfl
  have hL : ∀ e, om μ (rowE (c + 1) (q.val + 1) u) 1 Φ.1 (affPt (q.val + 1) x₀ e) *
      (ψ (-ch (affPt (q.val + 1) x₀ e)) : ℂ) = f (e + sRow q u e) := by
    intro e
    rw [om_rowE, affPt_mul_rowE, mat_add_gRow, ← affPt_eq]
    simp only [hf_def, ch_affPt_add_sRow]
  unfold opE
  simp_rw [hL]
  exact integral_shear ν (fun i => ∃ s, i.1.2 = Sum.inl s) (sRow q u) hS h0 h1 f hf
end GlobalTheory.RootEx.RowSign
