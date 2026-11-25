-- Prove2me | solution 1 for GlobalTheory.LocFlat.flRow_eq_opE_rowE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:11:44.815149+00:00
-- url     : https://prove2.me/submissions/ad64da8f-c057-4ad8-a808-39018afdc536

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowMapEqRootExchangeOperatorTranslate
import Theorems.Thm_GlobalTheory_RootEx_Exchange_affPt_eq
import Theorems.Thm_GlobalTheory_RootEx_Exchange_om_rowE
import Theorems.Thm_GlobalTheory_RootEx_Exchange_opE_rowE
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
open GlobalTheory.RootEx.Exchange
namespace GlobalTheory.LocFlat
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x : Matrix (n ⊕ Unit) n' k, GlobalTheory.LocFlat.flRow ψ ν p Φ x = opE ψ ν p (fun z => Φ (z * (rowE (c + 1) p (x (Sum.inr ()))).val)) x.toRows₁ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p hp hpc Φ hΦ x
  have := hν
  obtain ⟨q, rfl⟩ : ∃ q : Fin c, p = q.val + 1 := ⟨⟨p - 1, by omega⟩, by simp only; omega⟩
  have h := opE_rowE hψ ν 1 q (χ := fun _ => (1 : ℂ)) continuous_const hΦ.1.continuous x.toRows₁
    (x (Sum.inr ()))
  refine Eq.trans ?_ (h.symm.trans ?_)
  swap
  · rw [one_mul]
    congr 1
    funext z
    exact om_rowE _ _ _ _ _
  unfold flRow opE
  congr 1
  funext e
  have key : affPt (q.val + 1) x.toRows₁ e + rowAt n c (q.val + 1) (x (Sum.inr ())) =
      mat x.toRows₁ (ext0 (Free (q.val + 1)) e + gRow q (x (Sum.inr ()))) := by
    rw [affPt_eq]
    ext r s
    rcases r with r | r <;> rcases s with s | s <;>
      simp [mat, rowAt, gRow, Fin.val_inj, add_assoc]
  have hch : ch (mat x.toRows₁ (ext0 (Free (q.val + 1)) e + gRow q (x (Sum.inr ())))) =
      ch (affPt (q.val + 1) x.toRows₁ e) := by
    rw [affPt_eq]
    unfold ch
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mat, gRow]
  simp only [big]
  rw [key, hch, one_mul]
end GlobalTheory.LocFlat
