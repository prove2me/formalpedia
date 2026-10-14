-- Prove2me | solution 1 for NegativeDP.Switching.InH_zero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:29:26.551863+00:00
-- url     : https://prove2.me/submissions/389fa79a-f0d5-4951-a399-dbb13ee2b0b1

import Mathlib
import Definitions.Def_NegativeDP_Switching_Model
open MeasureTheory ProbabilityTheory
open DiscountedDP.Stationary (Hist Plan MarkovPlan)


namespace NegativeDP.Switching

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

lemma cont_heq (P : Problem S A) (σ : Plan (S := S) (A := A)) (s : S) :
    ∀ k, HEq (contKernel P σ 0 k (Hist.start s)) (historyLaw P σ s k) := by
  have key : ∀ m k, m = k → ∀ (μ : Measure (Hist S A m)) (ν : Measure (Hist S A k)), HEq μ ν →
      HEq (μ.bind (stepKernel P σ m)) (ν.bind (stepKernel P σ k)) := by
    intro m k hmk μ ν h; subst hmk; rw [eq_of_heq h]
  intro k
  induction k with
  | zero => simp only [contKernel, historyLaw]; rw [Kernel.id_apply]
  | succ k ih =>
    simp only [contKernel, historyLaw]
    rw [Kernel.comp_apply]
    exact key _ _ (Nat.zero_add k) _ _ ih

lemma cont_eq_I (P : Problem S A) (σ : Plan (S := S) (A := A)) (s : S) :
    contReturn P σ 0 (Hist.start s) = I P σ s := by
  have key : ∀ m k, m = k → ∀ (μ : Measure (Hist S A m)) (ν : Measure (Hist S A k)), HEq μ ν →
      ∫⁻ h', stepLoss P σ m h' ∂μ = ∫⁻ h', stepLoss P σ k h' ∂ν := by
    intro m k hmk μ ν h; subst hmk; rw [eq_of_heq h]
  unfold contReturn I stageLoss
  congr 3
  funext k
  exact key _ _ (Nat.zero_add k) _ _ (cont_heq P σ s k)

lemma contReturn_nonpos (P : Problem S A) (σ : Plan (S := S) (A := A)) (n : ℕ) (h : Hist S A n) :
    contReturn P σ n h ≤ 0 := by
  unfold contReturn
  rw [EReal.neg_le, neg_zero]; exact EReal.coe_ennreal_nonneg _

theorem InH_zero_core (P : Problem S A) (σ τ π : Plan (S := S) (A := A)) (s : S) :
    InH P π 0 (wmax P σ τ 0) s = wmax P σ τ 0 (Hist.start s) ∧
    wmax P σ τ 0 (Hist.start s) = max (I P σ s) (I P τ s) := by
  refine ⟨?_, ?_⟩
  · unfold InH
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, historyLaw]
    have : MeasurableSingletonClass S := by
      letI := upgradeStandardBorel S; infer_instance
    have : MeasurableSingletonClass A := by
      letI := upgradeStandardBorel A; infer_instance
    have : MeasurableSingletonClass (Hist S A 0) := by
      have : MeasurableSingletonClass (S × A) := inferInstance
      exact Prod.instMeasurableSingletonClass
    rw [lintegral_dirac]
    have h0 : wmax P σ τ 0 (Hist.start s) ≤ 0 :=
      max_le (contReturn_nonpos _ _ _ _) (contReturn_nonpos _ _ _ _)
    generalize wmax P σ τ 0 (Hist.start s) = x at h0 ⊢
    rw [EReal.coe_toENNReal (by simpa using h0)]
    simp
  · unfold wmax; rw [cont_eq_I, cont_eq_I]

end NegativeDP.Switching

open NegativeDP.Switching


theorem solution {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (σ τ π : Plan (S := S) (A := A)) (s : S) :
    InH P π 0 (wmax P σ τ 0) s = wmax P σ τ 0 (Hist.start s) ∧
    wmax P σ τ 0 (Hist.start s) = max (I P σ s) (I P τ s) := by
  exact InH_zero_core P σ τ π s
