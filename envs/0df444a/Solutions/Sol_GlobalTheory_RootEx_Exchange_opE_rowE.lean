-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.opE_rowE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:31:16.208904+00:00
-- url     : https://prove2.me/submissions/10718582-19be-40fe-9078-7822a7582175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Theorems.Thm_GlobalTheory_RootEx_Exchange_integral_shear
import Theorems.Thm_GlobalTheory_RootEx_Exchange_continuous_wittExtendByZero
import Theorems.Thm_GlobalTheory_RootEx_Exchange_mul_rowE
import Theorems.Thm_GlobalTheory_RootEx_Exchange_affPt_mul_rowE
import Theorems.Thm_GlobalTheory_RootEx_Exchange_om_rowE
import Theorems.Thm_GlobalTheory_RootEx_Exchange_continuous_mat
import Theorems.Thm_GlobalTheory_RootEx_Exchange_continuous_big
import Theorems.Thm_GlobalTheory_RootEx_Exchange_row_mul_rowE
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k]
open Classical
namespace GlobalTheory.RootEx.Exchange
theorem _root_.solution {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure]
    (μ : kˣ →* ℂˣ) (q : Fin c) {χ : (n' → k) → ℂ} (hχ : Continuous χ)
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Continuous Φ) (x₀ : Matrix n n' k) (u : n' → k) :
    χ u * opE ψ ν (q.val + 1) (om μ (rowE (c + 1) (q.val + 1) u) 1 Φ) x₀ =
      ∫ e, big ψ q χ Φ (mat x₀ (ext0 (Free (q.val + 1)) e + gRow q u)) ∂(Measure.pi fun _ => ν) := by
  haveI := t2Space k
  haveI := secondCountable k
  unfold opE
  rw [← integral_const_mul]
  refine Eq.trans ?_ (integral_shear ν (fun i => i.1.2.isLeft) (sRow q u) ?_ ?_ ?_
    (fun e => big ψ q χ Φ (mat x₀ (ext0 (Free (q.val + 1)) e + gRow q u)))
    ((continuous_big hψ q hχ hΦ).comp ((continuous_mat x₀).comp ((continuous_wittExtendByZero _).add continuous_const))))
  · congr 1
    funext e
    rw [← affPt_mul_rowE, big, row_mul_rowE, om_rowE, mul_assoc]
    congr 5
    unfold ch
    refine Finset.sum_congr rfl fun i _ => ?_
    have := mul_rowE q.castSucc u (affPt (q.val + 1) x₀ e) (Sum.inr i) (Sum.inr i.succ)
    rw [Fin.val_castSucc] at this
    rw [this]; simp
  · refine continuous_pi fun ⟨⟨r, s⟩, h⟩ => ?_
    rcases s with s | s
    · exact ((continuous_apply _).comp (continuous_wittExtendByZero _)).mul continuous_const
    · exact continuous_const
  · rintro e ⟨⟨r, s | s⟩, h⟩ hi
    · simp at hi
    · rfl
  · intro e e' h
    funext ⟨⟨r, s⟩, hi⟩
    rcases s with s | s
    · simp only [sRow, Sum.elim_inl, ext0]
      split_ifs with h1
      · rw [h ⟨_, h1⟩ (by simp)]
      · rfl
    · rfl
end GlobalTheory.RootEx.Exchange
