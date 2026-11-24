-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.opE_colE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:31:38.202042+00:00
-- url     : https://prove2.me/submissions/cc61901f-aa3a-4aa4-bbcc-0fd33a976b04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Theorems.Thm_GlobalTheory_RootEx_Exchange_integral_shear
import Theorems.Thm_GlobalTheory_RootEx_Exchange_continuous_wittExtendByZero
import Theorems.Thm_GlobalTheory_RootEx_Exchange_colE_inv_mul
import Theorems.Thm_GlobalTheory_RootEx_Exchange_colE_inv_mul_affPt
import Theorems.Thm_GlobalTheory_RootEx_Exchange_om_colE
import Theorems.Thm_GlobalTheory_RootEx_Exchange_continuous_mat
import Theorems.Thm_GlobalTheory_RootEx_Exchange_continuous_big
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
    (μ : kˣ →* ℂˣ) (q q' : Fin c) {χ : (n' → k) → ℂ} (hχ : Continuous χ)
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Continuous Φ) (x₀ : Matrix n n' k) (β : n → k) :
    opE ψ ν (q'.val + 1) (fun x => χ (fun s => x (Sum.inr q) (Sum.inl s)) *
        om μ 1 (colE c (q'.val + 1) β) Φ x) x₀ =
      ∫ e, big ψ q χ Φ (mat x₀ (ext0 (Free (q'.val + 1)) e + gCol q' (-β))) ∂(Measure.pi fun _ => ν) := by
  haveI := t2Space k
  haveI := secondCountable k
  unfold opE
  refine Eq.trans ?_ (integral_shear ν (fun i => i.1.1.isLeft) (sCol q' β) ?_ ?_ ?_
    (fun e => big ψ q χ Φ (mat x₀ (ext0 (Free (q'.val + 1)) e + gCol q' (-β))))
    ((continuous_big hψ q hχ hΦ).comp ((continuous_mat x₀).comp ((continuous_wittExtendByZero _).add continuous_const))))
  · congr 1
    funext e
    rw [← colE_inv_mul_affPt, big]
    simp only [om_colE, ch, colE_inv_mul, Sum.elim_inr, Pi.zero_apply, add_zero]
  · refine continuous_pi fun ⟨⟨r, s⟩, h⟩ => ?_
    rcases r with r | r
    · exact (continuous_const.mul ((continuous_apply _).comp (continuous_wittExtendByZero _))).neg
    · exact continuous_const
  · rintro e ⟨⟨r | r, s⟩, h⟩ hi
    · simp at hi
    · rfl
  · intro e e' h
    funext ⟨⟨r, s⟩, hi⟩
    rcases r with r | r
    · simp only [sCol, Sum.elim_inl, ext0]
      split_ifs with h1
      · rw [h ⟨_, h1⟩ (by simp)]
      · rfl
    · rfl
end GlobalTheory.RootEx.Exchange
