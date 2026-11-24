-- Prove2me | solution 1 for GlobalTheory.RootEx.Supp.char_eq_one_of_opE_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:03:15.282803+00:00
-- url     : https://prove2.me/submissions/a4685a4f-07d0-4829-a64c-50f2ff854ca2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Supp
namespace GlobalTheory.RootEx.Supp
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c p : ℕ} (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
    (F : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) (hF : opE ψ ν p F x₀ ≠ 0)
    (d : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (hd : ∀ r s, ¬ Free p (r, s) → d r s = 0)
    (hFd : ∀ x, F (x + d) = F x) : ψ (ch d) = 1 := by
  classical
  haveI := secondCountable k
  unfold opE at hF
  set e₀ : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k := fun rs => d rs.1.1 rs.1.2
  have hadd : ∀ e, affPt p x₀ (e₀ + e) = affPt p x₀ e + d := by
    intro e
    ext r s
    simp only [affPt, Matrix.add_apply, Matrix.of_apply]
    split_ifs with h
    · simp [e₀]; ring
    · simp [hd r s h]
  have hch : ∀ x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k, ch (x + d) = ch x + ch d := by
    intro x; simp [ch, Finset.sum_add_distrib]
  have key := integral_add_left_eq_self (μ := Measure.pi fun _ => ν)
    (fun e => F (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ)) e₀
  simp only [hadd, hFd, hch, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, ← mul_assoc] at key
  rw [integral_mul_const] at key
  have h1 : (ψ (-ch d) : ℂ) = 1 := by
    apply mul_left_cancel₀ hF
    rw [mul_one]
    convert key
  have h2 : ψ (-ch d) = 1 := Circle.coe_eq_one.1 h1
  rwa [AddChar.map_neg_eq_inv, inv_eq_one] at h2
end GlobalTheory.RootEx.Supp
