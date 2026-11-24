-- Prove2me | solution 1 for GlobalTheory.RootEx.Supp.exists_embX_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:17:50.100985+00:00
-- url     : https://prove2.me/submissions/2b1f9e93-8b6f-4ad5-884a-9031b0404962

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mul
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mono
import Theorems.Thm_GlobalTheory_RootEx_Supp_bd_one
import Theorems.Thm_GlobalTheory_RootEx_Supp_bd_zero
import Theorems.Thm_GlobalTheory_RootEx_Supp_bd_fromBlocks

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
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (m : GL (n ⊕ Fin c) k) (h0 : ∀ i s, m.val (Sum.inr i) (Sum.inl s) = 0) {γ : ValueGroupWithZero k}
    (hγ : 1 ≤ γ) (h1 : ∀ i j, valuation k (m.val (Sum.inr i) (Sum.inr j)) ≤ γ)
    (h2 : ∀ r j, valuation k ((m⁻¹).val r (Sum.inr j)) ≤ γ) :
    ∃ (x : GL n k) (w : GL (n ⊕ Fin c) k), m = embX c x * w ∧ Bd (γ * γ) w.val ∧ Bd (γ * γ) (w⁻¹).val := by
  obtain ⟨m, m', hm, hm'⟩ := m
  change ∀ r j, valuation k (m' r (Sum.inr j)) ≤ γ at h2
  dsimp only at h0 h1
  obtain ⟨a, B, C, t, rfl⟩ : ∃ a B C t, m = fromBlocks a B C t := ⟨_, _, _, _, (fromBlocks_toBlocks m).symm⟩
  obtain ⟨a', B', C', t', rfl⟩ : ∃ a B C t, m' = fromBlocks a B C t :=
    ⟨_, _, _, _, (fromBlocks_toBlocks m').symm⟩
  obtain rfl : C = 0 := by ext i s; exact h0 i s
  have hm2 := hm
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hm2
  obtain ⟨e1, e2, e3, e4⟩ := hm2
  simp only [Matrix.zero_mul, zero_add] at e3 e4
  have e5 : t' * t = 1 := mul_eq_one_comm.1 e4
  obtain rfl : C' = 0 := by rw [← Matrix.one_mul C', ← e5, Matrix.mul_assoc, e3, Matrix.mul_zero]
  simp only [Matrix.mul_zero, add_zero] at e1
  have hγ2 : γ ≤ γ * γ := le_mul_of_one_le_left' hγ
  have ht : Bd γ t := fun i j => h1 i j
  have ht' : Bd γ t' := fun i j => h2 (Sum.inr i) j
  have hB' : Bd γ B' := fun i j => h2 (Sum.inl i) j
  refine ⟨⟨a, a', e1, mul_eq_one_comm.1 e1⟩, ⟨fromBlocks 1 (-(B' * t)) 0 t, fromBlocks 1 B' 0 t', ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · simp [fromBlocks_multiply, Matrix.mul_assoc, e4]
  · simp [fromBlocks_multiply, e5]
  · ext1
    change fromBlocks a B 0 t = fromBlocks a 0 0 1 * fromBlocks 1 (-(B' * t)) 0 t
    have : a * (B' * t) = -B := by
      rw [← Matrix.mul_assoc, eq_neg_of_add_eq_zero_left e2, Matrix.neg_mul, Matrix.mul_assoc, e5, Matrix.mul_one]
    simp [fromBlocks_multiply, this]
  · refine bd_fromBlocks (bd_one.mono (hγ.trans hγ2)) ?_ (bd_zero _) (ht.mono hγ2)
    intro r s
    rw [Matrix.neg_apply, Valuation.map_neg]
    exact hB'.mul ht r s
  · exact bd_fromBlocks (bd_one.mono (hγ.trans hγ2)) (hB'.mono hγ2) (bd_zero _) (ht'.mono hγ2)
end GlobalTheory.RootEx.Supp
