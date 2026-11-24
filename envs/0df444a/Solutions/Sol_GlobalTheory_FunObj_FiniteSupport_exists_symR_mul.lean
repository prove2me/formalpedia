-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.exists_symR_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:50:15.87581+00:00
-- url     : https://prove2.me/submissions/698e2f6a-06fd-437e-937c-3801903c7eaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_midLev_lt_of_symLev_lt
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_mem_symN
import Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_mul_stepPt_apply
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mul
import Theorems.Thm_GlobalTheory_RootEx_Supp_bd_of_mem_KO
import Theorems.Thm_GlobalTheory_RootEx_Supp_exists_embX_mul
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul
import Theorems.Thm_GlobalTheory_SplitWeil_iwasawa_blockTriangular


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
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [Fintype n']
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution (hc : 1 ≤ c) (ψ : AddChar k Circle) {γ δ : ValueGroupWithZero k} (hγ : 1 ≤ γ)
    (hψ : ∀ a : k, (∀ t, valuation k t ≤ δ → ψ (a * t) = 1) → valuation k a ≤ γ)
    (h : GL (n ⊕ Fin c) k) (x₀ : Matrix n n' k) (e : StepVar n c n' → k)
    (h1 : Bd γ ((h⁻¹).val * stepPt x₀ e))
    (h2 : ∀ d : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k, (∀ r s, ¬ Free (c / 2 + 1) (r, s) → d r s = 0) →
      (∀ r s, d r (Sum.inl s) = 0) → Bd δ ((h⁻¹).val * d) → ψ (ch d) = 1) :
    ∃ r ∈ symR k n c, ∃ w : GL (n ⊕ Fin c) k, Bd (γ * γ) w.val ∧ Bd (γ * γ) (w⁻¹).val ∧ h = r * w := by
  obtain ⟨b, hb', κ, hκ, rfl⟩ := iwasawa_blockTriangular k (n ⊕ Fin c) (midLev (c / 2)) h
  have hb : b.val.BlockTriangular (symLev c) := fun r s hrs => hb' (midLev_lt_of_symLev_lt hrs)
  have hκ1 : Bd 1 κ.val := bd_of_mem_KO hκ
  have hκ2 : Bd 1 (κ⁻¹).val := bd_of_mem_KO (inv_mem hκ)
  have hdiag : ∀ i : Fin c, valuation k (b.val (Sum.inr i) (Sum.inr i)) ≤ γ := by
    intro i
    refine hψ _ fun t ht => ?_
    set E : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k := Matrix.single (Sum.inr i) (Sum.inr i.succ) t with hE
    have hEb : Bd δ E := by
      intro r s
      simp only [hE, Matrix.single, Matrix.of_apply]
      split_ifs
      · exact ht
      · simp
    have hd1 : ∀ r, (b.val * E) r (Sum.inr i.succ) = b.val r (Sum.inr i) * t := fun r => by
      rw [hE, Matrix.mul_single_apply_same]
    have hd2 : ∀ r s, s ≠ Sum.inr i.succ → (b.val * E) r s = 0 := fun r s hs => by
      rw [hE, Matrix.mul_single_apply_of_ne _ _ _ _ _ hs]
    have := h2 (b.val * E) ?_ (fun r s => hd2 _ _ (by simp)) ?_
    · have hc : ch (b.val * E) = b.val (Sum.inr i) (Sum.inr i) * t := by
        rw [ch, Finset.sum_eq_single i, hd1]
        · intro l _ hl; exact hd2 _ _ (by simpa using hl)
        · simp
      rwa [hc] at this
    · intro r s hf
      by_cases hs : s = Sum.inr i.succ
      · subst hs
        rw [hd1, hb' (i := r) (j := Sum.inr i), zero_mul]
        rcases r with r | r <;> simp [midLev, Free] at hf ⊢ <;> omega
      · exact hd2 r s hs
    · rw [← Matrix.mul_assoc, ← Units.val_mul, _root_.mul_inv_rev, inv_mul_cancel_right]
      simpa using hκ2.mul hEb
  have hbx : Bd γ ((b⁻¹).val * stepPt x₀ e) := by
    have := hκ1.mul h1
    rwa [one_mul, ← Matrix.mul_assoc, ← Units.val_mul, _root_.mul_inv_rev, mul_inv_cancel_left] at this
  have m0 : ∀ i s, (levi (symLev c) b hb).val (Sum.inr i) (Sum.inl s) = 0 := by
    intro i s
    change (if _ then _ else _) = _
    split_ifs with hl
    · apply hb'
      unfold symLev at hl
      split_ifs at hl <;> simp [lev, midLev] at hl ⊢ <;> omega
    · rfl
  have m1 : ∀ i j, valuation k ((levi (symLev c) b hb).val (Sum.inr i) (Sum.inr j)) ≤ γ := by
    intro i j
    change valuation k (if _ then _ else _) ≤ _
    split_ifs with hl
    · obtain rfl : i = j := Fin.ext (by
        unfold symLev at hl
        split_ifs at hl <;> simpa [lev, midLev] using hl)
      exact hdiag i
    · simp
  have m2 : ∀ r j, valuation k (((levi (symLev c) b hb)⁻¹).val r (Sum.inr j)) ≤ γ := by
    intro r j
    change valuation k (if _ then _ else _) ≤ _
    split_ifs with hl
    · rw [← mul_stepPt_apply (inv_blockTriangular hb') x₀ e r j hl]
      exact hbx _ _
    · simp
  obtain ⟨x, w, hxw, hw1, hw2⟩ := exists_embX_mul (levi (symLev c) b hb) (γ := γ) m0 hγ m1 m2
  refine ⟨b * (levi (symLev c) b hb)⁻¹ * embX c x, mul_mem (Subgroup.mem_sup_right (mem_symN hc ?_))
      (Subgroup.mem_sup_left ⟨x, rfl⟩), w * κ, ?_, ?_, ?_⟩
  · intro r s hrs
    change (b.val * diagPart (symLev c) (b⁻¹).val) r s = _
    rw [mul_diagPart_apply hb (inv_blockTriangular hb) hrs, b.mul_inv]
  · simpa using hw1.mul hκ1
  · rw [_root_.mul_inv_rev, Units.val_mul]
    simpa using hκ2.mul hw2
  · rw [mul_assoc, ← mul_assoc (embX c x), ← hxw]
    group
end GlobalTheory.FunObj.FiniteSupport
