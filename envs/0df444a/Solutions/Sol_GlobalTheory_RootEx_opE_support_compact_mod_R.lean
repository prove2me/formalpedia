-- Prove2me | solution 1 for GlobalTheory.RootEx.opE_support_compact_mod_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:32:57.166955+00:00
-- url     : https://prove2.me/submissions/26611d4b-827f-4fe2-9bcc-2d9455e2d864

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mul
import Theorems.Thm_GlobalTheory_RootEx_Supp_bd_of_mem_KO
import Theorems.Thm_GlobalTheory_RootEx_Supp_exists_bd_of_isCompact
import Theorems.Thm_GlobalTheory_RootEx_Supp_exists_bd_subset
import Theorems.Thm_GlobalTheory_RootEx_Supp_isCompact_bd
import Theorems.Thm_GlobalTheory_RootEx_Supp_exists_bd_of_char
import Theorems.Thm_GlobalTheory_RootEx_Supp_exists_embX_mul
import Theorems.Thm_GlobalTheory_RootEx_Supp_char_eq_one_of_opE_ne_zero
import Theorems.Thm_GlobalTheory_RootEx_Supp_inv_mul_affPt_apply
import Theorems.Thm_GlobalTheory_SplitWeil_iwasawa_blockTriangular


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
open GlobalTheory GlobalTheory.RootEx
open Supp
namespace GlobalTheory.RootEx
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (S : Set (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (_ : IsCompact S) (Λ : AddSubgroup (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (_ : IsOpen (Λ : Set (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))), ∃ Ω : Set (GL (n ⊕ Fin c) k), IsCompact Ω ∧ ∀ (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Function.support Φ ⊆ S → (∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x) → ∀ (χ : Matrix (n ⊕ Fin c) n' k → ℂ), IsLocallyConstant χ → ∀ (h : GL (n ⊕ Fin c) k) (x₀ : Matrix n n' k), opE ψ ν p (fun x => χ x.toCols₁ * om μ 1 h Φ x) x₀ ≠ 0 → ∃ r ∈ R k n c p, ∃ w ∈ Ω, h = r * w := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p _ _ ψ _ hψ ν _ S hS Λ hΛ
  obtain ⟨γ₁, hγ₁⟩ := exists_bd_of_isCompact hS
  obtain ⟨u, hu⟩ := exists_bd_subset Λ hΛ
  obtain ⟨γ₂, hγ₂⟩ := exists_bd_of_char ψ hψ u
  set γ : ValueGroupWithZero k := max 1 (max γ₁ γ₂) with hγ
  have g0 : 1 ≤ γ := le_max_left _ _
  have g1 : γ₁ ≤ γ := (le_max_left _ _).trans (le_max_right _ _)
  have g2 : γ₂ ≤ γ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨_, isCompact_bd (γ * γ), fun μ Φ hΦ hinv χ _ h x₀ hne => ?_⟩
  obtain ⟨b, hb', κ, hκ, rfl⟩ := iwasawa_blockTriangular k (n ⊕ Fin c)
    (Sum.elim (fun _ => 2 * p) (fun i => 2 * (i.val + 1) + 1)) h
  have hb : b.val.BlockTriangular (lev p) := by
    intro r s hrs
    apply hb'
    rcases r with r | r <;> rcases s with s | s <;> simp [lev] at hrs ⊢ <;> omega
  have hκ1 : Bd 1 κ.val := bd_of_mem_KO hκ
  have hκ2 : Bd 1 (κ⁻¹).val := bd_of_mem_KO (inv_mem hκ)
  have hdiag : ∀ i : Fin c, valuation k (b.val (Sum.inr i) (Sum.inr i)) ≤ γ₂ := by
    intro i
    refine hγ₂ _ fun t ht => ?_
    set E : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k := Matrix.single (Sum.inr i) (Sum.inr i.succ) t with hE
    have hEb : Bd (valuation k (u : k)) E := by
      intro r s
      simp only [hE, Matrix.single, Matrix.of_apply]
      split_ifs
      · exact ht
      · simp
    have hd : ∀ r s, (b.val * E) r s = if s = Sum.inr i.succ then b.val r (Sum.inr i) * t else 0 := by
      intro r s
      split_ifs with hs
      · rw [hs, hE, Matrix.mul_single_apply_same]
      · rw [hE, Matrix.mul_single_apply_of_ne _ _ _ _ _ hs]
    have := char_eq_one_of_opE_ne_zero ψ ν _ x₀ hne (b.val * E) ?_ ?_
    · have hc : ch (b.val * E) = b.val (Sum.inr i) (Sum.inr i) * t := by
        simp [ch, hd]
      rwa [hc] at this
    · intro r s hf
      rw [hd]
      split_ifs with hs
      · subst hs
        rw [hb (i := r) (j := Sum.inr i), zero_mul]
        rcases r with r | r <;> simp [lev, Free] at hf ⊢ <;> omega
      · rfl
    · intro x
      have e1 : (x + b.val * E).toCols₁ = x.toCols₁ := by
        ext r s
        simp [hd]
      have e2 : ((b * κ)⁻¹).val * (x + b.val * E) * (1 : GL (n' ⊕ Fin (c + 1)) k).val =
          ((b * κ)⁻¹).val * x * (1 : GL (n' ⊕ Fin (c + 1)) k).val + (κ⁻¹).val * E := by
        rw [Units.val_one, Matrix.mul_one, Matrix.mul_one, Matrix.mul_add, ← Matrix.mul_assoc, ← Units.val_mul,
          _root_.mul_inv_rev, inv_mul_cancel_right]
      have e3 : (κ⁻¹).val * E ∈ Λ := hu _ (by simpa using hκ2.mul hEb)
      simp only [om, e1, e2, hinv _ _ e3]
  obtain ⟨e, he⟩ : ∃ e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k,
      Φ (((b * κ)⁻¹).val * (affPt p x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    simp only [opE, om, Units.val_one, Matrix.mul_one, hcon, mul_zero, zero_mul, integral_zero]
  have hbx : Bd γ₁ ((b⁻¹).val * affPt p x₀ e) := by
    have := hκ1.mul (hγ₁ _ (hΦ he))
    rwa [one_mul, ← Matrix.mul_assoc, ← Units.val_mul, _root_.mul_inv_rev, mul_inv_cancel_left] at this
  have m0 : ∀ i s, (levi (lev p) b hb).val (Sum.inr i) (Sum.inl s) = 0 := by
    intro i s
    change (if _ then _ else _) = _
    split_ifs with hl
    · apply hb'
      simp [lev] at hl ⊢
      omega
    · rfl
  have m1 : ∀ i j, valuation k ((levi (lev p) b hb).val (Sum.inr i) (Sum.inr j)) ≤ γ := by
    intro i j
    change valuation k (if _ then _ else _) ≤ _
    split_ifs with hl
    · obtain rfl : i = j := Fin.ext (by simpa [lev] using hl)
      exact (hdiag i).trans g2
    · simp
  have m2 : ∀ r j, valuation k (((levi (lev p) b hb)⁻¹).val r (Sum.inr j)) ≤ γ := by
    intro r j
    change valuation k (if _ then _ else _) ≤ _
    split_ifs with hl
    · rw [← inv_mul_affPt_apply (inv_blockTriangular hb) x₀ e r j hl]
      exact (hbx _ _).trans g1
    · simp
  obtain ⟨x, w, hxw, hw1, hw2⟩ := exists_embX_mul (levi (lev p) b hb) (γ := γ) m0 g0 m1 m2
  · refine ⟨b * (levi (lev p) b hb)⁻¹ * embX c x, mul_mem (Subgroup.mem_sup_right (Subgroup.subset_closure ?_))
      (Subgroup.mem_sup_left ⟨x, rfl⟩), w * κ, ⟨?_, ?_⟩, ?_⟩
    · intro r s hrs
      change (b.val * diagPart (lev p) (b⁻¹).val) r s = _
      rw [mul_diagPart_apply hb (inv_blockTriangular hb) hrs, b.mul_inv]
    · simpa using hw1.mul hκ1
    · rw [_root_.mul_inv_rev, Units.val_mul]
      simpa using hκ2.mul hw2
    · rw [mul_assoc, ← mul_assoc (embX c x), ← hxw]
      group
end GlobalTheory.RootEx
