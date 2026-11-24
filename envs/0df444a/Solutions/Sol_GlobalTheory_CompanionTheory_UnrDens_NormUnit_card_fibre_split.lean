-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:28:49.623038+00:00
-- url     : https://prove2.me/submissions/c91bfdb1-ca16-4e2a-b342-173709567837

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_card_fixed_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_fixed_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_exists_idem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormUnit
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
namespace GlobalTheory.CompanionTheory.UnrDens.NormUnit
theorem _root_.solution (h : ResAlg E τ q ε) (hnf : ¬ IsField E) {t : E} (ht : τ t = t)
    (t0 : t ≠ 0) : Nat.card {a : E // a * τ a = t} = q - 1 := by
  obtain ⟨e, he1, he0⟩ := exists_idem h hnf
  have hτe : τ (τ e) = e := h.inv e
  have hee : e * e = e := by linear_combination e * he1 - he0
  have hff : τ e * τ e = τ e := by linear_combination τ e * he1 - he0
  have hiso : ∀ α : E, ∃ s : E, τ α = α → α ≠ 0 → α * s = 1 ∧ τ s = s := by
    intro α
    by_cases hc : τ α = α ∧ α ≠ 0
    · obtain ⟨s, hs⟩ := (h.fixedUnit α hc.1 hc.2).exists_right_inv
      exact ⟨s, fun _ _ => ⟨hs, fixed_inv hc.1 hs⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose s hs using hiso
  have hfixA : ∀ a : E, τ (a * e + τ a * τ e) = a * e + τ a * τ e := by
    intro a
    simp only [map_add, map_mul, h.inv]
    ring
  have hneA : ∀ a : E, a * τ a = t → a * e + τ a * τ e ≠ 0 := by
    intro a ha hα
    apply t0
    have h1 : a * e = 0 := by linear_combination e * hα - a * hee - τ a * he0
    have h2 : τ a * τ e = 0 := by linear_combination τ e * hα - τ a * hff - a * he0
    linear_combination -ha + τ a * h1 + a * h2 - a * τ a * he1
  rw [← card_fixed_ne h]
  exact Nat.card_congr
    { toFun := fun a => ⟨a.1 * e + τ a.1 * τ e, hfixA a.1, hneA a.1 a.2⟩
      invFun := fun x => ⟨x.1 * e + t * s x.1 * τ e, by
        obtain ⟨hs1, hs2⟩ := hs x.1 x.2.1 x.2.2
        simp only [map_add, map_mul, x.2.1, ht, hs2, hτe]
        linear_combination (x.1 ^ 2 + t ^ 2 * s x.1 ^ 2) * he0 + x.1 * t * s x.1 * hee +
          x.1 * t * s x.1 * hff + x.1 * t * s x.1 * he1 + t * hs1⟩
      left_inv := fun a => by
        obtain ⟨hs1, -⟩ := hs _ (hfixA a.1) (hneA a.1 a.2)
        have ha := a.2
        apply Subtype.ext
        dsimp only
        linear_combination a.1 * hee + (τ a.1 - a.1 ^ 2 * s (a.1 * e + τ a.1 * τ e)) * he0 + a.1 * he1 -
          s (a.1 * e + τ a.1 * τ e) * τ e * ha + a.1 * τ e * hs1 -
          a.1 * τ a.1 * s (a.1 * e + τ a.1 * τ e) * hff
      right_inv := fun x => by
        obtain ⟨-, hs2⟩ := hs x.1 x.2.1 x.2.2
        apply Subtype.ext
        dsimp only
        simp only [map_add, map_mul, x.2.1, ht, hs2, hτe]
        linear_combination x.1 * hee + 2 * t * s x.1 * he0 + x.1 * hff + x.1 * he1 }
end GlobalTheory.CompanionTheory.UnrDens.NormUnit
