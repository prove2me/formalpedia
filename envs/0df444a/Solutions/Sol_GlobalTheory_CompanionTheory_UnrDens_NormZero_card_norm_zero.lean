-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormZero.card_norm_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:26:28.184747+00:00
-- url     : https://prove2.me/submissions/1e7acb2c-6682-4a76-bc20-58838689f251

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormZero_exists_idem
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormZero_card_zero_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormZero
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
namespace GlobalTheory.CompanionTheory.UnrDens.NormZero
theorem _root_.solution : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε →
    (Nat.card {a : E // a * τ a = 0} : ℤ) = q * (1 + ε) - ε := by
  intro E _ τ q ε h
  rcases h.eps with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
  · haveI : IsDomain E := hf.isDomain
    have hu : ∀ a : {a : E // a * τ a = 0}, a = ⟨0, by simp⟩ := by
      rintro ⟨a, ha⟩
      apply Subtype.ext
      rcases mul_eq_zero.1 ha with h0 | h0
      · exact h0
      · have := h.inv a
        rw [h0, map_zero] at this
        exact this.symm
    have h1 : Nat.card {a : E // a * τ a = 0} = 1 := by
      haveI : Unique {a : E // a * τ a = 0} := ⟨⟨⟨0, by simp⟩⟩, hu⟩
      exact Nat.card_unique
    rw [h1]
    simp
  · obtain ⟨e, he, hτ⟩ := exists_idem h hf
    have h1 := card_zero_split h he hτ
    have h2 : (Nat.card {a : E // a * τ a = 0} : ℤ) + 1 = 2 * q := by exact_mod_cast h1
    linarith
end GlobalTheory.CompanionTheory.UnrDens.NormZero
