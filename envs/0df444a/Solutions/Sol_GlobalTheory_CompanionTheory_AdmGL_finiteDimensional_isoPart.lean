-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.finiteDimensional_isoPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:03:38.66416+00:00
-- url     : https://prove2.me/submissions/d253d6c0-3880-4e65-8caf-4bdde096e567

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDimensionalIsoPartOfSimple
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_isoPart_le_sup
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_finiteDimensional_isoPart_of_simple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdmGL
variable {K : Type} [Group K] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
namespace GlobalTheory.CompanionTheory.AdmGL
theorem _root_.solution {π : K →* (H →L[ℂ] H)} (hπ : ∀ k v, ‖π k v‖ = ‖v‖)
    (hadm : ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → (∀ k, ∀ w ∈ S, π k w ∈ S) →
      (∀ S' : Submodule ℂ H, S' ≤ S → (∀ k, ∀ w ∈ S', π k w ∈ S') → S' = ⊥ ∨ S' = S) →
      FiniteDimensional ℂ (sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧
        ∀ k, ∀ w ∈ S, T (π k w) = π k (T w)} : Submodule ℂ H))
    (d : ℕ) : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W),
      Module.finrank ℂ W = d → FiniteDimensional ℂ (isoPart π ρ) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro W _ _ _ ρ hd
  by_cases hs : ∀ W' : Submodule ℂ W, (∀ k, W' ≤ W'.comap (ρ k)) → W' = ⊥ ∨ W' = ⊤
  · exact finiteDimensional_isoPart_of_simple hadm ρ hs
  push Not at hs
  obtain ⟨W', hW, hbot, htop⟩ := hs
  have h1 : Module.finrank ℂ W' < d := hd ▸ Submodule.finrank_lt htop
  have h2 : Module.finrank ℂ (W ⧸ W') < d := by
    have hsum := Submodule.finrank_quotient_add_finrank W'
    have hpos : 0 < Module.finrank ℂ W' :=
      Nat.pos_of_ne_zero fun h => hbot (Submodule.finrank_eq_zero.1 h)
    omega
  have := ih _ h1 W' (ρ.subrepresentation W' hW) rfl
  have := ih _ h2 (W ⧸ W') (ρ.quotient W' hW) rfl
  exact Submodule.finiteDimensional_of_le (isoPart_le_sup hπ ρ W' hW)
end GlobalTheory.CompanionTheory.AdmGL
