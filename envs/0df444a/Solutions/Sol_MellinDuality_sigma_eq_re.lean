-- Prove2me | solution 1 for MellinDuality.sigma_eq_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:54.995216+00:00
-- url     : https://prove2.me/submissions/3b793136-584c-4ba4-abc0-ae0cd24bb4c5

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
public import Theorems.Thm_MellinDuality_sigma_neg
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
attribute [local simp] MellinDuality.gi_im
attribute [local simp] MellinDuality.gi_re



set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt}
variable (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
include hp8 hχ
namespace MellinDuality
theorem _root_.solution {c : GaussianInt} (hc : c = 1 ∨ c = gi ∨ c = -1 ∨ c = -gi) :
    sigma χ c = (star c * gamma χ).re := by
  rcases hc with rfl | rfl | rfl | rfl
  · simp [gamma]
  · simp [gamma, gi]
  · rw [sigma_neg hp8 hχ one_ne_zero]; simp [gamma]
  · rw [sigma_neg hp8 hχ (by decide : gi ≠ 0)]; simp [gamma, gi]
end MellinDuality
