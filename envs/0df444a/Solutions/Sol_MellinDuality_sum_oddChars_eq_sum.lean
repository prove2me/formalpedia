-- Prove2me | solution 1 for MellinDuality.sum_oddChars_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:53:55.110225+00:00
-- url     : https://prove2.me/submissions/b06bc3a8-7131-40c4-9b82-095deafd0364

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
public import Theorems.Thm_MellinDuality_apply_neg_one_sq

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (F : DirichletCharacter ℂ p → ℂ)
    (hF : ∀ ψ : DirichletCharacter ℂ p, ψ (-1) = 1 → F ψ = 0) :
    ∑ ψ ∈ oddChars p, F ψ = ∑ ψ, F ψ := by
  unfold oddChars
  refine sum_filter_of_ne fun ψ _ hψ => ?_
  have h : ψ (-1) * ψ (-1) = 1 := by rw [← sq]; exact apply_neg_one_sq ψ
  rcases mul_self_eq_one_iff.1 h with h | h
  · exact absurd (hF ψ h) hψ
  · exact h
end MellinDuality
