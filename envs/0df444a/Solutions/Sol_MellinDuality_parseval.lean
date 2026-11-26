-- Prove2me | solution 1 for MellinDuality.parseval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:37.65526+00:00
-- url     : https://prove2.me/submissions/905559b6-5ec3-4128-b11a-658b1e503905

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Parseval
public import Theorems.Thm_MellinDuality_parseval_general
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
namespace MellinDuality
theorem _root_.solution :
    ∑ ψ : DirichletCharacter ℂ p, ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (eps p n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) * ((p - 1) / 2 : ℕ) :=
  parseval_general (eps p) fun n => by
    unfold eps; rw [← pow_add, ← two_mul, pow_mul]; simp
end MellinDuality
