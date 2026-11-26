-- Prove2me | solution 1 for MellinDuality.parseval_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:06:07.987764+00:00
-- url     : https://prove2.me/submissions/c58d9898-765b-4885-87d2-04fde36fd12d

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_parseval


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
  parseval
end MellinDuality
