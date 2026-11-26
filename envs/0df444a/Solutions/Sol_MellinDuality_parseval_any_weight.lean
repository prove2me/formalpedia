-- Prove2me | solution 1 for MellinDuality.parseval_any_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:06:09.306719+00:00
-- url     : https://prove2.me/submissions/15b7fe6c-fc15-46fe-901f-e1c5ee1016cd

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_parseval_general


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (w : ℕ → ℤ) (hw : ∀ n, w n * w n = 1) :
    ∑ ψ : DirichletCharacter ℂ p,
        ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (w n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) * ((p - 1) / 2 : ℕ) :=
  parseval_general w hw
end MellinDuality
