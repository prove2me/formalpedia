-- Prove2me | solution 1 for N4Code.sum_sub_two_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:10.334139+00:00
-- url     : https://prove2.me/submissions/2e92c25b-ccdb-4505-975c-fbd1207e8cf2

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_sum_sub_two_pos

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (f g : Fin n → ℕ) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : f t₁ + 1 = g t₁) (h2 : f t₂ + 1 = g t₂)
    (hrest : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → f u = g u) :
    (∑ u : Fin n, f u) + 2 = (∑ u : Fin n, g u) := by
  have hpos : (∑ u : Fin n, g u) = (∑ u : Fin n, f u) + 2 := by
    apply sum_sub_two_pos g f t₁ t₂ htne
    · omega
    · omega
    · intro u hu1 hu2
      exact (hrest u hu1 hu2).symm
  omega
end N4Code
