-- Prove2me | solution 1 for MellinDuality.re_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:53:58.18886+00:00
-- url     : https://prove2.me/submissions/1b1f2f31-e196-415b-a081-922f10996c76

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
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
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → GaussianInt) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [sum_cons, sum_cons, Zsqrtd.re_add, ih]
end MellinDuality
