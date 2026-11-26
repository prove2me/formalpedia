-- Prove2me | solution 1 for MellinDuality.im_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:01.222855+00:00
-- url     : https://prove2.me/submissions/db086267-af55-4ede-adf2-12454d521895

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
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [sum_cons, sum_cons, Zsqrtd.im_add, ih]
end MellinDuality
