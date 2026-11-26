-- Prove2me | solution 1 for MellinDuality.band_sum_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:05:39.920855+00:00
-- url     : https://prove2.me/submissions/5f45e627-e3fc-4f3c-9787-b723fc1ea917

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
public import Theorems.Thm_MellinDuality_bandSum_eq_Icc


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) :
    bandSumPow χ 2 = ∑ n ∈ Icc 1 ((p - 1) / 2), χ (n : ZMod p) * (eps p n : R) :=
  bandSum_eq_Icc hp2 χ
end MellinDuality
