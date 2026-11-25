-- Prove2me | solution 1 for HiltonMilnerTheorem.hilton_milner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:36:16.265452+00:00
-- url     : https://prove2.me/submissions/8651f597-4897-460d-a2a3-7d85a1b33a5d

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_HiltonMilner
public import Definitions.Def_HiltonMilner_Solution
public import Theorems.Thm_HiltonMilner_hilton_milner


set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilnerTheorem
namespace HiltonMilnerTheorem
theorem _root_.solution {n k : ℕ} (hk : 2 ≤ k) (hkn : 2 * k < n) {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting) (hs : (𝒜 : Set (Finset (Fin n))).Sized k)
    (hnt : ∀ x : Fin n, ∃ A ∈ 𝒜, x ∉ A) :
    #𝒜 ≤ (n - 1).choose (k - 1) - (n - k - 1).choose (k - 1) + 1 :=
  HiltonMilner.hilton_milner hk hkn h𝒜 hs hnt
end HiltonMilnerTheorem
