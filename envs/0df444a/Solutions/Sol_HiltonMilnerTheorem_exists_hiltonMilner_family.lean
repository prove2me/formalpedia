-- Prove2me | solution 1 for HiltonMilnerTheorem.exists_hiltonMilner_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:29:47.405265+00:00
-- url     : https://prove2.me/submissions/9fd66ca5-eefa-4ce0-a59e-114ec29f7bdd

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_HiltonMilner
public import Definitions.Def_HiltonMilner_Solution
public import Theorems.Thm_HiltonMilner_exists_hiltonMilner_family


set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilnerTheorem
namespace HiltonMilnerTheorem
theorem _root_.solution {n k : ℕ} (hk : 2 ≤ k) (hkn : 2 * k < n) :
    ∃ 𝒜 : Finset (Finset (Fin n)), (𝒜 : Set (Finset (Fin n))).Intersecting ∧
      (𝒜 : Set (Finset (Fin n))).Sized k ∧ (∀ x : Fin n, ∃ A ∈ 𝒜, x ∉ A) ∧
      #𝒜 = (n - 1).choose (k - 1) - (n - k - 1).choose (k - 1) + 1 :=
  HiltonMilner.exists_hiltonMilner_family hk hkn
end HiltonMilnerTheorem
