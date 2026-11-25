-- Prove2me | solution 1 for KneserTheorem.lovasz_kneser
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:07:07.016147+00:00
-- url     : https://prove2.me/submissions/664b9bda-0a8d-43f5-aecb-28db5e1a0c4b

module
public import Mathlib
public import Definitions.Def_KneserLib_Kneser
public import Definitions.Def_KneserLovasz_Solution
public import Theorems.Thm_KneserColouring_lovasz_kneser


set_option autoImplicit true
@[expose] public section
public section
open KneserTheorem
namespace KneserTheorem
theorem _root_.solution {n k : ℕ} (hk : 0 < k) (hn : 2 * k ≤ n) :
    (kneserGraph n k).Colorable (n - 2 * k + 2) ∧
      ¬ (kneserGraph n k).Colorable (n - 2 * k + 1) :=
  KneserColouring.lovasz_kneser hk hn
end KneserTheorem
