-- Prove2me | solution 1 for KneserColouring.kLab_noComp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:00:24.195291+00:00
-- url     : https://prove2.me/submissions/b868035e-c8f3-430a-b2a3-0f8ade6a3b06

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel
public import Theorems.Thm_KneserColouring_maxCol_mono
public import Theorems.Thm_KneserColouring_maxCol_ne_of_disjoint
public import Theorems.Thm_KneserColouring_disjoint_posPart_negPart
public import Theorems.Thm_KneserColouring_one_le_maxCol_of_large
public import Theorems.Thm_KneserColouring_posPart_mono
public import Theorems.Thm_KneserColouring_negPart_mono
public import Theorems.Thm_KneserColouring_suppCard_mono
public import Theorems.Thm_KneserColouring_eq_of_suppCard_eq
public import Theorems.Thm_KneserColouring_abs_kLab_small
public import Theorems.Thm_KneserColouring_kLab_large_bound
public import Theorems.Thm_KneserColouring_kLab_ne_zero_and_le

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}
namespace KneserColouring
theorem _root_.solution (c : {s : Finset (Fin n) // s.card = k} → Fin q)
    (hc : ∀ s t, s ≠ t → Disjoint s.1 t.1 → c s ≠ c t) (hk : 0 < k)
    {x y : Fin n → SignType} (hx : x ≠ 0) (hxy : ∀ i, x i ≠ 0 → x i = y i) :
    kLab c x ≠ -kLab c y := by
  intro heq
  have hx0 := (kLab_ne_zero_and_le c hk hx).1
  have habs : |kLab c x| = |kLab c y| := by rw [heq, abs_neg]
  have hsxy := suppCard_mono hxy
  by_cases hsx : suppCard x ≤ 2 * k - 2
  · by_cases hsy : suppCard y ≤ 2 * k - 2
    · rw [abs_kLab_small c hsx, abs_kLab_small c hsy] at habs
      have hxy' := eq_of_suppCard_eq hxy (by exact_mod_cast habs)
      subst hxy'
      omega
    · have h1 := abs_kLab_small c hsx
      have h2 := kLab_large_bound c hk hsy
      omega
  · by_cases hsy : suppCard y ≤ 2 * k - 2
    · omega
    · have hmax := one_le_maxCol_of_large c hk hsx
      have hp := maxCol_mono c (posPart_mono hxy)
      have hn := maxCol_mono c (negPart_mono hxy)
      unfold kLab at heq
      rw [if_neg hsx, if_neg hsy] at heq
      split_ifs at heq with h1 h2 h2
      · omega
      · have he : maxCol c (posPart x) = maxCol c (negPart y) := by omega
        exact maxCol_ne_of_disjoint c hc hk
          (disjoint_of_subset_left (posPart_mono hxy) (disjoint_posPart_negPart y))
          (by omega) he
      · have he : maxCol c (negPart x) = maxCol c (posPart y) := by omega
        exact maxCol_ne_of_disjoint c hc hk
          (disjoint_of_subset_left (negPart_mono hxy) (disjoint_posPart_negPart y).symm)
          (by omega) he
      · omega
end KneserColouring
