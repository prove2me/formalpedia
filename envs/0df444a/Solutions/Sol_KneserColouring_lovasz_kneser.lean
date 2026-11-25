-- Prove2me | solution 1 for KneserColouring.lovasz_kneser
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:03:52.558903+00:00
-- url     : https://prove2.me/submissions/4fce48c2-d190-4ebf-ade0-8a51f5dfabb8

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerMain
public import Definitions.Def_KneserLib_KneserLabel
public import Definitions.Def_KneserLib_Kneser
public import Theorems.Thm_KneserColouring_octahedral_tucker
public import Theorems.Thm_KneserColouring_kLab_ne_zero_and_le
public import Theorems.Thm_KneserColouring_kLab_neg
public import Theorems.Thm_KneserColouring_kLab_noComp
public import Theorems.Thm_KneserColouring_upperCol_proper


set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
namespace KneserColouring
theorem _root_.solution {n k : ℕ} (hk : 0 < k) (hn : 2 * k ≤ n) :
    (kneserGraph n k).Colorable (n - 2 * k + 2) ∧
      ¬ (kneserGraph n k).Colorable (n - 2 * k + 1) := by
  refine ⟨⟨SimpleGraph.Coloring.mk (upperCol hk) ?_⟩, ?_⟩
  · intro s t hadj
    exact upperCol_proper hk hn s t hadj.2
  · rintro ⟨C⟩
    have hc : ∀ s t, s ≠ t → Disjoint s.1 t.1 → C s ≠ C t :=
      fun s t hne hd => C.valid ⟨hne, hd⟩
    obtain ⟨x, y, hx, hxy, heq⟩ := octahedral_tucker (m := 2 * k - 2 + (n - 2 * k + 1))
      (kLab C) (fun x hx => kLab_ne_zero_and_le C hk hx) (fun x hx => kLab_neg C hc hk hx)
      (by omega)
    exact kLab_noComp C hc hk hx hxy heq
end KneserColouring
