-- Prove2me | solution 1 for HurewiczSketchV2.cellular_hurewicz_isomorphism_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @loader3229
-- created : 2026-11-26T10:02:08.304071+00:00
-- url     : https://prove2.me/submissions/ea28d9af-897c-4b36-900d-8a315794dc7a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Category.TopCat.Basic
import Definitions.Def_HurewiczSketchV2
import Definitions.Def_SP4Homology
import Theorems.Thm_HurewiczSketchV2_exists_hurewicz_hom
import Theorems.Thm_HurewiczSketchV2_hurewicz_surjective_of_reduced_cw
import Theorems.Thm_HurewiczSketchV2_hurewicz_injective_of_reduced_cw

set_option autoImplicit false

open HurewiczSketchV2

/-- Hurewicz isomorphism via cellular comparison.

On a reduced CW model in degree `r = n+2`, the Hurewicz homomorphism `h : π_r → H_r`
exists (canonical map).  The `r`-cells generate both `π_r` and the cellular chain group
(so `h` is surjective), and the `(r+1)`-cells impose the same relations on both sides
(so `h` is injective).  A bijective additive homomorphism is an additive equivalence. -/
theorem solution (n : ℕ) (Y : TopCat) (y : Y)
    (hY : ReducedCWModel (n + 2) Y)
    (hH : ∀ i : ℕ, 0 < i → i < n + 2 → CategoryTheory.Limits.IsZero (SP4Homology.H i Y)) :
    Nonempty (Additive (HomotopyGroup.Pi (n + 2) Y y) ≃+ SP4Homology.H (n + 2) Y) := by
  obtain ⟨h⟩ := exists_hurewicz_hom n Y y
  exact ⟨AddEquiv.ofBijective h
    ⟨hurewicz_injective_of_reduced_cw n Y y hY hH h,
     hurewicz_surjective_of_reduced_cw n Y y hY hH h⟩⟩
