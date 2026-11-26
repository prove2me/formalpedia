-- Prove2me | solution 1 for HurewiczSketchV2.cellular_homology_vanish_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @loader3229
-- created : 2026-11-26T09:54:27.040684+00:00
-- url     : https://prove2.me/submissions/dcac32fa-a51c-43f8-ba34-39abe6c37060
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Homotopy.Contractible
import Definitions.Def_HurewiczSketchV2
import Definitions.Def_SP4Homology
import Definitions.Def_SP4WeakHomotopy
import Theorems.Thm_SP4Mission_whitehead_contractible
import Theorems.Thm_HurewiczSketchV2_low_skeleton_weakly_contractible
import Theorems.Thm_contractible_homology_vanish

set_option autoImplicit false

open HurewiczSketchV2

/-- Low-degree homology vanishing via Whitehead's theorem.

Let `Y` be a reduced CW model in degree `r = n+2`.  Its `(n+1)`-skeleton `A` is
weakly contractible (cellular approximation for degrees `≤ n+1`, dimension for
degrees `> n+1`).  Whitehead's theorem makes `A` contractible, hence its positive
singular homology vanishes; the relative cellular chain complex of `(Y,A)` then
transfers this vanishing to `Y` in every degree `0 < i < r`. -/
theorem solution (n : ℕ) (Y : TopCat) (hY : ReducedCWModel (n + 2) Y) :
    ∀ i : ℕ, 0 < i → i < n + 2 → CategoryTheory.Limits.IsZero (SP4Homology.H i Y) := by
  obtain ⟨A, a, hAt2, hAcw, hAweak, htransfer⟩ := low_skeleton_weakly_contractible n Y hY
  letI : T2Space (A : Type) := hAt2
  letI : Topology.CWComplex (Set.univ : Set (A : Type)) := Classical.choice hAcw
  have hAcontract : ContractibleSpace (A : Type) :=
    SP4Mission.whitehead_contractible (A : Type) hAweak
  letI : ContractibleSpace (A : Type) := hAcontract
  intro i hi0 hir
  exact htransfer i hi0 hir (contractible_homology_vanish A i hi0)
