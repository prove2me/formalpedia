-- Prove2me | solution 1 for HurewiczSketchV2.cellular_reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @loader3229
-- created : 2026-11-26T09:01:36.681004+00:00
-- url     : https://prove2.me/submissions/7820f6bc-8dbf-4534-99e1-0e4b45878b7b
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
import Theorems.Thm_HurewiczSketchV2_cw_approximation_skeleton
import Theorems.Thm_HurewiczSketchV2_collapse_contractible_skeleton

set_option autoImplicit false

open HurewiczSketchV2

/-- Cellular reduction via Whitehead's theorem.

The CW approximation supplies a CW complex `Z` and its `(n+1)`-skeleton `A`.  The
skeleton has trivial homotopy in every degree (below `n+1` by cellular approximation
and the connectivity of `Z`, above `n+1` by dimension), hence is weakly contractible;
Whitehead's theorem makes `A` contractible.  Collapsing `A` yields the reduced CW model
`Y`, with the degree-`n+2` homotopy and homology carried over from `Z`. -/
theorem solution (n : ℕ) (X : Type) [TopologicalSpace X] (x : X)
    (hconn : ∀ k : ℕ, k ≤ n + 1 → Subsingleton (HomotopyGroup.Pi k X x)) :
    ∃ (Y : TopCat) (y : Y),
      ReducedCWModel (n + 2) Y ∧
        Nonempty (Additive (HomotopyGroup.Pi (n + 2) Y y) ≃+ Additive (HomotopyGroup.Pi (n + 2) X x)) ∧
        Nonempty (SP4Homology.H (n + 2) Y ≃+ SP4Homology.H (n + 2) X) := by
  obtain ⟨Z, z, A, a, hZcw, hAt2, hAcw, hZlow, hAlow, hAhigh, hπZX, hHZX⟩ :=
    cw_approximation_skeleton n X x hconn
  have hAweak : SP4WeakHomotopy.WeaklyContractible (A : Type) := by
    refine ⟨⟨a⟩, ?_⟩
    intro k y
    by_cases hk : k ≤ n + 1
    · exact hAlow k hk y
    · exact hAhigh k (by omega) y
  letI : T2Space (A : Type) := hAt2
  letI : Topology.CWComplex (Set.univ : Set (A : Type)) := Classical.choice hAcw
  letI : ContractibleSpace (A : Type) := SP4Mission.whitehead_contractible (A : Type) hAweak
  obtain ⟨Y, y, hYred, hπYZ, hHYZ⟩ :=
    collapse_contractible_skeleton n X x Z z A hZcw hZlow hπZX hHZX
  obtain ⟨eπYZ⟩ := hπYZ
  obtain ⟨eHYZ⟩ := hHYZ
  obtain ⟨eπZX⟩ := hπZX
  obtain ⟨eHZX⟩ := hHZX
  exact ⟨Y, y, hYred, ⟨eπYZ.trans eπZX⟩, ⟨eHYZ.trans eHZX⟩⟩
