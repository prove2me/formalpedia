-- Prove2me | solution 1 for LatticeSeminorm.isSolid_of_mem_basisSets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:19:01.575356+00:00
-- url     : https://prove2.me/submissions/5220cf75-22fd-450c-95e1-c598d00c5ced

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LatticeSeminorm
section
@[expose] public section
open scoped Topology Pointwise
universe u v
namespace LatticeSeminorm
variable {E : Type u} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E]
private lemma finset_sup_mono_abs {ι : Type v} (p : ι → LatticeSeminorm E) (I : Finset ι)
    {x y : E} (hxy : |x| ≤ |y|) :
    I.sup (toSeminormFamily p) x ≤ I.sup (toSeminormFamily p) y := by
  refine Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi => ?_
  exact (p i).monotone_abs' hxy |>.trans
    (Seminorm.le_finset_sup_apply (p := toSeminormFamily p) (s := I) (x := y) hi)
end LatticeSeminorm
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology Pointwise
universe u v
open LatticeSeminorm
variable {E : Type u} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E]
namespace LatticeSeminorm
theorem _root_.solution {ι : Type v} (p : ι → LatticeSeminorm E) {s : Set E}
    (hs : s ∈ (toSeminormFamily p).basisSets) : LatticeOrderedAddCommGroup.IsSolid s := by
  rcases (SeminormFamily.basisSets_iff (p := toSeminormFamily p)).mp hs with ⟨I, r, hr, rfl⟩
  intro x hx y hy
  rw [Seminorm.mem_ball_zero] at hx ⊢
  exact (finset_sup_mono_abs p I hy).trans_lt hx
end LatticeSeminorm
