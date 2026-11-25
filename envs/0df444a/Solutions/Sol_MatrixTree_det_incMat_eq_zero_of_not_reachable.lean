-- Prove2me | solution 1 for MatrixTree.det_incMat_eq_zero_of_not_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:21:26.974009+00:00
-- url     : https://prove2.me/submissions/1c1117d2-63a6-47bc-bc1f-6a8c91faade6

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Theorems.Thm_MatrixTree_tl_ne_hd
public import Theorems.Thm_MatrixTree_mem_iff_tl_or_hd
public import Theorems.Thm_MatrixTree_inc_tl
public import Theorems.Thm_MatrixTree_inc_hd
public import Theorems.Thm_MatrixTree_inc_of_not_mem
public import Theorems.Thm_MatrixTree_fromEdgeSet_adj_tl_hd

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace MatrixTree
theorem _root_.solution (v : V) (g : {u // u ≠ v} → Sym2 V)
    (hg : ∀ w, ¬ (g w).IsDiag) (u : V) (hu : ¬ (fromEdgeSet (Set.range g)).Reachable v u) :
    (incMat v g).det = 0 := by
  set H := fromEdgeSet (Set.range g)
  have huv : u ≠ v := by rintro rfl; exact hu (Reachable.refl _)
  rw [← exists_vecMul_eq_zero_iff]
  refine ⟨fun x => if H.Reachable u x then 1 else 0, ?_, ?_⟩
  · intro hc
    have := congrFun hc ⟨u, huv⟩
    simp at this
  · ext w
    simp only [vecMul, dotProduct, incMat, of_apply, Pi.zero_apply, ite_mul, one_mul, zero_mul]
    have hadj := fromEdgeSet_adj_tl_hd v g hg w
    by_cases ha : H.Reachable u (tl (g w))
    · have hb : H.Reachable u (hd (g w)) := ha.trans hadj.reachable
      have hav : tl (g w) ≠ v := by rintro h; exact hu (h ▸ ha.symm)
      have hbv : hd (g w) ≠ v := by rintro h; exact hu (h ▸ hb.symm)
      rw [Fintype.sum_eq_add (⟨tl (g w), hav⟩ : {u // u ≠ v}) ⟨hd (g w), hbv⟩]
      · simp [ha, hb, inc_tl, inc_hd (hg w)]
      · intro h; exact tl_ne_hd (hg w) (congrArg Subtype.val h)
      · rintro ⟨x, hx⟩ ⟨h1, h2⟩
        have h1' : x ≠ tl (g w) := fun h => h1 (Subtype.ext h)
        have h2' : x ≠ hd (g w) := fun h => h2 (Subtype.ext h)
        rw [inc_of_not_mem (by rw [mem_iff_tl_or_hd]; tauto)]
        simp
    · refine Finset.sum_eq_zero fun x _ => ?_
      split_ifs with hx
      · apply inc_of_not_mem
        rw [mem_iff_tl_or_hd]
        rintro (h | h)
        · exact ha (h ▸ hx)
        · exact ha (hx.trans (h ▸ hadj.symm.reachable))
      · rfl
end MatrixTree
