-- Prove2me | solution 1 for MatrixTree.isUnit_det_incMat_of_isTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:30:36.623696+00:00
-- url     : https://prove2.me/submissions/88793088-ca18-4325-a648-7d1a75da4f16

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Theorems.Thm_MatrixTree_mem_iff_tl_or_hd
public import Theorems.Thm_MatrixTree_mem_of_inc_ne_zero
public import Theorems.Thm_MatrixTree_isUnit_inc
public import Theorems.Thm_MatrixTree_det_eq_prod_diag_of_lt
public import Theorems.Thm_MatrixTree_fromEdgeSet_adj_tl_hd

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace MatrixTree
theorem _root_.solution (v : V) (g : {u // u ≠ v} → Sym2 V)
    (hg : ∀ w, ¬ (g w).IsDiag) (hT : (fromEdgeSet (Set.range g)).IsTree) :
    IsUnit (incMat v g).det := by
  set H := fromEdgeSet (Set.range g)
  set d : V → ℕ := fun x => H.dist v x with hd_def
  have hadj := fromEdgeSet_adj_tl_hd v g hg
  have hne : ∀ w, d (tl (g w)) ≠ d (hd (g w)) := fun w => hT.dist_ne_of_adj v (hadj w)
  let low : {u // u ≠ v} → V := fun w =>
    if d (tl (g w)) < d (hd (g w)) then hd (g w) else tl (g w)
  have hlow : ∀ w, ∀ x ∈ g w, x = low w ∨ d x < d (low w) := by
    intro w x hx
    have := hne w
    rcases mem_iff_tl_or_hd.mp hx with rfl | rfl <;> simp only [low] <;> split_ifs <;>
      first | exact Or.inl rfl | (right; omega)
  have hlow_mem : ∀ w, low w ∈ g w := by
    intro w; simp only [low]; split_ifs
    · exact mem_iff_tl_or_hd.mpr (Or.inr rfl)
    · exact mem_iff_tl_or_hd.mpr (Or.inl rfl)
  have hlow_ne : ∀ w, low w ≠ v := by
    intro w h
    have := hne w
    have h0 : d v = 0 := dist_self
    simp only [low] at h
    split_ifs at h with hlt
    · rw [← h] at h0; omega
    · rw [← h] at h0; omega
  let lam : {u // u ≠ v} → {u // u ≠ v} := fun w => ⟨low w, hlow_ne w⟩
  have hsurj : Function.Surjective lam := by
    rintro ⟨x, hx⟩
    obtain ⟨p, hp⟩ := hT.connected.exists_walk_length_eq_dist x v
    cases p with
    | nil => exact absurd rfl hx
    | @cons _ y _ h q =>
      have hq := dist_le q
      have hdy : d y < d x := by
        simp only [hd_def, dist_comm (u := v)]
        rw [Walk.length_cons] at hp
        omega
      rw [fromEdgeSet_adj] at h
      obtain ⟨⟨w, hw⟩, -⟩ := h
      refine ⟨w, Subtype.ext ?_⟩
      have hx' : x ∈ g w := by rw [hw]; exact Sym2.mem_mk_left _ _
      have hy' : y ∈ g w := by rw [hw]; exact Sym2.mem_mk_right _ _
      rcases hlow w y hy' with h1 | h1
      · rcases hlow w x hx' with h2 | h2
        · exact h2.symm
        · rw [← h1] at h2; omega
      · rcases hlow w x hx' with h2 | h2
        · exact h2.symm
        · -- both endpoints differ from low w, impossible since low w ∈ {x, y}
          have hm := hlow_mem w
          rw [hw, Sym2.mem_iff] at hm
          rcases hm with hm | hm
          · rw [hm] at h2; omega
          · rw [hm] at h1; omega
  let π := Equiv.ofBijective lam ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  have hπ : ∀ x, low (π.symm x) = x.1 := fun x =>
    congrArg Subtype.val (π.apply_symm_apply x)
  have hdet := det_permute' π.symm (incMat v g)
  have hdiag := det_eq_prod_diag_of_lt ((incMat v g).submatrix id π.symm) (fun x => d x.1) (by
    intro u x hux
    simp only [submatrix_apply, id, incMat, of_apply] at hux
    rcases hlow _ _ (mem_of_inc_ne_zero hux) with h | h
    · left; exact Subtype.ext (h.trans (hπ x))
    · right; rw [hπ x] at h; exact h)
  have hunit : IsUnit ((incMat v g).submatrix id π.symm).det := by
    rw [hdiag]
    refine IsUnit.prod_iff.mpr fun x _ => ?_
    simp only [submatrix_apply, id, incMat, of_apply]
    apply isUnit_inc (hg _)
    rw [← hπ x]; exact hlow_mem _
  rw [hdet] at hunit
  exact (isUnit_of_mul_isUnit_right hunit)
end MatrixTree
