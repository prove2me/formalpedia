-- Prove2me | solution 1 for IsVLDisjoint.smul_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:30.961219+00:00
-- url     : https://prove2.me/submissions/a63e89a0-f382-4af7-897c-7c2deeb32092

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_P2M_abs_smul__56c684b926d9
public import Theorems.Thm_nonneg_smul_inf

section
@[expose] public section
open scoped Topology
open Filter Finset
section LatticeOrdered
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
end LatticeOrdered
section VectorLattice
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
private lemma disjoint_smul_nonneg {x y : X} (a : ℝ) (nonneg : 0 ≤ a)
    (h : x ⊓ y = 0) : (a • x) ⊓ y = 0 := by
  let aux (x y : X) (h : x ⊓ y = 0) (a : ℝ)
      (nonneg : 0 ≤ a) (hone : a ≤ 1) : (a • x) ⊓ y = 0 := by
    have xnonneg : 0 ≤ x := by rw [← h]; exact inf_le_left
    have ynonneg : 0 ≤ y := by rw [← h]; exact inf_le_right
    apply le_antisymm
    · calc
        a • x ⊓ y ≤ (1 : ℝ) • x ⊓ y := by
            apply inf_le_inf
            · exact smul_le_smul_of_nonneg_right hone xnonneg
            · exact le_refl y
          _ = 0 := by simp [h]
    · exact le_inf (smul_nonneg nonneg xnonneg) ynonneg
  have hbig (hone : ¬ a ≤ 1) : (a • x) ⊓ y = 0 := by
    push Not at hone
    suffices hsuf : x ⊓ (a⁻¹ • y) = 0 from by
      symm
      calc
        0 = a • ( x ⊓ (a⁻¹ • y) ):= by rw [hsuf, smul_zero]
        _ = (a • x ⊓ a • a⁻¹ • y) := nonneg_smul_inf x (a⁻¹ • y) a nonneg
        _ = (a • x) ⊓ y := by rw [smul_smul]; field_simp [hone]; simp
    rw [inf_comm]; rw [inf_comm] at h
    refine aux y x h a⁻¹ ?_ ?_
    · exact inv_nonneg.mpr nonneg
    · field_simp; exact le_of_lt hone
  by_cases hone : a ≤ 1
  · exact aux x y h a nonneg hone
  · exact hbig hone
end VectorLattice
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace IsVLDisjoint
theorem _root_.solution {x y : X} (h : IsVLDisjoint x y) (a : ℝ) :
    IsVLDisjoint (a • x) y := by
  change |a • x| ⊓ |y| = 0
  rw [abs_smul']
  exact disjoint_smul_nonneg (|a| : ℝ) (abs_nonneg a) h
end IsVLDisjoint
