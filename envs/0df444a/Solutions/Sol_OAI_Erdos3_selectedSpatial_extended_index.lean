-- Prove2me | solution 1 for OAI.Erdos3.selectedSpatial_extended_index
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:08:51.467869+00:00
-- url     : https://prove2.me/submissions/100cd74b-20d8-418e-aa29-f7ecd5791b91

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped Matrix ENNReal

end Erdos3

end

section

namespace Erdos3

theorem residueLatticeImage_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L m).toAddSubgroup.index = L.toAddSubgroup.index := by
  have hk : (integerResidueMap I m).toAddMonoidHom.ker ≤ L.toAddSubgroup := by
    change (LinearMap.ker (integerResidueMap I m)).toAddSubgroup ≤ L.toAddSubgroup
    rw [integerResidueMap_ker]
    exact hperiod
  have h := L.toAddSubgroup.index_map_eq (integerResidueMap_surjective I m) hk
  change (L.toAddSubgroup.map (integerResidueMap I m).toAddMonoidHom).index = _
  exact h

theorem residueLatticeImage_card_mul_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = m ^ Fintype.card I := by
  classical
  have h := (residueLatticeImage L m).toAddSubgroup.card_mul_index
  rw [residueLatticeImage_index L m hperiod] at h
  change Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = Nat.card (I → ZMod m) at h
  have heq : Nat.card (I → ZMod m) = m ^ Fintype.card I := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  exact h.trans heq

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

theorem residueLatticeImage_index_le {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    L.toAddSubgroup.index ≤ m ^ Fintype.card I := by
  have h := residueLatticeImage_card_mul_index L m hperiod
  have hpos := Nat.card_pos (α := residueLatticeImage L m)
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI

namespace Erdos3

theorem hasBoundedScalarPeriod_index_le {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (B : ℕ) (h : HasBoundedScalarPeriod L B) :
    L.toAddSubgroup.index ≤ B ^ Fintype.card I := by
  obtain ⟨a, ha, haB, hperiod⟩ := h
  let : NeZero a := ⟨ha.ne'⟩
  exact (residueLatticeImage_index_le L a hperiod).trans (Nat.pow_le_pow_left haB _)

end Erdos3

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RootDifferenceMatrix
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem rootDifferenceMatrix_mulVec {I J R : Type*} [Fintype J] [CommRing R]
    (root : J → R) (D : Matrix I J R) (x : R) (v : J → R) :
    rootDifferenceMatrix root D *ᵥ Sum.elim (fun _ : Unit => x) v =
      Sum.elim (fun _ : Unit => x + ∑ j, root j * v j) (D *ᵥ v) := by
  funext i
  cases i with
  | inl i =>
    cases i
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, rootDifferenceMatrix, Matrix.fromBlocks]
  | inr i => simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, rootDifferenceMatrix, Matrix.fromBlocks]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RootDifferencePeriod
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem rootDifferenceMatrix_period {I J : Type*} [Fintype I] [Fintype J]
    (root : J → ℤ) (D : Matrix I J ℤ) (a : ℤ)
    (hperiod : integerScalarLattice I a ≤ D.mulVecLin.range) :
    integerScalarLattice (Unit ⊕ I) a ≤ (rootDifferenceMatrix root D).mulVecLin.range := by
  rintro y ⟨z, rfl⟩
  have hz : a • (fun i => z (Sum.inr i)) ∈ integerScalarLattice I a :=
    ⟨fun i => z (Sum.inr i), rfl⟩
  obtain ⟨v, hv⟩ := hperiod hz
  refine ⟨Sum.elim (fun _ : Unit => a * z (Sum.inl ()) - ∑ j, root j * v j) v, ?_⟩
  change rootDifferenceMatrix root D *ᵥ _ = a • z
  rw [rootDifferenceMatrix_mulVec]
  funext i
  cases i with
  | inl i => cases i; simp
  | inr i => exact congrFun hv i

theorem rootDifferenceMatrix_bounded_period {I J : Type*} [Fintype I] [Fintype J]
    (root : J → ℤ) (D : Matrix I J ℤ) {B : ℕ}
    (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B) :
    HasBoundedScalarPeriod (rootDifferenceMatrix root D).mulVecLin.range B := by
  obtain ⟨a, ha, haB, hp⟩ := hperiod
  exact ⟨a, ha, haB, rootDifferenceMatrix_period root D (a : ℤ) hp⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialPivotNormalization
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem selectedSpatial_fromCols {I J R : Type*} [Fintype I] [CommRing R]
    (root : J → R) (D : Matrix I J R) (s : I ↪ J) :
    Matrix.fromCols (selectedSpatialPivot root D s) (selectedSpatialFreeColumns root D s) =
      (rootDifferenceMatrix root D).submatrix id (selectedSpatialColumnEquiv s) := by
  ext i j
  cases j with
  | inl j => cases j <;> cases i <;> rfl
  | inr j => cases i <;> rfl

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI

namespace Erdos3

open scoped BigOperators Matrix Classical

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open scoped Matrix

theorem integerMatrix_fromCols_range {I J N : Type*} [Fintype J] [Fintype N]
    (B : Matrix I J ℤ) (C : Matrix I N ℤ) :
    (Matrix.fromCols B C).mulVecLin.range = B.mulVecLin.range ⊔ C.mulVecLin.range := by
  ext v
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨B *ᵥ (fun j => x (.inl j)), ⟨_, rfl⟩,
      C *ᵥ (fun n => x (.inr n)), ⟨_, rfl⟩, ?_⟩
    exact (Matrix.fromCols_mulVec B C x).symm.trans hx
  · rintro ⟨b, ⟨x, rfl⟩, c, ⟨y, rfl⟩, h⟩
    refine ⟨Sum.elim x y, ?_⟩
    change Matrix.fromCols B C *ᵥ Sum.elim x y = v
    rw [Matrix.fromCols_mulVec_sumElim]
    exact h

theorem pivotFullImage_eq_range {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) :
    pivotFullImage A B = (Matrix.fromCols A B).mulVecLin.range :=
  (integerMatrix_fromCols_range A B).symm

theorem pivotFullImage_split {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C : Matrix I N ℤ) :
    pivotFullImage A (Matrix.fromCols B C) = pivotFullImage A B ⊔ C.mulVecLin.range := by
  unfold pivotFullImage
  rw [integerMatrix_fromCols_range, sup_assoc]

end Erdos3

namespace Erdos3

open scoped Matrix Classical

end Erdos3

namespace Erdos3

open scoped Classical

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

end Erdos3

namespace Erdos3

open scoped NNReal Matrix

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarSpatialScaleBounds
namespace OAI

namespace Erdos3

theorem integerColumnEquiv_range {I J K : Type*} [Fintype J] [Fintype K]
    (A : Matrix I J ℤ) (e : K ≃ J) : (A.submatrix id e).mulVecLin.range = A.mulVecLin.range := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  change Submodule.span ℤ (Set.range (fun k => fun i => A i (e k))) =
    Submodule.span ℤ (Set.range (fun j => fun i => A i j))
  congr 1
  ext v
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨e k, hk⟩
  · rintro ⟨j, hj⟩
    exact ⟨e.symm j, by simpa only [e.apply_symm_apply] using hj⟩

theorem selectedSpatial_full_image {I J : Type*} [Fintype I] [Fintype J]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) :
    pivotFullImage (selectedSpatialPivot root D s) (selectedSpatialFreeColumns root D s) =
      (rootDifferenceMatrix root D).mulVecLin.range := by
  rw [pivotFullImage_eq_range, selectedSpatial_fromCols]
  exact integerColumnEquiv_range _ _

theorem selectedSpatial_extended_period {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) (C : Matrix (Unit ⊕ I) N ℤ)
    {B : ℕ} (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B) :
    HasBoundedScalarPeriod
      (pivotFullImage (selectedSpatialPivot root D s) (Matrix.fromCols (selectedSpatialFreeColumns root D s) C)) B := by
  obtain ⟨a, ha, haB, hp⟩ := rootDifferenceMatrix_bounded_period root D hperiod
  refine ⟨a, ha, haB, ?_⟩
  rw [pivotFullImage_split, selectedSpatial_full_image]
  exact hp.trans le_sup_left

theorem selectedSpatial_extended_index {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) (C : Matrix (Unit ⊕ I) N ℤ)
    {B : ℕ} (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B) :
    (pivotFullImage (selectedSpatialPivot root D s)
      (Matrix.fromCols (selectedSpatialFreeColumns root D s) C)).toAddSubgroup.index ≤
        B^(Fintype.card I + 1) := by
  simpa only [Fintype.card_sum, Fintype.card_unit, Nat.add_comm] using
    hasBoundedScalarPeriod_index_le _ B (selectedSpatial_extended_period root D s C hperiod)

end Erdos3

end OAI

end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.selectedSpatial_extended_index.{u_1, u_2, u_3} := @OAI.Erdos3.selectedSpatial_extended_index.{u_1, u_2, u_3}
