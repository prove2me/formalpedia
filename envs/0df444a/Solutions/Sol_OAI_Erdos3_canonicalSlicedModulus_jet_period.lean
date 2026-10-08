-- Prove2me | solution 1 for OAI.Erdos3.canonicalSlicedModulus_jet_period
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T12:12:14.920983+00:00
-- url     : https://prove2.me/submissions/56253a62-4c9a-4c2e-bcbb-154505b21a89

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAffineResidues
namespace OAI

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

section

namespace Erdos3

open scoped BigOperators

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

section

namespace Erdos3

open scoped BigOperators Matrix

theorem integerScalarLattice_pow_le {O : Type*} [Fintype O]
    (a : ℤ) {h s : ℕ} (hh : h ≤ s) :
    integerScalarLattice O (a ^ s) ≤ integerScalarLattice O (a ^ h) := by
  rintro y ⟨z, rfl⟩
  refine ⟨a ^ (s - h) • z, ?_⟩
  change a ^ h • (a ^ (s - h) • z) = a ^ s • z
  rw [smul_smul, ← pow_add, Nat.add_sub_of_le hh]

theorem boundedDegreeIntegerJetMatrix_common_period {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (s h : ℕ) (hh : h ≤ s) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hdegree : ∀ o, (rows o).card ≤ h) :
    integerScalarLattice O (a ^ s) ≤ (boundedDegreeIntegerJetMatrix root D h rows).mulVecLin.range :=
  (integerScalarLattice_pow_le a hh).trans
    (boundedDegreeIntegerJetMatrix_period root D a hperiod h rows hinj hdegree)

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

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget
namespace OAI

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

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem goodKernelUniformCandidate_spec {α J : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] {L B : ℕ} {κ : ℝ}
    (selection : α ↪ J) (x : J → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection κ B x) (height : ℕ) :
    let period := kernelPeriodCandidate (height + 1) (goodKernelUniformCandidate selection x hx height)
    (∀ root : J → ℤ, integerScalarLattice (Unit ⊕ α) (period : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
    ∀ (O : Type*) [Fintype O] (degree : ℕ), degree ≤ height + 1 →
      ∀ rows : O → Finset α, Function.Injective rows →
        (∀ o, (rows o).card ≤ degree) →
          integerScalarLattice O (period : ℤ) ≤ (scalarKernelIntegerJet x degree rows).mulVecLin.range :=
by
  let a := Classical.choose hx.2
  obtain ⟨ha, haB, hp⟩ := Classical.choose_spec hx.2
  have hc : (goodKernelUniformCandidate selection x hx height).val + 1 = a := by
    dsimp only [goodKernelUniformCandidate, a]
    omega
  refine ⟨?_, ?_⟩
  · intro root
    rw [selectedSpatial_full_image, kernelPeriodCandidate, hc, Nat.cast_pow]
    apply (integerScalarLattice_pow_le (a : ℤ) (by omega : 1 ≤ height + 1)).trans
    simpa only [pow_one] using rootDifferenceMatrix_period root (scalarCubeDifferenceMatrix x) (a : ℤ) hp
  · intro O hO degree hdegree rows hinj hrows
    rw [kernelPeriodCandidate, hc, Nat.cast_pow]
    exact boundedDegreeIntegerJetMatrix_common_period _ _ (a : ℤ) hp (height + 1) degree
      hdegree rows hinj hrows

theorem integerScalarLattice_le_of_nat_dvd {O : Type*} [Fintype O] {a b : ℕ}
    (h : a ∣ b) : integerScalarLattice O (b : ℤ) ≤ integerScalarLattice O (a : ℤ) := by
  obtain ⟨c, rfl⟩ := h
  rintro y ⟨z, rfl⟩
  refine ⟨(c : ℤ) • z, ?_⟩
  change (a : ℤ) • ((c : ℤ) • z) = ((a * c : ℕ) : ℤ) • z
  rw [smul_smul, Nat.cast_mul]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedDetectedCanonicalPeriod
namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

theorem canonicalSlicedModulus_good (x : G → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x) :
    canonicalSlicedModulus (M := M) selection stride height x =
      residueRefinedPeriod (kernelPeriodCandidate (height + 1)
        (goodKernelUniformCandidate selection x hx height)) stride := by
  simp only [canonicalSlicedModulus, dif_pos hx]

theorem canonicalSlicedModulus_candidate_dvd
    (x : G → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    (candidate : Fin M) (hc : candidate = goodKernelUniformCandidate selection x hx height) :
    kernelPeriodCandidate (height + 1) candidate ∣
      canonicalSlicedModulus (M := M) selection stride height x := by
  subst candidate
  rw [canonicalSlicedModulus_good selection stride height x hx]
  exact ⟨∏ i, stride i, rfl⟩

end Erdos3

end

section

namespace Erdos3

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

theorem canonicalSlicedModulus_jet_period
    (x : G → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    {O : Type*} [Fintype O] (degree : ℕ) (hdegree : degree ≤ height + 1)
    (rows : O → Finset α) (hinj : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ degree) :
    integerScalarLattice O (canonicalSlicedModulus (M := M) selection stride height x : ℤ) ≤
      (scalarKernelIntegerJet x degree rows).mulVecLin.range := by
  have hd := canonicalSlicedModulus_candidate_dvd selection stride height x hx
    (goodKernelUniformCandidate selection x hx height) rfl
  exact (integerScalarLattice_le_of_nat_dvd hd).trans
    ((goodKernelUniformCandidate_spec selection x hx height).2 O degree hdegree rows hinj hrows)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)

variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)

variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)

variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)


end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.canonicalSlicedModulus_jet_period.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.canonicalSlicedModulus_jet_period.{u_1, u_2, u_3, u_4}
