-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedProductPrefactor_masked_density_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-11T15:42:12.818077+00:00
-- url     : https://prove2.me/submissions/6ccf8fa6-ac01-4bfb-a3f7-9c81fd6f2012

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B198

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

theorem integerResidueMap_apply {I : Type*} (m : ℕ) (v : I → ℤ) (i : I) :
    integerResidueMap I m v i = (v i : ZMod m) := rfl

end Erdos3

end

section

namespace Erdos3

open scoped Matrix ENNReal

end Erdos3

end

section

namespace Erdos3

theorem residueLatticeImage_comap {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L m).comap (integerResidueMap I m) = L := by
  apply Submodule.comap_map_eq_self
  rwa [integerResidueMap_ker]

theorem residueLatticeImage_mem_iff {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L)
    (v : I → ℤ) : v ∈ L ↔ integerResidueMap I m v ∈ residueLatticeImage L m := by
  change v ∈ L ↔ v ∈ (residueLatticeImage L m).comap (integerResidueMap I m)
  rw [residueLatticeImage_comap L m hperiod]

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

theorem integerMatrixResidue_mem {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (m : ℕ) (v : I → ZMod m) :
    v ∈ residueLatticeImage A.mulVecLin.range m ↔
      ∃ x : J → ZMod m, integerResidueMatrix A m *ᵥ x = v := by
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, hy⟩
    exact ⟨integerResidueMap J m x, (integerResidueMap_mulVec A m x).symm.trans hy⟩
  · rintro ⟨x, hx⟩
    obtain ⟨z, hz⟩ := integerResidueMap_surjective J m x
    refine ⟨A *ᵥ z, ⟨z, rfl⟩, ?_⟩
    rw [integerResidueMap_mulVec, hz, hx]

theorem integerMatrixImage_residue_iff {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (m : ℕ)
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range) (v : I → ℤ) :
    v ∈ A.mulVecLin.range ↔
      ∃ x : J → ZMod m, integerResidueMatrix A m *ᵥ x = integerResidueMap I m v := by
  rw [residueLatticeImage_mem_iff A.mulVecLin.range m hperiod, integerMatrixResidue_mem]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

end Erdos3.BooleanCubeKernel

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

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowReindex
namespace OAI

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

namespace Erdos3

theorem coefficientImageMultiplier_eq_of_output_residue
    {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (period : ℕ)
    (hperiod : integerScalarLattice I (period : ℤ) ≤ A.mulVecLin.range)
    (v w : I → ℤ) (hvw : integerResidueMap I period v = integerResidueMap I period w) :
    coefficientImageMultiplier A v = coefficientImageMultiplier A w := by
  classical
  have hmem : v ∈ A.mulVecLin.range ↔ w ∈ A.mulVecLin.range := by
    simp only [integerMatrixImage_residue_iff A period hperiod, hvw]
  simp only [coefficientImageMultiplier, hmem]

theorem coefficientResidueMultiplier_eq_of_output_residue
    {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I J ℤ) {modulus : ℕ} (r : Matrix I N (ZMod modulus)) (period : ℕ)
    (hperiod : integerScalarLattice I (period : ℤ) ≤ A.mulVecLin.range)
    (v w : I → ℤ) (hvw : integerResidueMap I period v = integerResidueMap I period w) :
    coefficientResidueMultiplier A r v = coefficientResidueMultiplier A r w := by
  apply coefficientImageMultiplier_eq_of_output_residue _ period _ v w hvw
  rw [integerMatrix_fromCols_range]
  exact hperiod.trans le_sup_left

open scoped Matrix

variable {I I' J : Type*} [Fintype J]

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformResidueSmallPeriod
namespace OAI

namespace Erdos3

open scoped BigOperators Classical Matrix

theorem uniformPMF_map_fiber {G H : Type*} [Fintype G] [Nonempty G]
    [DecidableEq H] (f : G → H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card G := by
  classical
  rw [pmf_map_toReal_indicator, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

theorem uniformPMF_map_hom_image {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      if y ∈ f.range then (Nat.card f.range : ℝ)⁻¹ else 0 := by
  classical
  rw [uniformPMF_map_fiber]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have he := AddMonoidHom.card_fiber_eq_of_mem_range f hy
      (show (0 : H) ∈ Set.range f from ⟨0, f.map_zero⟩)
    have hk : (Finset.univ.filter (fun x => f x = 0)).card = Fintype.card f.ker := by
      simp [Fintype.card_subtype, AddMonoidHom.mem_ker]
    have hc : Fintype.card f.ker * Fintype.card f.range = Fintype.card G := by
      simpa only [AddSubgroup.index_ker, Nat.card_eq_fintype_card] using f.ker.card_mul_index
    rw [he, hk, ← hc, Nat.cast_mul, Nat.card_eq_fintype_card]
    have hkn : (Fintype.card f.ker : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  · simp only [hy, ite_false]
    have hz : Finset.univ.filter (fun x => f x = y) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hy ⟨x, (Finset.mem_filter.mp hx).2⟩
    simp [hz]

theorem uniformPMF_map_hom_index {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      (if y ∈ f.range then (f.range.index : ℝ) else 0) / Fintype.card H := by
  classical
  rw [uniformPMF_map_hom_image]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have hcard : (Nat.card f.range : ℝ) * f.range.index = Fintype.card H := by
      have h := f.range.card_mul_index
      rw [Nat.card_eq_fintype_card (α := H)] at h
      exact_mod_cast h
    have hn : (Nat.card f.range : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have hh : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    apply (eq_div_iff hh).mpr
    rw [← hcard, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · simp [hy]

end Erdos3

namespace Erdos3

open scoped BigOperators Classical Matrix

theorem residueLatticeImage_index_le_period {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (d m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L d).toAddSubgroup.index ≤ m ^ Fintype.card I := by
  have hcard := residueLatticeImage_card_mul_index L m hperiod
  have hn : L.toAddSubgroup.index ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcard
    exact pow_ne_zero _ (NeZero.ne m) hcard.symm
  have hd := L.toAddSubgroup.index_map_dvd (f := (integerResidueMap I d).toAddMonoidHom)
    (integerResidueMap_surjective I d)
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd).trans
    (residueLatticeImage_index_le L m hperiod)

theorem uniformResidueMatrix_density_bound {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (d m : ℕ) [NeZero d] [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range) (r : I → ZMod d) :
    (d : ℝ) ^ Fintype.card I *
      (((PMF.uniformOfFintype (J → ZMod d)).map
        (fun x => integerResidueMatrix A d *ᵥ x)) r).toReal ≤ (m : ℝ) ^ Fintype.card I := by
  let f := (integerResidueMatrix A d).mulVecLin.toAddMonoidHom
  have hr : f.range = (residueLatticeImage A.mulVecLin.range d).toAddSubgroup := by
    ext y
    exact (integerMatrixResidue_mem A d y).symm
  have hi : (f.range.index : ℝ) ≤ (m : ℝ) ^ Fintype.card I := by
    rw [hr]
    exact_mod_cast residueLatticeImage_index_le_period A.mulVecLin.range d m hperiod
  have hc : (Fintype.card (I → ZMod d) : ℝ) = (d : ℝ) ^ Fintype.card I := by
    simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow]
  have hc0 : (Fintype.card (I → ZMod d) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change (d : ℝ) ^ Fintype.card I * (((PMF.uniformOfFintype (J → ZMod d)).map f) r).toReal ≤ _
  rw [uniformPMF_map_hom_index, ← hc]
  by_cases h : r ∈ f.range
  · simp only [h, ite_true]
    convert hi using 1
    field_simp
  · simp only [h, ite_false, zero_div, mul_zero]
    positivity

end Erdos3

namespace Erdos3

open scoped BigOperators Classical Matrix

theorem uniformPMF_map_hom_toReal_eq_of_sub_mem {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) {x y : H} (hxy : x - y ∈ f.range) :
    (((PMF.uniformOfFintype G).map f) x).toReal =
      (((PMF.uniformOfFintype G).map f) y).toReal := by
  have hmem : x ∈ f.range ↔ y ∈ f.range := by
    constructor
    · intro hx
      simpa only [sub_sub_cancel] using f.range.sub_mem hx hxy
    · intro hy
      simpa only [sub_add_cancel] using f.range.add_mem hxy hy
  simp only [uniformPMF_map_hom_image, hmem]

theorem uniformResidueMatrix_toReal_eq_of_period {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (d period : ℕ) [NeZero d]
    (hperiod : integerScalarLattice I (period : ℤ) ≤ A.mulVecLin.range)
    (v w : I → ℤ) (hvw : integerResidueMap I period v = integerResidueMap I period w) :
    (((PMF.uniformOfFintype (J → ZMod d)).map
      (fun z => integerResidueMatrix A d *ᵥ z)) (integerResidueMap I d v)).toReal =
    (((PMF.uniformOfFintype (J → ZMod d)).map
      (fun z => integerResidueMatrix A d *ᵥ z)) (integerResidueMap I d w)).toReal := by
  have hdiff : v - w ∈ A.mulVecLin.range := by
    apply hperiod
    rw [← integerResidueMap_ker, LinearMap.mem_ker, map_sub, hvw, sub_self]
  have himage : integerResidueMap I d (v - w) ∈ residueLatticeImage A.mulVecLin.range d :=
    ⟨v - w, hdiff, rfl⟩
  obtain ⟨z, hz⟩ := (integerMatrixResidue_mem A d _).mp himage
  apply uniformPMF_map_hom_toReal_eq_of_sub_mem (integerResidueMatrix A d).mulVecLin.toAddMonoidHom
  exact ⟨z, hz.trans (map_sub (integerResidueMap I d) v w)⟩

theorem uniformResidueSmallPeriodDensity_apply {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (d period : ℕ) [NeZero d] [NeZero period]
    (hperiod : integerScalarLattice I (period : ℤ) ≤ A.mulVecLin.range) (v : I → ℤ) :
    uniformResidueSmallPeriodDensity A d period (integerResidueMap I period v) =
      (d : ℝ) ^ Fintype.card I *
        (((PMF.uniformOfFintype (J → ZMod d)).map
          (fun z => integerResidueMatrix A d *ᵥ z)) (integerResidueMap I d v)).toReal := by
  unfold uniformResidueSmallPeriodDensity
  congr 1
  have h := uniformResidueMatrix_toReal_eq_of_period A d period hperiod
    (fun i => (((v i : ZMod period).val : ℕ) : ℤ)) v (by
      ext i
      simp only [integerResidueMap_apply, Int.cast_natCast, ZMod.natCast_zmod_val])
  simpa only [integerResidueMap, LinearMap.coe_mk, AddHom.coe_mk, Int.cast_natCast] using h

theorem uniformResidueSmallPeriodDensity_bounds {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (d period : ℕ) [NeZero d] [NeZero period]
    (hperiod : integerScalarLattice I (period : ℤ) ≤ A.mulVecLin.range) (r : I → ZMod period) :
    0 ≤ uniformResidueSmallPeriodDensity A d period r ∧
      uniformResidueSmallPeriodDensity A d period r ≤ (period : ℝ) ^ Fintype.card I := by
  constructor
  · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) ENNReal.toReal_nonneg
  · exact uniformResidueMatrix_density_bound A d period hperiod _

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteKernelRestriction
namespace OAI

section

namespace Erdos3

open MeasureTheory Topology
open scoped BigOperators

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
variable (C : G →+ H) [Fintype C.ker]

variable [TopologicalSpace G] [IsTopologicalAddGroup G]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
variable (C : G →+ H) [Fintype C.ker]

variable [T2Space G] [MeasurableSpace X] [MeasurableAdd₂ G]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

theorem uniformPMF_map_equiv {R S : Type*} [Fintype R] [Fintype S]
    [Nonempty R] [Nonempty S] (e : R ≃ S) :
    (PMF.uniformOfFintype R).map e = PMF.uniformOfFintype S := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [pmf_map_injective_at _ e e.injective, PMF.uniformOfFintype_apply,
    PMF.uniformOfFintype_apply, Fintype.card_congr e]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
variable [T2Space G] [CompactSpace G] [HasOuterApproxClosed G]
variable [MeasurableAdd₂ G]
variable [TopologicalSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
variable [MeasurableSpace X] (C : G →+ H) [Fintype C.ker]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientDeckImageCongruence
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem uniformPMF_pi_map {T : Type*} [Fintype T] [DecidableEq T] {X Y : T → Type*}
    [∀ t, Fintype (X t)] [∀ t, Nonempty (X t)] [∀ t, Fintype (Y t)]
    (f : ∀ t, X t → Y t) (y : ∀ t, Y t) :
    ((PMF.uniformOfFintype (∀ t, X t)).map (fun x t => f t (x t)) y).toReal =
      ∏ t, ((PMF.uniformOfFintype (X t)).map (f t) (y t)).toReal := by
  simp_rw [pmf_map_toReal_indicator, tsum_fintype]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hi : (if (fun t => f t (x t)) = y then (1 : ℝ) else 0) =
      ∏ t, if f t (x t) = y t then (1 : ℝ) else 0 := by
    by_cases h : (fun t => f t (x t)) = y
    · have he t := congrFun h t
      simp only [he, ite_true, Finset.prod_const_one]
    · have hn : ¬ ∀ t, f t (x t) = y t := fun he => h (funext he)
      obtain ⟨t, ht⟩ := not_forall.mp hn
      rw [if_neg h]
      exact (Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)).symm
  rw [hi]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fintype.card_pi, Nat.cast_prod, ENNReal.toReal_prod, Finset.prod_inv_distrib,
    Finset.prod_mul_distrib]

theorem uniformPMF_map_coordinates {X X' Y Y' : Type*}
    [Fintype X] [Nonempty X] [Fintype X'] [Nonempty X']
    (a : X ≃ X') (b : Y ≃ Y') (f : X → Y) (y : Y) :
    (PMF.uniformOfFintype X).map f y =
      (PMF.uniformOfFintype X').map (fun x => b (f (a.symm x))) (b y) := by
  have h : ((PMF.uniformOfFintype X).map f).map b =
      (PMF.uniformOfFintype X').map (fun x => b (f (a.symm x))) := by
    rw [← uniformPMF_map_equiv a.symm, PMF.map_comp, PMF.map_comp]
    rfl
  rw [← h]
  exact (pmf_map_injective_at _ b b.injective y).symm

theorem uniformPMF_transposed_images {T : Type*} [Fintype T] [DecidableEq T]
    {A B C V : T → Type*} [∀ t, Fintype (A t)] [∀ t, DecidableEq (A t)]
    [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]
    [∀ t, Fintype (C t)] [∀ t, DecidableEq (C t)]
    [∀ t, Fintype (V t)] [∀ t, Nonempty (V t)]
    (f : ∀ t, (A t → V t) → (C t → V t)) (y : ∀ t, C t → B t → V t) :
    ((PMF.uniformOfFintype (∀ t, A t → B t → V t)).map
      (fun x t c b => f t (fun a => x t a b) c) y).toReal =
      ∏ t, ∏ b, ((PMF.uniformOfFintype (A t → V t)).map (f t) (fun c => y t c b)).toReal := by
  let a : (∀ t, A t → B t → V t) ≃ (∀ t, B t → A t → V t) :=
    Equiv.piCongrRight fun t => Equiv.piComm (fun _ : A t => fun _ : B t => V t)
  let b : (∀ t, C t → B t → V t) ≃ (∀ t, B t → C t → V t) :=
    Equiv.piCongrRight fun t => Equiv.piComm (fun _ : C t => fun _ : B t => V t)
  rw [uniformPMF_map_coordinates a b]
  change ((PMF.uniformOfFintype (∀ t, B t → A t → V t)).map
    (fun x t b => f t (x t b)) (fun t b c => y t c b)).toReal = _
  refine (uniformPMF_pi_map (fun t (x : B t → A t → V t) b => f t (x b))
    (fun t b c => y t c b)).trans ?_
  apply Finset.prod_congr rfl
  intro t _
  exact uniformPMF_pi_map (fun _ : B t => f t) (fun b c => y t c b)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

attribute [local irreducible] coefficientDeckKernelEquiv

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

omit [Fintype α] [∀ j, Fintype (J j)] [∀ j, Fintype (B j)] in
theorem coefficientDeckJetMap_coordinate (d : ℕ) (r : CoefficientDeckResidues (K := K) B d)
    (j : Fin m) (i : B j) :
    (fun t => coefficientDeckJetMap root D rows d r j t i) =
      integerResidueMatrix (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d *ᵥ
        (fun e => r j e i) := by
  funext t
  change (∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e • r j e) i =
    ∑ e, ((boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e : ℤ) : ZMod d) * r j e i
  simp only [Finset.sum_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply]

variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelLiftChart
namespace OAI

section

namespace Erdos3

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable (C : G →+ H) (s : X → G) (q : X → H)

theorem kernelLiftChart_injOn (hproj : ∀ x, C (s x) = q x)
    {S : Set X} (hq : Set.InjOn q S) :
    Set.InjOn (fun p : X × C.ker => s p.1 + p.2.val) (S ×ˢ Set.univ) := by
  intro x hx y hy he
  change s x.1 + x.2.val = s y.1 + y.2.val at he
  have hkx : C x.2.val = 0 := x.2.property
  have hky : C y.2.val = 0 := y.2.property
  have hb : q x.1 = q y.1 := by
    have ht := congrArg C he
    simpa only [map_add, hproj, hkx, hky, add_zero] using ht
  have hxy : x.1 = y.1 := hq hx.1 hy.1 hb
  apply Prod.ext hxy
  apply Subtype.ext
  rw [hxy] at he
  exact add_left_cancel he

theorem kernelLiftChart_relabel_injOn {R : Type*} (e : R ≃ C.ker)
    (hproj : ∀ x, C (s x) = q x) {S : Set X} (hq : Set.InjOn q S) :
    Set.InjOn (fun p : X × R => s p.1 + (e p.2).val) (S ×ˢ Set.univ) := by
  intro x hx y hy he
  have hp := kernelLiftChart_injOn C s q hproj hq
    (show (x.1, e x.2) ∈ S ×ˢ Set.univ from ⟨hx.1, Set.mem_univ _⟩)
    (show (y.1, e y.2) ∈ S ×ˢ Set.univ from ⟨hy.1, Set.mem_univ _⟩) he
  exact Prod.ext (congrArg (fun z : X × C.ker => z.1) hp)
    (e.injective (congrArg (fun z : X × C.ker => z.2) hp))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedCoveredChart
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

theorem normalizedCoveredChart_injOn
    {Ω : Set (EuclideanSpace ℝ D)} (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    Set.InjOn (normalizedCoveredChart W b hb bW d)
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ) :=
  kernelLiftChart_relabel_injOn _ _ _
    (coverKernelBasisEquiv _ bW d (Nat.pos_of_ne_zero (NeZero.ne d))).toEquiv
    (normalizedCoverLift_projection W b hb d (Nat.pos_of_ne_zero (NeZero.ne d)))
    (normalizedLatticeQuotient_injOn W b hb hΩ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoveredJetChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J B : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem coveredJetChart_injOn (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    Set.InjOn (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) := by
  intro x hx y hy he
  funext j t
  exact normalizedCoveredChart_injOn _ (b j) (hb j) (bW j) d (hΩ j t)
    (hx j (Set.mem_univ j) t (Set.mem_univ t)) (hy j (Set.mem_univ j) t (Set.mem_univ t))
    (congrFun (congrFun he j) t)

variable [∀ j, Fintype (O j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
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

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}

variable [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {D α : Type*} [Fintype α] [DecidableEq α]
variable (B : D → Type*) (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

end Erdos3

end

section

namespace Erdos3

variable {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}

theorem partitionedPrincipalInput_value (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z) (z : Z → ℤ) {L : PrincipalTupleIndex B h → ℕ}
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L)
    (k : SamplerTupleIndex G B h) (a : Option α) :
    Sum.elim (Sum.elim z (principalTupleIntegers u)) (principalTupleIntegers v)
        (partitionedPrincipalInput P extra k a) =
      Sum.elim z (principalTupleIntegers (principalAxisJoin P u v)) (canonicalTupleInput extra k a) := by
  rcases k with g | ⟨d, b, r⟩
  · rfl
  · by_cases hp : P d <;>
      simp [partitionedPrincipalInput, canonicalTupleInput, principalTupleIntegers, principalAxisJoin, hp]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {G : Type*} [Fintype G] [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)


section Law

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]

end Law

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveAveragedProfileComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {S R T U : Type*} [Fintype S] [Fintype R] [Fintype T]

omit [Fintype R] [Fintype T] in
theorem maskedSiteFactor_prod (label : S → U → R) (r : S → R)
    (f : T → S → U → ℂ) (k : T) (u : S → U) :
    (∏ s, maskedSiteFactor label r f k s (u s)) =
      if (fun s => label s (u s)) = r then ∏ s, f k s (u s) else 0 := by
  by_cases hr : (fun s => label s (u s)) = r
  · have hs (s : S) : label s (u s) = r s := congrFun hr s
    simp only [ite_true, maskedSiteFactor, hs]
  · simp only [hr, ite_false]
    obtain ⟨s, hs⟩ : ∃ s, label s (u s) ≠ r s := by
      by_contra hn
      apply hr
      funext s
      by_contra hs
      exact hn ⟨s, hs⟩
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp only [maskedSiteFactor, hs, ite_false])

theorem maskedSiteExpansion_identity [DecidableEq S] (label : S → U → R) (mask : (S → R) → ℂ)
    (c : T → ℂ) (f : T → S → U → ℂ) (u : S → U) :
    (∑ r : S → R, ∑ k, (mask r*c k)*∏ s, maskedSiteFactor label r f k s (u s)) =
      mask (fun s => label s (u s))*(∑ k, c k*∏ s, f k s (u s)) := by
  simp_rw [maskedSiteFactor_prod]
  rw [Finset.sum_eq_single (fun s => label s (u s))]
  · simp only [ite_true, Finset.mul_sum, mul_assoc]
  · intro r _ hr
    simp only [Ne.symm hr, ite_false, mul_zero, Finset.sum_const_zero]
  · simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

section Ideal

variable {D G α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
  (h : D → ℕ) (e : ∀ d, J d ⊕ N d → SamplerTupleIndex G B h →₀ ℕ)
  (index : ∀ d, B d → J d ⊕ N d) (c w : ∀ d, J d ⊕ N d → ℝ)
  (sets : ∀ d, O d → Finset α)

end Ideal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) [Fintype Z] {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

theorem kernelExponent_eval_monomial {G X : Type*} {h : ℕ} (x : G ⊕ X → ℤ)
    (d : BoundedIntegerExponent G h) :
    MvPolynomial.eval x (MvPolynomial.monomial (kernelExponentEmbedding G X h d).val 1) =
      MvPolynomial.eval (fun g => x (.inl g)) (MvPolynomial.monomial d.val 1) := by
  change MvPolynomial.eval x (MvPolynomial.monomial (d.val.embDomain Function.Embedding.inl) 1) = _
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_embDomain]
  rfl

theorem integerMappedCubeTuple_kernel {G X Z Y α : Type*}
    (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℤ) (y : Y → ℤ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℤ)) (t : Finset α) :
    (fun g => integerMappedCubeTuple input z y t (.inl g)) =
      integerAffineCube (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) t := by
  funext g
  simp only [integerMappedCubeTuple, integerAffineCube, hfixed, scalarCubeDifferenceMatrix, sampledColumnMatrix]

theorem integerMappedJetMatrix_kernel {G X Z Y α O : Type*} [Fintype G] [DecidableEq α]
    (h : ℕ) (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℤ) (y : Y → ℤ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℤ)) (rows : O → Finset α) :
    (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (G ⊕ X) h => d.val)
      input z rows y).submatrix id (kernelExponentEmbedding G X h) = scalarKernelIntegerJet x h rows := by
  ext o d
  change booleanCoefficient (fun t => MvPolynomial.eval (integerMappedCubeTuple input z y t)
      (MvPolynomial.monomial (kernelExponentEmbedding G X h d).val 1)) (rows o) =
    booleanCoefficient (fun t => MvPolynomial.eval
      (integerAffineCube (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) t)
      (MvPolynomial.monomial d.val 1)) (rows o)
  apply congrArg (fun f : Finset α → ℤ => booleanCoefficient f (rows o))
  funext t
  rw [kernelExponent_eval_monomial, integerMappedCubeTuple_kernel input z y x hfixed t]

theorem integerMappedJetMatrix_kernel_split {G X Z Y α O : Type*} [Fintype G] [DecidableEq α]
    (h : ℕ) (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℤ) (y : Y → ℤ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℤ)) (rows : O → Finset α) :
    (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (G ⊕ X) h => d.val)
      input z rows y).submatrix id (kernelCoefficientEquiv G X h) =
      Matrix.fromCols (scalarKernelIntegerJet x h rows)
        (integerMappedJetMatrix (fun d : NonkernelCoefficient G X h => d.val.val) input z rows y) := by
  ext o d
  cases d with
  | inl d => exact congrFun (congrFun (integerMappedJetMatrix_kernel h input z y x hfixed rows) o) d
  | inr d => rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

theorem allocatedKernelJet_split {α O : Type*} [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (u : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) grid → ℤ)
    (v : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℤ)
    (rows : O → Finset α) :
    (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) => d.val)
      (partitionedPrincipalInput grid (fun g a => (g, a)))
      (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v).submatrix id reindex =
      Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) rows)
        (integerMappedJetMatrix (allocatedNonkernelExponent B j)
          (partitionedPrincipalInput grid (fun g a => (g, a)))
          (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v) :=
  integerMappedJetMatrix_kernel_split (j.val+1) _ _ _ x (fun _ _ => rfl) rows

theorem allocatedKernelJet_full_image {α O : Type*} [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (u : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) grid → ℤ)
    (v : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℤ)
    (rows : O → Finset α) :
    (Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) rows)
      (integerMappedJetMatrix (allocatedNonkernelExponent B j)
        (partitionedPrincipalInput grid (fun g a => (g, a)))
        (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v)).mulVecLin.range =
      (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) => d.val)
        (partitionedPrincipalInput grid (fun g a => (g, a)))
        (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v).mulVecLin.range := by
  rw [← allocatedKernelJet_split B U basis S j x u v rows]
  exact integerColumnEquiv_range _ reindex

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : I j)


local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators Matrix Classical

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : I j)


local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) 1

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBooleanSiteReconstruction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem integerBooleanSitesFromRows_coefficient (rows : Finset (Finset α))
    (z : rows → ℤ) (t : Finset α) :
    booleanCoefficient (integerBooleanSitesFromRows rows z) t =
      if ht : t ∈ rows then z ⟨t, ht⟩ else 0 := by
  calc
    _ = (booleanJetExtractionMatrix (id : Finset α → Finset α) *ᵥ
        integerBooleanSitesFromRows rows z) t :=
      (booleanJetExtractionMatrix_mulVec id (integerBooleanSitesFromRows rows z) t).symm
    _ = _ := by
      unfold integerBooleanSitesFromRows
      rw [Matrix.mulVec_mulVec, booleanJetExtraction_mul_reconstruction, Matrix.one_mulVec]

theorem integerBooleanSitesFromRows_coefficient_mem (rows : Finset (Finset α))
    (z : rows → ℤ) (t : rows) :
    booleanCoefficient (integerBooleanSitesFromRows rows z) t.val = z t := by
  rw [integerBooleanSitesFromRows_coefficient, dif_pos t.property]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoveredChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [∀ j, Fintype (E j)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem mixedCoveredJetChart_injOn (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    Set.InjOn (mixedCoveredJetChart U o b hb bW d) (mixedCoveredJetRegion U o b d Ω) := by
  intro z hz w hw he
  apply (mixedCoveredJetCoordinatesEquiv U o d).injective
  exact coveredJetChart_injOn U b hb bW d Ω hΩ hz hw he

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowRestrictedDeckSiteMask
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

theorem coefficientDeckJetDensity_product {α K : Type*} [DecidableEq α] [Fintype K]
    {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
    (d : ℕ) [NeZero d] (r : ∀ j, O j → B j → ZMod d) :
    coefficientDeckJetDensity root D rows d r =
      ∏ j, ∏ i : B j, (d : ℝ) ^ Fintype.card (O j) *
        (((PMF.uniformOfFintype (BoundedCoefficientExponent K (j.val + 1) → ZMod d)).map
          (fun z => integerResidueMatrix
            (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d *ᵥ z)) (fun t => r j t i)).toReal := by
  have he : (coefficientDeckJetMap (B := B) root D rows d :
      CoefficientDeckResidues (K := K) B d → (∀ j, O j → B j → ZMod d)) =
      (fun x j t i => (integerResidueMatrix
        (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d *ᵥ
          (fun e => x j e i)) t) := by
    funext x j t i
    exact congrFun (coefficientDeckJetMap_coordinate root D rows d x j i) t
  have hc : (Fintype.card (∀ j, O j → B j → ZMod d) : ℝ) =
      ∏ j, ∏ _i : B j, (d : ℝ) ^ Fintype.card (O j) := by
    simp only [Fintype.card_pi, ZMod.card, Nat.cast_prod, Nat.cast_pow,
      Finset.prod_const, Finset.card_univ]
    apply Finset.prod_congr rfl
    intro j _
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  unfold coefficientDeckJetDensity
  rw [he, uniformPMF_transposed_images, hc]
  simp only [Finset.prod_mul_distrib]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (d period : ℕ) [NeZero d]

theorem coefficientDeckSmallPeriodDensity_apply [NeZero period]
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range)
    (v : ∀ j, O j → B j → ℤ) :
    coefficientDeckSmallPeriodDensity root D rows d period (fun j t i => (v j t i : ZMod period)) =
      coefficientDeckJetDensity root D rows d (fun j t i => (v j t i : ZMod d)) := by
  rw [coefficientDeckJetDensity_product]
  unfold coefficientDeckSmallPeriodDensity
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro i _
  exact uniformResidueSmallPeriodDensity_apply
    (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d period (hperiod j) (fun t => v j t i)

theorem coefficientDeckSmallPeriodDensity_bounds [NeZero period]
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range)
    (r : ∀ j, O j → B j → ZMod period) :
    0 ≤ coefficientDeckSmallPeriodDensity root D rows d period r ∧
      coefficientDeckSmallPeriodDensity root D rows d period r ≤ coefficientDeckPeriodCap O B period := by
  have hb (j : Fin m) (i : B j) := uniformResidueSmallPeriodDensity_bounds
    (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d period (hperiod j) (fun t => r j t i)
  constructor
  · exact Finset.prod_nonneg (fun j _ => Finset.prod_nonneg (fun i _ => (hb j i).1))
  · exact Finset.prod_le_prod
      (fun j _ => Finset.prod_nonneg (fun i _ => (hb j i).1))
      (fun j _ => Finset.prod_le_prod (fun i _ => (hb j i).1) (fun i _ => (hb j i).2))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (d period : ℕ) [NeZero d] [NeZero period]

theorem coefficientDeckSiteMask_apply
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range)
    (v : Finset α → ∀ j, B j → ℤ) :
    coefficientDeckSiteMask root D rows d period (fun s j i => (v s j i : ZMod period)) =
      coefficientDeckJetDensity root D rows d
        (fun j t i => ((booleanCoefficient (fun s => v s j i) (rows j t) : ℤ) : ZMod d)) := by
  rw [← coefficientDeckSmallPeriodDensity_apply root D rows d period hperiod
    (fun j t i => booleanCoefficient (fun s => v s j i) (rows j t))]
  unfold coefficientDeckSiteMask
  congr 1
  funext j t i
  have h := congrFun (integerResidueMap_mulVec (booleanJetExtractionMatrix (rows j)) period
    (fun s => v s j i)) t
  simpa only [integerResidueMap, LinearMap.coe_mk, AddHom.coe_mk,
    booleanJetExtractionMatrix_mulVec] using h.symm

theorem coefficientDeckSiteMask_bounds
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range)
    (r : Finset α → ∀ j, B j → ZMod period) :
    0 ≤ coefficientDeckSiteMask root D rows d period r ∧
      coefficientDeckSiteMask root D rows d period r ≤ coefficientDeckPeriodCap O B period :=
  coefficientDeckSmallPeriodDensity_bounds root D rows d period hperiod _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I J Q : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (Q j)]


variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem integerBooleanSitesFromRows_eq_mulVec (rows : Finset (Finset α))
    (z : rows → ℤ) :
    integerBooleanSitesFromRows rows z = rowRestrictedSiteMatrix rows *ᵥ z := by
  funext s
  let F := fun t => booleanReconstructionMatrix α s t *
    (if ht : t ∈ rows then z ⟨t, ht⟩ else 0)
  have hsub : (∑ t ∈ rows, F t) = ∑ t : Finset α, F t := by
    apply Finset.sum_subset (Finset.subset_univ rows)
    intro t _ ht
    simp only [F, dif_neg ht, mul_zero]
  calc
    _ = ∑ t : Finset α, F t := rfl
    _ = ∑ t ∈ rows, F t := hsub.symm
    _ = ∑ t : rows, F t := Finset.sum_subtype rows (by simp) F
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      simp only [F, dif_pos t.property, rowRestrictedSiteMatrix]

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

omit [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)] in
theorem mixedCoveredRowsSiteValue_integer (d : ℕ)
    (z : MixedCoveredJetSource I rows E n d) (s : Finset α) (j : Fin m) (i : Fin (n j)) :
    ((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () =
      integerBooleanSitesFromRows (rowSets j) ((z.1 j).2 i) s := by
  rw [integerBooleanSitesFromRows_eq_mulVec]
  rfl

variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical BigOperators Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (root : K → ℤ) (D : Matrix α K ℤ)
variable (d period : ℕ) [NeZero d] [NeZero period]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α (Fin.val j + 1))
local notation "rows" => (fun j : Fin m => (Subtype.val : jets j → Finset α))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace VectorPolynomial

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))


end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem rowRestrictedExtraction_mul_reconstruction (rows : Finset (Finset α)) :
    booleanJetExtractionMatrix (Subtype.val : rows → Finset α) *
      rowRestrictedSiteMatrix rows = 1 := by
  ext s r
  change (booleanJetExtractionMatrix (Subtype.val : rows → Finset α) *ᵥ
    (fun t => if r.val ⊆ t then (1 : ℤ) else 0)) s = _
  rw [booleanJetExtractionMatrix_mulVec, booleanCoefficient_monomial]
  simp only [Matrix.one_apply, Subtype.val_inj]

theorem rowRestrictedReconstruction_zsmul_inverse {W : Type*} [AddCommGroup W]
    (rows : Finset (Finset α)) (x : rows → W) (r : rows) :
    (∑ s : Finset α, booleanJetExtractionMatrix Subtype.val r s •
      ∑ t : rows, rowRestrictedSiteMatrix rows s t • x t) = x r := by
  simp_rw [Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  change (∑ t, (booleanJetExtractionMatrix (Subtype.val : rows → Finset α) *
    rowRestrictedSiteMatrix rows) r t • x t) = x r
  rw [rowRestrictedExtraction_mul_reconstruction]
  simp [Matrix.one_apply]

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ}
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (root : K → ℤ) (D : Matrix α K ℤ)
variable (rowSets : Fin m → Finset (Finset α))
variable (d period : ℕ) [NeZero d] [NeZero period]

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rowMap" => (fun j => (Subtype.val : rows j → Finset α))

theorem coefficientDeckRowsSiteMask_of_lifts
    (hperiod : ∀ j, integerScalarLattice (rows j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rowMap j)).mulVecLin.range)
    (z : ∀ j, rows j → Q j → ZMod d) (v : Finset α → ∀ j, Q j → ℤ)
    (hv : ∀ s j i, (v s j i : ZMod d) =
      ∑ t, rowRestrictedSiteMatrix (rowSets j) s t • z j t i) :
    coefficientDeckSiteMask root D rowMap d period (fun s j i => (v s j i : ZMod period)) =
      coefficientDeckJetDensity root D rowMap d z := by
  have hjet (j : Fin m) (t : rows j) (i : Q j) :
      ((booleanCoefficient (fun s => v s j i) t.val : ℤ) : ZMod d) = z j t i := by
    rw [← booleanJetExtractionMatrix_mulVec (rowMap j) (fun s => v s j i) t]
    change ((∑ s, booleanJetExtractionMatrix (rowMap j) t s * v s j i : ℤ) : ZMod d) = _
    simp only [Int.cast_sum, Int.cast_mul, hv]
    simpa only [zsmul_eq_mul] using
      rowRestrictedReconstruction_zsmul_inverse (rowSets j) (fun t => z j t i) t
  have h := coefficientDeckSiteMask_apply root D rowMap d period hperiod v
  simpa only [hjet] using h

theorem coefficientDeckRowsSiteMask_reconstructed
    (hperiod : ∀ j, integerScalarLattice (rows j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rowMap j)).mulVecLin.range)
    {I : Fin m → Type*} {n : Fin m → ℕ}
    (z : MixedCoveredJetSource I rows Q n d) :
    coefficientDeckSiteMask root D rowMap d period
      (fun s j i => ((mixedCoveredRowsSiteValue rowSets d z s).2 j () i).val) =
      coefficientDeckJetDensity root D rowMap d z.2 := by
  have hv (s : Finset α) (j : Fin m) (i : Q j) :
      ((((mixedCoveredRowsSiteValue rowSets d z s).2 j () i).val : ℤ) : ZMod d) =
        ∑ t, rowRestrictedSiteMatrix (rowSets j) s t • z.2 j t i := by
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
    rfl
  have h := coefficientDeckRowsSiteMask_of_lifts root D rowSets d period hperiod z.2
    (fun s j i => ((mixedCoveredRowsSiteValue rowSets d z s).2 j () i).val) hv
  simpa only [Int.cast_natCast] using h

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongImage
namespace OAI

section

namespace Erdos3

theorem translatedIntegerMappedJetMatrix_zero {Z X K α O N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℤ)
    (rows : O → Finset α) (x : X → ℤ) :
    translatedIntegerMappedJetMatrix e input z rows x (fun _ => 0) =
      integerMappedJetMatrix e input z rows x := by
  simp only [translatedIntegerMappedJetMatrix, zero_add, integerMappedJetMatrix]

theorem translatedIntegerMappedJetMatrix_eq_boundedCoefficient {Z X K α O : Type*}
    [DecidableEq α] [Fintype K] (h : ℕ) (input : K → Option α → Z ⊕ X)
    (z : Z → ℤ) (rows : O → Finset α) (x : X → ℤ) (c : K → ℤ) :
    translatedIntegerMappedJetMatrix (fun e : VectorPolynomial.BoundedCoefficientExponent K h => e.val)
      input z rows x c =
      boundedCoefficientJetMatrix (fun k => c k + Sum.elim z x (input k none))
        (fun i k => Sum.elim z x (input k (some i))) h rows := by
  have hv : (fun t k => c k + integerMappedCubeTuple input z x t k) =
      integerAffineCube (fun k => c k + Sum.elim z x (input k none))
        (fun i k => Sum.elim z x (input k (some i))) := by
    funext t k
    simp only [integerMappedCubeTuple, integerAffineCube, add_assoc]
  change integerJetMatrix
      (fun e : VectorPolynomial.BoundedCoefficientExponent K h => MvPolynomial.monomial e.val 1)
      (fun t k => c k + integerMappedCubeTuple input z x t k) rows =
    integerJetMatrix
      (fun e : VectorPolynomial.BoundedCoefficientExponent K h => MvPolynomial.monomial e.val 1)
      (integerAffineCube (fun k => c k + Sum.elim z x (input k none))
        (fun i k => Sum.elim z x (input k (some i)))) rows
  rw [hv]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

omit [DecidableEq α] in
theorem allocatedPhysicalCube_mapped_root (c : LayerSamplerVariables G I n B → ℤ) :
    (fun k => c k + Sum.elim (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (principalTupleIntegers v) ((partitionedPrincipalInput grid (fun g a => (g, a))) k none)) =
      allocatedPhysicalCubeRoot B U b S c x (principalAxisJoin grid u v) := by
  funext k
  rw [partitionedPrincipalInput_value]
  cases k <;> rfl

omit [DecidableEq α] in
theorem allocatedPhysicalCube_mapped_directions :
    (fun i k => Sum.elim (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (principalTupleIntegers v) ((partitionedPrincipalInput grid (fun g a => (g, a))) k (some i))) = (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) := by
  funext i k
  rw [partitionedPrincipalInput_value]
  cases k <;> rfl

theorem allocatedTranslatedPartitionedJetMatrix_eq_physical
    (c : LayerSamplerVariables G I n B → ℤ) (j : Fin m) :
    allocatedTranslatedPartitionedJetMatrix B U b S x u v rows c j =
      boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S c x (principalAxisJoin grid u v)) (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) (j.val + 1) (rows j) := by
  unfold allocatedTranslatedPartitionedJetMatrix
  rw [translatedIntegerMappedJetMatrix_eq_boundedCoefficient,
    allocatedPhysicalCube_mapped_root, allocatedPhysicalCube_mapped_directions]

theorem allocatedPartitionedJetMatrix_eq_physical (j : Fin m) :
    allocatedPartitionedJetMatrix B U b S x u v rows j =
      boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) (j.val + 1) (rows j) := by
  rw [← allocatedTranslatedPartitionedJetMatrix_eq_physical B U b S x u v rows (fun _ => 0) j]
  exact (translatedIntegerMappedJetMatrix_zero _ (partitionedPrincipalInput grid (fun g a => (g, a))) (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (rows j) (principalTupleIntegers v)).symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "joined" => principalAxisJoin grid u v

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedWholeDeckLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v w : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

omit [∀ j, Fintype (O j)] in
theorem allocatedPartitionedJetMatrix_kernel_range_le (j : Fin m) :
    (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range ≤
      (allocatedPartitionedJetMatrix B U b S x u v rows j).mulVecLin.range := by
  have he := allocatedKernelJet_full_image B U b S j x
    (principalTupleIntegers u) (principalTupleIntegers v) (rows j)
  change _ = (allocatedPartitionedJetMatrix B U b S x u v rows j).mulVecLin.range at he
  rw [← he, integerMatrix_fromCols_range]
  exact le_sup_left

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" z => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x z
local notation "dirs" z => allocatedPhysicalCubeDirections B U b S x z

omit [∀ j, Fintype (O j)] in
theorem allocatedWholeJetMatrix_kernel_range_le (j : Fin m) :
    (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range ≤
      (boundedCoefficientJetMatrix (root y) (dirs y) (j.val + 1) (rows j)).mulVecLin.range := by
  have h := allocatedPartitionedJetMatrix_kernel_range_le B U b S x
    (principalAxisRestrict grid y) (principalAxisRestrict (fun a => ¬grid a) y) rows j
  rw [allocatedPartitionedJetMatrix_eq_physical, principalAxisJoin_restrict] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedPhysicalCoveredDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

theorem standardLatticeClosedQuarterBox_subset_smallBox (J : Type*) [Fintype J] :
    standardLatticeClosedQuarterBox J ⊆ standardLatticeSmallBox J := by
  intro x hx i
  exact (hx i).trans_lt (by norm_num)

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedActualProfileControl
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value

variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

omit [∀ j, Fintype (O j)] in
theorem allocatedLongJetMask_product_bound {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C)
    (z : AllocatedLongJetRows B U basis S O) :
    |∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)| ≤
      C ^ Fintype.card (LayerSamplerAxis I n) := by
  have hr (a : {a // ¬grid a}) :
      0 ≤ allocatedLongJetMask B U basis S x rows modulus residue a (z a) ∧
      allocatedLongJetMask B U basis S x rows modulus residue a (z a) ≤ C := by
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact ⟨zero_le_one, hC⟩
    · exact hm j _
  rw [abs_of_nonneg (Finset.prod_nonneg (fun a _ => (hr a).1))]
  calc
    _ ≤ ∏ _a : {a // ¬grid a}, C :=
      Finset.prod_le_prod (fun a _ => (hr a).1) (fun a _ => (hr a).2)
    _ = C ^ Fintype.card {a // ¬grid a} := by simp
    _ ≤ _ := pow_le_pow_right₀ hC (Fintype.card_subtype_le _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelSiteMask
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rowMap" => (fun j : Fin m => (Subtype.val : rows j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rows I n grid

variable (x : G → IntegerScalarCubeBox α S.value) (modulus : ℕ)
variable (residue : ∀ j, Matrix {t : Finset α // t ∈ rowSets j}
  (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

variable {Q : Fin m → Type*}

theorem allocatedKernelSiteMask_reconstructed (period : ℕ) [NeZero period]
    (hperiod : ∀ j, integerScalarLattice (rows j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rowMap j)).mulVecLin.range)
    (d : ℕ) (z : MixedCoveredJetSource I rows Q n d) :
    allocatedKernelSiteMask B U b S rowSets x modulus residue period
      (fun s j i => (((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () : ZMod period)) =
      ∏ a, allocatedLongJetMask B U b S x rowMap modulus residue a ((split z.1).2 a) := by
  unfold allocatedKernelSiteMask
  apply Finset.prod_congr rfl
  intro a _
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · rfl
  · change coefficientResidueMultiplier _ (residue j) _ =
      coefficientResidueMultiplier _ (residue j) ((z.1 j).2 i)
    apply coefficientResidueMultiplier_eq_of_output_residue _ _ period (hperiod j)
    funext t
    change (((booleanCoefficient (fun s =>
      (((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () : ZMod period)) t.val).val : ℤ) :
        ZMod period) = ((z.1 j).2 i t : ZMod period)
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, mixedCoveredRowsSiteValue_integer]
    have h := booleanCoefficient_map (Int.castRingHom (ZMod period))
      (integerBooleanSitesFromRows (rowSets j) ((z.1 j).2 i)) t.val
    rw [integerBooleanSitesFromRows_coefficient_mem] at h
    exact h.symm

omit [Fintype α] in
theorem allocatedKernelSiteMask_bound (period : ℕ)
    {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rowMap j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rowMap j modulus (residue j) z ≤ C)
    (r : Finset α → ∀ j, Fin (n j) → ZMod period) :
    |allocatedKernelSiteMask B U b S rowSets x modulus residue period r| ≤
      C ^ Fintype.card (LayerSamplerAxis I n) :=
  allocatedLongJetMask_product_bound B U b S x rowMap modulus residue hC hm _

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProductPrefactorMasks
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x y₀
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)

theorem allocatedClippedPrefactorSiteMask_reconstructed
    (hperiod : ∀ j, integerScalarLattice (rowTypes j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (z : MixedCoveredJetSource I rowTypes E n d) :
    allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
      (fun s => (fun j i => (((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () : ZMod period),
        fun j i => (((mixedCoveredRowsSiteValue rowSets d z s).2 j () i).val : ZMod period))) =
      coefficientDeckJetDensity root dirs rows d z.2 *
        ∏ a, allocatedLongJetMask B U b S x rows q residue a ((split z.1).2 a) := by
  rw [allocatedClippedPrefactorSiteMask,
    allocatedKernelSiteMask_reconstructed B U b S rowSets x q residue period hperiod d z,
    coefficientDeckRowsSiteMask_reconstructed root dirs rowSets d period
      (fun j => (hperiod j).trans (allocatedWholeJetMatrix_kernel_range_le B U b S x y₀ rows j)) z]
  exact mul_comm _ _

theorem allocatedClippedPrefactorSiteMask_bound
    (hperiod : ∀ j, integerScalarLattice (rowTypes j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j q (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j q (residue j) z ≤ C)
    (r : Finset α → (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) :
    |allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period r| ≤
      C ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period := by
  have hd := coefficientDeckSiteMask_bounds root dirs rows d period
    (fun j => (hperiod j).trans (allocatedWholeJetMatrix_kernel_range_le B U b S x y₀ rows j))
    (fun s => (r s).2)
  rw [allocatedClippedPrefactorSiteMask, abs_mul, abs_of_nonneg hd.1]
  exact mul_le_mul (allocatedKernelSiteMask_bound B U b S rowSets x q residue period hC hm _)
    hd.2 hd.1 (pow_nonneg (zero_le_one.trans hC) _)

variable (T : Fin m → ℝ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x y₀
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)

variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

theorem allocatedProductFullGridPrefactor_components
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f (chart z) =
      allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr (chart z) *
        ((coefficientDeckJetDensity root dirs rows d z.2 *
          (∏ a, allocatedLongJetMask B U b S x rows q residue a ((split z.1).2 a)) *
          f (allocatedLongJetRealCoordinates B U b S ((split z.1).2)) /
          (allocatedFullGridNaturalVolume B U b S rowSets * coveredJetArrayScale (O := rowTypes) U *
            ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a) : ℝ) : ℂ) := by
  have hinj := mixedCoveredJetChart_injOn U o b hb bW d
    (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  rw [allocatedProductFullGridPrefactor]
  unfold allocatedWholeMaskedGridlessProfile allocatedGridlessCoveredProfile
  rw [restrictedChartDensity_apply _ _ _ _ hinj hz]
  simp only [one_mul, principalAxisJoin_restrict, allocatedLongProfileDensity,
    Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv, mul_inv_rev]
  ring

theorem allocatedProductFullGridPrefactor_site_masks
    (hperiod : ∀ j, integerScalarLattice (rowTypes j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f (chart z) =
      allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr (chart z) *
        ((allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
          (fun s => (fun j i => (((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () : ZMod period),
            fun j i => (((mixedCoveredRowsSiteValue rowSets d z s).2 j () i).val : ZMod period))) *
          f (allocatedLongJetRealCoordinates B U b S ((split z.1).2)) /
          (allocatedFullGridNaturalVolume B U b S rowSets * coveredJetArrayScale (O := rowTypes) U *
            ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a) : ℝ) : ℂ) := by
  rw [allocatedClippedPrefactorSiteMask_reconstructed B U b S rowSets x y₀ q d period hperiod z]
  exact allocatedProductFullGridPrefactor_components B U b S rowSets x y₀ q d r hr hb o bW f z hz

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedGlobalMaskedDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "single" => (fun _ : Fin m => Unit)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

include hperiod hM hm in
theorem allocatedProductPrefactor_masked_density_error (hR : ∀ j, 0 < R j)
    {K : Type*} [Fintype K] (a : K → ℂ)
    (f : K → Finset α → MixedCoveredJetSource I (fun _ => Unit) E n d → ℂ)
    (D : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ) (ε : ℝ) (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region)
    (herr : ‖cutoff (chart z) * (((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (D
          (allocatedLongJetRealCoordinates B U b S (split z.1).2) : ℂ)) -
      ∑ k, a k * ∏ s, f k s (mixedCoveredRowsSiteValue rowSets d z s)‖ ≤ ε) :
    ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
        (D) (chart z) -
      ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k,
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k *
          ∏ s, maskedSiteFactor
            (fun _ v => (fun j i => ((v.1 j).2 i () : ZMod period),
              fun j i => ((v.2 j () i).val : ZMod period))) label f k s
              (mixedCoveredRowsSiteValue rowSets d z s)‖ ≤
      ‖inverseNormalizer‖ *
        (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) * ε := by
  let label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) := fun s =>
    (fun j i => (((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () : ZMod period),
      fun j i => (((mixedCoveredRowsSiteValue rowSets d z s).2 j () i).val : ZMod period))
  have hmask : ‖(mask label : ℂ)‖ ≤
      M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact allocatedClippedPrefactorSiteMask_bound B U b S rowSets x y₀ q d period hperiod hM hm label
  have hcap : 0 ≤ M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) (coefficientDeckPeriodCap_nonneg rowTypes E period)
  have hV : ((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) ≠ 0 := by
    have hp : 0 < (∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) := Finset.prod_pos (fun i _ => hR i.1.val.1)
    exact_mod_cast hp.ne'
  have halgebra (c t v a : ℂ) :
      c * (t * v / (baseVolume : ℂ)) - inverseNormalizer * (t * a) =
        inverseNormalizer * t * (c * (((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) * v) - a) := by
    simp only [allocatedProductIdealNormalizer, Complex.ofReal_mul]
    by_cases hN : (baseVolume : ℂ) = 0
    · simp only [hN, zero_mul, inv_zero, div_zero, mul_zero, zero_sub, neg_zero]
    · field_simp [hN, hV]
  have hsum : (∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k,
      allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k *
        ∏ s, maskedSiteFactor
          (fun _ v => (fun j i => ((v.1 j).2 i () : ZMod period),
            fun j i => ((v.2 j () i).val : ZMod period))) label f k s
            (mixedCoveredRowsSiteValue rowSets d z s)) =
      inverseNormalizer * ((mask label : ℂ) * ∑ k, a k * ∏ s, f k s (mixedCoveredRowsSiteValue rowSets d z s)) := by
    have hexp := maskedSiteExpansion_identity
      (fun (_ : Finset α) (v : MixedCoveredJetSource I (fun _ => Unit) E n d) =>
        (fun j i => ((v.1 j).2 i () : ZMod period), fun j i => ((v.2 j () i).val : ZMod period)))
      (fun label => (mask label : ℂ)) a f (mixedCoveredRowsSiteValue rowSets d z)
    change (∑ label, ∑ k, ((mask label : ℂ) * a k) * ∏ s, maskedSiteFactor
      (fun _ v => (fun j i => ((v.1 j).2 i () : ZMod period),
        fun j i => ((v.2 j () i).val : ZMod period))) label f k s
        (mixedCoveredRowsSiteValue rowSets d z s)) =
      (mask label : ℂ) * ∑ k, a k * ∏ s, f k s (mixedCoveredRowsSiteValue rowSets d z s) at hexp
    rw [← hexp]
    simp only [allocatedProductMaskedIdealCoefficient, Finset.mul_sum, mul_assoc]
  rw [hsum, allocatedProductFullGridPrefactor_site_masks B U b S rowSets x y₀ q d period
    r hr hb o bW (D) hperiod z hz]
  simp only [Complex.ofReal_div, Complex.ofReal_mul]
  rw [halgebra, norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hmask (norm_nonneg _)) herr (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) hcap)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedProductPrefactor_masked_density_error.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.allocatedProductPrefactor_masked_density_error.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
