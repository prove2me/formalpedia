-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedProductFullGridPrefactor_site_masks_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:21:14.148808+00:00
-- url     : https://prove2.me/submissions/966aa4be-766c-4d4b-8feb-ea6ecce8b8db

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

theorem integerResidueMap_apply {I : Type*} (m : ℕ) (v : I → ℤ) (i : I) :
    integerResidueMap I m v i = (v i : ZMod m) := rfl

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI


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

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteKernelRestriction
namespace OAI

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

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBooleanSiteReconstruction
namespace OAI

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

end Erdos3

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

theorem allocatedProductFullGridPrefactor_site_masks_s2_oai
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

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedProductFullGridPrefactor_site_masks_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedProductFullGridPrefactor_site_masks_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
