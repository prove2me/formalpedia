-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedMaskedProfile_chart_mean_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:06:44.449575+00:00
-- url     : https://prove2.me/submissions/e0e14cdc-5a00-473a-beb3-13694935a34c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B217
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedFullGridDensity_mean_s2
import Theorems.Thm_OAI_Erdos3_containedSupportedProgressionAxisLaw_residue_eq_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

theorem residueLatticeImage_comap {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L m).comap (integerResidueMap I m) = L := by
  apply Submodule.comap_map_eq_self
  rwa [integerResidueMap_ker]

theorem residueLatticeImage_determines_lattice {I : Type*} [Fintype I]
    (L K : Submodule ℤ (I → ℤ)) (m : ℕ)
    (hL : integerScalarLattice I (m : ℤ) ≤ L) (hK : integerScalarLattice I (m : ℤ) ≤ K)
    (h : residueLatticeImage L m = residueLatticeImage K m) : L = K := by
  rw [← residueLatticeImage_comap L m hL, ← residueLatticeImage_comap K m hK, h]

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

theorem integerMatrixResidue_image_eq {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (m : ℕ) :
    residueLatticeImage A.mulVecLin.range m =
      (integerResidueMatrix A m).mulVecLin.range.restrictScalars ℤ := by
  ext v
  exact integerMatrixResidue_mem A m v

theorem integerMatrixImage_eq_of_residueMatrix {I J : Type*} [Fintype I] [Fintype J]
    (A B : Matrix I J ℤ) (m : ℕ)
    (hA : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (hB : integerScalarLattice I (m : ℤ) ≤ B.mulVecLin.range)
    (hAB : integerResidueMatrix A m = integerResidueMatrix B m) :
    A.mulVecLin.range = B.mulVecLin.range := by
  apply residueLatticeImage_determines_lattice _ _ m hA hB
  rw [integerMatrixResidue_image_eq, integerMatrixResidue_image_eq, hAB]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialResidues
namespace OAI

section

namespace Erdos3

theorem integerPolynomial_eval_residue {X : Type*} (p : MvPolynomial X ℤ)
    (m : ℕ) (x : X → ℤ) :
    ((MvPolynomial.eval x p : ℤ) : ZMod m) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod m)) (integerResidueMap X m x) p := by
  have heq : integerResidueMap X m x = (fun i => (x i : ZMod m)) := rfl
  rw [heq]
  simpa only [MvPolynomial.eval₂_id, RingHom.comp_id, Int.coe_castRingHom] using
    MvPolynomial.hom_eval₂ p (RingHom.id ℤ) (Int.castRingHom (ZMod m)) x

theorem integerPolynomial_eval_congr {X : Type*} (p : MvPolynomial X ℤ)
    (m : ℕ) {x y : X → ℤ} (hxy : integerResidueMap X m x = integerResidueMap X m y) :
    ((MvPolynomial.eval x p : ℤ) : ZMod m) = ((MvPolynomial.eval y p : ℤ) : ZMod m) := by
  rw [integerPolynomial_eval_residue, integerPolynomial_eval_residue, hxy]

theorem integerBooleanCoefficient_residue {α : Type*} [DecidableEq α]
    (m : ℕ) (f : Finset α → ℤ) (s : Finset α) :
    ((booleanCoefficient f s : ℤ) : ZMod m) =
      booleanCoefficient (fun t => (f t : ZMod m)) s :=
  booleanCoefficient_map (Int.castRingHom (ZMod m)) f s

theorem integerBooleanCoefficient_congr {α : Type*} [DecidableEq α]
    (m : ℕ) (f g : Finset α → ℤ) (s : Finset α)
    (hfg : ∀ t ∈ s.powerset, (f t : ZMod m) = (g t : ZMod m)) :
    ((booleanCoefficient f s : ℤ) : ZMod m) = ((booleanCoefficient g s : ℤ) : ZMod m) := by
  rw [integerBooleanCoefficient_residue, integerBooleanCoefficient_residue]
  unfold booleanCoefficient
  apply Finset.sum_congr rfl
  intro t ht
  dsimp only
  rw [hfg t ht]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAffineResidues
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem integerJetMatrix_residue_eq {α K O J : Type*} [DecidableEq α]
    (basis : J → MvPolynomial K ℤ) (vertices vertices' : Finset α → K → ℤ)
    (rows : O → Finset α) (m : ℕ)
    (hvertices : ∀ o t, t ∈ (rows o).powerset →
      integerResidueMap K m (vertices t) = integerResidueMap K m (vertices' t)) :
    integerResidueMatrix (integerJetMatrix basis vertices rows) m =
      integerResidueMatrix (integerJetMatrix basis vertices' rows) m := by
  ext o j
  apply integerBooleanCoefficient_congr
  intro t ht
  exact integerPolynomial_eval_congr (basis j) m (hvertices o t ht)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerAffineCube_residue_eq {α K : Type*}
    (root root' : K → ℤ) (D D' : Matrix α K ℤ) (m : ℕ)
    (hroot : integerResidueMap K m root = integerResidueMap K m root')
    (hD : integerResidueMatrix D m = integerResidueMatrix D' m) (t : Finset α) :
    integerResidueMap K m (integerAffineCube root D t) =
      integerResidueMap K m (integerAffineCube root' D' t) := by
  funext k
  change ((root k + ∑ r ∈ t, D r k : ℤ) : ZMod m) =
    ((root' k + ∑ r ∈ t, D' r k : ℤ) : ZMod m)
  push_cast
  have hk : (root k : ZMod m) = (root' k : ZMod m) := congrFun hroot k
  rw [hk]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  exact congrFun (congrFun hD r) k

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

theorem monomialCoefficientMatrix_residue_eq {α K I N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (vertices vertices' : Finset α → K → ℤ) (rows : I → Finset α) (m : ℕ)
    (hv : ∀ t, integerResidueMap K m (vertices t) = integerResidueMap K m (vertices' t)) :
    integerResidueMatrix (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) vertices rows) m =
      integerResidueMatrix (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) vertices' rows) m :=
  integerJetMatrix_residue_eq _ _ _ _ _ (fun _ t _ => hv t)


open MeasureTheory
open scoped BigOperators NNReal

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


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalResidueMixture
namespace OAI

section

namespace Erdos3

theorem integerMappedCubeTuple_residue_both {Z X K α : Type*}
    (input : K → Option α → Z ⊕ X) (z w : Z → ℤ) (x y : X → ℤ) (q : ℕ)
    (hzw : integerResidueMap Z q z = integerResidueMap Z q w)
    (hxy : integerResidueMap X q x = integerResidueMap X q y) (t : Finset α) :
    integerResidueMap K q (integerMappedCubeTuple input z x t) =
      integerResidueMap K q (integerMappedCubeTuple input w y t) := by
  apply integerAffineCube_residue_eq
  · funext k
    change ((Sum.elim z x (input k none) : ℤ) : ZMod q) =
      ((Sum.elim w y (input k none) : ℤ) : ZMod q)
    cases input k none with
    | inl j => exact congrFun hzw j
    | inr j => exact congrFun hxy j
  · funext i k
    change ((Sum.elim z x (input k (some i)) : ℤ) : ZMod q) =
      ((Sum.elim w y (input k (some i)) : ℤ) : ZMod q)
    cases input k (some i) with
    | inl j => exact congrFun hzw j
    | inr j => exact congrFun hxy j

theorem integerMappedJetMatrix_residue_both {Z X K α I N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
    (z w : Z → ℤ) (rows : I → Finset α) (x y : X → ℤ) (q : ℕ)
    (hzw : integerResidueMap Z q z = integerResidueMap Z q w)
    (hxy : integerResidueMap X q x = integerResidueMap X q y) :
    integerResidueMatrix (integerMappedJetMatrix e input z rows x) q =
      integerResidueMatrix (integerMappedJetMatrix e input w rows y) q :=
  monomialCoefficientMatrix_residue_eq e _ _ rows q
    (integerMappedCubeTuple_residue_both input z w x y q hzw hxy)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_mul_const {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → ℝ) (c : ℝ) : p.mean (fun x => f x * c) = p.mean f * c := by
  simp only [mean, ← mul_assoc, Finset.sum_mul]

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformImageLawCongruence
namespace OAI

section

namespace Erdos3

open scoped Classical Matrix

theorem uniformPMF_map_hom_eq_of_range_eq {G G' H : Type*}
    [AddCommGroup G] [AddCommGroup G'] [AddCommGroup H]
    [Fintype G] [Fintype G'] [Fintype H]
    (f : G →+ H) (g : G' →+ H) (h : f.range = g.range) :
    (PMF.uniformOfFintype G).map f = (PMF.uniformOfFintype G').map g := by
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [uniformPMF_map_hom_image, h]

theorem integerResidueMatrix_range_eq_of_integer_range_eq
    {I J K : Type*} [Fintype J] [Fintype K]
    (A : Matrix I J ℤ) (B : Matrix I K ℤ)
    (h : A.mulVecLin.range = B.mulVecLin.range) (d : ℕ) :
    (integerResidueMatrix A d).mulVecLin.toAddMonoidHom.range =
      (integerResidueMatrix B d).mulVecLin.toAddMonoidHom.range := by
  ext y
  change (∃ x, integerResidueMatrix A d *ᵥ x = y) ↔
    (∃ x, integerResidueMatrix B d *ᵥ x = y)
  rw [← integerMatrixResidue_mem, ← integerMatrixResidue_mem, h]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientDeckImageCongruence
namespace OAI

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

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

omit [∀ j, Fintype (O j)] [∀ j, Fintype (B j)] in
theorem coefficientDeckJetMap_mem_range_iff (d : ℕ)
    (v : ∀ j, O j → B j → ZMod d) :
    v ∈ (coefficientDeckJetMap root D rows d).range ↔
      ∀ j (i : B j), (fun t => v j t i) ∈
        (integerResidueMatrix (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d).mulVecLin.toAddMonoidHom.range := by
  constructor
  · rintro ⟨a, rfl⟩ j i
    exact ⟨(fun e => a j e i), (coefficientDeckJetMap_coordinate root D rows d a j i).symm⟩
  · intro h
    change ∀ j (i : B j), ∃ a, integerResidueMatrix
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d *ᵥ a = (fun t => v j t i) at h
    choose a ha using h
    refine ⟨(fun j e i => a j i e), ?_⟩
    funext j t i
    exact (congrFun (coefficientDeckJetMap_coordinate root D rows d (fun j e i => a j i e) j i) t).trans
      (congrFun (ha j i) t)

omit [∀ j, Fintype (O j)] [∀ j, Fintype (B j)] in
theorem coefficientDeckJetMap_range_eq_of_integer_range_eq
    (root' : K → ℤ) (D' : Matrix α K ℤ)
    (h : ∀ j, (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range =
      (boundedCoefficientJetMatrix root' D' (j.val + 1) (rows j)).mulVecLin.range)
    (d : ℕ) :
    (coefficientDeckJetMap (B := B) root D rows d).range =
      (coefficientDeckJetMap (B := B) root' D' rows d).range := by
  ext v
  simp only [coefficientDeckJetMap_mem_range_iff]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro i
  rw [integerResidueMatrix_range_eq_of_integer_range_eq _ _ (h j) d]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteGoodSupport
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem mean_congr_on_support {f g : X → ℝ}
    (h : ∀ x, p.weight x ≠ 0 → f x = g x) : p.mean f = p.mean g :=
  le_antisymm (p.mean_mono_on_support (fun x hx => (h x hx).le))
    (p.mean_mono_on_support (fun x hx => (h x hx).ge))

end Erdos3.FiniteProbabilityWeights

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidue
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
local notation "grid" => allocatedGridAxis (I := I) U b S.value
variable (u u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α) (q : ℕ)
variable (hu : principalResidueLabel q u = principalResidueLabel q u₀)
variable (hv : principalResidueLabel q v = principalResidueLabel q v₀)

include hu hv

theorem allocatedNonkernelJetMatrix_residue_both (j : Fin m) :
    integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) q =
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u₀ rows j v₀) q := by
  apply integerMappedJetMatrix_residue_both
  · funext z
    cases z with
    | inl z => rfl
    | inr z => exact congrFun (congrArg principalTupleResidues hu) z
  · exact congrArg principalTupleResidues hv

theorem allocatedPartitionedJetMatrix_residue_both (j : Fin m) :
    integerResidueMatrix (allocatedPartitionedJetMatrix B U b S x u v rows j) q =
      integerResidueMatrix (allocatedPartitionedJetMatrix B U b S x u₀ v₀ rows j) q := by
  apply integerMappedJetMatrix_residue_both
  · funext z
    cases z with
    | inl z => rfl
    | inr z => exact congrFun (congrArg principalTupleResidues hu) z
  · exact congrArg principalTupleResidues hv

variable [∀ j, Fintype (O j)]

theorem allocatedPartitionedJetMatrix_image_eq_of_residue_both
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range) (j : Fin m) :
    (allocatedPartitionedJetMatrix B U b S x u v rows j).mulVecLin.range =
      (allocatedPartitionedJetMatrix B U b S x u₀ v₀ rows j).mulVecLin.range := by
  apply integerMatrixImage_eq_of_residueMatrix _ _ q
  · exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u v rows j)
  · exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u₀ v₀ rows j)
  · exact allocatedPartitionedJetMatrix_residue_both B U b S x u u₀ v v₀ rows q hu hv j

theorem allocatedPhysicalDeckJet_law_eq_of_residue_both
    (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (d : ℕ) [NeZero d] :
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) rows d) =
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u₀ v₀))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u₀ v₀)) rows d) := by
  have hr (j : Fin m) :
      (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) (j.val + 1) (rows j)).mulVecLin.range =
      (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u₀ v₀))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u₀ v₀)) (j.val + 1) (rows j)).mulVecLin.range := by
    rw [← allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j,
      ← allocatedPartitionedJetMatrix_eq_physical B U b S x u₀ v₀ rows j]
    exact allocatedPartitionedJetMatrix_image_eq_of_residue_both B U b S x u u₀ v v₀ rows q hu hv hperiod j
  exact uniformPMF_map_hom_eq_of_range_eq _ _
    (coefficientDeckJetMap_range_eq_of_integer_range_eq
      (α := α) (K := LayerSamplerVariables G I n B) (O := O) (B := Q) _ _ rows _ _ hr d)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) ((allocatedPrincipalSides B U b S) j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (u u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u ≠ 0) (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

include hu hu₀

theorem allocatedSupportedSlicedNonkernel_residue_constant (j : Fin m) :
    integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) q =
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u₀ rows j v₀) q := by
  have hlabel := containedSupportedProgressionAxisLaw_residue_eq_s2 B (layerSamplerDegree I n) sides H step c
    (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid u u₀ hu hu₀
  exact allocatedNonkernelJetMatrix_residue_both B U b S x u u₀ v₀ v₀ rows q hlabel rfl j

variable [∀ j, Fintype (O j)]

theorem allocatedSupportedSlicedDeck_law_constant
    (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (d : ℕ) [NeZero d] :
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)) rows d) =
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u₀ v₀))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u₀ v₀)) rows d) := by
  have hlabel := containedSupportedProgressionAxisLaw_residue_eq_s2 B (layerSamplerDegree I n) sides H step c
    (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid u u₀ hu hu₀
  exact allocatedPhysicalDeckJet_law_eq_of_residue_both B U b S x u u₀ v₀ v₀ rows q hlabel rfl Q hperiod d

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSupportedSlicedUniformPhysicalSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => {t : Finset α // t ∈ rowSets j}) j) (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) ((fun j => (Subtype.val : rowSets j → Finset α)) j)).mulVecLin.range)
local notation "root" u => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" u => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "residue" u:max => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) q)

include hu₀ hperiod in

theorem allocatedSupportedSlicedDeck_density_constant
    (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U b S))
    (hu : (gridLaw).weight u ≠ 0) (z : ∀ j, rowTypes j → Q j → ZMod d) :
    coefficientDeckJetDensity (root u) (dirs u) rows d z =
      coefficientDeckJetDensity (root u₀) (dirs u₀) rows d z := by
  have he := allocatedSupportedSlicedDeck_law_constant B U b S x H step c hH hsubset q r hcell
    u u₀ hu hu₀ v₀ rows Q hperiod d
  unfold coefficientDeckJetDensity
  convert congrArg (fun p : PMF (∀ j, rowTypes j → Q j → ZMod d) =>
    (Fintype.card (∀ j, rowTypes j → Q j → ZMod d) : ℝ) * (p z).toReal) he using 1 <;> congr!

include hu₀ hperiod in

theorem allocatedSupportedSlicedCoveredFactor_mean
    (z : ∀ j, (I j → rowTypes j → ℝ) × (Fin (n j) → rowTypes j → ℤ))
    (deck : ∀ j, rowTypes j → Q j → ZMod d) :
    (gridLaw).mean (fun u => allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z deck) =
      allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val) *
        coefficientDeckJetDensity (root u₀) (dirs u₀) rows d deck / coveredJetArrayScale (O := rowTypes) U := by
  have he : (gridLaw).mean (fun u => allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z deck) =
      (gridLaw).mean (fun u => allocatedGridJetDensity B U b hR hσ S x u v₀ rows
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val) *
        coefficientDeckJetDensity (root u₀) (dirs u₀) rows d deck / coveredJetArrayScale (O := rowTypes) U) := by
    apply FiniteProbabilityWeights.mean_congr_on_support
    intro u hu
    unfold allocatedCoveredFixedFactor
    rw [allocatedSupportedSlicedDeck_density_constant B U b S rowSets H step c hH hsubset q r hcell x u₀ hu₀ v₀ Q d hperiod u hu]
  rw [he]
  simp only [div_eq_mul_inv, FiniteProbabilityWeights.mean_mul_const]
  rw [allocatedSupportedSlicedFullGridDensity_mean_s2 B U b hR hσ S rowSets H step c hH hsubset q r hcell x v₀]

include hu₀ in

theorem allocatedSupportedSlicedLongProfile_constant
    (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U b S))
    (hu : (gridLaw).weight u ≠ 0)
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (z : AllocatedLongJetRows B U b S rowTypes) :
    allocatedLongProfileDensity B U b S x rows q (residue u) f z =
      allocatedLongProfileDensity B U b S x rows q (residue u₀) f z := by
  have he : (residue u) = (residue u₀) := by
    funext j
    exact allocatedSupportedSlicedNonkernel_residue_constant B U b S x H step c hH hsubset q r hcell
      u u₀ hu hu₀ v₀ rows j
  rw [he]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => {t : Finset α // t ∈ rowSets j}) j) (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) ((fun j => (Subtype.val : rowSets j → Finset α)) j)).mulVecLin.range)
local notation "root" u => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" u => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "residue" u:max => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) q)

include hu₀ hperiod in

theorem allocatedSupportedSlicedMaskedCoveredFactor_mean
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (z : ∀ j, (I j → rowTypes j → ℝ) × (Fin (n j) → rowTypes j → ℤ))
    (deck : ∀ j, rowTypes j → Q j → ZMod d) :
    (gridLaw).mean (fun u => allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z deck *
      allocatedLongProfileDensity B U b S x rows q (residue u) f
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val)) =
    (allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val) *
      coefficientDeckJetDensity (root u₀) (dirs u₀) rows d deck / coveredJetArrayScale (O := rowTypes) U) *
      allocatedLongProfileDensity B U b S x rows q (residue u₀) f
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val) := by
  have he : (gridLaw).mean (fun u => allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z deck *
      allocatedLongProfileDensity B U b S x rows q (residue u) f
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val)) =
    (gridLaw).mean (fun u => allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z deck *
      allocatedLongProfileDensity B U b S x rows q (residue u₀) f
        (fun a => coefficientJetAxisEquiv rowTypes I n z a.val)) := by
    apply FiniteProbabilityWeights.mean_congr_on_support
    intro u hu
    rw [allocatedSupportedSlicedLongProfile_constant B U b S rowSets H step c hH hsubset q r hcell x
      u₀ hu₀ v₀ u hu]
  rw [he, FiniteProbabilityWeights.mean_mul_const,
    allocatedSupportedSlicedCoveredFactor_mean B U b hR hσ S rowSets H step c hH hsubset q r hcell x
      u₀ hu₀ v₀ Q d hperiod]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => {t : Finset α // t ∈ rowSets j}) j) (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) ((fun j => (Subtype.val : rowSets j → Finset α)) j)).mulVecLin.range)
local notation "root" u => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" u => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "residue" u:max => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) q)

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "quarter" => (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter
local notation "y₀" => principalAxisJoin grid u₀ v₀
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x

include hu₀ hperiod in

theorem allocatedSupportedSlicedMaskedProfile_chart_mean_s2_oai
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (z : MixedCoveredJetSource I rowTypes Q n d) (hz : z ∈ region) :
    (gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
      (principalAxisJoin grid u v₀) q f (chart z)) =
    gridDensity (allocatedFullGridRowsOfMixed B U b S rowSets z.1) *
      allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f (chart z) := by
  have hinj := mixedCoveredJetChart_injOn U o b hb bW d quarter
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  simp only [allocatedWholeMaskedCoveredProfile, allocatedWholeMaskedGridlessProfile,
    principalAxisRestrict_join_left, principalAxisRestrict_join_right,
    allocatedCoveredProfileDensity, allocatedGridlessCoveredProfile,
    restrictedChartDensity_apply _ _ _ _ hinj hz, one_mul]
  have h := allocatedSupportedSlicedMaskedCoveredFactor_mean B U b hR hσ S rowSets
    H step c hH hsubset q r hcell x u₀ hu₀ v₀ Q d hperiod f z.1 z.2
  convert h using 1 <;> try rfl
  change gridDensity (fun a => coefficientJetAxisEquiv rowTypes I n z.1 a.val) *
    (coefficientDeckJetDensity (root u₀) (dirs u₀) rows d z.2 / coveredJetArrayScale (O := rowTypes) U *
      allocatedLongProfileDensity B U b S x rows q (residue u₀) f
        (fun a => coefficientJetAxisEquiv rowTypes I n z.1 a.val)) = _
  ring

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uα, u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedMaskedProfile_chart_mean_s2_oai.{uα, u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedMaskedProfile_chart_mean_s2_oai.{uα, u_1, u_2, u_3, u_4, u_5}
