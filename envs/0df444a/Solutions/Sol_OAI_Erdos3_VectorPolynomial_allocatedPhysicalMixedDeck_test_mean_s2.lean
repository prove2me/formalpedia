-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedPhysicalMixedDeck_test_mean_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:35:44.099533+00:00
-- url     : https://prove2.me/submissions/b60ab80e-e477-46a2-a35d-34444b063014

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedPhysicalMixedJet_test_mean_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem complexMean_congr_support {f g : X → ℂ}
    (h : ∀ x, p.weight x ≠ 0 → f x = g x) : p.complexMean f = p.complexMean g := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p.weight x = 0
  · simp only [hx, Complex.ofReal_zero, zero_mul]
  · rw [h x hx]

end Erdos3.FiniteProbabilityWeights

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

theorem integerMappedCubeTuple_residue {Z X K α : Type*}
    (input : K → Option α → Z ⊕ X) (z : Z → ℤ) (x y : X → ℤ) (m : ℕ)
    (hxy : integerResidueMap X m x = integerResidueMap X m y) (t : Finset α) :
    integerResidueMap K m (integerMappedCubeTuple input z x t) =
      integerResidueMap K m (integerMappedCubeTuple input z y t) := by
  apply integerAffineCube_residue_eq
  · funext k
    change ((Sum.elim z x (input k none) : ℤ) : ZMod m) =
      ((Sum.elim z y (input k none) : ℤ) : ZMod m)
    cases input k none with
    | inl j => rfl
    | inr j => exact congrFun hxy j
  · funext i k
    change ((Sum.elim z x (input k (some i)) : ℤ) : ZMod m) =
      ((Sum.elim z y (input k (some i)) : ℤ) : ZMod m)
    cases input k (some i) with
    | inl j => rfl
    | inr j => exact congrFun hxy j

theorem integerMappedJetMatrix_residue {Z X K α I N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℤ)
    (rows : I → Finset α) (x y : X → ℤ) (m : ℕ)
    (hxy : integerResidueMap X m x = integerResidueMap X m y) :
    integerResidueMatrix (integerMappedJetMatrix e input z rows x) m =
      integerResidueMatrix (integerMappedJetMatrix e input z rows y) m :=
  monomialCoefficientMatrix_residue_eq e _ _ rows m (integerMappedCubeTuple_residue input z x y m hxy)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem mixedScalarArrayLaw_probability {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Z → J → PMF ℤ) :
    IsProbabilityMeasure (mixedScalarArrayLaw c w p) := by
  let : ∀ i j, IsProbabilityMeasure (affineCoefficientMeasure (c i j) (w i j)) :=
    fun i j => affineCoefficientMeasure_probability _ (hw i j)
  unfold mixedScalarArrayLaw
  infer_instance

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CoveredJetSampler
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical Matrix

theorem mixedArrayIntegerImage_measurable {I Z J O : Type*} [Fintype J]
    (A : Matrix O J ℤ) :
    Measurable (mixedArrayIntegerImage (I := I) (Z := Z) A) := by
  unfold mixedArrayIntegerImage Matrix.mulVec dotProduct
  fun_prop

namespace VectorPolynomial

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

omit [∀ j, Fintype (I j)] [Fintype α] in
theorem canonicalCoefficientJetArrays_measurable :
    Measurable (canonicalCoefficientJetArrays (I := I) (n := n) root A rows) := by
  apply measurable_pi_iff.mpr
  intro j
  exact (mixedArrayIntegerImage_measurable
    (boundedCoefficientJetMatrix root A (j.val + 1) (rows j))).comp (measurable_pi_apply j)

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedCoefficientSampler
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedCoefficientSource_probability :
    IsProbabilityMeasure (allocatedCoefficientSource B U b hR hσ S) := by
  let : ∀ j, IsProbabilityMeasure (mixedScalarArrayLaw (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j)) :=
    fun j => mixedScalarArrayLaw_probability _ _ (allocatedLayerWidths_pos B U b hR hσ S j) _
  exact Measure.pi.instIsProbabilityMeasure _

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

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

omit [∀ j, Fintype (O j)] in
theorem allocatedPartitionedJetMatrix_kernel_range_le (j : Fin m) :
    (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range ≤
      (allocatedPartitionedJetMatrix B U b S x u v rows j).mulVecLin.range := by
  have he := allocatedKernelJet_full_image B U b S j x
    (principalTupleIntegers u) (principalTupleIntegers v) (rows j)
  change _ = (allocatedPartitionedJetMatrix B U b S x u v rows j).mulVecLin.range at he
  rw [← he, integerMatrix_fromCols_range]
  exact le_sup_left

theorem allocatedPartitionedJetMatrix_image_eq_of_residue (M : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hvw : principalResidueLabel M v = principalResidueLabel M w) (j : Fin m) :
    (allocatedPartitionedJetMatrix B U b S x u v rows j).mulVecLin.range =
      (allocatedPartitionedJetMatrix B U b S x u w rows j).mulVecLin.range := by
  apply integerMatrixImage_eq_of_residueMatrix _ _ M
  · exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u v rows j)
  · exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u w rows j)
  · apply integerMappedJetMatrix_residue
    exact congrArg principalTupleResidues hvw

theorem allocatedPhysicalDeckJet_law_eq_of_residue
    (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (M : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hvw : principalResidueLabel M v = principalResidueLabel M w) (d : ℕ) [NeZero d] :
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (root v) (dirs v) rows d) =
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
        (coefficientDeckJetMap (root w) (dirs w) rows d) := by
  have hr (j : Fin m) :
      (boundedCoefficientJetMatrix (root v) (dirs v) (j.val + 1) (rows j)).mulVecLin.range =
        (boundedCoefficientJetMatrix (root w) (dirs w) (j.val + 1) (rows j)).mulVecLin.range := by
    rw [← allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j,
      ← allocatedPartitionedJetMatrix_eq_physical B U b S x u w rows j]
    exact allocatedPartitionedJetMatrix_image_eq_of_residue B U b S x u v w rows M hperiod hvw j
  exact uniformPMF_map_hom_eq_of_range_eq _ _
    (coefficientDeckJetMap_range_eq_of_integer_range_eq
      (α := α) (K := LayerSamplerVariables G I n B) (O := O) (B := Q)
      (root v) (dirs v) rows (root w) (dirs w) hr d)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoveredFixedTest
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem finitePMF_integral_measurable {X T : Type*} [MeasurableSpace X]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (p : PMF T) (f : X → T → ℂ) (hf : ∀ t, Measurable (fun x => f x t)) :
    Measurable (fun x => ∫ t, f x t ∂p.toMeasure) := by
  simp only [PMF.integral_eq_sum, Complex.real_smul]
  exact Finset.measurable_sum _ (fun t _ => (hf t).const_mul ((p t).toReal : ℂ))

theorem finitePMF_integral_norm_le {T : Type*} [MeasurableSpace T]
    (p : PMF T) (f : T → ℂ) {C : ℝ} (hf : ∀ t, ‖f t‖ ≤ C) :
    ‖∫ t, f t ∂p.toMeasure‖ ≤ C := by
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (ae_of_all p.toMeasure hf)

theorem finitePMF_integral_comp {T Y : Type*} [Fintype T] [Fintype Y]
    [MeasurableSpace T] [MeasurableSingletonClass T]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (p : PMF T) (f : T → Y) (φ : Y → ℂ) :
    (∫ t, φ (f t) ∂p.toMeasure) = ∫ y, φ y ∂(p.map f).toMeasure := by
  rw [← PMF.toMeasure_map f p (measurable_of_finite f)]
  exact (integral_map (measurable_of_finite f).aemeasurable
    (measurable_of_finite φ).aestronglyMeasurable).symm

theorem probabilityProduct_finiteMean {X Y T : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (w : FiniteProbabilityWeights T) (f : T → X × Y → ℂ)
    (hf : ∀ t, Measurable (f t)) {C : ℝ} (hb : ∀ t p, ‖f t p‖ ≤ C) :
    (∫ p, w.complexMean (fun t => f t p) ∂μ.prod ν) =
      ∫ x, w.complexMean (fun t => ∫ y, f t (x, y) ∂ν) ∂μ := by
  have hi (t) : Integrable (f t) (μ.prod ν) :=
    Integrable.of_bound (hf t).aestronglyMeasurable C (ae_of_all _ (hb t))
  rw [integral_prod _ (w.complexMean_integrable _ _ hi)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  apply w.integral_complexMean
  intro t
  exact Integrable.of_bound ((hf t).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    C (ae_of_all _ (fun y => hb t (x, y)))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "split" => allocatedCoefficientSplit B U b S
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

variable (φ : (AllocatedFrozenCoefficients B U b S ×
  (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))) × (∀ j, O j → Q j → ZMod d) → ℂ)

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedDeckMixedTest_measurable (hφ : Measurable φ) :
    Measurable (fun p : AllocatedFrozenCoefficients B U b S ×
      (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) =>
        allocatedDeckMixedTest B U b S x u v₀ rows Q d φ p.1 p.2) :=
  finitePMF_integral_measurable deck _ (fun _ => hφ.comp (measurable_id.prodMk measurable_const))

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedDeckMixedTest_norm_le {C : ℝ} (hφ : ∀ p, ‖φ p‖ ≤ C)
    (a₀ : AllocatedFrozenCoefficients B U b S)
    (t : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :
    ‖allocatedDeckMixedTest B U b S x u v₀ rows Q d φ a₀ t‖ ≤ C :=
  finitePMF_integral_norm_le deck _ (fun _ => hφ _)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

theorem allocatedPhysicalMixedDeck_test_mean_s2_oai
    (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (M : ℕ) (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hresidue : ∀ v, weights.weight v ≠ 0 → principalResidueLabel M v = principalResidueLabel M v₀)
    (hφ : Measurable φ) {C : ℝ} (hbound : ∀ p, ‖φ p‖ ≤ C) :
    (∫ p, weights.complexMean (fun v =>
      φ (((split p.1).1, canonicalCoefficientJetArrays (root v) (dirs v) rows p.1),
        coefficientDeckJetMap (root v) (dirs v) rows d p.2)) ∂(source).prod (deck).toMeasure) =
      ∫ a₀, ∫ z,
        (weights.mean (fun v => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) : ℂ) *
          allocatedDeckMixedTest B U b S x u v₀ rows Q d φ a₀
            (allocatedMixedJetReconstruct B U b S x u v₀ rows a₀ z) ∂reference ∂frozenSource := by
  let : IsProbabilityMeasure source := allocatedCoefficientSource_probability B U b hR hσ S
  have htest (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
      Measurable (fun p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
        CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d =>
        φ (((split p.1).1, canonicalCoefficientJetArrays (root v) (dirs v) rows p.1),
          coefficientDeckJetMap (root v) (dirs v) rows d p.2)) :=
    hφ.comp ((((split).measurable.comp measurable_fst).fst.prodMk
      ((canonicalCoefficientJetArrays_measurable (root v) (dirs v) rows).comp measurable_fst)).prodMk
        ((measurable_of_finite (coefficientDeckJetMap (B := Q) (root v) (dirs v) rows d)).comp measurable_snd))
  calc
    _ = ∫ a, weights.complexMean (fun v => ∫ r,
        φ (((split a).1, canonicalCoefficientJetArrays (root v) (dirs v) rows a),
          coefficientDeckJetMap (root v) (dirs v) rows d r) ∂(deck).toMeasure) ∂source :=
      probabilityProduct_finiteMean source (deck).toMeasure weights _ htest (fun _ p => hbound _)
    _ = ∫ a, weights.complexMean (fun v => allocatedDeckMixedTest B U b S x u v₀ rows Q d φ
        (split a).1 (canonicalCoefficientJetArrays (root v) (dirs v) rows a)) ∂source := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a
      apply weights.complexMean_congr_support
      intro v hv
      let F := fun e => φ (((split a).1, canonicalCoefficientJetArrays (root v) (dirs v) rows a), e)
      have hlaw := allocatedPhysicalDeckJet_law_eq_of_residue B U b S x u v v₀ rows Q M hperiod
        (hresidue v hv) d
      exact (finitePMF_integral_comp deck (coefficientDeckJetMap (root v) (dirs v) rows d) F).trans
        ((congrArg (fun p : PMF (∀ j, O j → Q j → ZMod d) => ∫ e, F e ∂p.toMeasure) hlaw).trans
          (finitePMF_integral_comp deck (coefficientDeckJetMap (root v₀) (dirs v₀) rows d) F).symm)
    _ = _ := allocatedPhysicalMixedJet_test_mean_s2 B U b hR hσ S x u v₀ rows s hA hσ1 weights
      (allocatedDeckMixedTest B U b S x u v₀ rows Q d φ)
      (allocatedDeckMixedTest_measurable B U b S x u v₀ rows Q d φ hφ)
      (allocatedDeckMixedTest_norm_le B U b S x u v₀ rows Q d φ hbound)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedPhysicalMixedDeck_test_mean_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.allocatedPhysicalMixedDeck_test_mean_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
