-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedRecoveredSample_site_chart_base
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-12T00:02:25.074029+00:00
-- url     : https://prove2.me/submissions/efa61b66-711b-45a0-8e83-7293b8d41524

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B147
import Definitions.Def_OAIErdos3B163
import Definitions.Def_OAIErdos3B173

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory Module _root_.Set
open scoped ENNReal

variable {E T I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] [Fintype I]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D : Type*} [Fintype D] {n : ℕ}

end Erdos3

end

section

namespace Erdos3

open Module Submodule _root_.Set

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)

variable [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
variable [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem orthonormalMixedChart_sum_zsmul (o : OrthonormalBasis I ℝ W)
    {S : Type*} (s : Finset S) (a : S → ℤ)
    (x : S → (I → ℝ) × (Fin n → ℤ)) :
    orthonormalMixedChart o (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • orthonormalMixedChart o (x i) := by
  change orthonormalMixedChartHom W o _ = _
  simp only [map_sum, map_zsmul, orthonormalMixedChartHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

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
open scoped BigOperators ENNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem mixedArrayRegroup_apply {I Z J : Type*} (x : (I → J → ℝ) × (Z → J → ℤ)) (j : J) :
    mixedArrayRegroup I Z J x j = (fun i => x.1 i j, fun z => x.2 z j) := rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module
open scoped BigOperators ENNReal

variable {E I Z O : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [Fintype I] [Fintype Z] (o : OrthonormalBasis I ℝ E)

variable [Fintype O]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedArrayIntegerImage
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

variable {D I J O Z : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}

omit [Fintype I] in
theorem mixedArrayIntegerImage_regroup (A : Matrix O J ℤ)
    (x : (I → J → ℝ) × (Z → J → ℤ)) (r : O) :
    mixedArrayRegroup I Z O (mixedArrayIntegerImage A x) r =
      ∑ j, A r j • mixedArrayRegroup I Z J x j := by
  apply Prod.ext
  · funext i
    simp only [mixedArrayIntegerImage, mixedArrayRegroup_apply, Prod.fst_sum,
      Finset.sum_apply]
    change (∑ j, (A r j : ℝ) * x.1 i j) = ∑ j, A r j • x.1 i j
    exact Finset.sum_congr rfl (fun j _ => Int.cast_smul_eq_zsmul ℝ (A r j) (x.1 i j))
  · funext z
    simp only [mixedArrayIntegerImage, mixedArrayRegroup_apply, Prod.snd_sum,
      Finset.sum_apply]
    change (∑ j, A r j * x.2 z j) = ∑ j, A r j • x.2 z j
    simp only [smul_eq_mul]

variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (o : OrthonormalBasis I ℝ W)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxObservedMean
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

namespace BooleanCubeKernel

open scoped BigOperators

theorem integerPhysicalSite_add {K I : Type*} [Fintype K]
    (root : K → ℤ) (z w : Option K × I → ℤ) :
    integerPhysicalSite root (z + w) = integerPhysicalSite root z + integerPhysicalSite root w := by
  funext i
  simp only [integerPhysicalSite, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem integerPhysicalSite_baseTranslation {K I : Type*} [Fintype K]
    (root : K → ℤ) (b : I → ℤ) :
    integerPhysicalSite root (integerBaseTranslation b) = b := by
  funext i
  simp [integerPhysicalSite, integerBaseTranslation, baseArrayJoin]

theorem integerPhysicalSite_baseTranslation_add {K I : Type*} [Fintype K]
    (root : K → ℤ) (b : I → ℤ) (z : Option K × I → ℤ) :
    integerPhysicalSite root (integerBaseTranslation b + z) = b + integerPhysicalSite root z := by
  rw [integerPhysicalSite_add, integerPhysicalSite_baseTranslation]

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (N : I → ℕ) (hN : (integerBox N).Nonempty)

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open BooleanCubeKernel
open scoped BigOperators Classical

variable {K : Type*} {P : K → ℕ} {q r : ℕ}

variable [Fintype K] {X : Type*}

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

open scoped BigOperators

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

theorem coefficientDeckKernel_jets (d : ℕ) (hd : 0 < d)
    (r : CoefficientDeckResidues (K := K) B d) (j : Fin m) (t : O j) :
    euclideanCoefficientJetMap U root D rows (coefficientDeckKernelEquiv U bW d hd r).val j t =
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (coefficientDeckJetMap root D rows d r j t)).val := by
  rw [euclideanCoefficientJetMap_apply]
  simp_rw [coefficientDeckKernelEquiv_coordinate]
  let f := ((quotientIntegerCover
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup d).ker.subtype).comp
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd).toAddMonoidHom
  change (∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e • f (r j e)) =
    f (∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e • r j e)
  simp only [map_sum, map_zsmul]

variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem canonicalCoefficientDeckSample_jets (d : ℕ) (hd : 0 < d)
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d)
    (j : Fin m) (t : O j) :
    euclideanCoefficientJetMap U root D rows (canonicalCoefficientDeckSample U bW b hb o d hd x r) j t =
      euclideanCoefficientJetMap U root D rows (canonicalCoefficientCoverLift U b hb o d x) j t +
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (coefficientDeckJetMap root D rows d r j t)).val := by
  simp only [canonicalCoefficientDeckSample, map_add, Pi.add_apply,
    coefficientDeckKernel_jets]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientDeckChartRecovery
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical
attribute [local irreducible] coefficientDeckKernelEquiv

variable {K : Type*} {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem canonicalCoefficientDeckSample_existsUnique_residue (q : ℕ) (hq : 0 < q)
    (x : CoefficientSamplerArrays (K := K) I n) (y : CoefficientTorus (K := K) U)
    (hy : quotientIntegerCover (coefficientIntegerLattice (K := K) U) q y =
      canonicalCoefficientSample U b hb o x) :
    ∃! r : CoefficientDeckResidues (K := K) E q,
      canonicalCoefficientDeckSample U bW b hb o q hq x r = y := by
  let z : (quotientIntegerCover (coefficientIntegerLattice (K := K) U) q).ker :=
    ⟨y - canonicalCoefficientCoverLift U b hb o q x, by
      change quotientIntegerCover (coefficientIntegerLattice (K := K) U) q
        (y - canonicalCoefficientCoverLift U b hb o q x) = 0
      rw [map_sub, hy, canonicalCoefficientCoverLift_projection U b hb o q hq, sub_self]⟩
  let r := (coefficientDeckKernelEquiv U bW q hq).symm z
  have hr : canonicalCoefficientDeckSample U bW b hb o q hq x r = y := by
    unfold canonicalCoefficientDeckSample
    change canonicalCoefficientCoverLift U b hb o q x +
      (coefficientDeckKernelEquiv U bW q hq ((coefficientDeckKernelEquiv U bW q hq).symm z)).val = y
    rw [AddEquiv.apply_symm_apply]
    change canonicalCoefficientCoverLift U b hb o q x +
      (y - canonicalCoefficientCoverLift U b hb o q x) = y
    abel
  exact ⟨r, hr, fun s hs => canonicalCoefficientDeckSample_residue_injective
    U bW b hb o q hq x (hs.trans hr.symm)⟩

variable [Fintype K]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredMixedArrayImage
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

variable [∀ j, Fintype (O j)]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I : Fin m → Type*} [∀ j, Fintype (O j)]
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem normalizedLatticeRepresentative_sum_zsmul {S : Type*} (s : Finset S)
    (a : S → ℤ) (x : S → W × (Fin n → ℤ)) :
    normalizedLatticeRepresentative W b hb (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • normalizedLatticeRepresentative W b hb (x i) := by
  change normalizedLatticeRepresentativeHom W b hb _ = _
  simp only [map_sum, map_zsmul, normalizedLatticeRepresentativeHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk]

theorem normalizedCoverLift_sum_zsmul (d : ℕ) {S : Type*} (s : Finset S)
    (a : S → ℤ) (x : S → W × (Fin n → ℤ)) :
    normalizedCoverLift W b hb d (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • normalizedCoverLift W b hb d (x i) := by
  have he (i) : (d : ℝ)⁻¹ • (a i • normalizedLatticeRepresentative W b hb (x i)) =
      a i • ((d : ℝ)⁻¹ • normalizedLatticeRepresentative W b hb (x i)) := smul_comm _ _ _
  simp only [normalizedCoverLift, normalizedLatticeRepresentative_sum_zsmul,
    Finset.smul_sum, he]
  change QuotientAddGroup.mk' _ (∑ i ∈ s, a i • ((d : ℝ)⁻¹ •
    normalizedLatticeRepresentative W b hb (x i))) = _
  simp only [map_sum, map_zsmul]
  rfl

namespace VectorPolynomial

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable {ns : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bs : ∀ j, Basis (Fin (ns j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hbs : ∀ j, span ℤ (Set.range (bs j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

theorem canonicalCoefficientCoverLift_jets (d : ℕ)
    (x : CoefficientSamplerArrays (K := K) I ns) (j : Fin m) (t : O j) :
    euclideanCoefficientJetMap U root A rows (canonicalCoefficientCoverLift U bs hbs o d x) j t =
      normalizedCoverLift (euclideanSubspace (U j)) (bs j) (hbs j) d
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _
          (canonicalCoefficientJetArrays root A rows x j) t)) := by
  rw [euclideanCoefficientJetMap_apply]
  simp only [canonicalCoefficientCoverLift, AddEquiv.apply_symm_apply]
  rw [canonicalCoefficientJetArrays, mixedArrayIntegerImage_regroup,
    orthonormalMixedChart_sum_zsmul, normalizedCoverLift_sum_zsmul]

theorem canonicalCoefficientDeckSample_mixed_jets
    {B : Fin m → Type*} [∀ j, Fintype (B j)]
    (bW : ∀ j, Basis (B j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) (hd : 0 < d) (x : CoefficientSamplerArrays (K := K) I ns)
    (r : CoefficientDeckResidues (K := K) B d) (j : Fin m) (t : O j) :
    euclideanCoefficientJetMap U root A rows
        (canonicalCoefficientDeckSample U bW bs hbs o d hd x r) j t =
      normalizedCoverLift (euclideanSubspace (U j)) (bs j) (hbs j) d
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _
          (canonicalCoefficientJetArrays root A rows x j) t)) +
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (coefficientDeckJetMap root A rows d r j t)).val := by
  rw [canonicalCoefficientDeckSample_jets, canonicalCoefficientCoverLift_jets]

end VectorPolynomial

end Erdos3

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

namespace VectorPolynomial

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

variable [∀ j, Fintype (B j)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem canonicalCoefficientDeckSample_chart (d : ℕ) [NeZero d]
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d) :
    euclideanCoefficientJetMap U root A rows
      (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) x r) =
    coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d
      (canonicalCoefficientJetArrays root A rows x, coefficientDeckJetMap root A rows d r)) := by
  funext j t
  exact canonicalCoefficientDeckSample_mixed_jets U b hb o root A rows bW d
    (Nat.pos_of_ne_zero (NeZero.ne d)) x r j t

variable [∀ j, Fintype (O j)]

end VectorPolynomial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem boundedCoefficientJetMatrix_empty {α K : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ)
    (e : VectorPolynomial.BoundedCoefficientExponent K h) :
    boundedCoefficientJetMatrix root D h (fun _ : Unit => ∅) () e =
      VectorPolynomial.boundedSiteMatrix h (fun _ : Unit => root) () e := by
  simp [boundedCoefficientJetMatrix, boundedDegreeIntegerJetMatrix,
    boundedCoefficientIntegerExponentEquiv, integerJetMatrix, booleanCoefficient,
    integerAffineCube, VectorPolynomial.boundedSiteMatrix, MvPolynomial.eval_monomial]

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X K : Type*} [Fintype X] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3
open scoped BigOperators Classical

namespace VectorPolynomial
open Module
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S))

local notation "root" => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)]
variable [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]


namespace NormalizedPolynomialTwist

variable {X : Type*} [Fintype X] {periodCap coverCap : ℝ} {L : ℝ≥0}

end NormalizedPolynomialTwist

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped Classical NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable [CompactSpace (EuclideanJetLayers U (fun _ => Unit))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]


namespace NormalizedPolynomialTwist

variable {X : Type*} [Fintype X] {periodCap coverCap : ℝ} {L : ℝ≥0}

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleCongruenceOutput
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical
open BooleanCubeKernel

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedOriginalSampleDeckValue_residue
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (q : ℕ) (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty sides)
    (j : Fin m) :
    coefficientDeckJetMap
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (fun (_ : Fin m) (_ : Unit) => (∅ : Finset Empty)) q
      (fun j d e => (deck j d e : ZMod q)) j () =
      integerResidueMap (E j) q (allocatedOriginalSampleDeckValue B U basis S deck x y j) := by
  funext e
  simp only [coefficientDeckJetMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Finset.sum_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply,
    boundedCoefficientJetMatrix_empty]
  change (∑ d, (boundedSiteMatrix (j.val + 1)
    (fun _ : Unit => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) () d : ZMod q) *
      (deck j d e : ZMod q)) =
    (allocatedOriginalSampleDeckValue B U basis S deck x y j e : ZMod q)
  simp only [allocatedOriginalSampleDeckValue, modularBoundedCoefficientPolynomial,
    map_sum, MvPolynomial.eval_monomial, Finsupp.prod, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro d _
  exact mul_comm _ _

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CenteredCoefficientDeckChartMeasurable
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
attribute [local irreducible] coefficientDeckKernelEquiv canonicalCoefficientDeckSample coefficientSamplerAmbientPoint

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped Classical

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical
variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

omit [Fintype K] in
theorem coefficientEventRead_chart_identity (q : ℕ) [NeZero q]
    (sample : CoefficientSamplerArrays (K := K) I n) (y : CoefficientTorus (K := K) U)
    (hbase : quotientIntegerCover (coefficientIntegerLattice U) q y =
      canonicalCoefficientSample U b hb o sample)
    (hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o sample a| < 1/2)
    (read : CoefficientChartResidues K n E q)
    (hread : ∀ event : CoefficientChartResidues K n E q → Prop,
      coefficientDeckChartEvent U bW b hb o q event y ↔ event read) :
    canonicalCoefficientDeckSample U bW b hb o q (NeZero.pos q) sample
      (fun j a i => read j a (.inr i)) = y := by
  obtain ⟨r, hr, _⟩ := canonicalCoefficientDeckSample_existsUnique_residue
    U bW b hb o q (NeZero.pos q) sample y hbase
  have hevent := (hread (fun r => r = read)).mpr rfl
  rw [← hr, coefficientDeckChartEvent_sample_iff U bW b hb o q _ sample hsmall r] at hevent
  have he : r = (fun j a i => read j a (.inr i)) := by
    funext j a i
    exact congrFun (congrFun (congrFun hevent j) a) (.inr i)
  simpa only [he] using hr

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*}

theorem coefficientEventRead_jet_chart (root : K → ℤ) (D : Matrix α K ℤ)
    (rows : ∀ j, O j → Finset α) (q : ℕ) [NeZero q]
    (sample : CoefficientSamplerArrays (K := K) I n) (y : CoefficientTorus (K := K) U)
    (hbase : quotientIntegerCover (coefficientIntegerLattice U) q y =
      canonicalCoefficientSample U b hb o sample)
    (hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o sample a| < 1/2)
    (read : CoefficientChartResidues K n E q)
    (hread : ∀ event : CoefficientChartResidues K n E q → Prop,
      coefficientDeckChartEvent U bW b hb o q event y ↔ event read) :
    euclideanCoefficientJetMap U root D rows y =
      coveredJetChart U b hb bW q (mixedCoveredJetCoordinates U o q
        (canonicalCoefficientJetArrays root D rows sample,
          coefficientDeckJetMap root D rows q (fun j a i => read j a (.inr i)))) := by
  rw [← coefficientEventRead_chart_identity U bW b hb o q sample y hbase hsmall read hread]
  exact canonicalCoefficientDeckSample_chart U o root D rows b hb bW q sample _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped Classical

variable {K X : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [CompactSpace (CoefficientTorus (K := K) U)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedRecoveredSampleSiteChart
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators Matrix

variable {K X : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem affineCoefficientCoverSample_emptyJet
    (root : K → ℤ) (D : Matrix Empty K ℤ) (q : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j a, coefficients (poly j) a ∈ U j)
    (z : Option K × X → ℤ) :
    euclideanCoefficientJetMap U root D (fun _ (_ : Unit) => ∅)
      (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) =
      physicalSingleSiteValue U q poly hm (physicalAffineSite root z) := by
  let f : Option K → X → ℝ := fun k x => (z (k,x) : ℝ)
  have hpoint : (fun x => MvPolynomial.aeval (fun k => (root k : ℝ))
      (affineParameterSubstitution f x)) = physicalAffineSite root z := by
    funext x
    rw [affineParameterSubstitution_eval]
    simp [physicalAffineSite, integerSiteValue, Fintype.sum_option, Finset.sum_apply,
      zsmul_eq_mul, mul_comm, f]
  funext j t
  cases t
  let v := substitute (affineParameterSubstitution f)
    (restrictCoefficients (U j) (poly j) (hm j))
  have hv : DegreeLE (1 : K → ℕ) (j.val + 1) v :=
    degreeLE_substitute_affine (affineParameterSubstitution f)
      (affineParameterSubstitution_degree f) _
      (degreeLE_restrictCoefficients (U j) (poly j) (hm j) (hp j))
  have he := congrFun (siteEvaluation_bounded_coefficients (fun _ : Unit => root) v hv) ()
  change eval (fun k => (root k : ℝ)) v =
    ∑ e, (boundedSiteMatrix (j.val + 1) (fun _ : Unit => root) () e : ℝ) • coefficients v e.val at he
  dsimp only [v] at he
  rw [eval_substitute, hpoint] at he
  change (euclideanSubspaceTorusEquiv (U j)).symm
    (arrayCoordinateTorus (U j)
      (coefficientBooleanJetTorusMap U root D (fun _ (_ : Unit) => ∅)
        (affineCoefficientCoverSample U poly hm q f) j) ()) = _
  rw [affineCoefficientCoverSample, coefficientBooleanJetTorusMap_mk,
    arrayCoordinateTorus_mk]
  apply congrArg (euclideanSubspaceTorusEquiv (U j)).symm
  apply congrArg (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U j)))
  funext t
  change (∑ e, (boundedCoefficientJetMatrix root D (j.val + 1)
    (fun _ : Unit => ∅) () e : ℝ) •
      ((q : ℝ)⁻¹ • coefficients v e.val)) = _
  simp_rw [boundedCoefficientJetMatrix_empty, smul_comm _ ((q : ℝ)⁻¹)]
  rw [← Finset.smul_sum, ← he]

section Allocated
variable {G : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedRecoveredSample_site_chart
    (q : ℕ) [NeZero q]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j a, coefficients (poly j) a ∈ U j)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hbase : canonicalCoefficientSample U b hb o sample =
      affineSampleCoefficientTorus U poly hm (fun k x => (noise (k,x) : ℝ)))
    (hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o sample a| < 1/2)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
      coefficientDeckChartEvent U bW b hb o q event
        (affineCoefficientCoverSample U poly hm q (fun k x => (noise (k,x) : ℝ))) ↔
      event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod q))))
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S))
    (j : Fin m) :
    physicalSingleSiteValue U q poly hm
      (fun z => (integerPhysicalSite (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y) noise z : ℝ)) j () =
      normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) q
        (orthonormalMixedChart (o j) (allocatedOriginalSamplePhysicalMixedValue B U b S sample x y j),
          integerResidueMap (E j) q
            (allocatedOriginalSampleDeckValue B U b S (allocatedReadDeck read) x y j)) := by
  have hprojection : quotientIntegerCover (coefficientIntegerLattice U) q
      (affineCoefficientCoverSample U poly hm q (fun k z => (noise (k,z) : ℝ))) =
      canonicalCoefficientSample U b hb o sample := by
    rw [affineCoefficientCoverSample_projection U poly hm q (NeZero.pos q)]
    exact hbase.symm
  have hjet := coefficientEventRead_jet_chart U bW b hb o
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
    (allocatedPhysicalCubeDirections B U b S x y) (fun _ (_ : Unit) => ∅) q sample
    (affineCoefficientCoverSample U poly hm q (fun k z => (noise (k,z) : ℝ)))
    hprojection hsmall (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod q))) hread
  rw [affineCoefficientCoverSample_emptyJet U _ _ q poly hp hm noise] at hjet
  have h := congrFun (congrFun hjet j) ()
  simp_rw [integerPhysicalSite_cast_apply]
  change _ = normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) q
    (orthonormalMixedChart (o j) (allocatedOriginalSamplePhysicalMixedValue B U b S sample x y j),
      integerResidueMap (E j) q (allocatedOriginalSampleDeckValue B U b S (allocatedReadDeck read) x y j))
  rw [← allocatedOriginalSampleDeckValue_residue B U b S (allocatedReadDeck read) q x y j]
  exact h

theorem allocatedRecoveredSample_site_chart_base
    (q : ℕ) [NeZero q]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j a, coefficients (poly j) a ∈ U j)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hbase : canonicalCoefficientSample U b hb o sample =
      affineSampleCoefficientTorus U poly hm (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base + noise) (k,x) : ℝ)))
    (hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o sample a| < 1/2)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
      coefficientDeckChartEvent U bW b hb o q event
        (affineCoefficientCoverSample U poly hm q (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base + noise) (k,x) : ℝ))) ↔
      event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod q))))
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S))
    (j : Fin m) :
    physicalSingleSiteValue U q poly hm
      (fun z => (base z + integerPhysicalSite (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y) noise z : ℝ)) j () =
      normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) q
        (orthonormalMixedChart (o j) (allocatedOriginalSamplePhysicalMixedValue B U b S sample x y j),
          integerResidueMap (E j) q
            (allocatedOriginalSampleDeckValue B U b S (allocatedReadDeck read) x y j)) := by
  simpa only [integerPhysicalSite_baseTranslation_add, Pi.add_apply, Int.cast_add] using
    allocatedRecoveredSample_site_chart U B bW b hb o S q poly hp hm
      (integerBaseTranslation (K := LayerSamplerVariables G I n B) base + noise) sample hbase hsmall read hread x y j

end Allocated
end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedRecoveredSample_site_chart_base.{u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.allocatedRecoveredSample_site_chart_base.{u_2, u_3, u_4, u_5, u_6, u_7}
