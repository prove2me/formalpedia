-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_recovered_native_atom_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:20:44.675007+00:00
-- url     : https://prove2.me/submissions/db3c9bca-276e-4eee-b607-502a63ab3fcf

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B232
import Definitions.Def_OAIE3v2B235
import Definitions.Def_OAIE3v2B236
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_NormalizedPolynomialTwist_forecastShortGridTest_originalSample_eq_eval_s2

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3


open scoped BigOperators Classical

theorem integerScalarCubeWeights_root_bounds {α : Type*} [Fintype α] [DecidableEq α]
    {H : ℕ} (hH : 0 < H) (z : IntegerScalarCubeBox α H)
    (hz : (integerScalarCubeWeights α H hH).weight z ≠ 0) :
    0 ≤ (z none : ℤ) ∧ (z none : ℤ) ≤ ((H - 1 : ℕ) : ℤ) := by
  have hmem : z ∈ integerScalarCubeSet α H := by
    by_contra hn
    apply hz
    simp only [integerScalarCubeWeights, FiniteProbabilityWeights.condition,
      hn, ite_false, zero_div]
  have hr := ((mem_integerScalarCubeSet H z).mp hmem) ∅
  simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at hr
  exact ⟨hr.1, by omega⟩

theorem integerScalarCubePi_root_bounds {G : Type*} [Fintype G]
    (H : G → ℕ) (hH : ∀ g, 0 < H g)
    (z : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hz : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight z ≠ 0)
    (g : G) :
    0 ≤ (z g none : ℤ) ∧ (z g none : ℤ) ≤ ((H g - 1 : ℕ) : ℤ) := by
  apply integerScalarCubeWeights_root_bounds (hH g) (z g)
  change (∏ g, (integerScalarCubeWeights Empty (H g) (hH g)).weight (z g)) ≠ 0 at hz
  exact Finset.prod_ne_zero_iff.mp hz g (Finset.mem_univ g)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem mixedArrayRegroup_apply {I Z J : Type*} (x : (I → J → ℝ) × (Z → J → ℤ)) (j : J) :
    mixedArrayRegroup I Z J x j = (fun i => x.1 i j, fun z => x.2 z j) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientDeckChartRecovery
namespace OAI

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

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredMixedArrayImage
namespace OAI

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

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ContainedProgressionCubeMap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem containedProgressionCubeMap_value (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) (hz : IntegerScalarCube H (fun i => (z i : ℤ)))
    (i : Option I) :
    (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ) =
      (if i = none then c else 0) + (step : ℤ) * (z i : ℤ) := by
  rw [containedProgressionCubeMap, dif_pos hz]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxObservedMean
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalJoinedResidues
namespace OAI

section

namespace Erdos3

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}

theorem principalResidueLabel_join (P : D → Prop) [DecidablePred P]
    {L : PrincipalTupleIndex B h → ℕ} (u : PrincipalAxisTuples (α := α) P L)
    (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L) (m : ℕ) :
    principalResidueLabel m (principalAxisJoin P u v) =
      principalAxisResidueJoin P u m (principalResidueLabel m v) := by
  funext j i
  by_cases hp : P j.1 <;>
    simp only [principalResidueLabel, principalAxisJoin, principalAxisResidueJoin, hp, ↓reduceDIte]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CenteredCoefficientDeckChartMeasurable
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover
namespace OAI

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

theorem allocatedOriginalSamplePhysicalMixedValue_integer (j : Fin m) (i : Fin (n j)) :
    (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y j).2 i =
      MvPolynomial.eval (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (∑ d, MvPolynomial.monomial d.val ((sample j).2 i d)) := by
  simp only [map_sum, MvPolynomial.eval_monomial, Finsupp.prod]
  change (∑ d, boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (j.val + 1) (fun _ : Unit => ∅) () d * (sample j).2 i d) = _
  apply Finset.sum_congr rfl
  intro d _
  rw [boundedCoefficientJetMatrix_empty]
  exact mul_comm _ _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedOriginalSampleResidueMixtureForecast
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides
local notation "ActiveTuple" => PrincipalAxisTuples (α := Empty) (fun a => ¬short a) sides

theorem allocatedPrincipalResidueJoin_label_join (q : ℕ) (u : ShortTuple) (v : ActiveTuple) :
    principalResidueLabel q (principalAxisJoin short u v) =
      allocatedPrincipalResidueJoin B U basis S q u (fun j => ((v j none : ℤ) : ZMod q)) := by
  rw [principalResidueLabel_join]
  unfold allocatedPrincipalResidueJoin
  congr 1
  funext j c
  cases c with
  | none => rfl
  | some e => exact e.elim

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem spatialRankPolynomial_actual_eval {K X : Type*} [Fintype K]
    (base : X → ℤ) (noise : Option K × X → ℤ) (x : X) (t : K → ℤ) :
    MvPolynomial.eval t (C (base x) + spatialRankPolynomial (fun e => noise (e,x))) =
      BooleanCubeKernel.jointIntegerPhysicalSite t (base, noise) x := by
  rw [spatialRankPolynomial_eq]
  simp only [map_add, eval_C, map_sum, map_mul, eval_X]
  simp only [BooleanCubeKernel.jointIntegerPhysicalSite, Pi.add_apply,
    BooleanCubeKernel.integerPhysicalSite]
  congr 1
  simp only [mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineFixedPathRationalReference
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S

variable (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (deck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis short j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)

theorem allocatedJointResidueOutput_actual
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (q : ℕ)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (v : PrincipalIntegerTuples B degree Empty sides) :
    allocatedJointResidueOutput B U basis S base noise deck projection q
        (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q v) =
      fun o => ((MvPolynomial.eval (Sum.elim (fun g => (x g none : ℤ))
        (fun j => (v j none : ℤ)))
        (allocatedUnconditionedCongruenceIntegerPolynomial short o.1 base noise deck
          (projection o.1) o.2) : ℤ) : ZMod q) := by
  funext o
  rw [integerPolynomial_eval_residue]
  unfold allocatedJointResidueOutput allocatedForecastPolynomial allocatedSeparatedCongruencePolynomial
  rw [MvPolynomial.eval₂_rename]
  congr 1
  funext k
  cases k with
  | inl g => rfl
  | inr j =>
    by_cases hj : short j.1
    · simp only [Function.comp_apply, samplerSeparatedVariable_inactive short degree _ _ _ hj,
        Sum.elim_inr, principalResidueLabel]
      rfl
    · simp only [Function.comp_apply, samplerSeparatedVariable_active short degree _ _ _ hj,
        Sum.elim_inl, Sum.elim_inr, principalResidueLabel]
      rfl

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

local notation "short" => allocatedShortAxis (I := I) U basis S.value
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

theorem allocatedOriginalSample_jointResidueOutput_eq_congruence
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (q : ℕ) (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty sides) :
    allocatedJointResidueOutput B U basis S base noise deck
      (allocatedOriginalSampleCongruenceProjection B U basis S sample) q
      (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q y) =
      fun o => (forecastCongruenceOutput (R := ℤ) short
        (base + integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) noise)
        (fun j => Sum.elim
          (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y j).2
          (allocatedOriginalSampleDeckValue B U basis S deck x y j)) o : ZMod q) := by
  rw [allocatedJointResidueOutput_actual]
  have hroot : Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) =
      allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y := by
    funext v
    simp only [allocatedPhysicalCubeRoot, zero_add]
  rw [hroot]
  funext o
  apply congrArg (fun z : ℤ => (z : ZMod q))
  rcases o with ⟨j, a | e | i⟩
  · exact spatialRankPolynomial_actual_eval base noise a.val _
  · rfl
  · change MvPolynomial.eval _ (modularBoundedCoefficientPolynomial _
      ((sample j).2 i.val)) =
      (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y j).2 i.val
    exact (allocatedOriginalSamplePhysicalMixedValue_integer B U basis S sample x y j i.val).symm

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

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedActiveContainedTupleMap
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))

theorem allocatedActiveContainedProgression_value
    (step H : Input → ℕ) (c : Input → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (v : ∀ j, IntegerScalarCubeBox Empty (H j))
    (hv : (FiniteProbabilityWeights.pi
      (fun j => integerScalarCubeWeights Empty (H j) (hH j))).weight v ≠ 0) (j : Input) :
    (allocatedActiveContainedProgression B U basis S step H c hsubset v j none : ℤ) =
      c j + (step j : ℤ) * (v j none : ℤ) := by
  have hb := integerScalarCubePi_root_bounds H hH v hv j
  have hc : IntegerScalarCube (H j) (fun i => (v j i : ℤ)) := by
    intro t
    have ht : t = ∅ := Subsingleton.elim _ _
    subst t
    simpa only [integerScalarCubeValue, Finset.sum_empty, add_zero] using
      (show 0 ≤ (v j none : ℤ) ∧ (v j none : ℤ) < (H j : ℤ) from ⟨hb.1, by have := hH j; omega⟩)
  simpa only [allocatedActiveContainedProgression, ite_true] using
    containedProgressionCubeMap_value Empty S.value (H j) (step j) (c j)
      S.positive (hsubset j) (v j) hc none

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSlicedPhysicalResidueIdentity
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem containedProgressionCubePi_residue
    {G : Type*} [Fintype G] (L : ℕ) (hL : 0 < L)
    (H step : G → ℕ) (c : G → ℤ) (hH : ∀ g, 0 < H g)
    (hsubset : ∀ g, integerProgressionSupport (c g) (step g : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (L : ℤ))
    (x : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hx : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight x ≠ 0)
    (q : ℕ) :
    (fun g => ((containedProgressionCubeMap Empty L (H g) (step g) (c g)
      hL (hsubset g) (x g) none : ℤ) : ZMod q)) =
      fun g => ((c g + (step g : ℤ) * (x g none : ℤ) : ℤ) : ZMod q) := by
  funext g
  have hb := integerScalarCubePi_root_bounds H hH x hx g
  have hc : IntegerScalarCube (H g) (fun a => (x g a : ℤ)) := by
    intro row
    have he : row = ∅ := Subsingleton.elim _ _
    simp only [he, integerScalarCubeValue, Finset.sum_empty, add_zero]
    exact ⟨hb.1, by have := hH g; omega⟩
  rw [containedProgressionCubeMap_value Empty L (H g) (step g) (c g) hL (hsubset g) (x g) hc]
  rfl

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedActiveContainedProgression_residue_join
    (step H : Input → ℕ) (c : Input → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (v : ∀ j, IntegerScalarCubeBox Empty (H j))
    (hv : (FiniteProbabilityWeights.pi
      (fun j => integerScalarCubeWeights Empty (H j) (hH j))).weight v ≠ 0)
    (q : ℕ) (u : PrincipalAxisTuples (α := Empty) short sides) :
    principalResidueLabel q (principalAxisJoin short u
      (allocatedActiveContainedProgression B U basis S step H c hsubset v)) =
      allocatedPrincipalResidueJoin B U basis S q u
        (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q)) := by
  rw [allocatedPrincipalResidueJoin_label_join]
  congr 1
  funext j
  rw [allocatedActiveContainedProgression_value B U basis S step H c hH hsubset v hv j]

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathAnchoredNativeComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "Original" => PrincipalIntegerTuples B degree Empty sides

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
local notation "selected" => allocatedShortIntegerSelection U basis S.value

attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedNativeAtomCoverNeZero
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
  (allocatedLayerWidths B U basis S j)
  (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable (base : X → ℤ) (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (box : X → ℕ) (hbox : ∀ a, 0 < box a) {τ : ℝ} (hτ : τ ≠ 0)
variable (q : ℕ) [NeZero q] (hm : 0 < m)
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E W.cover → Prop,
  coefficientDeckChartEvent U bW basis hb o W.cover event
    (affineCoefficientCoverSample U nativePoly hmem W.cover
      (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
        integerFrame) (k, x) : ℝ))) ↔
    event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod W.cover))))

include hs hbox hτ hdegree hbase hsmallChart hread in

theorem allocatedFixedPath_recovered_physical_native_atom
    (x : G → IntegerScalarCubeBox Empty S.value) (v : Original) :
    W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / box a) τ
      (forecastInactiveShortGrid B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) (principalAxisRestrict short v))
      (allocatedJointResidueOutput B U basis S base integerFrame (allocatedReadDeck read)
        (allocatedOriginalSampleCongruenceProjection B U basis S sample) q
        (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q v))
      ((fun a : Σ _ : X, Unit ⊕ Empty =>
          (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v)
            integerFrame a.1 : ℝ) / (τ * (box a.1 : ℝ) / 8)),
        fun a : Output => allocatedFullMixedSiteValue (R := R) U basis
          (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x v) a.1.val) =
      W.eval box nativePoly (fun a => base a + integerPhysicalSite
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a) := by
  rw [allocatedOriginalSample_jointResidueOutput_eq_congruence]
  have hsite : base + integerPhysicalSite
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame =
        fun a => base a + integerPhysicalSite
          (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a := rfl
  rw [hsite]
  have hc j := allocatedRecoveredSample_site_chart_base U B bW basis hb o S W.cover
    nativePoly hdegree hmem base integerFrame sample hbase hsmallChart read hread x v j
  simpa only [Pi.add_apply, Int.cast_add, add_sub_cancel_left] using
    W.forecastShortGridTest_originalSample_eq_eval_s2 U basis hb o bW R B S hR hσ sample hs x v
      q hm hperiod hcover base
      (fun a => base a + integerPhysicalSite
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x v) integerFrame a)
      box hbox hτ (allocatedOriginalSampleDeckValue B U basis S (allocatedReadDeck read) x v)
      nativePoly hmem (fun j => by simpa only [Pi.add_apply, Int.cast_add] using hc j)

include hs hbox hτ hdegree hbase hsmallChart hread in

theorem allocatedFixedPath_sliced_recovered_native_atom_s2_oai
    (HG : G → ℕ) (hHG : ∀ g, 0 < HG g) (cG : G → ℤ) (stepG : ℕ)
    (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (step H : Input → ℕ) (c : Input → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (u : ShortTuple)
    (x : ∀ g, IntegerScalarCubeBox Empty (HG g))
    (hx : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (HG g) (hHG g))).weight x ≠ 0)
    (v : ∀ j, IntegerScalarCubeBox Empty (H j))
    (hv : (FiniteProbabilityWeights.pi
      (fun j => integerScalarCubeWeights Empty (H j) (hH j))).weight v ≠ 0) :
    let embed := fun g => containedProgressionCubeMap Empty S.value (HG g) stepG (cG g)
      S.positive (hcontainedG g) (x g)
    let joined := principalAxisJoin short u (allocatedActiveContainedProgression B U basis S step H c hsubset v)
    W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
      (fun a => (base a : ℝ) / box a) τ
      (forecastInactiveShortGrid B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) u)
      (allocatedJointResidueOutput B U basis S base integerFrame (allocatedReadDeck read)
        (allocatedOriginalSampleCongruenceProjection B U basis S sample) q
        (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
        (allocatedPrincipalResidueJoin B U basis S q u
          (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))))
      ((fun a : Σ _ : X, Unit ⊕ Empty =>
          (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) embed joined)
            integerFrame a.1 : ℝ) / (τ * (box a.1 : ℝ) / 8)),
        fun a : Output => allocatedFullMixedSiteValue (R := R) U basis
          (allocatedOriginalSamplePhysicalMixedValue B U basis S sample embed joined) a.1.val) =
      W.eval box nativePoly (fun a => base a + integerPhysicalSite
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) embed joined) integerFrame a) := by
  intro embed joined
  have he := allocatedFixedPath_recovered_physical_native_atom B U basis hR hσ S hb o bW W
    sample hs base integerFrame box hbox hτ q hm hperiod hcover nativePoly hmem hdegree
    hbase hsmallChart read hread embed joined
  dsimp only [embed, joined] at he
  rw [principalAxisRestrict_join_left,
    containedProgressionCubePi_residue S.value S.positive HG (fun _ => stepG) cG hHG
      hcontainedG x hx q,
    allocatedActiveContainedProgression_residue_join B U basis S step H c hH hsubset v hv q u] at he
  exact he

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_recovered_native_atom_s2_oai.{u_1, u_2, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_recovered_native_atom_s2_oai.{u_1, u_2, u_4, u_5, u_6, u_7}
