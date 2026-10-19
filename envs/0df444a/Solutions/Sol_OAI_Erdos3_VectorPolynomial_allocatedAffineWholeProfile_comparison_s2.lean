-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedAffineWholeProfile_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:01:13.217992+00:00
-- url     : https://prove2.me/submissions/84d44ca2-07d3-4c1e-b3e1-1009856b6158

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B127
import Definitions.Def_OAIE3v2B213
import Definitions.Def_OAIE3v2B217
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineCoveredProfile_mean_test_integral_s2
import Theorems.Thm_OAI_Erdos3_containedSupportedProgressionLaw_integral_comparison_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentFiniteConditioning
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]

theorem pi_condition (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (G : ∀ j, Finset (Ω j)) (hG : ∀ j, 0 < (p j).mass (G j)) :
    pi (fun j => (p j).condition (G j) (hG j)) =
      (pi p).condition (piRestrictionSet G) (piRestriction_mass_pos p G hG) := by
  classical
  apply ext_weight
  funext x
  change (∏ j, (if x j ∈ G j then (p j).weight (x j) else 0) / (p j).mass (G j)) =
    (if x ∈ piRestrictionSet G then ∏ j, (p j).weight (x j) else 0) /
      (pi p).mass (piRestrictionSet G)
  rw [piRestriction_mass, Finset.prod_div_distrib]
  congr 1
  by_cases hx : ∀ j, x j ∈ G j
  · simp only [hx, ite_true, (mem_piRestrictionSet G x).mpr hx]
  · rw [if_neg ((mem_piRestrictionSet G x).not.mpr hx)]
    obtain ⟨j, hj⟩ := not_forall.mp hx
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3

theorem scalarCubeResiduePi_condition {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (r : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I+1)*M j ≤ L j) :
    FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j)) =
      (FiniteProbabilityWeights.pi (fun j => integerScalarCubeWeights I (L j) (hL j))).condition
        (FiniteProbabilityWeights.piRestrictionSet (fun j => scalarCubeResidueSet I (L j) (m j) (r j)))
        (FiniteProbabilityWeights.piRestriction_mass_pos _ _
          (fun j => scalarCubeResidue_mass_pos I (L j) (M j) (hL j) (m j) (r j) (hm j) (hmM j) (hsize j))) :=
  FiniteProbabilityWeights.pi_condition _ _ _

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalResidueMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem principalResidueWeights_eq_condition {D α : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) (hm : 0 < m)
    (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j) :
    principalResidueWeights B h L hL m hm r hsize =
      (principalTupleWeights (α := α) B h L hL).condition
        (Finset.univ.filter (fun y => principalResidueLabel m y = r))
        (principalResidueCell_mass_pos B h L hL m hm r hsize) := by
  classical
  simp only [principalResidueCell_eq]
  exact scalarCubeResiduePi_condition L (fun _ => m) hL (fun _ _ => m) r
    (fun _ _ => hm) (fun _ _ => le_rfl) hsize

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

theorem mixedArrayRegroup_apply {I Z J : Type*} (x : (I → J → ℝ) × (Z → J → ℤ)) (j : J) :
    mixedArrayRegroup I Z J x j = (fun i => x.1 i j, fun z => x.2 z j) := rfl

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

theorem normalizedCoveredChart_continuous :
    Continuous (normalizedCoveredChart W b hb bW d) := by
  have hk : Continuous (fun r : R → ZMod d =>
      (coverKernelBasisEquiv (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
        bW d (Nat.pos_of_ne_zero (NeZero.ne d)) r).val) := continuous_of_discreteTopology
  exact ((normalizedCoverLift_continuous W b hb d).comp continuous_fst).add
    (hk.comp continuous_snd)

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

theorem coveredJetChart_continuous : Continuous (coveredJetChart (O := O) U b hb bW d) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro t
  exact (normalizedCoveredChart_continuous _ (b j) (hb j) (bW j) d).comp
    ((continuous_apply t).comp (continuous_apply j))

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

theorem mixedCoveredJetCoordinates_measurable (d : ℕ) :
    Measurable (mixedCoveredJetCoordinates (O := O) (B := B) (n := n) U o d) := by
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro t
  exact ((orthonormalMixedChart (o j)).measurable.comp
    (((measurable_pi_apply t).comp (mixedArrayRegroup _ _ _).measurable).comp
      ((measurable_pi_apply j).comp measurable_fst))).prodMk
    ((measurable_pi_apply t).comp ((measurable_pi_apply j).comp measurable_snd))

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

omit [∀ j, Fintype (I j)] [Fintype α] in
theorem canonicalCoefficientJetArrays_measurable :
    Measurable (canonicalCoefficientJetArrays (I := I) (n := n) root A rows) := by
  apply measurable_pi_iff.mpr
  intro j
  exact (mixedArrayIntegerImage_measurable
    (boundedCoefficientJetMatrix root A (j.val + 1) (rows j))).comp (measurable_pi_apply j)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IndependentEmbeddedMixture
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {X R : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
  [∀ j, DecidableEq (R j)]

theorem pi_condition_fiber (p : ∀ j, FiniteProbabilityWeights (X j))
    (F : ∀ j, X j → R j) (r : ∀ j, R j)
    (hr : ∀ j, 0 < (p j).mass (Finset.univ.filter (fun x => F j x = r j))) :
    (pi p).condition (Finset.univ.filter (fun x => (fun j => F j (x j)) = r))
        (pi_fiber_mass_pos p F r hr) =
      pi (fun j => (p j).condition (Finset.univ.filter (fun x => F j x = r j)) (hr j)) := by
  simpa only [← pi_fiber_set F r] using
    (pi_condition p (fun j => Finset.univ.filter (fun x => F j x = r j)) hr).symm

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveFiberMarginal
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {J : Type*} [Fintype J] [DecidableEq J]
variable {X R : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
variable [∀ j, DecidableEq (R j)]
variable (p : ∀ j, FiniteProbabilityWeights (X j))
variable (F : ∀ j, X j → R j) (r : ∀ j, R j)
variable (hcell : 0 < (pi p).mass
  (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)))

theorem pi_condition_positive_fiber :
    (pi p).condition (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)) hcell =
      pi (fun j => (p j).condition (Finset.univ.filter (fun x => F j x = r j))
        (coordinate_fiber_mass_pos p F r hcell j)) :=
  pi_condition_fiber p F r (coordinate_fiber_mass_pos p F r hcell)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedResidueInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "coord" => principalSupportedCoordinateWeights B h L hL q r hcell
local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B h L hL)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

theorem principalSupportedResidueWeights_eq_pi :
    (conditioned) = FiniteProbabilityWeights.pi (coord) :=
  FiniteProbabilityWeights.pi_condition_positive_fiber
    (fun t => integerScalarCubeWeights α (L t) (hL t))
    (fun t (z : IntegerScalarCubeBox α (L t)) i => ((z i : ℤ) : ZMod q)) r hcell

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PrincipalCubeSupportedCell
namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (P : D → Prop) [DecidablePred P]

local notation "BP" => (fun a : {a // P a} => B (Subtype.val a))
local notation "hP" => (fun a : {a // P a} => h (Subtype.val a))
local notation "embed" => (fun j : PrincipalTupleIndex BP hP => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B h))
local notation "rP" => (fun j : PrincipalTupleIndex BP hP => r (embed j))
local notation "hHP" => (fun j : PrincipalTupleIndex BP hP => hH (embed j))

include hq in
theorem containedSupportedProgressionAxisLaw_eq_of_size
    (hsize : ∀ j : PrincipalTupleIndex BP hP, (Fintype.card α + 1) * q ≤ H (embed j)) :
    containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P =
      containedProgressionResidueLaw BP hP (principalAxisLength P L) (principalAxisLength P H)
        (principalAxisLength P step) (fun j => c (embed j)) (fun j => hL (embed j)) hHP
        (fun j => hsubset (embed j)) q hq rP hsize := by
  have hres := principalResidueWeights_eq_condition BP hP (principalAxisLength P H) hHP q hq rP hsize
  have hcond := principalSupportedResidueWeights_eq_pi BP hP (principalAxisLength P H) hHP q rP
    (principalResidueCell_mass_pos BP hP (principalAxisLength P H) hHP q hq rP hsize)
  exact congrArg (fun w => w.fiberLaw (containedProgressionTupleMap BP hP
    (principalAxisLength P L) (principalAxisLength P H) (principalAxisLength P step)
    (fun j => c (embed j)) (fun j => hL (embed j)) (fun j => hsubset (embed j)))) (hres.trans hcond).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OneCubePrincipalSliceRiemann
namespace OAI

section

namespace Erdos3
open scoped Classical

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)

omit [DecidableEq α] in
theorem principalProgressionSlice_parameters [DecidableEq α]
    (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ)) :
    ∀ i, 0 < principalProgressionSliceWidth (α := α) B h L H step i ∧
      δ / 2 ≤ |principalProgressionSliceWidth (α := α) B h L H step i| ∧
      |principalProgressionSliceCenter (α := α) B h L c i| +
        |principalProgressionSliceWidth (α := α) B h L H step i| ≤ 1 := by
  intro i
  let j : PrincipalTupleIndex B h := ⟨i.1, i.2.1, i.2.2.1⟩
  have hg := progression_slice_endpoint_geometry (c j) (hL j) (hstep j) (hH j) hδ
    (hsubset j) (hdense j)
  have hp : 0 < (step j : ℝ) * ((H j : ℝ) - 1) / L j := (half_pos hδ).trans_le hg.2.1
  refine ⟨hp, ?_, ?_⟩
  · change δ / 2 ≤ |(step j : ℝ) * ((H j : ℝ) - 1) / L j|
    rw [abs_of_pos hp]
    exact hg.2.1
  · change |if i.2.2.2 = none then (c j : ℝ) / L j else 0| +
      |(step j : ℝ) * ((H j : ℝ) - 1) / L j| ≤ 1
    split_ifs
    · exact hg.2.2.1
    · simpa only [abs_zero, zero_add] using
        (le_add_of_nonneg_left (abs_nonneg ((c j : ℝ) / L j))).trans hg.2.2.1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredJetSampleMeasurable
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {K α : Type*} [Fintype K] [Fintype α] [DecidableEq α]
variable {m : ℕ} {J I Q O : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable [∀ j, Fintype (Q j)] [∀ j, Fintype (O j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (dirs : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem canonicalCoefficientDeckSample_jet_measurable (d : ℕ) [NeZero d] :
    Measurable (fun p : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) Q d =>
      euclideanCoefficientJetMap U root dirs rows
        (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)) := by
  have hchart := (coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
    (mixedCoveredJetCoordinates_measurable (O := O) (B := Q) (n := n) U o d)
  have hjet := canonicalCoefficientJetArrays_measurable (I := I) (n := n) root dirs rows
  have hdeck : Measurable (coefficientDeckJetMap (B := Q) root dirs rows d) := measurable_of_finite _
  convert hchart.comp ((hjet.comp measurable_fst).prodMk (hdeck.comp measurable_snd)) using 1
  funext p
  exact canonicalCoefficientDeckSample_chart U o root dirs rows b hb bW d p.1 p.2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedFiniteModelComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

omit [∀ index, DecidableEq (I index)] [∀ axis, DecidableEq (B axis)] [Fintype α] in
theorem allocatedWholeMaskedCoveredProfile_join
    (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U b S))
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
    (q : ℕ) (f : ((Σ a : {a // ¬grid a}, O a.val.1) → ℝ) → ℝ) :
    allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
      (principalAxisJoin grid u v) q f =
    allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
      (allocatedLongProfileDensity B U b S x rows q
        (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) q) f) := by
  simp only [allocatedWholeMaskedCoveredProfile, principalAxisRestrict_join_left,
    principalAxisRestrict_join_right]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedProgressionDensityIdentity
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ)

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

omit [DecidableEq G] [∀ index, DecidableEq (B index)]
  [∀ index, DecidableEq (O index)] in
theorem allocatedProgressionCoveredIntegrand_integrable
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1) :
    Integrable (fun p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
      CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d =>
      F (((allocatedCoefficientSplit B U basis S) p.1).1,
        euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows
          (canonicalCoefficientDeckSample U bW basis hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
      ((source).prod (deck).toMeasure) := by
  let : IsProbabilityMeasure source := allocatedCoefficientSource_probability B U basis hR hσ S
  apply Integrable.of_bound (C := 1)
  · exact (hF.comp
      ((((allocatedCoefficientSplit B U basis S).measurable.comp measurable_fst).fst).prodMk
        (canonicalCoefficientDeckSample_jet_measurable U o (wholeRoot y) (wholeDirs y)
          rows basis hb bW d))).aestronglyMeasurable
  · exact ae_of_all _ (fun p => hFbound _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineWholeProfileComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (s : ∀ j : Fin m, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := O j)
  S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => O
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ)

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S)
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "actual" => allocatedProgressionCoveredExpectation B U basis hR hσ S rows x Q hb o bW d F
  H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
omit [∀ index, Nonempty (O index)] in
theorem allocatedAffineWholeCovered_comparison
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j) (hH : ∀ j : Tuple, 2 ≤ H j)
    (_ : 0 < δ)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hsize : ∀ j : Tuple, (Fintype.card α + 1) * modulus ≤ H j)
    (hsmall : ∀ j : Tuple, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j : Tuple, (step j : ℝ) / L j ≤ ε)
    (selection : α ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hq : Fintype.card α ≤ m + 1)
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ (u : GridTuples) j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ∧ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ≤ Cmask)
    (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1) :
    let center := principalProgressionSliceCenter (α := α) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := α) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, O a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let outputResidue := fun (u : GridTuples) j => integerResidueMatrix
      (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    ‖actual - FiniteProbabilityWeights.complexMean gridLaw (fun u => ∫ a₀, ∫ z,
      (allocatedLongProfileDensity B U basis S x rows modulus (outputResidue u) ideal z : ℂ) *
        allocatedCoveredFixedTest B U basis S x u v₀ rows Q hb o bW d F a₀ z
      ∂reference ∂frozenSource)‖ ≤
      (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (Fintype.card {a // ¬grid a} * εcoef *
          (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
            Fintype.card {a // ¬grid a}) +
      allocatedAffineSourceReferenceError B U basis S α O (ρ grid) P η (fun _ => modulus) H ε mesh Cmask
 := by
  intro center width ideal outputResidue
  let f := fun (p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
      CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
      (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S)) =>
    F (((allocatedCoefficientSplit B U basis S) p.1).1,
      euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows
        (canonicalCoefficientDeckSample U bW basis hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2))
  have hf (y) : Integrable (fun p => f p y) ((source).prod (deck).toMeasure) :=
    allocatedProgressionCoveredIntegrand_integrable B U basis hR hσ S rows x Q hb o bW d F y hF hFbound
  apply containedSupportedProgressionLaw_integral_comparison_s2 B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
    ((source).prod (deck).toMeasure) f hf
  intro u hu
  have heq := containedSupportedProgressionAxisLaw_eq_of_size B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus hm r₀ hcell
    (fun a => ¬grid a) hsize
  rw [heq]
  exact hs U basis hR hσ S hσsmall x u s hA hMk hi hP hMkP hRP hRi hσi hcount
    H step c hstep hH hsubset hdense modulus hm residue hsize hsmall hε hmesh
    selection hgood hq he hεcoef hεe hlarge hperiod v₀ hv₀ hmesh0 hmesh1 hscaleMesh hCmask (hmask u)
    Q hb o bW d F hF hFbound

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (s : ∀ j : Fin m, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := O j)
  S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => O
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : EuclideanJetLayers U O → ℂ)

local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S)
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "actual" => allocatedProgressionCoveredExpectation B U basis hR hσ S rows x Q hb o bW d (fun p => F (Prod.snd p))
  H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
omit [∀ index, Nonempty (O index)] in
theorem allocatedAffineWholeProfile_comparison_s2_oai
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid) (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j) (hH : ∀ j : Tuple, 2 ≤ H j)
    (hδ : 0 < δ)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hsize : ∀ j : Tuple, (Fintype.card α + 1) * modulus ≤ H j)
    (hsmall : ∀ j : Tuple, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j : Tuple, (step j : ℝ) / L j ≤ ε)
    (selection : α ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hq : Fintype.card α ≤ m + 1)
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ (u : GridTuples) j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ∧ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ≤ Cmask)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1) :
    let center := principalProgressionSliceCenter (α := α) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := α) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, O a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let _ := fun (u : GridTuples) j => integerResidueMatrix
      (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    ‖actual - (∫ y, ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile
      B U basis hR hσ S x rows hb o bW d (principalAxisJoin grid u v₀) modulus ideal y) : ℂ) * F y
        ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))‖ ≤
      (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (Fintype.card {a // ¬grid a} * εcoef *
          (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
            Fintype.card {a // ¬grid a}) +
      allocatedAffineSourceReferenceError B U basis S α O (ρ grid) P η (fun _ => modulus) H ε mesh Cmask
 := by
  intro center width ideal outputResidue
  have hw := principalProgressionSlice_parameters (α := α) activeB activeDegree
    L H step c positiveLengths hstep hH hδ hsubset hdense
  have ht := allocatedAffineCoveredProfile_mean_test_integral_s2 B U basis S rows x hR (ρ grid)
    center width hσ v₀ Q hb o bW d ν hρ hρ1 (fun i => (hw i).2.2) hRP hRi
    modulus gridLaw outputResidue hCmask hmask (fun j => (hσsmall j).trans htone)
    T hT hsource C hC hchart hbudget F hF hFbound
  have hc := allocatedAffineWholeCovered_comparison B U basis hR hσ S rows x s hA hMk hi
    hP hMkP hRP hRi hσi hcount Q hb o bW d (fun p => F (Prod.snd p))
    H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell ρ t htone hs hσsmall hstep hH hδ hdense
    hm hsize hsmall hε hmesh selection hgood hq he hεcoef hεe hlarge hperiod v₀ hv₀
    hmesh0 hmesh1 hscaleMesh hCmask hmask (hF.comp measurable_snd) (fun p => hFbound p.2)
  change ‖actual - (gridLaw).complexMean (fun u => ∫ a₀, ∫ z,
    (allocatedLongProfileDensity B U basis S x rows modulus (outputResidue u) ideal z : ℂ) *
      allocatedCoveredFixedTest B U basis S x u v₀ rows Q hb o bW d (fun p => F (Prod.snd p)) a₀ z
        ∂reference ∂frozenSource)‖ ≤ _ at hc
  rw [ht] at hc
  simpa only [allocatedWholeMaskedCoveredProfile_join] using hc

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uJ, uQ, u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedAffineWholeProfile_comparison_s2_oai.{uJ, uQ, u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedAffineWholeProfile_comparison_s2_oai.{uJ, uQ, u_1, u_2, u_3, u_4, u_5}
