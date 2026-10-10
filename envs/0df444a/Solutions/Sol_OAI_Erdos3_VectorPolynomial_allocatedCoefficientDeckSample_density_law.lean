-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedCoefficientDeckSample_density_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T00:07:57.597574+00:00
-- url     : https://prove2.me/submissions/36318079-c69a-4dab-aec0-cd10cb9253b2

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B136

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

theorem mixedScalarArrayLaw_probability {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Z → J → PMF ℤ) :
    IsProbabilityMeasure (mixedScalarArrayLaw c w p) := by
  let : ∀ i j, IsProbabilityMeasure (affineCoefficientMeasure (c i j) (w i j)) :=
    fun i j => affineCoefficientMeasure_probability _ (hw i j)
  unfold mixedScalarArrayLaw
  infer_instance

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteKernelRestriction
namespace OAI

section

namespace Erdos3

open MeasureTheory Topology
open scoped BigOperators

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
variable (C : G →+ H) [Fintype C.ker]

theorem finiteFiberAverage_eq_of_map_eq (f : G → ℝ) {x y : G} (hxy : C x = C y) :
    finiteFiberAverage C f x = finiteFiberAverage C f y := by
  classical
  have hk : x - y ∈ C.ker := by
    change C (x - y) = 0
    rw [map_sub, hxy, sub_self]
  unfold finiteFiberAverage
  congr 1
  apply Fintype.sum_equiv (Equiv.addLeft (⟨x - y, hk⟩ : C.ker))
  intro k
  congr 1
  change x + k.val = y + (x - y + k.val)
  abel

theorem finiteFiberAverage_integral_uniform
    [MeasurableSpace C.ker] [MeasurableSingletonClass C.ker] (f : G → ℝ) (x : G) :
    (∫ k : C.ker, f (x + k.val) ∂(PMF.uniformOfFintype C.ker).toMeasure) =
      finiteFiberAverage C f x := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← Finset.mul_sum, finiteFiberAverage]

variable [TopologicalSpace G] [IsTopologicalAddGroup G]

theorem finiteFiberAverage_continuous {f : G → ℝ} (hf : Continuous f) :
    Continuous (finiteFiberAverage C f) := by
  apply continuous_const.mul
  apply continuous_finsetSum
  intro k _
  exact hf.comp (continuous_id.add continuous_const)

theorem finiteFiberAverage_factor [CompactSpace G] [TopologicalSpace H] [T2Space H]
    (hC : Continuous C) (hCs : Function.Surjective C) {f : G → ℝ} (hf : Continuous f) :
    ∃ g : H → ℝ, Continuous g ∧ ∀ x, g (C x) = finiteFiberAverage C f x := by
  let e : ContinuousMap G H := ⟨C, hC⟩
  have hq : IsQuotientMap e := IsQuotientMap.of_surjective_continuous hCs hC
  let a : ContinuousMap G ℝ := ⟨finiteFiberAverage C f, finiteFiberAverage_continuous C hf⟩
  have hfac : Function.FactorsThrough a e :=
    fun _ _ hxy => finiteFiberAverage_eq_of_map_eq C f hxy
  let g := hq.lift a hfac
  refine ⟨g, g.continuous, ?_⟩
  intro x
  exact DFunLike.congr_fun (hq.lift_comp a hfac) x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
variable (C : G →+ H) [Fintype C.ker]

theorem finiteFiberAverage_integral_of_invariant
    (μ : Measure G) [IsFiniteMeasure μ]
    (hμ : ∀ k : C.ker, μ.map (fun x => x + k.val) = μ)
    (f : G → ℝ) (hf : Continuous f) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    (∫ x, finiteFiberAverage C f x ∂μ) = ∫ x, f x ∂μ := by
  have hi (k : C.ker) : Integrable (fun x => f (x + k.val)) μ :=
    Integrable.of_bound (hf.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      B (ae_of_all μ (fun x => hB _))
  have he (k : C.ker) : (∫ x, f (x + k.val) ∂μ) = ∫ x, f x ∂μ := by
    have hm : Measurable (fun x : G => x + k.val) :=
      (continuous_id.add continuous_const).measurable
    have h := integral_map hm.aemeasurable
      (hf.aestronglyMeasurable (μ := μ.map (fun x => x + k.val)))
    rw [hμ k] at h
    exact h.symm
  unfold finiteFiberAverage
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => hi k)]
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card C.ker : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

variable [T2Space G] [MeasurableSpace X] [MeasurableAdd₂ G]

omit [IsTopologicalAddGroup G] in
theorem finiteKernelLiftLaw_integral (ρ : Measure X) [IsFiniteMeasure ρ]
    (s : X → G) (hs : Measurable s) (f : G → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    (∫ y, f y ∂finiteKernelLiftLaw C ρ s) = ∫ x, finiteFiberAverage C f (s x) ∂ρ := by
  have hL : Measurable (fun p : X × C.ker => s p.1 + p.2.val) :=
    (hs.comp measurable_fst).add (measurable_subtype_coe.comp measurable_snd)
  have hi : Integrable (fun p : X × C.ker => f (s p.1 + p.2.val))
      (ρ.prod (PMF.uniformOfFintype C.ker).toMeasure) :=
    Integrable.of_bound (hf.comp hL).aestronglyMeasurable B (ae_of_all _ (fun p => hB _))
  rw [finiteKernelLiftLaw, integral_map hL.aemeasurable hf.aestronglyMeasurable,
    integral_prod _ hi]
  exact integral_congr_ae (ae_of_all ρ (fun x => finiteFiberAverage_integral_uniform C f (s x)))

theorem finiteKernelLiftLaw_eq [CompactSpace G] [HasOuterApproxClosed G]
    [TopologicalSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (hC : Continuous C) (hCs : Function.Surjective C)
    (μ : Measure G) [IsFiniteMeasure μ]
    (hμ : ∀ k : C.ker, μ.map (fun x => x + k.val) = μ)
    (ρ : Measure X) [IsFiniteMeasure ρ] (s : X → G) (hs : Measurable s)
    (hbase : ρ.map (C ∘ s) = μ.map C) :
    finiteKernelLiftLaw C ρ s = μ := by
  let _ : IsFiniteMeasure (finiteKernelLiftLaw C ρ s) := by
    unfold finiteKernelLiftLaw
    infer_instance
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  obtain ⟨g, hgc, hg⟩ := finiteFiberAverage_factor C hC hCs φ.continuous
  calc
    (∫ y, φ y ∂finiteKernelLiftLaw C ρ s) =
        ∫ x, finiteFiberAverage C φ (s x) ∂ρ :=
      finiteKernelLiftLaw_integral C ρ s hs φ φ.continuous.measurable φ.norm_coe_le_norm
    _ = ∫ x, g (C (s x)) ∂ρ := by simp_rw [hg]
    _ = ∫ y, g y ∂ρ.map (C ∘ s) :=
      (integral_map (hC.measurable.comp hs).aemeasurable hgc.aestronglyMeasurable).symm
    _ = ∫ y, g y ∂μ.map C := by rw [hbase]
    _ = ∫ x, g (C x) ∂μ := integral_map hC.measurable.aemeasurable hgc.aestronglyMeasurable
    _ = ∫ x, finiteFiberAverage C φ x ∂μ := by simp_rw [hg]
    _ = ∫ x, φ x ∂μ :=
      finiteFiberAverage_integral_of_invariant C μ hμ φ φ.continuous φ.norm_coe_le_norm

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

theorem finiteKernelLift_density (hC : Continuous C) (hCs : Function.Surjective C)
    (μ : Measure G) [μ.IsAddLeftInvariant] (ν : Measure H)
    (hmp : MeasurePreserving C μ ν)
    (D : H → ℝ) (hD : Measurable D) (hi : Integrable D ν) (h0 : ∀ y, 0 ≤ D y)
    (ρ : Measure X) [IsFiniteMeasure ρ] (s : X → G) (hs : Measurable s)
    (hbase : ρ.map (C ∘ s) = realDensityMeasure ν D) :
    finiteKernelLiftLaw C ρ s = realDensityMeasure μ (fun x => D (C x)) := by
  have hci : Integrable (fun x => D (C x)) μ := hmp.integrable_comp_of_integrable hi
  let _ := realDensityMeasure_finite μ (fun x => D (C x)) hci (fun x => h0 _)
  refine finiteKernelLiftLaw_eq C hC hCs (realDensityMeasure μ (fun x => D (C x)))
    ?_ ρ s hs ?_
  · intro k
    rw [realDensityMeasure_map_add_right]
    congr 1
    funext x
    rw [map_sub, show C k.val = 0 from k.property, sub_zero]
  · rw [measurePreserving_realDensity_map μ ν C hmp D hD hi h0]
    exact hbase

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalCoverLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] (U : Submodule ℝ (D → ℝ))
variable [MeasurableSpace (SubspaceArrayTorus Unit U)] [BorelSpace (SubspaceArrayTorus Unit U)]

variable (ν : Measure (euclideanSubspace U ⧸
  (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {K : Type*} [Fintype K] {m : ℕ} {J I : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include ν in
theorem canonicalCoefficientCoverLaw
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (hw : ∀ j i e, 0 < w j i e)
    (hs : ∀ j e x, mixedCoefficientDensity (fun i => c j i e) (fun i => w j i e)
      (fun i => p j i e) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))
    (d : ℕ) (hd : 0 < d) :
    letI := coefficientCoverKernelFintype (K := K) U d hd
    finiteKernelLiftLaw (G := CoefficientTorus (K := K) U) (H := CoefficientTorus (K := K) U)
        (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d)
        (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j)))
        (canonicalCoefficientCoverLift U b hb o d) =
      realDensityMeasure μ (fun y => canonicalCoefficientDensity U b hb o c w p
        (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d y)) := by
  let _ := coefficientCoverKernelFintype (K := K) U d hd
  let : ∀ j, IsProbabilityMeasure (mixedScalarArrayLaw (c j) (w j) (p j)) :=
    fun j => mixedScalarArrayLaw_probability _ _ (hw j) _
  let : IsProbabilityMeasure (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) :=
    Measure.pi.instIsProbabilityMeasure _
  have hi := (canonicalCoefficientDensity_mass U b hb o c w p μ ν hw hs).1
  apply finiteKernelLift_density (G := CoefficientTorus (K := K) U) (H := CoefficientTorus (K := K) U)
    (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d)
    (quotientIntegerCover_continuous _ d) (quotientIntegerCover_surjective _ d hd)
    μ μ (coefficientCover_measurePreserving U μ d hd)
    (canonicalCoefficientDensity U b hb o c w p)
    (canonicalCoefficientDensity_measurable U b hb o c w p) hi
    (canonicalCoefficientDensity_nonneg U b hb o c w p hw)
    _ _ (canonicalCoefficientCoverLift_measurable U b hb o d)
  have he : quotientIntegerCover (coefficientIntegerLattice (K := K) U) d ∘
      canonicalCoefficientCoverLift U b hb o d = canonicalCoefficientSample U b hb o :=
    funext (canonicalCoefficientCoverLift_projection U b hb o d hd)
  rw [he]
  exact canonicalCoefficientDensity_law U b hb o c w p μ ν hw hs

end Erdos3.VectorPolynomial

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

theorem canonicalCoefficientDeckSample_relabel (d : ℕ) [NeZero d]
    [Fintype (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker]
    (ρ : Measure (CoefficientSamplerArrays (K := K) I n)) [SFinite ρ] :
    (ρ.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
        (fun x : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d =>
          canonicalCoefficientDeckSample (K := K) U bW b hb o d
            (Nat.pos_of_ne_zero (NeZero.ne d)) x.1 x.2) =
      finiteKernelLiftLaw (G := CoefficientTorus (K := K) U) (H := CoefficientTorus (K := K) U)
        (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d) ρ
        (canonicalCoefficientCoverLift (K := K) U b hb o d) := by
  let e : CoefficientDeckResidues (K := K) B d ≃
      (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker :=
    (coefficientDeckKernelEquiv (K := K) (J := J) (B := B) U bW d
      (Nat.pos_of_ne_zero (NeZero.ne d))).toEquiv
  have he : Measurable e := measurable_of_finite _
  have hm : (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure.map e =
      (PMF.uniformOfFintype
        (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker).toMeasure := by
    rw [PMF.toMeasure_map e _ he, uniformPMF_map_equiv e]
  have hp := Measure.map_prod_map ρ
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure measurable_id he
  rw [Measure.map_id, hm] at hp
  have hg : Measurable (fun p : CoefficientSamplerArrays (K := K) I n ×
      (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker =>
        canonicalCoefficientCoverLift U b hb o d p.1 + p.2.val) :=
    ((canonicalCoefficientCoverLift_measurable U b hb o d).comp measurable_fst).add
      (measurable_subtype_coe.comp measurable_snd)
  rw [finiteKernelLiftLaw, hp, Measure.map_map hg (measurable_id.prodMap he)]
  rfl

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include ν in
theorem canonicalCoefficientDeckSample_law
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (hw : ∀ j i e, 0 < w j i e)
    (hs : ∀ j e x, mixedCoefficientDensity (fun i => c j i e) (fun i => w j i e)
      (fun i => p j i e) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))
    (d : ℕ) [NeZero d] :
    ((Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))).prod
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
        (fun x : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d =>
          canonicalCoefficientDeckSample (K := K) U bW b hb o d
          (Nat.pos_of_ne_zero (NeZero.ne d)) x.1 x.2) =
      realDensityMeasure μ (fun y => canonicalCoefficientDensity U b hb o c w p
        (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d y)) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let _ := coefficientCoverKernelFintype (K := K) U d hd
  let : ∀ j, IsProbabilityMeasure (mixedScalarArrayLaw (c j) (w j) (p j)) :=
    fun j => mixedScalarArrayLaw_probability _ _ (hw j) _
  let : IsProbabilityMeasure (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) :=
    Measure.pi.instIsProbabilityMeasure _
  exact (canonicalCoefficientDeckSample_relabel (K := K) U bW b hb o d
    (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j)))).trans
      (canonicalCoefficientCoverLaw (K := K) U b hb o μ ν c w p hw hs d hd)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedProgressionDensityIdentity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

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

include ν in
theorem canonicalCoefficientDeckSample_law_of_eq
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (hw : ∀ j i e, 0 < w j i e)
    (hs : ∀ j e x, mixedCoefficientDensity (fun i => c j i e) (fun i => w j i e)
      (fun i => p j i e) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))
    (source : Measure (CoefficientSamplerArrays (K := K) I n))
    (density : CoefficientTorus (K := K) U → ℝ)
    (hsource : source = Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j)))
    (hdensity : density = canonicalCoefficientDensity U b hb o c w p)
    (d : ℕ) [NeZero d] :
    CoefficientDeckDensityLaw U bW b hb o μ source density d := by
  subst source density
  exact canonicalCoefficientDeckSample_law U bW b hb o μ ν c w p hw hs d

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

include ν in
theorem allocatedCoefficientDeckSample_density_law
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ C j * ‖z‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) :
    CoefficientDeckDensityLaw U bW basis hb o μ source density d := by
  exact canonicalCoefficientDeckSample_law_of_eq U bW basis hb o μ ν
    (allocatedLayerCenters B U basis S) (allocatedLayerWidths B U basis S)
    (allocatedLayerIntegerPMFs B U basis hR hσ S)
    (allocatedLayerWidths_pos B U basis hR hσ S)
    (allocatedLayerColumns_chart B U basis hR hσ S o hσ1 C hC hchart hsmall)
    source density rfl rfl d

end Erdos3.VectorPolynomial

end

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
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ)

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "actual" => (∫ p, FiniteProbabilityWeights.complexMean wholeLaw (fun y =>
  F (Prod.fst ((allocatedCoefficientSplit B U basis S) (Prod.fst p)),
    euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows
      (canonicalCoefficientDeckSample U bW basis hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) (Prod.fst p) (Prod.snd p))))
  ∂(Measure.prod source (PMF.toMeasure deck)))

end Erdos3.VectorPolynomial

end

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
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "ξ" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedCoefficientDeckSample_density_law.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedCoefficientDeckSample_density_law.{u_1, u_2, u_3, u_4, u_5}
