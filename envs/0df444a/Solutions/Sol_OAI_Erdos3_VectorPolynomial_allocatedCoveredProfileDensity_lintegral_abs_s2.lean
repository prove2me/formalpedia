-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedCoveredProfileDensity_lintegral_abs_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:26:11.922721+00:00
-- url     : https://prove2.me/submissions/0868fd63-ce79-4bf3-8623-e4c1e67ccd83

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_coveredJetArray_density_law_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityMixtureAELaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem pmf_real_mass {X : Type*} (p : PMF X) : (∑' x, (p x).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (p.apply_ne_top), p.tsum_coe, ENNReal.toReal_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem realDensityMeasure_lintegral_of_map (μ : Measure X) (ν : Measure Y)
    (q : X → Y) (hq : Measurable q) (f : X → ℝ) (g : Y → ℝ)
    (hlaw : Measure.map q (realDensityMeasure μ f) = realDensityMeasure ν g) :
    (∫⁻ y, ENNReal.ofReal (g y) ∂ν) = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  have h := congrArg (fun ρ : Measure Y => ρ Set.univ) hlaw
  rw [Measure.map_apply hq MeasurableSet.univ, Set.preimage_univ] at h
  simpa only [realDensityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using h.symm

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem restrictedChartDensity_indicator (q : X → Y) (S : Set X) (c : ℝ) (f : X → ℝ) :
    restrictedChartDensity q S c (S.indicator f) = restrictedChartDensity q S c f := by
  unfold restrictedChartDensity
  congr 1
  funext x
  exact indicator_of_mem x.property f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductChartReference
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

theorem ennreal_smul_sigmaFinite {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (c : ℝ≥0∞) (hc : c ≠ ∞) : SigmaFinite (c • μ) where
  out' := ⟨{
    set := spanningSets μ
    set_mem := fun _ => trivial
    finite := by
      intro i
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top hc.lt_top (measure_spanningSets_lt_top μ i)
    spanning := iUnion_spanningSets μ }⟩

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

theorem pi_count_measure {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] [∀ i, Countable (X i)] :
    Measure.pi (fun i => (Measure.count : Measure (X i))) =
      (Measure.count : Measure (∀ i, X i)) := by
  apply Measure.ext_of_singleton
  intro x
  simp only [Measure.pi_singleton, Measure.count_singleton, Finset.prod_const_one]

theorem pi_smul_finite {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (c : I → ℝ≥0∞) (hc : ∀ i, c i ≠ ∞) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  let : ∀ i, SigmaFinite (c i • μ i) := fun i => ennreal_smul_sigmaFinite (μ i) (c i) (hc i)
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SigmaFiniteProductMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem sigmaFiniteProductMeasure_flatten {D : Type*} [Fintype D] {I : D → Type*}
    [∀ d, Fintype (I d)] {X : (Σ d, I d) → Type*}
    [∀ s, MeasurableSpace (X s)] (μ : ∀ s, Measure (X s)) [∀ s, SigmaFinite (μ s)] :
    (Measure.pi (fun d => Measure.pi (fun i => μ ⟨d, i⟩))).map
      (fun x (s : Σ d, I d) => x s.1 s.2) = Measure.pi μ := by
  have hm : Measurable (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) :=
    measurable_pi_iff.mpr (fun s => (measurable_pi_apply s.2).comp (measurable_pi_apply s.1))
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun d => Set.univ.pi (fun i => s ⟨d, i⟩)) := by
    ext x
    constructor
    · intro hx d _ i _
      exact hx ⟨d, i⟩ (Set.mem_univ _)
    · intro hx t _
      exact hx t.1 (Set.mem_univ _) t.2 (Set.mem_univ _)
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_sigma]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientDeckDensityLawCongruence
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

theorem pmf_realDensity_uniform {X : Type*} [Fintype X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : PMF X) :
    p.toMeasure = realDensityMeasure (PMF.uniformOfFintype X).toMeasure
      (fun x => (Fintype.card X : ℝ) * (p x).toReal) := by
  apply Measure.ext_of_singleton
  intro x
  rw [realDensityMeasure, withDensity_apply _ (measurableSet_singleton x), lintegral_singleton]
  rw [p.toMeasure_apply_singleton x (measurableSet_singleton x),
    (PMF.uniformOfFintype X).toMeasure_apply_singleton x (measurableSet_singleton x)]
  simp only [PMF.uniformOfFintype_apply,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.ofReal_toReal (p.apply_ne_top x)]
  have hc : (Fintype.card X : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_right_comm, ENNReal.mul_inv_cancel hc (by simp), one_mul]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

theorem coefficientDeckJetDensity_nonneg (d : ℕ) [NeZero d]
    (r : ∀ j, O j → B j → ZMod d) : 0 ≤ coefficientDeckJetDensity root A rows d r :=
  mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg

theorem coefficientDeckJetDensity_le_card (d : ℕ) [NeZero d]
    (r : ∀ j, O j → B j → ZMod d) :
    coefficientDeckJetDensity root A rows d r ≤ Fintype.card (∀ j, O j → B j → ZMod d) := by
  let p := (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
    (coefficientDeckJetMap root A rows d)
  have hp : (p r).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one r)
  exact (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)).trans_eq (mul_one _)

theorem coefficientDeckJetDensity_law (d : ℕ) [NeZero d] :
    ((PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
      (coefficientDeckJetMap root A rows d)).toMeasure =
    realDensityMeasure (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure
      (coefficientDeckJetDensity root A rows d) :=
  pmf_realDensity_uniform _

theorem coefficientDeckJetDensity_probability (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (realDensityMeasure
      (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure
      (coefficientDeckJetDensity root A rows d)) := by
  rw [← coefficientDeckJetDensity_law]
  infer_instance

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ControlledJointGrid
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem pmf_real_integral_count {X : Type*} [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : PMF X) :
    (∫ x, (p x).toReal ∂Measure.count) = 1 := by
  rw [integral_countable (pmf_real_integrable p)]
  simpa only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    using pmf_real_mass p

end Erdos3

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

theorem normalizedCoveredChart_continuous :
    Continuous (normalizedCoveredChart W b hb bW d) := by
  have hk : Continuous (fun r : R → ZMod d =>
      (coverKernelBasisEquiv (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
        bW d (Nat.pos_of_ne_zero (NeZero.ne d)) r).val) := continuous_of_discreteTopology
  exact ((normalizedCoverLift_continuous W b hb d).comp continuous_fst).add
    (hk.comp continuous_snd)

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

theorem coveredJetChart_continuous : Continuous (coveredJetChart (O := O) U b hb bW d) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro t
  exact (normalizedCoveredChart_continuous _ (b j) (hb j) (bW j) d).comp
    ((continuous_apply t).comp (continuous_apply j))

theorem coveredJetChart_injOn (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    Set.InjOn (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) := by
  intro x hx y hy he
  funext j t
  exact normalizedCoveredChart_injOn _ (b j) (hb j) (bW j) d (hΩ j t)
    (hx j (Set.mem_univ j) t (Set.mem_univ t)) (hy j (Set.mem_univ j) t (Set.mem_univ t))
    (congrFun (congrFun he j) t)

variable [∀ j, Fintype (O j)]

omit [∀ j, Fintype (B j)] [NeZero d] in
theorem coveredJetSourceRegion_measurable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t)) :
    MeasurableSet (coveredJetSourceRegion (B := B) U b d Ω) := by
  apply MeasurableSet.univ_pi
  intro j
  apply MeasurableSet.univ_pi
  intro t
  exact ((hΩm j t).preimage (normalizedLatticePoint_continuous _ (b j)).measurable).prod
    MeasurableSet.univ

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

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteGoodSupport
namespace OAI

section

namespace Erdos3

variable {X Y : Type*} (q : X → Y) (S : Set X) (hinj : Set.InjOn q S)

include hinj

theorem restrictedChartDensity_eq_of_values (g : Y → ℝ) (f : X → ℝ)
    (hvalue : ∀ x ∈ S, g (q x) = f x) (hzero : ∀ y ∉ q '' S, g y = 0) :
    g = restrictedChartDensity q S 1 f := by
  funext y
  by_cases hy : y ∈ q '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [restrictedChartDensity_apply q S 1 f hinj hx, one_mul, hvalue x hx]
  · rw [hzero y hy, restrictedChartDensity_zero q S 1 f hy]

end Erdos3

end

section

namespace Erdos3

variable {X Y : Type*} (q : X → Y) (S : Set X) (hinj : Set.InjOn q S)

include hinj

theorem restrictedChartDensity_abs (f : X → ℝ) :
    (fun y => |restrictedChartDensity q S 1 f y|) =
      restrictedChartDensity q S 1 (fun x => |f x|) := by
  apply restrictedChartDensity_eq_of_values q S hinj
  · intro x hx
    simp only [restrictedChartDensity_apply q S 1 _ hinj hx, one_mul]
  · intro y hy
    rw [restrictedChartDensity_zero q S 1 f hy, abs_zero]

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

theorem mixedCoveredJetChart_image (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j))) :
    mixedCoveredJetChart U o b hb bW d '' mixedCoveredJetRegion U o b d Ω =
      coveredJetChart U b hb bW d '' coveredJetSourceRegion U b d Ω := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨mixedCoveredJetCoordinates U o d z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := (mixedCoveredJetCoordinatesEquiv (O := O) (E := E) (n := n) U o d).surjective z
    refine ⟨w, ?_, ?_⟩
    · change mixedCoveredJetCoordinates U o d w ∈ coveredJetSourceRegion U b d Ω
      change mixedCoveredJetCoordinates U o d w = z at hw
      rwa [hw]
    · change coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d w) = _
      exact congrArg (coveredJetChart U b hb bW d) hw

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedCoveredRowReindex
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical BigOperators ENNReal

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem coveredJetArrayReference_eq_smul (d : ℕ) [NeZero d] :
    coveredJetArrayReference (O := O) (I := I) (B := B) (n := n) U d =
      (∏ j, (ENNReal.ofReal (ZLattice.covolume
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))))⁻¹ ^
          Fintype.card (O j)) •
        ((Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod
          (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure) := by
  unfold coveredJetArrayReference
  rw [pi_smul_finite _ _ (fun j => ENNReal.pow_ne_top
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos _ volume)).ne')),
    Measure.prod_smul_left]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}

theorem coveredJetArrayReference_eq_real_smul (d : ℕ) [NeZero d] :
    coveredJetArrayReference (O := O) (I := I) (B := B) (n := n) U d =
      ENNReal.ofReal (coveredJetArrayScale (O := O) U) •
        ((Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod
          (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure) := by
  rw [coveredJetArrayReference_eq_smul]
  congr 1
  symm
  rw [coveredJetArrayScale, ENNReal.ofReal_prod_of_nonneg (fun j _ =>
    pow_nonneg (inv_nonneg.mpr (ZLattice.covolume_pos _ volume).le) _)]
  apply Finset.prod_congr rfl
  intro j _
  rw [ENNReal.ofReal_pow (inv_nonneg.mpr (ZLattice.covolume_pos _ volume).le),
    ENNReal.ofReal_inv_of_pos (ZLattice.covolume_pos _ volume)]

theorem coveredJetArrayReference_density (d : ℕ) [NeZero d]
    (f : ((∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) → ℝ) :
    realDensityMeasure (coveredJetArrayReference U d)
      (fun x => f x / coveredJetArrayScale (O := O) U) =
    realDensityMeasure
      ((Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod
        (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure) f := by
  rw [coveredJetArrayReference_eq_real_smul,
    realDensityMeasure_smul_real _ _ (coveredJetArrayScale_pos U).le]
  congr 1
  funext x
  field_simp [(coveredJetArrayScale_pos (O := O) U).ne']

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedCoveredDensityMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d Ω
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := E) (n := n) d

include hΩm hΩ

theorem mixedCoveredJet_density_law (f : MixedCoveredJetSource I O E n d → ℝ)
    (hf : ∀ z ∉ region, f z = 0) :
    Measure.map chart (realDensityMeasure (coveredJetArrayReference U d) f) =
      realDensityMeasure haar (restrictedChartDensity chart region 1 f) := by
  have h := coveredJetArray_density_law_s2 U o b hb bW d ν Ω hΩm hΩ f hf
  have he : restrictedChartDensity (coveredJetChart U b hb bW d)
      (coveredJetSourceRegion U b d Ω) 1 (fun z => f ((mixedCoveredJetEquiv U o d).symm z)) =
      restrictedChartDensity chart region 1 f := by
    apply restrictedChartDensity_eq_of_values chart region
      (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ)
    · intro z hz
      rw [mixedCoveredJetChart, restrictedChartDensity_apply _ _ _ _
        (coveredJetChart_injOn U b hb bW d Ω hΩ) hz, one_mul]
      exact congrArg f ((mixedCoveredJetEquiv U o d).symm_apply_apply z)
    · intro y hy
      apply restrictedChartDensity_zero
      rwa [← mixedCoveredJetChart_image U o b hb bW d Ω]
  rw [he] at h
  exact h

theorem mixedCoveredJet_normalized_density_law (f : MixedCoveredJetSource I O E n d → ℝ) :
    Measure.map chart (realDensityMeasure raw (Set.indicator region f)) =
      realDensityMeasure haar (restrictedChartDensity chart region 1
        (fun z => f z / coveredJetArrayScale (O := O) U)) := by
  have he : (fun z => Set.indicator region f z / coveredJetArrayScale (O := O) U) =
      Set.indicator region (fun z => f z / coveredJetArrayScale (O := O) U) := by
    funext z
    by_cases hz : z ∈ region
    · simp only [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz, zero_div]
  unfold mixedCoveredJetRawReference
  rw [← coveredJetArrayReference_density U d (Set.indicator region f)]
  rw [he, mixedCoveredJet_density_law U o b hb bW d ν Ω hΩm hΩ _
    (fun z hz => Set.indicator_of_notMem hz _), restrictedChartDensity_indicator]

theorem mixedCoveredJet_normalized_lintegral (f : MixedCoveredJetSource I O E n d → ℝ) :
    (∫⁻ y, ENNReal.ofReal (restrictedChartDensity chart region 1
      (fun z => f z / coveredJetArrayScale (O := O) U) y) ∂haar) =
      ∫⁻ z in region, ENNReal.ofReal (f z) ∂raw := by
  have h := realDensityMeasure_lintegral_of_map raw haar chart
    ((coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
      (mixedCoveredJetCoordinates_measurable (O := O) (B := E) (n := n) U o d))
    (Set.indicator region f) _ (mixedCoveredJet_normalized_density_law U o b hb bW d ν Ω hΩm hΩ f)
  rw [h]
  have hS : MeasurableSet region := (coveredJetSourceRegion_measurable U b d Ω hΩm).preimage
    (mixedCoveredJetCoordinates_measurable (O := O) (B := E) (n := n) U o d)
  have he : (fun z => ENNReal.ofReal (Set.indicator region f z)) =
      Set.indicator region (fun z => ENNReal.ofReal (f z)) := by
    funext z
    by_cases hz : z ∈ region
    · simp only [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz, ENNReal.ofReal_zero]
  rw [he, lintegral_indicator hS]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedFrozenJetDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedGridJetFactor_mem_Icc (a : {a // grid a}) (z : CoefficientJetAxisRow O a.val) :
    allocatedGridJetFactor B U b hR hσ S x u v rows a z ∈ Set.Icc (0 : ℝ) 1 := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · refine ⟨ENNReal.toReal_nonneg, ?_⟩
    exact (ENNReal.toReal_mono ENNReal.one_ne_top ((integerMatrixImagePMF
      (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j))
      (allocatedLayerIntegerPMFs B U b hR hσ S j i)).coe_le_one z)).trans_eq ENNReal.toReal_one

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedGridJetDensity_mem_Icc (z : AllocatedFrozenJetRows B U b S O) :
    allocatedGridJetDensity B U b hR hσ S x u v rows z ∈ Set.Icc (0 : ℝ) 1 := by
  have h := allocatedGridJetFactor_mem_Icc B U b hR hσ S x u v rows
  exact ⟨Finset.prod_nonneg (fun a _ => (h a (z a)).1),
    Finset.prod_le_one (fun a _ => (h a (z a)).1) (fun a _ => (h a (z a)).2)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

theorem allocatedGridJetFactor_probability_data
    (a : {a // allocatedGridAxis (I := I) U b S.value a}) :
    Integrable (allocatedGridJetFactor B U b hR hσ S x u v rows a)
      (coefficientJetAxisReference O a.val) ∧
    (∫ z, allocatedGridJetFactor B U b hR hσ S x u v rows a z
      ∂coefficientJetAxisReference O a.val) = 1 := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · change Integrable _ (Measure.count : Measure (O j → ℤ)) ∧
      (∫ z : O j → ℤ, _ ∂Measure.count) = 1
    exact ⟨pmf_real_integrable _, pmf_real_integral_count _⟩

theorem allocatedGridJetDensity_probability_data :
    Integrable (allocatedGridJetDensity B U b hR hσ S x u v rows)
      (allocatedFrozenJetReference B U b S O) ∧
    (∫ z, allocatedGridJetDensity B U b hR hσ S x u v rows z
      ∂allocatedFrozenJetReference B U b S O) = 1 := by
  have hp := allocatedGridJetFactor_probability_data B U b S O hR hσ x u v rows
  refine ⟨Integrable.fintype_prod_dep (fun a => (hp a).1), ?_⟩
  change (∫ z, (∏ a, allocatedGridJetFactor B U b hR hσ S x u v rows a (z a))
    ∂Measure.pi (fun a : {a // allocatedGridAxis (I := I) U b S.value a} =>
      coefficientJetAxisReference O a.val)) = 1
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_eq_one (fun a _ => (hp a).2)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JetAxisReference
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} (O I : Fin m → Type*) (n : Fin m → ℕ)
variable [∀ j, Fintype (O j)] [∀ j, Fintype (I j)]

theorem coefficientJetAxisEquiv_measurePreserving :
    MeasurePreserving (coefficientJetAxisEquiv O I n)
      (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j)))
      (Measure.pi (coefficientJetAxisReference O)) := by
  let laws := coefficientJetAxisReference (I := I) (n := n) O
  have hinner (j : Fin m) : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi
        (fun a : I j ⊕ Fin (n j) => CoefficientJetAxisRow O ⟨j, a⟩)).symm
      (mixedArrayReference (I j) (Fin (n j)) (O j))
      (Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)) := by
    have hc : (Measure.pi (fun _ : Fin (n j) => (Measure.count : Measure (O j → ℤ)))) =
        Measure.count := pi_count_measure
    have h := measurePreserving_sumPiEquivProdPi_symm
      (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)
    change MeasurePreserving _
      ((Measure.pi (fun _ : I j => (volume : Measure (O j → ℝ)))).prod
        (Measure.pi (fun _ : Fin (n j) => (Measure.count : Measure (O j → ℤ))))) _ at h
    rw [hc] at h
    change MeasurePreserving _
      ((volume : Measure (I j → O j → ℝ)).prod
        (Measure.count : Measure (Fin (n j) → O j → ℤ))) _
    rw [volume_pi]
    exact h
  have houter := measurePreserving_pi
    (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))
    (fun j => Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)) hinner
  have hflat : MeasurePreserving
      (MeasurableEquiv.piCurry
        (fun j (a : I j ⊕ Fin (n j)) => CoefficientJetAxisRow O ⟨j, a⟩)).symm
      (Measure.pi (fun j => Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)))
      (Measure.pi laws) :=
    ⟨(MeasurableEquiv.piCurry
      (fun j (a : I j ⊕ Fin (n j)) => CoefficientJetAxisRow O ⟨j, a⟩)).symm.measurable,
      sigmaFiniteProductMeasure_flatten laws⟩
  exact hflat.comp houter

theorem coefficientJetAxisSplit_measurePreserving
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    MeasurePreserving (coefficientJetAxisSplit O I n P)
      (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j)))
      ((Measure.pi (fun a : {a // P a} => coefficientJetAxisReference O a.val)).prod
        (Measure.pi (fun a : {a // ¬P a} => coefficientJetAxisReference O a.val))) :=
  (measurePreserving_piEquivPiSubtypeProd (coefficientJetAxisReference O) P).comp
    (coefficientJetAxisEquiv_measurePreserving O I n)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoveredSiteExpansion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d Ω

variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "profile" => allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d Ω

variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "reference" => allocatedLongJetReference B U b S O

include hΩm hΩ in
theorem allocatedCoveredProfileDensity_lintegral_abs_s2_oai
    (f : AllocatedLongJetRows B U b S O → ℝ) (hf : Integrable f reference) :
    (∫⁻ y, ENNReal.ofReal |profile f y| ∂haar) ≤ ENNReal.ofReal (∫ z, |f z| ∂reference) := by
  let μf := allocatedFrozenJetReference B U b S O
  let μd := (PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure
  let μraw := (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod μd
  let fg := allocatedGridJetDensity B U b hR hσ S x u v rows
  let fd : (∀ j, O j → Q j → ZMod d) → ℝ := coefficientDeckJetDensity root dirs rows d
  let e := MeasurableEquiv.prodCongr split (MeasurableEquiv.refl (∀ j, O j → Q j → ZMod d))
  let F := fun z : (AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O) ×
      (∀ j, O j → Q j → ZMod d) => fg z.1.1 * |f z.1.2| * fd z.2
  have hfg : Integrable fg μf ∧ (∫ z, fg z ∂μf) = 1 :=
    allocatedGridJetDensity_probability_data B U b S O hR hσ x u v rows
  have hfg0 (z) : 0 ≤ fg z := (allocatedGridJetDensity_mem_Icc B U b hR hσ S x u v rows z).1
  let : IsProbabilityMeasure (realDensityMeasure μd fd) := coefficientDeckJetDensity_probability _ _ rows d
  have hfd := boundedDensity_mass μd fd (measurable_of_finite _) (coefficientDeckJetDensity_nonneg _ _ rows d)
    (coefficientDeckJetDensity_le_card _ _ rows d)
  have hFi : Integrable F ((μf.prod reference).prod μd) := (hfg.1.mul_prod hf.abs).mul_prod hfd.1
  have hF0 (z) : 0 ≤ F z := mul_nonneg (mul_nonneg (hfg0 _) (abs_nonneg _))
    (coefficientDeckJetDensity_nonneg _ _ rows d _)
  have hFm : (∫ z, F z ∂(μf.prod reference).prod μd) = ∫ z, |f z| ∂reference := by
    dsimp only [F]
    rw [integral_prod_mul (μ := μf.prod reference) (ν := μd)
      (fun z : AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O => fg z.1 * |f z.2|) fd,
      integral_prod_mul (μ := μf) (ν := reference) fg (fun z => |f z|), hfg.2, hfd.2, one_mul, mul_one]
  have he : MeasurePreserving e μraw ((μf.prod reference).prod μd) :=
    (coefficientJetAxisSplit_measurePreserving O I n grid).prod (MeasurePreserving.id μd)
  have hident : (fun z : MixedCoveredJetSource I O Q n d =>
      |allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 * f ((split z.1).2)|) =
      (fun z => F (e z) / coveredJetArrayScale (O := O) U) := by
    funext z
    change |(fg ((split z.1).1) * fd z.2 / coveredJetArrayScale (O := O) U) * f ((split z.1).2)| =
      (fg ((split z.1).1) * |f ((split z.1).2)| * fd z.2) / coveredJetArrayScale (O := O) U
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (hfg0 _),
      abs_of_nonneg (coefficientDeckJetDensity_nonneg _ _ rows d _), abs_of_pos (coveredJetArrayScale_pos U)]
    ring
  have ha := restrictedChartDensity_abs chart region
    (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ)
    (fun z : MixedCoveredJetSource I O Q n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 * f ((split z.1).2))
  calc
    _ = ∫⁻ y, ENNReal.ofReal (restrictedChartDensity chart region 1
        (fun z => F (e z) / coveredJetArrayScale (O := O) U) y) ∂haar := by
      apply lintegral_congr
      intro y
      change ENNReal.ofReal |restrictedChartDensity chart region 1 _ y| = _
      rw [congrFun ha y, hident]
    _ = ∫⁻ z in region, ENNReal.ofReal (F (e z)) ∂μraw :=
      mixedCoveredJet_normalized_lintegral U o b hb bW d ν Ω hΩm hΩ (fun z => F (e z))
    _ ≤ ∫⁻ z, ENNReal.ofReal (F (e z)) ∂μraw := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ z, ENNReal.ofReal (F z) ∂(μf.prod reference).prod μd :=
      he.lintegral_comp_emb e.measurableEmbedding (fun z => ENNReal.ofReal (F z))
    _ = ENNReal.ofReal (∫ z, |f z| ∂reference) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hFi (Filter.Eventually.of_forall hF0), hFm]

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedCoveredProfileDensity_lintegral_abs_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.allocatedCoveredProfileDensity_lintegral_abs_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
