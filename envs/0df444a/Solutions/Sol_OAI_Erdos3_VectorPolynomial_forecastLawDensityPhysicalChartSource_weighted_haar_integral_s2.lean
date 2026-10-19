-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalChartSource_weighted_haar_integral_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:12:21.830614+00:00
-- url     : https://prove2.me/submissions/4d70adb0-4525-41a0-b3dd-99938840a92e

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B112
import Definitions.Def_OAIE3v2B113
import Definitions.Def_OAIE3v2B186
import Definitions.Def_OAIE3v2B199
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_mixedCoveredJet_reference_map_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

theorem restrictedComplexChartDensity_apply (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) (hinj : Set.InjOn q S) {x : X} (hx : x ∈ S) :
    restrictedComplexChartDensity q S c f (q x) = (c : ℂ) * f x := by
  have he : Function.Injective (fun x : S => q x.val) := fun a b h => Subtype.ext (hinj a.property b.property h)
  exact congrArg (fun z : ℂ => (c : ℂ) * z) (he.extend_apply (fun x => f x.val) (fun _ => 0) ⟨x, hx⟩)

theorem restrictedComplexChartDensity_zero (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) {y : Y} (hy : y ∉ q '' S) :
    restrictedComplexChartDensity q S c f y = 0 := by
  have hy' : y ∉ Set.range (fun x : S => q x.val) := by
    rintro ⟨x, rfl⟩
    exact hy ⟨x.val, x.property, rfl⟩
  simp only [restrictedComplexChartDensity, Function.extend_apply' _ _ _ hy', mul_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RestrictedComplexChartSupport
namespace OAI

section

namespace Erdos3

variable {X Y : Type*}

theorem restrictedComplexChartDensity_measurable [MeasurableSpace X] [MeasurableSpace Y]
    (q : X → Y) (S : Set X) (he : MeasurableEmbedding (fun x : S => q x.val))
    (c : ℝ) (f : X → ℂ) (hf : Measurable f) :
    Measurable (restrictedComplexChartDensity q S c f) :=
  measurable_const.mul (he.measurable_extend (hf.comp measurable_subtype_coe) measurable_const)

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

theorem coveredJetChart_embedding (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    MeasurableEmbedding (fun x : coveredJetSourceRegion (B := B) U b d Ω =>
      coveredJetChart U b hb bW d x.val) := by
  let : ∀ j, PolishSpace ((euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) :=
    fun _ => inferInstance
  let : ∀ j, PolishSpace (O j → (euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) :=
    fun _ => by constructor
  let : PolishSpace (CoveredJetChartSource U O B n d) := by constructor
  exact ContinuousOn.measurableEmbedding (coveredJetSourceRegion_measurable U b d Ω hΩm)
    (coveredJetChart_continuous U b hb bW d).continuousOn
    (coveredJetChart_injOn U b hb bW d Ω hΩ)

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

theorem standardLatticeClosedQuarterBox_isCompact (J : Type*) [Fintype J] :
    IsCompact (standardLatticeClosedQuarterBox J) := by
  have he : standardLatticeClosedQuarterBox J =
      (PiLp.homeomorph 2 (fun _ : J => ℝ)) ⁻¹'
        Set.Icc (fun _ => -(1 / 4 : ℝ)) (fun _ => (1 / 4 : ℝ)) := by
    ext x
    simp only [standardLatticeClosedQuarterBox, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_Icc, Pi.le_def, abs_le, forall_and]
    rfl
  rw [he]
  exact (PiLp.homeomorph 2 (fun _ : J => ℝ)).isClosedEmbedding.isCompact_preimage isCompact_Icc

theorem standardLatticeClosedQuarterBox_subset_smallBox (J : Type*) [Fintype J] :
    standardLatticeClosedQuarterBox J ⊆ standardLatticeSmallBox J := by
  intro x hx i
  exact (hx i).trans_lt (by norm_num)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoveredSiteExpansion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d Ω

include hΩ

omit [∀ j, Fintype (O j)] in
theorem mixedCoveredJet_restrictedComplexDensity_eq (f : MixedCoveredJetSource I O E n d → ℂ) :
    restrictedComplexChartDensity chart region 1 f =
      restrictedComplexChartDensity (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) 1
        (fun z => f ((mixedCoveredJetEquiv U o d).symm z)) := by
  funext y
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [restrictedComplexChartDensity_apply _ _ _ _
      (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ) hz]
    change _ = restrictedComplexChartDensity (coveredJetChart U b hb bW d)
      (coveredJetSourceRegion U b d Ω) 1 _
      (coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d z))
    rw [restrictedComplexChartDensity_apply _ _ _ _
      (coveredJetChart_injOn U b hb bW d Ω hΩ) hz]
    exact congrArg (fun w => (1 : ℂ) * f w) ((mixedCoveredJetEquiv U o d).symm_apply_apply z).symm
  · rw [restrictedComplexChartDensity_zero _ _ _ _ hy]
    symm
    apply restrictedComplexChartDensity_zero
    rwa [← mixedCoveredJetChart_image U o b hb bW d Ω]

theorem mixedCoveredJet_restrictedComplexDensity_measurable
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (f : MixedCoveredJetSource I O E n d → ℂ) (hf : Measurable f) :
    Measurable (restrictedComplexChartDensity chart region 1 f) := by
  rw [mixedCoveredJet_restrictedComplexDensity_eq U o b hb bW d Ω hΩ]
  exact restrictedComplexChartDensity_measurable _ _
    (coveredJetChart_embedding U b hb bW d Ω hΩm hΩ) 1 _
    (hf.comp (mixedCoveredJetEquiv U o d).symm.measurable)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory _root_.Set _root_.OAI.Set
open scoped Classical

theorem restrictedComplexChartDensity_weighted_integral_of_map
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (q : X → Y) (hq : Measurable q) (S : Set X) (hS : MeasurableSet S)
    (hinj : Set.InjOn q S) (himage : MeasurableSet (q '' S))
    (μ : Measure X) (ν : Measure Y)
    (hmap : Measure.map q (μ.restrict S) = ν.restrict (q '' S))
    (f : X → ℂ) (test : Y → ℂ)
    (hm : Measurable (fun y => restrictedComplexChartDensity q S 1 f y * test y)) :
    (∫ y, restrictedComplexChartDensity q S 1 f y * test y ∂ν) =
      ∫ x in S, f x * test (q x) ∂μ := by
  let F := fun y => restrictedComplexChartDensity q S 1 f y * test y
  have hind : (q '' S).indicator F = F := by
    funext y
    by_cases hy : y ∈ q '' S
    · exact indicator_of_mem hy F
    · simp only [indicator_of_notMem hy, F,
        restrictedComplexChartDensity_zero q S 1 f hy, zero_mul]
  calc
    _ = ∫ y in q '' S, F y ∂ν := by rw [← integral_indicator himage, hind]
    _ = ∫ x in S, F (q x) ∂μ := by
      rw [← hmap, integral_map_of_stronglyMeasurable hq hm.stronglyMeasurable]
    _ = _ := by
      apply setIntegral_congr_fun hS
      intro x hx
      simp only [F, restrictedComplexChartDensity_apply q S 1 f hinj hx,
        Complex.ofReal_one, one_mul]

namespace VectorPolynomial

open Module Submodule

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

theorem mixedCoveredJet_weighted_complex_integral
    (f : MixedCoveredJetSource I O E n d → ℂ) (hf : Measurable f)
    (test : EuclideanJetLayers U O → ℂ) (htest : Measurable test) :
    (∫ y, restrictedComplexChartDensity chart region 1 f y * test y ∂haar) =
      (coveredJetArrayScale (O := O) U : ℂ) *
        ∫ z in region, f z * test (chart z) ∂raw := by
  have hq : Measurable chart :=
    (coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
      (mixedCoveredJetCoordinates_measurable (O := O) (B := E) (n := n) U o d)
  have hS : MeasurableSet region :=
    (coveredJetSourceRegion_measurable U b d Ω hΩm).preimage
      (mixedCoveredJetCoordinates_measurable (O := O) (B := E) (n := n) U o d)
  have himage : MeasurableSet (chart '' region) := by
    rw [mixedCoveredJetChart_image U o b hb bW d Ω]
    have h := (coveredJetChart_embedding U b hb bW d Ω hΩm hΩ).measurableSet_range
    have he : Set.range (fun x : coveredJetSourceRegion U b d Ω =>
        coveredJetChart U b hb bW d x.val) =
        coveredJetChart U b hb bW d '' coveredJetSourceRegion U b d Ω := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x.val, x.property, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rwa [he] at h
  rw [restrictedComplexChartDensity_weighted_integral_of_map chart hq region hS
    (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ) himage
    (coveredJetArrayReference U d) haar
    (mixedCoveredJet_reference_map_s2 U o b hb bW d ν Ω hΩm hΩ) f test
    ((mixedCoveredJet_restrictedComplexDensity_measurable U o b hb bW d Ω hΩ hΩm f hf).mul htest)]
  rw [coveredJetArrayReference_eq_real_smul, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (coveredJetArrayScale_pos (O := O) U).le]
  rfl

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

omit [∀ j, Fintype (I j)] in
theorem allocatedFullMixedSiteValue_continuous :
    Continuous (allocatedFullMixedSiteValue (I := I) (R := R) U b) := by
  apply continuous_pi
  rintro ⟨j, i | i⟩
  · change Continuous (fun w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ) => (w j).1 i / R j)
    fun_prop
  · change Continuous (fun w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ) =>
      ((w j).2 i : ℝ) / (basisAxisScale (b j) i : ℝ) / R j)
    fun_prop

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal BigOperators

variable {X : Type*} [Fintype X]

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (P : LayerSamplerAxis I n → Prop)
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
variable (R : Fin m → ℝ)

theorem forecastNormalizedActiveCoordinates_lipschitz :
    LipschitzWith 1 (forecastNormalizedActiveCoordinates P) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  exact (dist_pi_le_iff dist_nonneg).mpr (fun a => dist_le_pi_dist v w a.1.val)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawNativeRawJointMean
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

theorem forecastLawDensityPhysicalChartSource_measurable
    (hdensity : Measurable density) (u : X → ℤ) :
    Measurable (forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
      active Y N volume base physicalN τ u) := by
  let source := MixedCoveredJetSource I single Eout n N
  let w : source → ∀ j, (I j → ℝ) × (Fin (n j) → ℤ) :=
    fun z j => mixedArrayRegroup _ _ _ (z.1 j) ()
  have hw : Measurable w := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_pi_apply ()).comp
      ((mixedArrayRegroup _ _ _).measurable.comp
        ((measurable_pi_apply j).comp measurable_fst))
  have hcoord : Measurable (fun z : source =>
      forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue (R := R) U basis (w z))) :=
    (forecastNormalizedActiveCoordinates_lipschitz short).continuous.measurable.comp
      ((allocatedFullMixedSiteValue_continuous (I := I) (R := R) U basis).measurable.comp hw)
  have hreal : Measurable (fun z : source => density
      ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
        forecastNormalizedActiveCoordinates short
          (allocatedFullMixedSiteValue (R := R) U basis (w z)))) :=
    hdensity.comp (measurable_const.prodMk hcoord)
  let integerData : source → (∀ j, Fin (n j) → ℤ) × (∀ j, Eout j → ℤ) :=
    fun z => (fun j i => (z.1 j).2 i (), fun j i => ((z.2 j () i).val : ℤ))
  have hdata : Measurable integerData := by
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro j
      apply measurable_pi_iff.mpr
      intro i
      exact (measurable_pi_apply ()).comp ((measurable_pi_apply i).comp
        (measurable_snd.comp ((measurable_pi_apply j).comp measurable_fst)))
    · exact (measurable_of_finite
        (fun v : ∀ j, Unit → Eout j → ZMod N => fun j i => ((v j () i).val : ℤ))).comp
        measurable_snd
  let rational : (∀ j, Fin (n j) → ℤ) × (∀ j, Eout j → ℤ) → ℝ :=
    fun v => rationalInactiveForecast law active
      (forecastInactiveFixedOutput B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
      Y N volume (fun a _ => v.1 (selected a).1 (selected a).2)
      (fun output => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (v.1 j) (v.2 j)) output : ZMod N))
  have hrational : Measurable rational := measurable_of_countable rational
  exact hreal.complex_ofReal.mul ((hrational.comp hdata).complex_ofReal)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawOriginalNativeHaarJointMean
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N

theorem forecastLawDensityPhysicalChartSource_weighted_haar_integral_s2_oai
    (hdensity : Measurable density) (u : X → ℤ)
    (test : EuclideanJetLayers U single → ℂ) (htest : Measurable test) :
    (∫ y, restrictedComplexChartDensity chart region 1 (chartSource u) y * test y ∂haar) =
      (coveredJetArrayScale (O := single) U : ℂ) *
        ∫ z in region, chartSource u z * test (chart z) ∂raw := by
  exact mixedCoveredJet_weighted_complex_integral U o basis hb bW N ν _
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).isClosed.measurableSet)
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
    (chartSource u)
    (forecastLawDensityPhysicalChartSource_measurable B U basis S law density selected sample x
      active Y N volume base physicalN τ hdensity u) test htest

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8} : type_of% @OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalChartSource_weighted_haar_integral_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8} := @OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalChartSource_weighted_haar_integral_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8}
