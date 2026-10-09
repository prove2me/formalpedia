-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.mixedCoveredJet_normalized_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T11:57:17.952209+00:00
-- url     : https://prove2.me/submissions/a9be0562-b702-423d-b35c-8c8a7999f85a

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B114
import Definitions.Def_OAIErdos3B128

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeCoverMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem latticeQuotient_compact : CompactSpace (E ⧸ Λ.toAddSubgroup) := by
  have hc := IsZLattice.isCompact_range_of_periodic Λ
    (QuotientAddGroup.mk' Λ.toAddSubgroup) QuotientAddGroup.continuous_mk (by
      intro x z hz
      have hz0 : QuotientAddGroup.mk' Λ.toAddSubgroup z = 0 :=
        (QuotientAddGroup.eq_zero_iff z).mpr hz
      rw [map_add, hz0, add_zero])
  rw [Set.range_eq_univ.mpr (QuotientAddGroup.mk'_surjective _)] at hc
  exact ⟨hc⟩

variable [MeasurableSpace E] [BorelSpace E]

theorem latticeCover_measurePreserving
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (d : ℕ) (hd : 0 < d) :
    MeasurePreserving (quotientIntegerCover Λ.toAddSubgroup d) μ μ := by
  let : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discrete
  let : CompactSpace (E ⧸ Λ.toAddSubgroup) := latticeQuotient_compact Λ
  let : BorelSpace (E ⧸ Λ.toAddSubgroup) := QuotientAddGroup.borelSpace
  let : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving
    (quotientIntegerCover_continuous Λ.toAddSubgroup d)
    (quotientIntegerCover_surjective Λ.toAddSubgroup d hd) rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set

end Erdos3

end

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

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

end Erdos3

end

section

namespace Erdos3

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

theorem finiteKernelLiftLaw_relabel {G H X R : Type*}
    [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableAdd₂ G] [MeasurableSpace X]
    (C : G →+ H) [Fintype C.ker] [Fintype R] [Nonempty R]
    [MeasurableSpace R] [MeasurableSingletonClass R]
    (e : R ≃ C.ker) (ρ : Measure X) [SFinite ρ]
    (s : X → G) (hs : Measurable s) :
    (ρ.prod (PMF.uniformOfFintype R).toMeasure).map
        (fun p => s p.1 + (e p.2).val) = finiteKernelLiftLaw C ρ s := by
  have he : Measurable e := measurable_of_finite _
  have hm : (PMF.uniformOfFintype R).toMeasure.map e =
      (PMF.uniformOfFintype C.ker).toMeasure := by
    rw [PMF.toMeasure_map e _ he, uniformPMF_map_equiv]
  have hp : ρ.prod (PMF.uniformOfFintype C.ker).toMeasure =
      (ρ.prod (PMF.uniformOfFintype R).toMeasure).map (Prod.map id e) := by
    rw [← hm, ← Measure.map_prod_map _ _ measurable_id he, Measure.map_id]
  rw [finiteKernelLiftLaw, hp, Measure.map_map]
  · rfl
  · exact (hs.comp measurable_fst).add (measurable_subtype_coe.comp measurable_snd)
  · exact measurable_id.prodMap he

theorem finiteKernelLiftLaw_basisResidues {E I X : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype I]
    (Γ : AddSubgroup E) (b : Module.Basis I ℤ Γ)
    [TopologicalSpace (E ⧸ Γ)] [T2Space (E ⧸ Γ)]
    [MeasurableSpace (E ⧸ Γ)] [BorelSpace (E ⧸ Γ)] [MeasurableAdd₂ (E ⧸ Γ)]
    [MeasurableSpace X] (d : ℕ) [NeZero d]
    [Fintype (quotientIntegerCover Γ d).ker]
    (ρ : Measure X) [SFinite ρ] (s : X → E ⧸ Γ) (hs : Measurable s) :
    (ρ.prod (PMF.uniformOfFintype (I → ZMod d)).toMeasure).map
        (fun p => s p.1 + (coverKernelBasisEquiv Γ b d (Nat.pos_of_ne_zero (NeZero.ne d)) p.2).val) =
      finiteKernelLiftLaw (quotientIntegerCover Γ d) ρ s :=
  finiteKernelLiftLaw_relabel _ (coverKernelBasisEquiv Γ b d _).toEquiv ρ s hs

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

theorem realDensityMeasure_indicator_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S : Set X} (hS : MeasurableSet S) :
    realDensityMeasure μ (S.indicator (fun _ => (1 : ℝ))) = μ.restrict S := by
  have he : (fun x => ENNReal.ofReal (S.indicator (fun _ => (1 : ℝ)) x)) =
      S.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [realDensityMeasure, he]
  exact withDensity_indicator_one hS

theorem finiteKernelLift_restrict {G H X : Type*}
    [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    [T2Space G] [CompactSpace G] [HasOuterApproxClosed G] [MeasurableAdd₂ G]
    [TopologicalSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace X] (C : G →+ H) [Fintype C.ker]
    (hC : Continuous C) (hCs : Function.Surjective C)
    (μ : Measure G) [μ.IsAddLeftInvariant] (ν : Measure H) [IsFiniteMeasure ν]
    (hmp : MeasurePreserving C μ ν) {S : Set H} (hS : MeasurableSet S)
    (ρ : Measure X) [IsFiniteMeasure ρ] (s : X → G) (hs : Measurable s)
    (hbase : ρ.map (C ∘ s) = ν.restrict S) :
    finiteKernelLiftLaw C ρ s = μ.restrict (C ⁻¹' S) := by
  have hb : ρ.map (C ∘ s) = realDensityMeasure ν (S.indicator (fun _ => (1 : ℝ))) := by
    rw [realDensityMeasure_indicator_one ν hS]
    exact hbase
  have he : (fun x => S.indicator (fun _ => (1 : ℝ)) (C x)) =
      (C ⁻¹' S).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : C x ∈ S <;> simp [hx]
  rw [finiteKernelLift_density C hC hCs μ ν hmp _ (measurable_const.indicator hS)
    ((integrable_const (1 : ℝ)).indicator hS)
    (fun x => by by_cases hx : x ∈ S <;> simp [hx]) ρ s hs hb,
    he, realDensityMeasure_indicator_one μ (hS.preimage hC.measurable)]

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

theorem piChart_reference_map {I : Type*} [Fintype I] {X Y : I → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (ν : ∀ i, Measure (Y i)) [∀ i, SigmaFinite (ν i)]
    (q : ∀ i, X i → Y i) (hq : ∀ i, Measurable (q i)) (S : ∀ i, Set (X i))
    (hmap : ∀ i, ((μ i).restrict (S i)).map (q i) = (ν i).restrict (q i '' S i)) :
    ((Measure.pi μ).restrict (Set.univ.pi S)).map (fun x i => q i (x i)) =
      (Measure.pi ν).restrict ((fun x i => q i (x i)) '' Set.univ.pi S) := by
  let : ∀ i, SigmaFinite (((μ i).restrict (S i)).map (q i)) := by
    intro i
    rw [hmap i]
    infer_instance
  rw [Measure.restrict_pi_pi, Measure.pi_map_pi (fun i => (hq i).aemeasurable)]
  simp_rw [hmap]
  rw [← Measure.restrict_pi_pi]
  congr 1
  exact (Set.piMap_image_univ_pi q S).symm

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

theorem uniformPMF_toMeasure_pi {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] :
    (PMF.uniformOfFintype (∀ i, X i)).toMeasure =
      Measure.pi (fun i => (PMF.uniformOfFintype (X i)).toMeasure) := by
  apply Measure.ext_of_singleton
  intro x
  rw [(PMF.uniformOfFintype (∀ i, X i)).toMeasure_apply_singleton x (measurableSet_singleton x),
    Measure.pi_singleton]
  have he (i) : (PMF.uniformOfFintype (X i)).toMeasure {x i} =
      (Fintype.card (X i) : ℝ≥0∞)⁻¹ := by
    rw [(PMF.uniformOfFintype (X i)).toMeasure_apply_singleton (x i) (measurableSet_singleton _),
      PMF.uniformOfFintype_apply]
  simp only [he, PMF.uniformOfFintype_apply, Fintype.card_pi, Nat.cast_prod]
  exact ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (ENNReal.natCast_ne_top _))

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

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module
open scoped BigOperators ENNReal

theorem mixedArrayRegroup_volume_count (I Z O : Type*) [Fintype I] [Fintype Z] [Fintype O] :
    MeasurePreserving (mixedArrayRegroup I Z O) (mixedArrayReference I Z O)
      (Measure.pi (fun _ : O => (volume : Measure (I → ℝ)).prod (Measure.count : Measure (Z → ℤ)))) := by
  simpa only [mixedArrayReference, volume_pi, pi_count_measure] using
    (mixedArrayRegroup_measurePreserving (fun _ : I => fun _ : O => (volume : Measure ℝ))
      (fun _ : Z => fun _ : O => (Measure.count : Measure ℤ)))

variable {E I Z O : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [Fintype I] [Fintype Z] (o : OrthonormalBasis I ℝ E)

variable [Fintype O]

theorem orthonormalArrayChart_measurePreserving :
    MeasurePreserving (orthonormalArrayChart (O := O) (Z := Z) o) (mixedArrayReference I Z O)
      (Measure.pi (fun _ : O => (volume : Measure E).prod (Measure.count : Measure (Z → ℤ)))) := by
  have h := measurePreserving_pi
    (fun _ : O => (volume : Measure (I → ℝ)).prod (Measure.count : Measure (Z → ℤ)))
    (fun _ : O => (volume : Measure E).prod (Measure.count : Measure (Z → ℤ)))
    (fun _ => orthonormalMixedChart_measurePreserving (J := Z) o)
  exact h.comp (mixedArrayRegroup_volume_count I Z O)

theorem orthonormalArrayChart_scaled_reference (c : ℝ≥0∞) (hc : c ≠ ∞) :
    MeasurePreserving (orthonormalArrayChart (O := O) (Z := Z) o)
      (c ^ Fintype.card O • mixedArrayReference I Z O)
      (Measure.pi (fun _ : O => c • (volume : Measure E).prod (Measure.count : Measure (Z → ℤ)))) := by
  refine ⟨(orthonormalArrayChart o).measurable, ?_⟩
  rw [Measure.map_smul,
    (orthonormalArrayChart_measurePreserving o).map_eq,
    pi_smul_finite _ _ (fun _ => hc)]
  simp only [Finset.prod_const, Finset.card_univ]

theorem arrayResidueChart_measurePreserving {R : Type*} [MeasurableSpace R]
    (ν : Measure R) [SigmaFinite ν] (c : ℝ≥0∞) (hc : c ≠ ∞) :
    MeasurePreserving (arrayResidueChart (O := O) (Z := Z) o)
      ((c ^ Fintype.card O • mixedArrayReference I Z O).prod (Measure.pi (fun _ : O => ν)))
      (Measure.pi (fun _ : O => (c • (volume : Measure E).prod (Measure.count : Measure (Z → ℤ))).prod ν)) := by
  let : SigmaFinite (c • (volume : Measure E).prod (Measure.count : Measure (Z → ℤ))) :=
    ennreal_smul_sigmaFinite _ c hc
  have h₁ := (orthonormalArrayChart_scaled_reference (O := O) (Z := Z) o c hc).prod
    (MeasurePreserving.id (Measure.pi (fun _ : O => ν)))
  have h₂ := (measurePreserving_arrowProdEquivProdArrow (E × (Z → ℤ)) R O
    (fun _ => c • (volume : Measure E).prod (Measure.count : Measure (Z → ℤ)))
    (fun _ => ν)).symm (MeasurableEquiv.arrowProdEquivProdArrow (E × (Z → ℤ)) R O)
  exact h₂.comp h₁

end Erdos3

end

end OAI

end

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

theorem normalizedChartRegion_measurable
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    MeasurableSet (normalizedChartRegion W b hb Ω) := by
  have he := normalizedLatticeQuotient_embedding W b hb hΩm hΩ
  have hr : Set.range (fun x : normalizedLatticePoint W b ⁻¹' Ω =>
      normalizedLatticeQuotient W b hb x.val) = normalizedChartRegion W b hb Ω := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hr]
  exact he.measurableSet_range

variable [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
variable [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

theorem normalizedChartReference_map
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    (normalizedChartReference W b Ω).map (normalizedLatticeQuotient W b hb) =
      μ.restrict (normalizedChartRegion W b hb Ω) := by
  have hc : ENNReal.ofReal (ZLattice.covolume
      (latticeSection (standardEuclideanLattice D) W)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos _ volume)).ne'
  rw [normalizedChartReference,
    Measure.map_smul,
    normalizedLatticeQuotient_map_restrict W b hb μ hΩm hΩ, smul_smul,
    ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_smul]
  rfl

include hb μ in
theorem normalizedChartReference_finite
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    IsFiniteMeasure (normalizedChartReference W b Ω) := by
  have : IsFiniteMeasure ((normalizedChartReference W b Ω).map
      (normalizedLatticeQuotient W b hb)) := by
    rw [normalizedChartReference_map W b hb μ hΩm hΩ]
    infer_instance
  exact Measure.isFiniteMeasure_of_map (normalizedLatticeQuotient_measurable W b hb).aemeasurable

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalCoefficientCoverLift
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
variable (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
variable [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

theorem normalizedCoverLift_reference (d : ℕ) (hd : 0 < d)
    [Fintype (quotientIntegerCover (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d).ker]
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    finiteKernelLiftLaw
      (quotientIntegerCover (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d)
      (normalizedChartReference W b Ω) (normalizedCoverLift W b hb d) =
    μ.restrict (quotientIntegerCover
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d ⁻¹'
        normalizedChartRegion W b hb Ω) := by
  let Λ := latticeSection (standardEuclideanLattice D) W
  let : DiscreteTopology Λ.toAddSubgroup := latticeSection_discrete (standardEuclideanLattice D) W
  let : IsClosed (Λ.toAddSubgroup : Set W) := AddSubgroup.isClosed_of_discrete
  let : CompactSpace (W ⧸ Λ.toAddSubgroup) := latticeQuotient_compact Λ
  let : BorelSpace (W ⧸ Λ.toAddSubgroup) := QuotientAddGroup.borelSpace
  let : IsFiniteMeasure (normalizedChartReference W b Ω) :=
    normalizedChartReference_finite W b hb μ hΩm hΩ
  apply finiteKernelLift_restrict _ (quotientIntegerCover_continuous _ d)
    (quotientIntegerCover_surjective _ d hd) μ μ
    (latticeCover_measurePreserving Λ μ d hd)
    (normalizedChartRegion_measurable W b hb hΩm hΩ) _ _
    (normalizedCoverLift_continuous W b hb d).measurable
  have he : (quotientIntegerCover Λ.toAddSubgroup d ∘ normalizedCoverLift W b hb d) =
      normalizedLatticeQuotient W b hb := by
    funext x
    exact normalizedCoverLift_projection W b hb d hd x
  rw [he]
  exact normalizedChartReference_map W b hb μ hΩm hΩ

theorem normalizedCoverResidues_reference
    (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
    (d : ℕ) [NeZero d]
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    ((normalizedChartReference W b Ω).prod
      (PMF.uniformOfFintype (R → ZMod d)).toMeasure).map
        (fun p => normalizedCoverLift W b hb d p.1 +
          (coverKernelBasisEquiv (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
            bW d (Nat.pos_of_ne_zero (NeZero.ne d)) p.2).val) =
    μ.restrict (quotientIntegerCover
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d ⁻¹'
        normalizedChartRegion W b hb Ω) := by
  let Λ := latticeSection (standardEuclideanLattice D) W
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let : Fintype (quotientIntegerCover Λ.toAddSubgroup d).ker :=
    Fintype.ofEquiv (R → ZMod d) (coverKernelBasisEquiv Λ.toAddSubgroup bW d hd).toEquiv
  let : DiscreteTopology Λ.toAddSubgroup := latticeSection_discrete (standardEuclideanLattice D) W
  let : IsClosed (Λ.toAddSubgroup : Set W) := AddSubgroup.isClosed_of_discrete
  let : BorelSpace (W ⧸ Λ.toAddSubgroup) := QuotientAddGroup.borelSpace
  let : IsFiniteMeasure (normalizedChartReference W b Ω) :=
    normalizedChartReference_finite W b hb μ hΩm hΩ
  rw [finiteKernelLiftLaw_basisResidues Λ.toAddSubgroup bW d _ _
    (normalizedCoverLift_continuous W b hb d).measurable]
  exact normalizedCoverLift_reference W b hb μ d hd hΩm hΩ

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

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

theorem kernelLiftChart_image (hproj : ∀ x, C (s x) = q x) (S : Set X) :
    (fun p : X × C.ker => s p.1 + p.2.val) '' (S ×ˢ Set.univ) = C ⁻¹' (q '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.1, hx.1, ?_⟩
    have hk : C x.2.val = 0 := x.2.property
    simp only [map_add, hproj, hk, add_zero]
  · rintro ⟨x, hx, hxy⟩
    have hk : y - s x ∈ C.ker := by
      change C (y - s x) = 0
      rw [map_sub, hproj, ← hxy, sub_self]
    refine ⟨(x, ⟨y - s x, hk⟩), ⟨hx, Set.mem_univ _⟩, ?_⟩
    change s x + (y - s x) = y
    rw [← add_sub_assoc, add_sub_cancel_left]

theorem kernelLiftChart_relabel_injOn {R : Type*} (e : R ≃ C.ker)
    (hproj : ∀ x, C (s x) = q x) {S : Set X} (hq : Set.InjOn q S) :
    Set.InjOn (fun p : X × R => s p.1 + (e p.2).val) (S ×ˢ Set.univ) := by
  intro x hx y hy he
  have hp := kernelLiftChart_injOn C s q hproj hq
    (show (x.1, e x.2) ∈ S ×ˢ Set.univ from ⟨hx.1, Set.mem_univ _⟩)
    (show (y.1, e y.2) ∈ S ×ˢ Set.univ from ⟨hy.1, Set.mem_univ _⟩) he
  exact Prod.ext (congrArg (fun z : X × C.ker => z.1) hp)
    (e.injective (congrArg (fun z : X × C.ker => z.2) hp))

theorem kernelLiftChart_relabel_image {R : Type*} (e : R ≃ C.ker)
    (hproj : ∀ x, C (s x) = q x) (S : Set X) :
    (fun p : X × R => s p.1 + (e p.2).val) '' (S ×ˢ Set.univ) = C ⁻¹' (q '' S) := by
  rw [← kernelLiftChart_image C s q hproj S]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x.1, e x.2), ⟨hx.1, Set.mem_univ _⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x.1, e.symm x.2), ⟨hx.1, Set.mem_univ _⟩, by simp only [e.apply_symm_apply]⟩

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

theorem normalizedCoveredChart_image (Ω : Set (EuclideanSpace ℝ D)) :
    normalizedCoveredChart W b hb bW d ''
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ) =
    quotientIntegerCover (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d ⁻¹'
      normalizedChartRegion W b hb Ω :=
  kernelLiftChart_relabel_image _ _ _
    (coverKernelBasisEquiv _ bW d (Nat.pos_of_ne_zero (NeZero.ne d))).toEquiv
    (normalizedCoverLift_projection W b hb d (Nat.pos_of_ne_zero (NeZero.ne d))) _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedCoveredDensity
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))

variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

theorem normalizedCoveredReference_restrict (Ω : Set (EuclideanSpace ℝ D)) :
    (normalizedCoveredReference (R := R) (n := n) W d).restrict
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ) =
    (normalizedChartReference W b Ω).prod (PMF.uniformOfFintype (R → ZMod d)).toMeasure := by
  rw [normalizedCoveredReference, ← Measure.restrict_prod_eq_prod_univ, Measure.restrict_smul]
  rfl

variable [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
variable (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
variable [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

theorem normalizedCoveredChart_reference_map
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    ((normalizedCoveredReference (R := R) (n := n) W d).restrict
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ)).map
        (normalizedCoveredChart W b hb bW d) =
    μ.restrict (normalizedCoveredChart W b hb bW d ''
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ)) := by
  rw [normalizedCoveredReference_restrict W b d Ω, normalizedCoveredChart_image]
  exact normalizedCoverResidues_reference W b hb μ bW d hΩm hΩ

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredJetReference
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

theorem normalizedCoveredReference_sigmaFinite {D R : Type*} [Fintype D] [Fintype R]
    {n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)] (d : ℕ) [NeZero d] :
    SigmaFinite (normalizedCoveredReference (R := R) (n := n) W d) := by
  have hc : (ENNReal.ofReal (ZLattice.covolume
      (latticeSection (standardEuclideanLattice D) W)))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos _ volume)).ne'
  let : SigmaFinite ((ENNReal.ofReal (ZLattice.covolume
      (latticeSection (standardEuclideanLattice D) W)))⁻¹ •
        ((volume : Measure W).prod (Measure.count : Measure (Fin n → ℤ)))) :=
    ennreal_smul_sigmaFinite ((volume : Measure W).prod (Measure.count : Measure (Fin n → ℤ))) _ hc
  unfold normalizedCoveredReference
  infer_instance

namespace VectorPolynomial

variable {m : ℕ} {O J B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

theorem coveredJetChart_reference_map (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    ((coveredJetReference U d).restrict (coveredJetSourceRegion U b d Ω)).map
      (coveredJetChart U b hb bW d) =
    (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))).restrict
      (coveredJetChart U b hb bW d '' coveredJetSourceRegion U b d Ω) := by
  let : ∀ j, SigmaFinite (normalizedCoveredReference (R := B j) (n := n j)
      (euclideanSubspace (U j)) d) := fun j => normalizedCoveredReference_sigmaFinite _ d
  let : ∀ j, BorelSpace (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun _ => QuotientAddGroup.borelSpace
  let q := fun j => normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) d
  have hq (j) : Measurable (q j) := (normalizedCoveredChart_continuous _ (b j) (hb j) (bW j) d).measurable
  unfold coveredJetReference coveredJetSourceRegion coveredJetChart
  refine piChart_reference_map
    (fun j => Measure.pi (fun _ : O j => normalizedCoveredReference (R := B j) (n := n j)
      (euclideanSubspace (U j)) d))
    (fun j => Measure.pi (fun _ : O j => ν j))
    (fun j (x : O j → (euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) t => q j (x t))
    (fun j => measurable_pi_iff.mpr (fun t => (hq j).comp (measurable_pi_apply t))) _ ?_
  intro j
  refine piChart_reference_map
    (fun _ : O j => normalizedCoveredReference (R := B j) (n := n j) (euclideanSubspace (U j)) d)
    (fun _ : O j => ν j) (fun _ : O j => q j) (fun _ => hq j) _ ?_
  intro t
  exact normalizedCoveredChart_reference_map _ (b j) (hb j) (bW j) d (ν j) (hΩm j t) (hΩ j t)

theorem coveredJetChart_density_law (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))
    (f : CoveredJetChartSource U O B n d → ℝ)
    (hf : ∀ x ∉ coveredJetSourceRegion U b d Ω, f x = 0) :
    (realDensityMeasure (coveredJetReference U d) f).map (coveredJetChart U b hb bW d) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))
      (restrictedChartDensity (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) 1 f) := by
  apply restrictedChartDensity_law _ (coveredJetChart_continuous U b hb bW d).measurable
    (coveredJetSourceRegion_measurable U b d Ω hΩm)
    (coveredJetChart_embedding U b hb bW d Ω hΩm hΩ) _ _ zero_le_one _ f hf
  simpa only [ENNReal.ofReal_one, one_smul] using
    coveredJetChart_reference_map U b hb bW d ν Ω hΩm hΩ

end VectorPolynomial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPiProduct
namespace OAI

section

namespace Erdos3

open MeasureTheory MeasureTheory.Measure MeasurableSpace

theorem dependentPiProd_measurePreserving {I : Type*} [Fintype I] {X Y : I → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (X i)) (ν : ∀ i, Measure (Y i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (dependentPiProd I X Y) (Measure.pi (fun i => (μ i).prod (ν i)))
      ((Measure.pi μ).prod (Measure.pi ν)) where
  measurable := (dependentPiProd I X Y).measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).prod
        (FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn)) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).isCountablySpanning
      · exact (FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply]
      rw [show (dependentPiProd I X Y) ⁻¹' (Set.univ.pi s ×ˢ Set.univ.pi t) =
          Set.univ.pi (fun i => s i ×ˢ t i) by
        ext x
        simp [dependentPiProd, Set.mem_pi, forall_and]]
      simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Finset.prod_mul_distrib]

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

variable [∀ j, Fintype (B j)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, Fintype (O j)]

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
open scoped Classical

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

end Erdos3.VectorPolynomial

end

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

theorem mixedCoveredJetEquiv_measurePreserving
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))) (d : ℕ) [NeZero d] :
    MeasurePreserving (mixedCoveredJetEquiv (O := O) (B := B) (n := n) U o d)
      (coveredJetArrayReference U d) (coveredJetReference U d) := by
  let c := fun j => (ENNReal.ofReal (ZLattice.covolume
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))))⁻¹
  have hc (j) : c j ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos _ volume)).ne'
  let μ := fun j => c j ^ Fintype.card (O j) • mixedArrayReference (I j) (Fin (n j)) (O j)
  let ν := fun j => (PMF.uniformOfFintype (O j → B j → ZMod d)).toMeasure
  let : ∀ j, SigmaFinite (μ j) := fun j =>
    ennreal_smul_sigmaFinite (mixedArrayReference (I j) (Fin (n j)) (O j)) _
      (ENNReal.pow_ne_top (hc j))
  let : ∀ j, SigmaFinite (normalizedCoveredReference (R := B j) (n := n j)
      (euclideanSubspace (U j)) d) := fun j => normalizedCoveredReference_sigmaFinite _ d
  have h (j) : MeasurePreserving
      (arrayResidueChart (O := O j) (Z := Fin (n j)) (R := B j → ZMod d) (o j))
      ((μ j).prod (ν j)) (Measure.pi (fun _ : O j =>
        normalizedCoveredReference (R := B j) (n := n j) (euclideanSubspace (U j)) d)) := by
    simpa only [μ, ν, normalizedCoveredReference, uniformPMF_toMeasure_pi] using
      arrayResidueChart_measurePreserving (O := O j) (Z := Fin (n j)) (o j)
        (PMF.uniformOfFintype (B j → ZMod d)).toMeasure (c j) (hc j)
  have h₁ := (dependentPiProd_measurePreserving μ ν).symm
    (dependentPiProd (Fin m)
      (fun j => (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
      (fun j => O j → B j → ZMod d))
  have h₂ := measurePreserving_pi (fun j => (μ j).prod (ν j))
    (fun j => Measure.pi (fun _ : O j =>
      normalizedCoveredReference (R := B j) (n := n j) (euclideanSubspace (U j)) d)) h
  change MeasurePreserving _ ((Measure.pi μ).prod
    (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure) (coveredJetReference U d)
  rw [uniformPMF_toMeasure_pi]
  exact h₂.comp h₁

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

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical ENNReal

namespace VectorPolynomial

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set
open scoped Classical BigOperators

variable {m : ℕ} {I O O' E J : Fin m → Type*} {n : Fin m → ℕ}
variable (e : ∀ j, O' j ≃ O j)

variable [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))

variable [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)]

variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

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

end Erdos3.FiniteProbabilityWeights

end

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

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped Classical

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedCoveredDensityMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

theorem coveredJetArray_density_law (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))
    (f : ((∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) → ℝ)
    (hf : ∀ p, mixedCoveredJetCoordinates U o d p ∉ coveredJetSourceRegion U b d Ω → f p = 0) :
    (realDensityMeasure (coveredJetArrayReference U d) f).map
      (fun p => coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d p)) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))
      (restrictedChartDensity (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) 1
        (fun x => f ((mixedCoveredJetEquiv U o d).symm x))) := by
  let e := mixedCoveredJetEquiv (O := O) (B := B) (n := n) U o d
  have he : MeasurePreserving e (coveredJetArrayReference U d) (coveredJetReference U d) :=
    mixedCoveredJetEquiv_measurePreserving U o d
  have hq := (coveredJetChart_continuous (O := O) U b hb bW d).measurable
  change (realDensityMeasure (coveredJetArrayReference U d) f).map
    (coveredJetChart U b hb bW d ∘ e) = _
  rw [← Measure.map_map hq e.measurable, realDensityMeasure_map_equiv, he.map_eq]
  apply coveredJetChart_density_law U b hb bW d ν Ω hΩm hΩ
  intro x hx
  apply hf
  change e (e.symm x) ∉ coveredJetSourceRegion U b d Ω
  simpa only [e.apply_symm_apply] using hx

end Erdos3.VectorPolynomial

end

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
  have h := coveredJetArray_density_law U o b hb bW d ν Ω hΩm hΩ f hf
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

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.mixedCoveredJet_normalized_lintegral.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.mixedCoveredJet_normalized_lintegral.{u_1, u_2, u_3, u_4}
