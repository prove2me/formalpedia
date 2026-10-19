-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalTarget_nativeHaarExpansion_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:37:08.789175+00:00
-- url     : https://prove2.me/submissions/4358d5ac-9fb0-4308-bd60-1970221aacbc

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B216
import Definitions.Def_OAIE3v2B217
import Definitions.Def_OAIE3v2B301

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PhysicalSiteProjection
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

omit [∀ j, Fintype (J j)] in
theorem physicalEuclideanSitePoint_apply (w : X → ℝ) (j : Fin m) (i : J j) :
    (physicalEuclideanSitePoint U p hm w j).val i = eval w (p j) i := by
  change (eval w (restrictCoefficients (U j) (p j) (hm j))).val i = _
  rw [eval_restrictCoefficients]

theorem physicalSingleSiteValue_eq_mk (d : ℕ) (w : X → ℝ) (j : Fin m) :
    physicalSingleSiteValue U d p hm w j () =
      QuotientAddGroup.mk ((d : ℝ)⁻¹ • physicalEuclideanSitePoint U p hm w j) := by
  apply (euclideanSubspaceTorusEquiv (U j)).injective
  change euclideanSubspaceTorusEquiv (U j)
    ((euclideanSubspaceTorusEquiv (U j)).symm _) =
      euclideanSubspaceTorusEquiv (U j) (QuotientAddGroup.mk' _
        ((d : ℝ)⁻¹ • physicalEuclideanSitePoint U p hm w j))
  rw [AddEquiv.apply_symm_apply, euclideanSubspaceTorusEquiv_mk]
  congr 1

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped Classical NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem singleSiteIntegerCover_continuous (d : ℕ) :
    Continuous (singleSiteIntegerCover U d) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro t
  exact (quotientIntegerCover_continuous _ d).comp
    ((continuous_apply t).comp (continuous_apply j))

theorem singleSiteIntegerCover_surjective (d : ℕ) (hd : 0 < d) :
    Function.Surjective (singleSiteIntegerCover U d) := by
  intro y
  choose x hx using fun j t => quotientIntegerCover_surjective
    (latticeSection (standardEuclideanLattice (J j))
      (euclideanSubspace (U j))).toAddSubgroup d hd (y j t)
  exact ⟨x, funext fun j => funext fun t => hx j t⟩

theorem coveredJetAmbientTorus_singleSiteIntegerCover (d : ℕ)
    (y : EuclideanJetLayers U (fun _ => Unit)) :
    coveredJetAmbientTorus U 1 (singleSiteIntegerCover U d y) =
      coveredJetAmbientTorus U d y := by
  ext a
  simp only [coveredJetAmbientTorus, singleSiteIntegerCover, AddMonoidHom.coe_mk,
    quotientIntegerCover, nsmulAddMonoidHom_apply, one_nsmul]
  rfl

theorem physicalSingleSiteValue_product_projection
    {X : Type*} (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (a d : ℕ) (ha : 0 < a) (u : X → ℝ) :
    singleSiteIntegerCover U a (physicalSingleSiteValue U (a * d) poly hm u) =
      physicalSingleSiteValue U d poly hm u := by
  have ha0 : (a : ℝ) ≠ 0 := (Nat.cast_pos.mpr ha).ne'
  ext j t
  cases t
  change quotientIntegerCover _ a (physicalSingleSiteValue U (a * d) poly hm u j ()) = _
  rw [physicalSingleSiteValue_eq_mk, physicalSingleSiteValue_eq_mk]
  change quotientIntegerCover _ a (QuotientAddGroup.mk' _ _) = QuotientAddGroup.mk' _ _
  rw [quotientIntegerCover_mk, smul_smul, Nat.cast_mul, mul_inv_rev]
  congr 1
  congr 1
  calc
    (a : ℝ) * ((d : ℝ)⁻¹ * (a : ℝ)⁻¹) =
        (d : ℝ)⁻¹ * ((a : ℝ) * (a : ℝ)⁻¹) := by ring
    _ = (d : ℝ)⁻¹ := by rw [mul_inv_cancel₀ ha0, mul_one]

theorem physicalSingleSiteValue_divisor_projection
    {X : Type*} (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (Q d : ℕ) (hQ : 0 < Q) (hd : d ∣ Q) (u : X → ℝ) :
    singleSiteIntegerCover U (Q / d) (physicalSingleSiteValue U Q poly hm u) =
      physicalSingleSiteValue U d poly hm u := by
  have hdpos := Nat.pos_of_dvd_of_pos hd hQ
  have ha : 0 < Q / d := Nat.div_pos (Nat.le_of_dvd hQ hd) hdpos
  simpa only [Nat.div_mul_cancel hd] using
    physicalSingleSiteValue_product_projection U poly hm (Q / d) d ha u

theorem physicalSingleSiteValue_gridFactorInput
    {X : Type*} (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (d : ℕ) (u : X → ℝ) :
    (fun a : Σ j, J j => coveredJetAmbientTorus U 1
      (physicalSingleSiteValue U d poly hm u) ⟨a.1, (), a.2⟩) =
      physicalGridFactorInput d poly u := by
  funext a
  change subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1)
    (1 • (euclideanSubspaceTorusEquiv (U a.1)).symm
      (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U a.1))
        (fun _ => (d : ℝ)⁻¹ • eval u
          (restrictCoefficients (U a.1) (poly a.1) (hm a.1)))))) a.2 = _
  rw [one_nsmul, AddEquiv.apply_symm_apply, subspaceAmbientTorus_mk]
  simp only [Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, eval_restrictCoefficients,
    physicalGridFactorInput, div_eq_mul_inv, mul_comm]

theorem physicalSingleSiteValue_commonCover_gridFactorInput
    {X : Type*} (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (Q d : ℕ) (hQ : 0 < Q) (hd : d ∣ Q) (u : X → ℝ) :
    (fun a : Σ j, J j => coveredJetAmbientTorus U (Q / d)
      (physicalSingleSiteValue U Q poly hm u) ⟨a.1, (), a.2⟩) =
      physicalGridFactorInput d poly u := by
  rw [← coveredJetAmbientTorus_singleSiteIntegerCover,
    physicalSingleSiteValue_divisor_projection U poly hm Q d hQ hd]
  exact physicalSingleSiteValue_gridFactorInput U poly hm d u

variable [CompactSpace (EuclideanJetLayers U (fun _ => Unit))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))

theorem singleSiteIntegerCover_measurePreserving (d : ℕ) (hd : 0 < d) :
    MeasurePreserving (singleSiteIntegerCover U d) haar haar := by
  let : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : Unit => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  let : IsProbabilityMeasure haar := Measure.pi.instIsProbabilityMeasure _
  let : ∀ j, (Measure.pi (fun _ : Unit => ν j)).IsAddLeftInvariant :=
    fun _ => Measure.pi.isAddLeftInvariant _
  let : Measure.IsAddLeftInvariant haar := Measure.pi.isAddLeftInvariant _
  let : Measure.IsAddHaarMeasure haar :=
    { toIsFiniteMeasureOnCompacts := ⟨fun s _ =>
        (measure_mono (Set.subset_univ s)).trans_lt (by simp)⟩
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := haar) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving (singleSiteIntegerCover_continuous U d)
    (singleSiteIntegerCover_surjective U d hd) rfl

theorem singleSiteIntegerCover_integral (d : ℕ) (hd : 0 < d)
    (f : EuclideanJetLayers U (fun _ => Unit) → ℂ)
    (hf : AEStronglyMeasurable f haar) :
    (∫ y, f (singleSiteIntegerCover U d y) ∂haar) = ∫ y, f y ∂haar := by
  have hp := singleSiteIntegerCover_measurePreserving U ν d hd
  have hf' : AEStronglyMeasurable f (Measure.map (singleSiteIntegerCover U d) haar) := by
    rwa [hp.map_eq]
  simpa only [hp.map_eq] using (integral_map hp.measurable.aemeasurable hf').symm

namespace NormalizedPolynomialTwist

variable {X : Type*} [Fintype X] {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem frozenSingleSiteHaarReference_commonCover
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ)
    (Q : ℕ) (hQ : 0 < Q) (hcover : W.cover ∣ Q) :
    (∫ y, W.frozenTorus residue center
      (fun a => coveredJetAmbientTorus U (Q / W.cover) y ⟨a.1, (), a.2⟩) ∂haar) =
      W.frozenSingleSiteHaarReference U ν residue center := by
  have hd : 0 < Q / W.cover := Nat.div_pos (Nat.le_of_dvd hQ hcover) W.cover_pos
  have h := singleSiteIntegerCover_integral U ν (Q / W.cover) hd
    (fun y => W.frozenTorus residue center
      (fun a => coveredJetAmbientTorus U 1 y ⟨a.1, (), a.2⟩))
    (W.frozenSingleSiteHaarReference_integrable U ν residue center).aestronglyMeasurable
  simpa only [coveredJetAmbientTorus_singleSiteIntegerCover, frozenSingleSiteHaarReference]
    using h

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ConstantPolynomialSingleSiteRealization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped Classical NNReal

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem exists_constantPolynomial_singleSiteValue
    (Q : ℕ) (hQ : 0 < Q) (y : EuclideanJetLayers U (fun _ => Unit)) :
    ∃ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j e, coefficients (poly j) e ∈ U j),
      (∀ j, DegreeLE (1 : X → ℕ) 0 (poly j)) ∧
      ∀ u : X → ℝ, physicalSingleSiteValue U Q poly hm u = y := by
  have hQ0 : (Q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hQ).ne'
  choose x hx using fun j => QuotientAddGroup.mk'_surjective
    (latticeSection (standardEuclideanLattice (J j))
      (euclideanSubspace (U j))).toAddSubgroup (y j ())
  let c : ∀ j, U j := fun j => (Q : ℝ) • euclideanSubspaceArrayEquiv (U j) (x j) ()
  let poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ) := fun j => monomial 0 (c j).val
  have hm : ∀ j e, coefficients (poly j) e ∈ U j := by
    intro j e
    by_cases he : e = 0
    · subst e
      simp [poly]
    · simp [poly, Ne.symm he]
  refine ⟨poly, hm, ?_, ?_⟩
  · intro j e he
    have he0 : e ≠ 0 := by
      intro h
      simp [h] at he
    simp [poly, Ne.symm he0]
  · intro u
    funext j t
    cases t
    rw [physicalSingleSiteValue_eq_mk]
    have hpoint : physicalEuclideanSitePoint U poly hm u j = (Q : ℝ) • x j := by
      apply Subtype.ext
      ext i
      rw [physicalEuclideanSitePoint_apply]
      simp [poly, c, euclideanSubspaceArrayEquiv_apply]
    rw [hpoint, smul_smul, inv_mul_cancel₀ hQ0, one_smul]
    exact hx j

namespace NormalizedPolynomialTwist

variable [Fintype X] {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem eval_commonCover
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (Q : ℕ) (hQ : 0 < Q) (hcover : W.cover ∣ Q) (u : X → ℤ) :
    W.eval N poly u = W.frozenTorus (fun i => (u i : ZMod W.modulus))
      (fun i => (u i : ℝ) / N i)
      (fun a => coveredJetAmbientTorus U (Q / W.cover)
        (physicalSingleSiteValue U Q poly hm (fun i => (u i : ℝ))) ⟨a.1, (), a.2⟩) := by
  rw [physicalSingleSiteValue_commonCover_gridFactorInput U poly hm Q W.cover hQ hcover]
  rfl

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePhysicalHaarExpansion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {X : Type*} [Fintype X] {pw cw : ℝ} {Lw : ℝ≥0}

theorem nativeSingleSiteCoverObservable_continuous
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (physicalN : X → ℕ) (u : X → ℤ) (Q : ℕ) :
    Continuous (nativeSingleSiteCoverObservable U W physicalN u Q) := by
  apply (W.frozenTorus_lipschitz _ _).continuous.comp
  apply continuous_pi
  intro a
  exact (continuous_apply (⟨a.1, (), a.2⟩ : JetAmbientIndex (fun _ => Unit) J)).comp
    (coveredJetAmbientTorus_continuous U (Q / W.cover))

theorem norm_nativeSingleSiteCoverObservable_le
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (physicalN : X → ℕ) (u : X → ℤ) (Q : ℕ)
    (y : EuclideanJetLayers U (fun _ => Unit)) :
    ‖nativeSingleSiteCoverObservable U W physicalN u Q y‖ ≤ 1 :=
  W.norm_frozenTorus_le _ _ _

theorem nativeSingleSiteCoverObservable_physical
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (physicalN : X → ℕ) (u : X → ℤ) (Q : ℕ) (hQ : 0 < Q) (hd : W.cover ∣ Q)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j) :
    nativeSingleSiteCoverObservable U W physicalN u Q
      (physicalSingleSiteValue U Q poly hm (fun i => (u i : ℝ))) = W.eval physicalN poly u :=
  (W.eval_commonCover U physicalN poly hm Q hQ hd u).symm

theorem nativeSingleSiteCoverObservable_projection
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (physicalN : X → ℕ) (u : X → ℤ) (N Q : ℕ) (hN : 0 < N) (hQ : 0 < Q)
    (hNQ : N ∣ Q) (hWN : W.cover ∣ N)
    (y : EuclideanJetLayers U (fun _ => Unit)) :
    nativeSingleSiteCoverObservable U W physicalN u N (singleSiteIntegerCover U (Q / N) y) =
      nativeSingleSiteCoverObservable U W physicalN u Q y := by
  obtain ⟨poly, hm, _, hy⟩ := exists_constantPolynomial_singleSiteValue (X := X) U Q hQ y
  rw [← hy (fun i => (u i : ℝ)), physicalSingleSiteValue_divisor_projection U poly hm Q N hQ hNQ,
    nativeSingleSiteCoverObservable_physical U W physicalN u N hN hWN,
    nativeSingleSiteCoverObservable_physical U W physicalN u Q hQ (hWN.trans hNQ)]

variable [CompactSpace (EuclideanJetLayers U (fun _ => Unit))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))

theorem nativePhysicalHaarExpansion
    {T : Type*} [Fintype T] {pf cf : ℝ} {Lf : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (F : T → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
    (c : T → ℂ) (κ : ℂ) (δ : ℝ)
    (physicalN : X → ℕ) (u : X → ℤ) (N : ℕ) (hN : 0 < N) (hWN : W.cover ∣ N)
    (f : EuclideanJetLayers U (fun _ => Unit) → ℂ) (hf : Measurable f)
    (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j e, coefficients (poly j) e ∈ U j),
      ‖κ * f (physicalSingleSiteValue U N poly hm (fun i => (u i : ℝ))) -
        ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ) :
    ‖(∫ y, κ * f y * nativeSingleSiteCoverObservable U W physicalN u N y ∂haar) -
      ∑ i, c i * (W.product (F i)).frozenSingleSiteHaarReference U ν
        (fun j => (u j : ZMod (W.product (F i)).modulus))
        (fun j => (u j : ℝ) / physicalN j)‖ ≤ δ := by
  have : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : Unit => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  have : IsProbabilityMeasure haar := Measure.pi.instIsProbabilityMeasure _
  let Q := N * ∏ i, (W.product (F i)).cover
  have hQ : 0 < Q := Nat.mul_pos hN (Finset.prod_pos fun i _ => (W.product (F i)).cover_pos)
  have hNQ : N ∣ Q := dvd_mul_right _ _
  have hprod (i : T) : (W.product (F i)).cover ∣ Q :=
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) N
  have hF (i : T) : (F i).cover ∣ Q :=
    (dvd_mul_left (F i).cover W.cover).trans (hprod i)
  let projection := singleSiteIntegerCover U (Q / N)
  let left := fun y => κ * f (projection y) * nativeSingleSiteCoverObservable U W physicalN u Q y
  let right := fun y => ∑ i, c i * nativeSingleSiteCoverObservable U (W.product (F i)) physicalN u Q y
  have herr (y) : ‖left y - right y‖ ≤ δ := by
    obtain ⟨poly, hm, _, hy⟩ := exists_constantPolynomial_singleSiteValue (X := X) U Q hQ y
    have ha := happrox poly hm
    have hw := W.norm_eval_le physicalN poly u
    have hfactor : left y - right y = W.eval physicalN poly u *
        (κ * f (physicalSingleSiteValue U N poly hm (fun i => (u i : ℝ))) -
          ∑ i, c i * (F i).eval physicalN poly u) := by
      dsimp [left, right, projection]
      rw [← hy (fun i => (u i : ℝ)),
        physicalSingleSiteValue_divisor_projection U poly hm Q N hQ hNQ,
        nativeSingleSiteCoverObservable_physical U W physicalN u Q hQ (hWN.trans hNQ)]
      simp_rw [nativeSingleSiteCoverObservable_physical U (W.product _) physicalN u Q hQ (hprod _),
        NormalizedPolynomialTwist.product_eval]
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro i _
        ring
    rw [hfactor, norm_mul]
    exact (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans (by simpa using ha)
  have hrightInt : Integrable right haar := by
    apply integrable_finsetSum
    intro i _
    apply Integrable.const_mul
    apply Integrable.of_bound
      (nativeSingleSiteCoverObservable_continuous U (W.product (F i)) physicalN u Q).aestronglyMeasurable 1
    exact ae_of_all _ fun y => norm_nativeSingleSiteCoverObservable_le U _ physicalN u Q y
  have hrightBound (y) : ‖right y‖ ≤ ∑ i, ‖c i‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (norm_nativeSingleSiteCoverObservable_le U _ physicalN u Q y)
      (norm_nonneg _)).trans_eq (mul_one _)
  have hleftMeas : Measurable left :=
    (measurable_const.mul (hf.comp (singleSiteIntegerCover_continuous U (Q / N)).measurable)).mul
      (nativeSingleSiteCoverObservable_continuous U W physicalN u Q).measurable
  have hleftInt : Integrable left haar := by
    apply Integrable.of_bound hleftMeas.aestronglyMeasurable (δ + ∑ i, ‖c i‖)
    apply ae_of_all
    intro y
    calc
      ‖left y‖ ≤ ‖left y - right y‖ + ‖right y‖ := norm_le_norm_sub_add _ _
      _ ≤ δ + ∑ i, ‖c i‖ := add_le_add (herr y) (hrightBound y)
  have hcomparison := probability_integral_approximation haar left right hleftInt hrightInt herr
  have hleft : (∫ y, left y ∂haar) =
      ∫ y, κ * f y * nativeSingleSiteCoverObservable U W physicalN u N y ∂haar := by
    have he (y) : left y =
        (fun z => κ * f z * nativeSingleSiteCoverObservable U W physicalN u N z) (projection y) := by
      dsimp [left, projection]
      rw [nativeSingleSiteCoverObservable_projection U W physicalN u N Q hN hQ hNQ hWN]
    simp_rw [he]
    exact singleSiteIntegerCover_integral U ν (Q / N) (Nat.div_pos (Nat.le_of_dvd hQ hNQ) hN) _
      ((measurable_const.mul hf).mul
        (nativeSingleSiteCoverObservable_continuous U W physicalN u N).measurable).aestronglyMeasurable
  have hright : (∫ y, right y ∂haar) =
      ∑ i, c i * (W.product (F i)).frozenSingleSiteHaarReference U ν
        (fun j => (u j : ZMod (W.product (F i)).modulus))
        (fun j => (u j : ℝ) / physicalN j) := by
    rw [show (∫ y, right y ∂haar) = ∑ i, ∫ y,
      c i * nativeSingleSiteCoverObservable U (W.product (F i)) physicalN u Q y ∂haar from
      integral_finsetSum _ (fun i _ => by
        apply Integrable.const_mul
        apply Integrable.of_bound
          (nativeSingleSiteCoverObservable_continuous U (W.product (F i)) physicalN u Q).aestronglyMeasurable 1
        exact ae_of_all _ fun y => norm_nativeSingleSiteCoverObservable_le U _ physicalN u Q y)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul]
    congr 1
    exact (W.product (F i)).frozenSingleSiteHaarReference_commonCover U ν _ _ Q hQ (hprod i)
  rwa [hleft, hright] at hcomparison

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawPhysicalAmbientHaarComparison
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
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))

variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]

include hcompact

theorem forecastLawDensityPhysicalTarget_nativeHaarExpansion_s2_oai
    (hdensity : Measurable density)
    {T : Type*} [Fintype T] {pw cw pf cf : ℝ} {Lw Lf : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (F : T → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
    (c : T → ℂ) (κ : ℂ) (δ : ℝ) (hWN : W.cover ∣ N)
    (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j e, coefficients (poly j) e ∈ U j) (u : X → ℤ),
      ‖κ * forecastLawDensityPhysicalTarget B U basis S law density selected sample x
        active Y N volume base physicalN τ o hb bW poly hm u -
          ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ)
    (u : X → ℤ) :
    ‖(∫ y, κ * restrictedComplexChartDensity chart region 1 (chartSource u) y *
        nativeSingleSiteCoverObservable U W physicalN u N y ∂haar) -
      ∑ i, c i * (W.product (F i)).frozenSingleSiteHaarReference U ν
        (fun j => (u j : ZMod (W.product (F i)).modulus))
        (fun j => (u j : ℝ) / physicalN j)‖ ≤ δ := by
  let : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit)) := hcompact
  apply nativePhysicalHaarExpansion (X := X) (m := m) (J := J) U ν W F c κ δ physicalN u N
    (Nat.pos_of_ne_zero (NeZero.ne N)) hWN
  · apply mixedCoveredJet_restrictedComplexDensity_measurable U o basis hb bW N
      (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
      (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).isClosed.measurableSet)
    exact forecastLawDensityPhysicalChartSource_measurable B U basis S law density selected sample x
      active Y N volume base physicalN τ hdensity u
  · intro poly hm
    exact happrox poly hm u

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9} : type_of% @OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalTarget_nativeHaarExpansion_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9} := @OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalTarget_nativeHaarExpansion_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9}
