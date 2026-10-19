-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedWholeMaskedCoveredProfile_measurable_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:08:04.637812+00:00
-- url     : https://prove2.me/submissions/5371712b-d812-4d7d-b045-7d7400894c93

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B217

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem restrictedChartDensity_measurable (q : X → Y) {S : Set X}
    (he : MeasurableEmbedding (fun x : S => q x.val)) (c : ℝ)
    (f : X → ℝ) (hf : Measurable f) :
    Measurable (restrictedChartDensity q S c f) :=
  embeddingDensity_measurable _ he c _ (hf.comp measurable_subtype_coe)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedActualProfileControl
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value

theorem allocatedLongJetRealCoordinates_measurable :
    Measurable (allocatedLongJetRealCoordinates B U basis S (O := O)) := by
  apply measurable_pi_iff.mpr
  intro q
  rcases q with ⟨⟨⟨j, i | i⟩, ha⟩, o⟩
  · exact (measurable_pi_apply o).comp
      (show Measurable (fun z : AllocatedLongJetRows B U basis S O =>
        z ⟨⟨j, .inl i⟩, ha⟩) from measurable_pi_apply _)
  · exact (measurable_of_countable
      (fun z : O j → ℤ => (z o : ℝ) / (basisAxisScale (basis j) i : ℝ))).comp
      (show Measurable (fun z : AllocatedLongJetRows B U basis S O =>
        z ⟨⟨j, .inr i⟩, ha⟩) from measurable_pi_apply _)

variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

theorem allocatedLongJetMask_measurable (a : {a // ¬grid a}) :
    Measurable (allocatedLongJetMask B U basis S x rows modulus residue a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact measurable_const
  · change Measurable (allocatedIntegerKernelMask B U basis S x rows j modulus (residue j))
    exact measurable_of_countable _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedLongIntegralMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

theorem allocatedLongProfileDensity_measurable (f : (output → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (allocatedLongProfileDensity B U b S x rows modulus residue f) := by
  have hm : Measurable (fun z : AllocatedLongJetRows B U b S O =>
      ∏ a, allocatedLongJetMask B U b S x rows modulus residue a (z a)) :=
    Finset.measurable_prod _ (fun a _ =>
      (allocatedLongJetMask_measurable B U b S x rows modulus residue a).comp (measurable_pi_apply a))
  exact (hm.mul (hf.comp (allocatedLongJetRealCoordinates_measurable B U b S))).div_const _

end Erdos3.VectorPolynomial

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
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d Ω

include hΩ in
omit [∀ j, Fintype (O j)] in
theorem mixedCoveredJet_restrictedDensity_eq (f : MixedCoveredJetSource I O E n d → ℝ) :
    restrictedChartDensity chart region 1 f =
      restrictedChartDensity (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) 1
        (fun z => f ((mixedCoveredJetEquiv U o d).symm z)) := by
  symm
  apply restrictedChartDensity_eq_of_values chart region
    (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ)
  · intro z hz
    rw [mixedCoveredJetChart, restrictedChartDensity_apply _ _ _ _
      (coveredJetChart_injOn U b hb bW d Ω hΩ) hz, one_mul]
    exact congrArg f ((mixedCoveredJetEquiv U o d).symm_apply_apply z)
  · intro y hy
    apply restrictedChartDensity_zero
    rwa [← mixedCoveredJetChart_image U o b hb bW d Ω]

include hΩm hΩ in
theorem mixedCoveredJet_restrictedDensity_measurable
    (f : MixedCoveredJetSource I O E n d → ℝ) (hf : Measurable f) :
    Measurable (restrictedChartDensity chart region 1 f) := by
  rw [mixedCoveredJet_restrictedDensity_eq U o b hb bW d Ω hΩ]
  exact restrictedChartDensity_measurable _ (coveredJetChart_embedding U b hb bW d Ω hΩm hΩ)
    1 _ (hf.comp (mixedCoveredJetEquiv U o d).symm.measurable)

end Erdos3.VectorPolynomial

end

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

theorem allocatedGridJetDensity_measurable :
    Measurable (allocatedGridJetDensity B U b hR hσ S x u v rows) := by
  have hr (a : {a // grid a}) : Measurable (allocatedGridJetFactor B U b hR hσ S x u v rows a) := by
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · change Measurable (fun z : O j → ℤ =>
        (integerMatrixImagePMF (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j))
          (allocatedLayerIntegerPMFs B U b hR hσ S j i) z).toReal)
      exact measurable_of_countable _
  exact Finset.measurable_prod _ (fun a _ => (hr a).comp (measurable_pi_apply a))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))

variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "profile" => allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d Ω

include hΩm hΩ in
omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedCoveredProfileDensity_measurable
    (f : AllocatedLongJetRows B U b S O → ℝ) (hf : Measurable f) : Measurable (profile f) := by
  apply mixedCoveredJet_restrictedDensity_measurable U o b hb bW d Ω hΩm hΩ
  have hs : Measurable (fun z : MixedCoveredJetSource I O Q n d => split z.1) :=
    (split).measurable.comp measurable_fst
  have hd : Measurable (coefficientDeckJetDensity root dirs rows d : (∀ j, O j → Q j → ZMod d) → ℝ) :=
    measurable_of_finite _
  change Measurable (fun z : MixedCoveredJetSource I O Q n d =>
    (allocatedGridJetDensity B U b hR hσ S x u v rows ((split z.1).1) *
      coefficientDeckJetDensity root dirs rows d z.2 / coveredJetArrayScale (O := O) U) * f ((split z.1).2))
  exact (((allocatedGridJetDensity_measurable B U b hR hσ S x u v rows).comp
    (measurable_fst.comp hs)).mul (hd.comp measurable_snd)).div_const _ |>.mul (hf.comp (measurable_snd.comp hs))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedProductPrefactorCap
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem allocatedWholeMaskedCoveredProfile_measurable_s2_oai
    (w : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ) (f : ((Σ a : {a // ¬grid a}, O a.val.1) → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d w q f) := by
  apply allocatedCoveredProfileDensity_measurable B U b hR hσ S x
    (principalAxisRestrict grid w) (principalAxisRestrict (fun a => ¬grid a) w) rows hb o bW d
    (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).measurableSet)
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  exact allocatedLongProfileDensity_measurable B U b S x rows q _ f hf

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedWholeMaskedCoveredProfile_measurable_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.allocatedWholeMaskedCoveredProfile_measurable_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
