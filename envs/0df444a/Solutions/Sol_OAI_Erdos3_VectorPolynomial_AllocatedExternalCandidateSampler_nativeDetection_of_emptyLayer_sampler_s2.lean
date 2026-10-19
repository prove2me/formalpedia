-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.nativeDetection_of_emptyLayer_sampler_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:27:21.513978+00:00
-- url     : https://prove2.me/submissions/20d8cb42-4f3d-419b-85a1-ac34987e4190

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B272

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.EmptyCoefficientDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped BigOperators

theorem canonicalMixedDensity_empty
    {D I : Type*} [Fintype D] [Fintype I] [IsEmpty D] [IsEmpty I]
    {n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (o : OrthonormalBasis I ℝ W)
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (c w : I → ℝ) (p : Fin n → PMF ℤ)
    (y : W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) :
    canonicalMixedDensity W b hb o c w p y = 1 := by
  let Q := W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
  let : Subsingleton Q := ⟨by
    intro x y
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact congrArg QuotientAddGroup.mk (Subsingleton.elim x y)⟩
  let μ : Measure Q := probabilityAddHaar Q
  let : IsProbabilityMeasure μ := probabilityAddHaar_probability Q
  let : μ.IsAddLeftInvariant := probabilityAddHaar_invariant Q
  have hmass := (canonicalMixedDensity_mass W b hb o μ c w
    (fun i => isEmptyElim i) p (fun _ _ i => isEmptyElim i)).2
  have hconst : canonicalMixedDensity W b hb o c w p =
      fun _ => canonicalMixedDensity W b hb o c w p y := by
    funext z
    exact congrArg (canonicalMixedDensity W b hb o c w p) (Subsingleton.elim z y)
  rw [hconst] at hmass
  simpa using hmass

namespace VectorPolynomial

theorem canonicalCoefficientDensity_empty
    {K : Type*} [Fintype K] {m : ℕ}
    {J I : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
    [∀ j, IsEmpty (J j)] [∀ j, IsEmpty (I j)]
    {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (c w : ∀ j, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (y : CoefficientTorus (K := K) U) :
    canonicalCoefficientDensity U b hb o c w p y = 1 := by
  unfold canonicalCoefficientDensity
  apply Finset.prod_eq_one
  intro j _
  unfold canonicalArrayDensity
  apply Finset.prod_eq_one
  intro e _
  exact canonicalMixedDensity_empty _ (b j) (hb j) (o j) _ _ _ _

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SampledCommonBox
namespace OAI

section

namespace Erdos3

theorem commonStrideBox_map_coordinateEquiv {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (c : X → ℤ) (m : ℕ) (H : X → ℕ) :
    (commonStrideBox c m H).map (integerPointCoordinateEquiv e).toEmbedding =
      commonStrideBox (integerPointCoordinateEquiv e c) m
        (coordinateReindexedSides e H) := by
  classical
  ext y
  rw [Finset.mem_map_equiv]
  simp only [commonStrideBox, Fintype.mem_piFinset]
  change (∀ i, y (e i) ∈ integerProgressionSupport (c i) m (H i)) ↔
    ∀ j, y j ∈ integerProgressionSupport (c (e.symm j)) m (H (e.symm j))
  constructor
  · intro h j
    simpa only [Equiv.apply_symm_apply] using h (e.symm j)
  · intro h i
    simpa only [Equiv.symm_apply_apply] using h (e i)

theorem commonStrideBox_image_coordinateEquiv {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (c : X → ℤ) (m : ℕ) (H : X → ℕ) :
    (commonStrideBox c m H).image (integerPointCoordinateEquiv e) =
      commonStrideBox (integerPointCoordinateEquiv e c) m
        (coordinateReindexedSides e H) := by
  simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using
    commonStrideBox_map_coordinateEquiv e c m H

theorem IsDenseCommonStrideBox.coordinateEquiv {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) {N : X → ℕ} {p : ℝ} {A : Finset (X → ℤ)}
    (h : IsDenseCommonStrideBox N p A) :
    IsDenseCommonStrideBox (coordinateReindexedSides e N) p
      (A.image (integerPointCoordinateEquiv e)) := by
  obtain ⟨c, m, H, hm, hH, hsub, hdense, rfl⟩ := h
  refine ⟨integerPointCoordinateEquiv e c, m, coordinateReindexedSides e H,
    hm, fun j => hH (e.symm j), fun j => hsub (e.symm j),
    fun j => hdense (e.symm j), commonStrideBox_image_coordinateEquiv e c m H⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I J : Fin m → Type*} {n : Fin m → ℕ}
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (Fin (n j))]
    (B : LayerSamplerAxis I n → Type*)

variable [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}

variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedExternalCandidateSides_empty_layers_fun :
    allocatedExternalCandidateSides B U b S =
      fun _ : LayerSamplerVariables G I n B => S.value :=
  funext (allocatedExternalCandidateSides_empty_layers B U b S)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledNativeDetectionEmptyTags
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

theorem SampledSliceNativeDetection.retag_of_isEmpty
    {m m' : ℕ} {X Ω T : Type} [Fintype X] [DecidableEq X] [Fintype Ω] [Fintype T]
    {Tests : Ω → Type} (J : Fin m → Type) [∀ j, Fintype (J j)]
    [IsEmpty (Σ j, J j)] (J' : Fin m' → Type) [∀ j, Fintype (J' j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (poly' : ∀ j, VectorPolynomial X ℝ (J' j → ℝ))
    (pathLaw : FiniteProbabilityWeights Ω) (physical : Ω → T → X → ℤ)
    (slices : ∀ z, Tests z → Finset T) (weight : ∀ z, Tests z → T → ℂ)
    (degree : ℕ) (pNative α : ℝ)
    (h : SampledSliceNativeDetection J N hbox poly pathLaw physical slices weight
      degree pNative α) :
    SampledSliceNativeDetection J' N hbox poly' pathLaw physical slices weight
      degree pNative α := by
  intro signal hsignal hsupp hlarge
  obtain ⟨W, g, hmodel, hcorr⟩ := h signal hsignal hsupp hlarge
  refine ⟨W.eraseEmptyTags (Σ j, J' j), g, hmodel, ?_⟩
  simpa only [W.eval_eraseEmptyTags N poly poly'] using hcorr

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarReferenceNativeDetectionCoordinateEquiv
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

private theorem normalizedSliceTest_equiv
    {T T' : Type*} [Fintype T] [Fintype T']
    (e : T ≃ T') (S : Finset T) (w : T → ℂ) (t : T) :
    normalizedSliceTest (S.map e.toEmbedding) (fun u => w (e.symm u)) (e t) =
      normalizedSliceTest S w t := by
  simp [normalizedSliceTest, Fintype.card_congr e]

private theorem sampledSingleSliceSeminorm_equiv
    {T T' X : Type*} [Fintype T] [Fintype T']
    (e : T ≃ T') (F : T → X) (S : Finset T) (w : T → ℂ) :
    sampledSingleTestSeminorm (fun u => F (e.symm u))
      (normalizedSliceTest (S.map e.toEmbedding) (fun u => w (e.symm u))) =
    sampledSingleTestSeminorm F (normalizedSliceTest S w) := by
  ext v
  change ‖𝔼 u : T', v (F (e.symm u)) *
    normalizedSliceTest (S.map e.toEmbedding) (fun t => w (e.symm t)) u‖ =
      ‖𝔼 t : T, v (F t) * normalizedSliceTest S w t‖
  congr 1
  symm
  apply Fintype.expect_equiv e
  intro t
  rw [e.symm_apply_apply, normalizedSliceTest_equiv]

theorem sampledSliceSeminorm_coordinateEquiv
    {Ω Ω' T T' X : Type*} [Fintype Ω] [Fintype Ω'] [Fintype T] [Fintype T']
    (e : Ω ≃ Ω') (d : T ≃ T')
    (p : FiniteProbabilityWeights Ω) (p' : FiniteProbabilityWeights Ω')
    (hweight : ∀ z, p'.weight (e z) = p.weight z)
    {Tests : Ω → Type*} (F : Ω → T → X)
    (S : ∀ z, Tests z → Finset T) (w : ∀ z, Tests z → T → ℂ) :
    sampledSliceSeminorm p' (fun z t => F (e.symm z) (d.symm t))
      (fun z (j : Tests (e.symm z)) => (S (e.symm z) j).map d.toEmbedding)
      (fun z j t => w (e.symm z) j (d.symm t)) =
    sampledSliceSeminorm p F S w := by
  ext v
  change p'.mean (fun z =>
    (⨆ j : Tests (e.symm z), sampledSingleTestSeminorm
      (fun t => F (e.symm z) (d.symm t))
      (normalizedSliceTest ((S (e.symm z) j).map d.toEmbedding)
        (fun t => w (e.symm z) j (d.symm t)))) v) =
    p.mean (fun z => (⨆ j : Tests z, sampledSingleTestSeminorm (F z)
      (normalizedSliceTest (S z j) (w z j))) v)
  simp_rw [sampledSingleSliceSeminorm_equiv]
  unfold FiniteProbabilityWeights.mean
  symm
  apply Fintype.sum_equiv e
  intro z
  rw [hweight]
  exact congrArg (fun z' => p.weight z *
    (⨆ j : Tests z', sampledSingleTestSeminorm (F z')
      (normalizedSliceTest (S z' j) (w z' j))) v) (e.symm_apply_apply z).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {K K' X : Type*}

variable [Fintype K] [Fintype K'] [Fintype X]

namespace BooleanCubeKernel

omit [Fintype X] in

theorem jointIntegerPhysicalSite_scalarNoiseIndexEquiv (e : K ≃ K')
    (root : K → ℤ) (a : X → ℤ) (z : Option K × X → ℤ) :
    jointIntegerPhysicalSite (fun k' => root (e.symm k'))
        (a, fun j => z ((scalarNoiseIndexEquiv e).symm j)) =
      jointIntegerPhysicalSite root (a, z) := by
  funext x
  simp only [jointIntegerPhysicalSite, Pi.add_apply, integerPhysicalSite,
    scalarNoiseIndexEquiv_symm, scalarNoiseIndexEquiv_none, scalarNoiseIndexEquiv_some]
  congr 2
  exact e.symm.sum_comp (fun k => root k * z (some k, x))

theorem jointIntegerPhysicalSite_scalarJointPathEquiv (e : K ≃ K')
    (B τ : ℝ) (N : X → ℕ) (A : Finset (X → ℤ)) (root : K → ℤ)
    (z : A × rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1) :
    jointIntegerPhysicalSite (fun k' => root (e.symm k'))
        ((scalarJointPathEquiv e B τ N A z).1.val,
          (scalarJointPathEquiv e B τ N A z).2.val) =
      jointIntegerPhysicalSite root (z.1.val, z.2.val) :=
  jointIntegerPhysicalSite_scalarNoiseIndexEquiv e root z.1.val z.2.val

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {K K' X : Type*} [Fintype K] [Fintype K'] [Fintype X]
    (e : K ≃ K') (B τ : ℝ) (N : X → ℕ)

local notation "W" => trimmedSpatialWidths (K := K) B τ N
local notation "W'" => trimmedSpatialWidths (K := K') B τ N

variable (hW : ∀ i : Option K × X, 0 < trimmedSpatialWidths B τ N i)
    (hW' : ∀ i : Option K' × X, 0 < trimmedSpatialWidths B τ N i)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := K) B τ N) z)
    (hZ' : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := K') B τ N) z)

include hW hW' hZ hZ'

theorem selectedResidueFiniteLaw_scalarCoordinateEquiv_weight
    (z : rectangularWeightIndices 0 W 1) :
    (selectedResidueFiniteLaw (fun _ : X => 1) {0} W' hW' hZ').weight
        (scalarNoiseSupportEquiv e B τ N z) =
      (selectedResidueFiniteLaw (fun _ : X => 1) {0} W hW hZ).weight z := by
  change selectedResidueSmoothWeight (fun _ : X => 1) {0} W'
      (scalarNoiseSupportEquiv e B τ N z).val /
      (∑' y, selectedResidueSmoothWeight (fun _ : X => 1) {0} W' y) =
    selectedResidueSmoothWeight (fun _ : X => 1) {0} W z.val /
      (∑' y, selectedResidueSmoothWeight (fun _ : X => 1) {0} W y)
  exact congrArg₂ (fun a b : ℝ => a / b)
    (selectedResidueSmoothWeight_one_reindex (scalarNoiseIndexEquiv e) W W'
      (trimmedSpatialWidths_scalarNoiseIndexEquiv e B τ N) z.val)
    (selectedResidueSmoothMass_scalarCoordinateEquiv e B τ N)

variable {Y : Type*} (A : Finset Y) (hA : A.Nonempty)

theorem selectedJointReference_scalarCoordinateEquiv_weight
    (z : A × rectangularWeightIndices 0 W 1) :
    (selectedJointReference A hA (fun _ : X => 1) {0} W' hW' hZ').weight
        (scalarJointPathEquiv e B τ N A z) =
      (selectedJointReference A hA (fun _ : X => 1) {0} W hW hZ).weight z := by
  change (FiniteProbabilityWeights.uniformFinset A hA).weight z.1 *
      (selectedResidueFiniteLaw (fun _ : X => 1) {0} W' hW' hZ').weight
        (scalarNoiseSupportEquiv e B τ N z.2) =
    (FiniteProbabilityWeights.uniformFinset A hA).weight z.1 *
      (selectedResidueFiniteLaw (fun _ : X => 1) {0} W hW hZ).weight z.2
  rw [selectedResidueFiniteLaw_scalarCoordinateEquiv_weight e B τ N hW hW' hZ hZ']

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

private theorem niltestSliceSeminorm_coordinateEquiv
    {degree : ℕ} {X K K' Ω Ω' : Type}
    [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K']
    [Fintype Ω] [Fintype Ω']
    (e : K ≃ K') (ep : Ω ≃ Ω') (sides : K → ℕ)
    (law : FiniteProbabilityWeights Ω) (law' : FiniteProbabilityWeights Ω')
    (hweight : ∀ z, law'.weight (ep z) = law.weight z)
    (physical : Ω → integerBox sides → X)
    {Tests : Ω → Type}
    {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)]
    [∀ z j, LieAlgebra ℚ (Ldetect z j)] {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
    (D : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) degree (dims z j))
    (V : ∀ z j, (D z j).Niltest (fun _ : K => 1))
    (slices : ∀ z, Tests z → Finset (integerBox sides))
    (origin : ∀ z, Tests z → K → ℤ) (step : ∀ z, Tests z → ℕ) :
    sampledSliceSeminorm law'
      (fun z t => physical (ep.symm z) ((integerBoxCoordinateEquiv e sides).symm t))
      (fun z (j : Tests (ep.symm z)) =>
        (slices (ep.symm z) j).map (integerBoxCoordinateEquiv e sides).toEmbedding)
      (fun z j t => star (((V (ep.symm z) j).coordinateEquiv e).eval
        (commonStrideIndex (integerPointCoordinateEquiv e (origin (ep.symm z) j))
          (step (ep.symm z) j) t.val))) =
    sampledSliceSeminorm law physical slices
      (fun z j t => star ((V z j).eval (commonStrideIndex (origin z j) (step z j) t.val))) := by
  have hcoord (z : Ω') (j : Tests (ep.symm z))
      (t : integerBox (coordinateReindexedSides e sides)) :
      ((V (ep.symm z) j).coordinateEquiv e).eval
        (commonStrideIndex (integerPointCoordinateEquiv e (origin (ep.symm z) j))
          (step (ep.symm z) j) t.val) =
      (V (ep.symm z) j).eval
        (commonStrideIndex (origin (ep.symm z) j) (step (ep.symm z) j)
          ((integerBoxCoordinateEquiv e sides).symm t).val) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_coordinateEquiv]
    congr 1
    funext k
    simp only [commonStrideIndex, integerPointCoordinateEquiv_apply,
      Equiv.symm_apply_apply, integerBoxCoordinateEquiv_symm_val,
      integerPointCoordinateEquiv_symm_apply]
  simp_rw [hcoord]
  exact sampledSliceSeminorm_coordinateEquiv ep (integerBoxCoordinateEquiv e sides)
    law law' hweight physical slices
    (fun z j t => star ((V z j).eval (commonStrideIndex (origin z j) (step z j) t.val)))

theorem OrdinarySliceNativeDetection.coordinateReturn
    {m degree : ℕ} {X K K' Ω Ω' : Type}
    [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]
    [Fintype K'] [DecidableEq K'] [Fintype Ω] [Fintype Ω']
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (e : K ≃ K') (ep : Ω ≃ Ω') (sides : K → ℕ)
    (law : FiniteProbabilityWeights Ω) (law' : FiniteProbabilityWeights Ω')
    (hweight : ∀ z, law'.weight (ep z) = law.weight z)
    (physical : Ω → integerBox sides → X → ℤ)
    (physical' : Ω' → integerBox (coordinateReindexedSides e sides) → X → ℤ)
    (hphysical : ∀ z t, physical' (ep z) (integerBoxCoordinateEquiv e sides t) = physical z t)
    (pSlice pTest pNative α : ℝ)
    (h : OrdinarySliceNativeDetection (degree := degree) J N hbox poly
      (coordinateReindexedSides e sides) law' physical' pSlice pTest pNative α) :
    OrdinarySliceNativeDetection (degree := degree) J N hbox poly
      sides law physical pSlice pTest pNative α := by
  have hphys : physical' = fun z t =>
      physical (ep.symm z) ((integerBoxCoordinateEquiv e sides).symm t) := by
    funext z t
    simpa only [Equiv.apply_symm_apply] using
      hphysical (ep.symm z) ((integerBoxCoordinateEquiv e sides).symm t)
  subst physical'
  intro Tests _ Ldetect _ _ dims _ _ _ _ D V slices origin step length
    hstep hshape hdense hcomplex hnorm
  let es := integerBoxCoordinateEquiv e sides
  let slices' := fun z (j : Tests (ep.symm z)) => (slices (ep.symm z) j).map es.toEmbedding
  have himage (z : Ω') (j : Tests (ep.symm z)) :
      (slices' z j).image Subtype.val =
        ((slices (ep.symm z) j).image Subtype.val).image (integerPointCoordinateEquiv e) := by
    simp only [slices', Finset.map_eq_image, Equiv.coe_toEmbedding, Finset.image_image]
    rfl
  have hshape' (z : Ω') (j : Tests (ep.symm z)) :
      (slices' z j).image Subtype.val =
        commonStrideBox (integerPointCoordinateEquiv e (origin (ep.symm z) j))
          (step (ep.symm z) j) (coordinateReindexedSides e (length (ep.symm z) j)) := by
    rw [himage, hshape, commonStrideBox_image_coordinateEquiv]
  have hdense' (z : Ω') (j : Tests (ep.symm z)) :
      IsDenseCommonStrideBox (coordinateReindexedSides e sides) pSlice
        ((slices' z j).image Subtype.val) := by
    rw [himage]
    exact (hdense (ep.symm z) j).coordinateEquiv e
  have hdet := h (fun z j => D (ep.symm z) j)
    (fun z j => (V (ep.symm z) j).coordinateEquiv e) slices'
    (fun z j => integerPointCoordinateEquiv e (origin (ep.symm z) j))
    (fun z j => step (ep.symm z) j)
    (fun z j => coordinateReindexedSides e (length (ep.symm z) j))
    (fun z j => hstep (ep.symm z) j) hshape' hdense'
    (fun z j => hcomplex (ep.symm z) j) (fun z j => hnorm (ep.symm z) j)
  have hseminorm := niltestSliceSeminorm_coordinateEquiv e ep sides law law' hweight
    physical D V slices origin step

  intro signal hsignal hsupp hlarge
  exact hdet signal hsignal hsupp (by rw [hseminorm]; exact hlarge)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem ScalarReferenceNativeDetection.coordinateReturn
    {m degree : ℕ} {X K K' : Type}
    [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]
    [Fintype K'] [DecidableEq K']
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (e : K ≃ K') (S : ℕ) (W τ : ℝ)
    (hbase : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hW : ∀ z : Option K × X, 0 < trimmedSpatialWidths W τ N z)
    (hW' : ∀ z : Option K' × X, 0 < trimmedSpatialWidths W τ N z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := K) W τ N) z)
    (hZ' : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := K') W τ N) z)
    (pSlice pTest pNative α : ℝ)
    (h : ScalarReferenceNativeDetection (degree := degree) J N hbox poly S W τ
      hbase hW' hZ' pSlice pTest pNative α) :
    ScalarReferenceNativeDetection (degree := degree) J N hbox poly S W τ
      hbase hW hZ pSlice pTest pNative α := by
  exact OrdinarySliceNativeDetection.coordinateReturn J N hbox poly e
    (scalarJointPathEquiv e W τ N _) (fun _ : K => S)
    (selectedJointReference _ hbase _ _ _ hW hZ)
    (selectedJointReference _ hbase _ _ _ hW' hZ')
    (selectedJointReference_scalarCoordinateEquiv_weight e W τ N hW hW' hZ hZ' _ hbase)
    (fun z t => jointIntegerPhysicalSite t.val (z.1.val, z.2.val))
    (fun z t => jointIntegerPhysicalSite t.val (z.1.val, z.2.val))
    (fun z t => jointIntegerPhysicalSite_scalarJointPathEquiv e W τ N _ t.val z)
    pSlice pTest pNative α h

theorem ScalarReferenceNativeDetection.retag_of_isEmpty
    {m m' degree : ℕ} {X K : Type} [Fintype X] [DecidableEq X]
    [Fintype K] [DecidableEq K]
    (J : Fin m → Type) [∀ j, Fintype (J j)] [IsEmpty (Σ j, J j)]
    (J' : Fin m' → Type) [∀ j, Fintype (J' j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (poly' : ∀ j, VectorPolynomial X ℝ (J' j → ℝ))
    (S : ℕ) (W τ : ℝ)
    (hbase : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hW : ∀ z : Option K × X, 0 < trimmedSpatialWidths W τ N z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := K) W τ N) z)
    (pSlice pTest pNative α : ℝ)
    (h : ScalarReferenceNativeDetection (degree := degree) J N hbox poly S W τ
      hbase hW hZ pSlice pTest pNative α) :
    ScalarReferenceNativeDetection (degree := degree) J' N hbox poly' S W τ
      hbase hW hZ pSlice pTest pNative α := by
  intro Tests _ Ldetect _ _ dims _ _ _ _ D V slices origin step length
    hstep hshape hdense hcomplex hnorm
  exact (h D V slices origin step length hstep hshape hdense hcomplex hnorm).retag_of_isEmpty
    J J' N hbox poly poly' _ _ _ _ degree pNative α

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedEmptyLayerLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (J j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

omit [Fintype X] in

@[simp] theorem allocatedCenteredJointDensity_empty_layers
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center a z = 1 := by
  exact canonicalCoefficientDensity_empty U b hb o _ _ _ _

variable (N : X → ℕ) (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

theorem AllocatedExternalCandidateSampler.law_empty_layers
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
      N poly hm τ ξ stride cells center) :
    A.law = selectedJointReference (trimmedIntegerBox N (spatialTrimMargin τ N))
      A.bases_nonempty stride cells (allocatedExternalCandidateWidths B U b S N τ ξ)
      A.widths_pos A.smooth_mass_pos := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro z
  rw [AllocatedExternalCandidateSampler.law, selectedJointFiniteLaw,
    FiniteProbabilityWeights.reweightPositive_weight]
  simp only [allocatedCenteredJointDensity_empty_layers, FiniteProbabilityWeights.mean_const,
    mul_one, div_one]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerDetectorReturn
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (J j)]
    {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler
variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
  N poly hm τ ξ (fun _ : X => 1) {0} center)

omit [∀ j, IsEmpty (J j)]
  [∀ j, IsZLattice ℝ
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
include A in
theorem scalarWidths_pos_empty_layers :
    ∀ z : Option (LayerSamplerVariables G I n B) × X,
      0 < trimmedSpatialWidths ((Fintype.card G : ℝ) * S.value) τ N z := by
  simpa only [allocatedExternalCandidateWidths_empty_layers] using A.widths_pos

theorem nativeDetection_iff_scalarReference_empty_layers
    (hW : ∀ z : Option (LayerSamplerVariables G I n B) × X,
      0 < trimmedSpatialWidths ((Fintype.card G : ℝ) * S.value) τ N z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := LayerSamplerVariables G I n B)
        ((Fintype.card G : ℝ) * S.value) τ N) z)
    (degree : ℕ) (pSlice pTest pNative α : ℝ) :
    A.NativeDetection degree pSlice pTest pNative α ↔
    ScalarReferenceNativeDetection (degree := degree) J N A.integerBox_nonempty poly
      S.value ((Fintype.card G : ℝ) * S.value) τ A.bases_nonempty
      hW hZ pSlice pTest pNative α := by
  unfold NativeDetection ScalarReferenceNativeDetection OrdinarySliceNativeDetection
  simp only [law_empty_layers]
  unfold physical Path Site sides
  generalize_proofs hbox hbase hpos hmass
  revert hW hZ hpos hmass
  rw [allocatedExternalCandidateSides_empty_layers_fun,
    allocatedExternalCandidateWidths_empty_layers]
  intros
  rfl

theorem nativeDetection_to_scalarAxes_empty_layers
    (degree : ℕ) (pSlice pTest pNative α : ℝ)
    (h : A.NativeDetection degree pSlice pTest pNative α) :
    ScalarReferenceNativeDetection (degree := degree) J N A.integerBox_nonempty poly
      S.value ((Fintype.card G : ℝ) * S.value) τ A.bases_nonempty
      A.scalarAxesWidths_pos_empty_layers A.scalarAxesMass_pos_empty_layers
      pSlice pTest pNative α := by
  have hlocal : ScalarReferenceNativeDetection (degree := degree) J N A.integerBox_nonempty poly
      S.value ((Fintype.card G : ℝ) * S.value) τ A.bases_nonempty
      A.scalarWidths_pos_empty_layers A.scalarMass_pos_empty_layers
      pSlice pTest pNative α := (A.nativeDetection_iff_scalarReference_empty_layers
    A.scalarWidths_pos_empty_layers A.scalarMass_pos_empty_layers
    degree pSlice pTest pNative α).mp h
  exact @ScalarReferenceNativeDetection.coordinateReturn m degree X G
    (LayerSamplerVariables G I n B) inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance J inferInstance
    N A.integerBox_nonempty poly
    (emptyLayerVariablesEquiv (G := G) B).symm S.value ((Fintype.card G : ℝ) * S.value) τ
    A.bases_nonempty A.scalarAxesWidths_pos_empty_layers A.scalarWidths_pos_empty_layers
    A.scalarAxesMass_pos_empty_layers A.scalarMass_pos_empty_layers pSlice pTest pNative α (@hlocal)

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler
variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
  N poly hm τ ξ (fun _ : X => 1) {0} center)

theorem nativeDetection_of_emptyTag_scalarReference
    {q : ℕ} (Jsource : Fin q → Type) [∀ j, Fintype (Jsource j)]
    [IsEmpty (Σ j, Jsource j)]
    (sourcePoly : ∀ j, VectorPolynomial X ℝ (Jsource j → ℝ))
    (degree : ℕ) (pSlice pTest pNative α : ℝ)
    (hsource : ScalarReferenceNativeDetection (degree := degree) Jsource N
      A.integerBox_nonempty sourcePoly S.value ((Fintype.card G : ℝ) * S.value) τ
      A.bases_nonempty A.scalarAxesWidths_pos_empty_layers A.scalarAxesMass_pos_zero_layers
      pSlice pTest pNative α) :
    A.NativeDetection degree pSlice pTest pNative α := by
  let : ∀ j, IsEmpty (I j) := fun j => Fin.elim0 j
  let : ∀ j, IsEmpty (J j) := fun j => Fin.elim0 j
  let : ∀ j, IsEmpty (Fin (n j)) := fun j => Fin.elim0 j
  have hscalar : ScalarReferenceNativeDetection (degree := degree) J N A.integerBox_nonempty poly
      S.value ((Fintype.card G : ℝ) * S.value) τ A.bases_nonempty
      A.scalarAxesWidths_pos_empty_layers A.scalarAxesMass_pos_empty_layers
      pSlice pTest pNative α :=
    @ScalarReferenceNativeDetection.retag_of_isEmpty q 0 degree X G
      inferInstance inferInstance inferInstance inferInstance
      Jsource inferInstance inferInstance J inferInstance N A.integerBox_nonempty
      sourcePoly poly S.value ((Fintype.card G : ℝ) * S.value) τ A.bases_nonempty
      A.scalarAxesWidths_pos_empty_layers A.scalarAxesMass_pos_zero_layers
      pSlice pTest pNative α (@hsource)
  apply (A.nativeDetection_iff_scalarReference_empty_layers
    A.scalarWidths_pos_empty_layers A.scalarMass_pos_empty_layers
    degree pSlice pTest pNative α).mpr
  exact @ScalarReferenceNativeDetection.coordinateReturn 0 degree X
    (LayerSamplerVariables G I n B) G inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance J inferInstance
    N A.integerBox_nonempty poly
    (emptyLayerVariablesEquiv (G := G) B) S.value ((Fintype.card G : ℝ) * S.value) τ
    A.bases_nonempty A.scalarWidths_pos_empty_layers A.scalarAxesWidths_pos_empty_layers
    A.scalarMass_pos_empty_layers A.scalarAxesMass_pos_empty_layers pSlice pTest pNative α (@hscalar)

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedZeroLayerDetectionFromEmptySampler
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler
variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
  N poly hm τ ξ (fun _ : X => 1) {0} center)

theorem nativeDetection_of_emptyLayer_sampler_s2_oai
    {q : ℕ} {I' J' : Fin q → Type}
    [∀ j, Fintype (I' j)] [∀ j, Fintype (J' j)]
    [∀ j, IsEmpty (I' j)] [∀ j, IsEmpty (J' j)]
    {n' : Fin q → ℕ} [∀ j, IsEmpty (Fin (n' j))]
    {B' : LayerSamplerAxis I' n' → Type} [∀ a, Fintype (B' a)]
    {U' : ∀ j, Submodule ℝ (J' j → ℝ)}
    {b' : ∀ j, Basis (Fin (n' j)) ℝ (euclideanSubspace (U' j))ᗮ}
    {R' σ' : Fin q → ℝ} {S' : LayerSamplerScale (G := G) B' U' b' R' σ'}
    {hb' : ∀ j, span ℤ (Set.range (b' j)) = projectedIntegerLattice (euclideanSubspace (U' j))}
    {o' : ∀ j, OrthonormalBasis (I' j) ℝ (euclideanSubspace (U' j))}
    {hR' : ∀ j, 0 < R' j} {hσ' : ∀ j, 0 < σ' j}
    {poly' : ∀ j, VectorPolynomial X ℝ (J' j → ℝ)}
    {hm' : ∀ j e, coefficients (poly' j) e ∈ U' j}
    {ξ' : ℝ} {center' : CoefficientTorus (K := LayerSamplerVariables G I' n' B') U'}
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J' j)) (euclideanSubspace (U' j)))]
    (Asource : AllocatedExternalCandidateSampler B' U' b' S' hb' o' hR' hσ'
      N poly' hm' τ ξ' (fun _ : X => 1) {0} center')
    (hvalue : S'.value = S.value)
    (degree : ℕ) (pSlice pTest pNative α : ℝ)
    (hsource : Asource.NativeDetection degree pSlice pTest pNative α) :
    A.NativeDetection degree pSlice pTest pNative α := by
  have hscalarSource : ScalarReferenceNativeDetection (degree := degree) J' N
      Asource.integerBox_nonempty poly' S'.value ((Fintype.card G : ℝ) * S'.value) τ
      Asource.bases_nonempty Asource.scalarAxesWidths_pos_empty_layers
      Asource.scalarAxesMass_pos_empty_layers pSlice pTest pNative α :=
    @nativeDetection_to_scalarAxes_empty_layers q G X inferInstance inferInstance
      I' J' inferInstance inferInstance inferInstance inferInstance n' inferInstance
      B' inferInstance U' b' R' σ' S' hb' o' hR' hσ' N poly' hm' τ ξ' center'
      inferInstance Asource degree pSlice pTest pNative α (@hsource)
  have heq :
      ScalarReferenceNativeDetection (degree := degree) J' N
        Asource.integerBox_nonempty poly' S'.value ((Fintype.card G : ℝ) * S'.value) τ
        Asource.bases_nonempty Asource.scalarAxesWidths_pos_empty_layers
        Asource.scalarAxesMass_pos_empty_layers pSlice pTest pNative α =
      ScalarReferenceNativeDetection (degree := degree) J' N
        A.integerBox_nonempty poly' S.value ((Fintype.card G : ℝ) * S.value) τ
        A.bases_nonempty A.scalarAxesWidths_pos_empty_layers A.scalarAxesMass_pos_zero_layers
        pSlice pTest pNative α := by
    simp only [hvalue]
  let : IsEmpty (Σ j, J' j) := ⟨fun x => isEmptyElim x.2⟩
  exact @nativeDetection_of_emptyTag_scalarReference G X inferInstance inferInstance
    I J inferInstance inferInstance n B inferInstance U b R σ S hb o hR hσ N poly hm
    τ ξ center inferInstance A q J' inferInstance inferInstance poly'
    degree pSlice pTest pNative α (@Eq.mp _ _ heq (@hscalarSource))

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.nativeDetection_of_emptyLayer_sampler_s2_oai := @OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.nativeDetection_of_emptyLayer_sampler_s2_oai
