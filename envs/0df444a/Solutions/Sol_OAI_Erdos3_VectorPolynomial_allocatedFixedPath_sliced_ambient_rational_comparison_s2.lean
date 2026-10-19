-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_ambient_rational_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:13:10.508503+00:00
-- url     : https://prove2.me/submissions/01aacbe4-0c56-471b-ac41-8cb012eb9ae0

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B266
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_fixedSpatialSliceNativeAmbientRationalMean_comparison_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ContainedKernelPhysicalDisplacement
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem rectangularWeightIndices_normalized_norm_le
    {K : Type*} [Fintype K] (V : K → ℝ) (hV : ∀ k, 0 < V k)
    {z : K → ℤ} (hz : z ∈ rectangularWeightIndices 0 V 1) :
    ‖fun k => (z k : ℝ) / V k‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro k
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hV k), div_le_one (hV k)]
  exact rectangularWeightIndices_zero_bound V hz k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedPathKernelFrameBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "FullInput" => PrincipalTupleIndex B (layerSamplerDegree I n)

theorem allocatedFixedPathKernel_card_mul_scale_le_budget :
    (Fintype.card G : ℝ) * (S.value : ℝ) ≤ budget := by
  rw [allocatedPhysicalRootBudget_zero]
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Nat.cast_le.mpr (Fintype.card_le_of_injective
    (Sum.inl : G → LayerSamplerVariables G I n B) Sum.inl_injective)

theorem allocatedFixedPathKernelFrame_abs_le_one
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : 0 < ξ)
    (box : X → ℕ) (hbox : ∀ x, 0 < box x)
    (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box) 1)
    (a : Option G × X) :
    |allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame a| ≤ 1 := by
  have hnorm := rectangularWeightIndices_normalized_norm_le _
    (narrowTrimmedSpatialWidths_pos
      (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)) hτ hξ box hbox) hframe
  change |(integerFrame (canonicalZeroSpatialKernelEmbedding G FullInput X a) : ℝ) /
    narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box
      (canonicalZeroSpatialKernelEmbedding G FullInput X a)| ≤ 1
  exact (Real.norm_eq_abs _).symm ▸
    (norm_le_pi_norm _ (canonicalZeroSpatialKernelEmbedding G FullInput X a)).trans hnorm

theorem allocatedFixedPathKernelFrame_geometry
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : 0 < ξ)
    (box : X → ℕ) (hbox : ∀ x, 0 < box x)
    (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box) 1) :
    0 ≤ budget ∧ 0 ≤ (S.value : ℝ) ∧
      (Fintype.card G : ℝ) * (S.value : ℝ) ≤ budget ∧
      ∀ a, |allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame a| ≤ 1 :=
  ⟨allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0), Nat.cast_nonneg _,
    allocatedFixedPathKernel_card_mul_scale_le_budget B U basis S,
    allocatedFixedPathKernelFrame_abs_le_one B U basis S hτ hξ box hbox integerFrame hframe⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProgressionEndpointUnitBox
namespace OAI

section

namespace Erdos3

theorem progression_slice_endpoint_unit_box {S step H : ℕ} (c : ℤ)
    (hS : 0 < S) (hstep : 0 < step) (hH : 0 < H)
    (hcontained : integerProgressionSupport c (step : ℤ) H ⊆
      Finset.Ico (0 : ℤ) (S : ℤ)) :
    0 ≤ (c : ℝ) / S ∧
      0 ≤ (step : ℝ) * ((H - 1 : ℕ) : ℝ) / S ∧
      (c : ℝ) / S + (step : ℝ) * ((H - 1 : ℕ) : ℝ) / S ≤ 1 := by
  have hfirst := hcontained (integerProgressionSupport_point c step H hstep 0 hH)
  have hlast := hcontained (integerProgressionSupport_point c step H hstep
    (H - 1) (by omega))
  have hc : (0 : ℝ) ≤ c := by
    have he : (0 : ℤ) ≤ c := by simpa using (Finset.mem_Ico.mp hfirst).1
    exact_mod_cast he
  have hend : (c : ℝ) + (step : ℝ) * ((H - 1 : ℕ) : ℝ) < S := by
    exact_mod_cast (Finset.mem_Ico.mp hlast).2
  have hSreal : (0 : ℝ) < S := by exact_mod_cast hS
  refine ⟨div_nonneg hc hSreal.le, by positivity, ?_⟩
  rw [← add_div]
  exact (div_le_one hSreal).mpr hend.le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedFixedPath_sliced_kernel_geometry
    (HG : G → ℕ) (hHG : ∀ g, 2 ≤ HG g) (cG : G → ℤ)
    (stepG : ℕ) (hstepG : 0 < stepG)
    (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ)) :
    (∀ g, 0 ≤ (cG g : ℝ) / S.value) ∧
    (∀ g, 0 ≤ (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value) ∧
    (∀ g, (cG g : ℝ) / S.value +
      (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value ≤ 1) ∧
    (∀ g, 0 < (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value) := by
  have hg (g : G) := progression_slice_endpoint_unit_box (cG g) S.positive
    hstepG (by have := hHG g; omega) (hcontainedG g)
  refine ⟨fun g => (hg g).1, fun g => (hg g).2.1, fun g => (hg g).2.2, ?_⟩
  intro g
  simpa only [Int.cast_natCast] using fixedSpatialKernelProgression_width_pos S.positive
    (show (0 : ℤ) < stepG by exact_mod_cast hstepG) (hHG g)

local notation "Active" => {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))

theorem allocatedFixedPath_sliced_principal_geometry
    (stepG : ℕ) (hstepG : 0 < stepG) (H : Input → ℕ) (c : Input → ℤ)
    (hH : ∀ j, 2 ≤ H j) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ)) :
    let lower := fun (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) =>
      (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) =>
      (stepG : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    (∀ a p, δ / 2 ≤ width a p) ∧ (∀ a p, 0 ≤ lower a p) ∧
      (∀ a p, |lower a p| + |width a p| ≤ 1) := by
  intro lower width
  have hg (j : Input) := progression_slice_endpoint_geometry (c j) S.positive hstepG
    (hH j) hδ (hsubset j) (hdense j)
  exact ⟨fun a p => (hg ⟨a, p⟩).2.1, fun a p => (hg ⟨a, p⟩).1,
    fun a p => (hg ⟨a, p⟩).2.2.1⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G T : Type*} {X : Type} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedAmbientNativeCRTNeZero
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (h0 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (hm : 0 < m) (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ} (hV : gridVolume ≠ 0)

local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "nativeTest" => W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
  (fun a => (base a : ℝ) / box a) τ
local notation "actualDensity" => allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box
  integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c
local notation "projection" => allocatedOriginalSampleCongruenceProjection B U basis S sample
local notation "rationalReference" => allocatedSlicedPhysicalRationalMean B U basis S primes exponent
  HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected xref base
  (allocatedReadDeck read) projection hcoprime hqN (gridVolume := gridVolume) nativeTest actualDensity

local instance slicedAmbientRecoveredCoverNeZero_r35fd75_1 : NeZero W.cover := ⟨W.cover_pos.ne'⟩
variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
variable (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E W.cover → Prop,
  coefficientDeckChartEvent U bW basis hb o W.cover event
    (affineCoefficientCoverSample U nativePoly hmem W.cover
      (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
        integerFrame) (k, x) : ℝ))) ↔
    event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod W.cover))))

local notation "actualLaw" => principalAffineIntervalLaw B degree
  (allocatedPrincipalSides B U basis S) HP stepP cP hinsideP hHP
local notation "actualActive" => (fun _ : Original => crtPolynomialInputLaw primes exponent
  (fun l => padicValNat (primes l) stepG) hcoprime
  (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l))))
local notation "actualOutput" => (fun v : Original => integerLongPolynomialOutput
  (allocatedForecastPolynomial short base integerFrame (allocatedReadDeck read) projection)
  (fun k => (v (Prod.fst k) (Prod.snd k) : ℤ)) Ncrt)
local notation "κ" => ((forecastGeometricJacobian (X := X) (I := I)
  U basis R S.value gridVolume τ : ℝ) : ℂ)
local notation "actualTarget" => forecastLawDensityPhysicalTarget B U basis S actualLaw
  actualDensity selected sample xref actualActive actualOutput Ncrt gridVolume
  base box τ o hb bW

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
variable (radius : ℝ≥0) (hradius0 : 0 < radius) (hradius3 : (3 : ℝ) ≤ radius)
variable (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
variable (chartCap : Fin m → ℝ) (hchartCap : ∀ j, 0 ≤ chartCap j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
  chartCap j * ‖v‖)
variable (hchartBudget : ∀ j, chartCap j * (((Fintype.card (I j) : ℝ) + 1) *
  (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ box i ≤ box i)
variable (htrimbase : base ∈ trimmedIntegerBox box (spatialTrimMargin τ box))
variable (hVpos : 0 < gridVolume)
variable {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
variable (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
variable (nativeCoeff : Findex → ℂ) (δnative : ℝ)
variable (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hpoly : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖((forecastGeometricJacobian (X := X) (I := I) U basis R S.value gridVolume τ : ℝ) : ℂ) * (forecastLawDensityPhysicalTarget B U basis S (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) HP stepP cP hinsideP hHP) (allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c) (allocatedShortIntegerSelection U basis S.value) sample xref (fun _ : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) => crtPolynomialInputLaw primes exponent (fun l => padicValNat (primes l) stepG) hcoprime (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l)))) (fun v : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) => integerLongPolynomialOutput (allocatedForecastPolynomial (allocatedShortAxis (I := I) U basis S.value) base integerFrame (allocatedReadDeck read) (allocatedOriginalSampleCongruenceProjection B U basis S sample)) (fun k => (v (Prod.fst k) (Prod.snd k) : ℤ)) (∏ l, primes l ^ exponent l)) (∏ l, primes l ^ exponent l) gridVolume base box τ o hb bW) poly hpoly u - ∑ i, nativeCoeff i * (F i).eval box poly u‖ ≤ δnative)
variable {Pambient Eprec Rrank M : ℝ} (hPambient : 0 ≤ Pambient) (hEprec : 0 ≤ Eprec)
variable (hX : (Fintype.card X : ℝ) ≤ Pambient)
variable (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ Pambient)
variable (hLip : ((Lip * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal coverCap) : ℝ≥0) : ℝ) ≤ Real.exp Pambient)
variable (hcoverF : ∀ i, ((W.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmodF : ∀ i, ((W.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmass : ∑ i, ‖nativeCoeff i‖ ≤ M)
variable (hlarge : ∀ i, Real.exp ((max Pambient Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (box i : ℝ))
variable (hRrank : Real.exp ((max Pambient Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (box i : ℝ))
  Rrank (U j) (nativePoly j))
variable (cutoff : ℕ) (hcutoff : 0 < cutoff)
variable {D Pdecay δgrid : ℝ} (hD : 0 ≤ D)
variable (hPdecay : ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) + 2 : ℕ) : ℝ) ≤ Pdecay)
variable (hdecay : ∀ i (χ : AddChar ((Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) → ZMod (∏ l, primes l ^ exponent l)) ℂ),
  ‖finiteImageCharacteristic ((fun _ : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) => crtPolynomialInputLaw primes exponent (fun l => padicValNat (primes l) stepG) hcoprime (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l)))) i) (fun x j => ((fun v : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) => integerLongPolynomialOutput (allocatedForecastPolynomial (allocatedShortAxis (I := I) U basis S.value) base integerFrame (allocatedReadDeck read) (allocatedOriginalSampleCongruenceProjection B U basis S sample)) (fun k => (v (Prod.fst k) (Prod.snd k) : ℤ)) (∏ l, primes l ^ exponent l)) i x j : ZMod (∏ l, primes l ^ exponent l))) χ‖ ≤
    D * (orderOf χ : ℝ) ^ (-Pdecay))
variable (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)
variable (hgridmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) /
  forecastJointGridScale U basis R S.value box τ j ≤ δgrid)

include hR hσ hs hτ hξ hbox hframe hcontainedG hH hδ hsubset hdense ν hlattice hcompact hσ1
  hradius0 hradius3 hradius hchartCap hchart hchartBudget hmargin htrimbase hVpos
  happrox hdegree hPambient hEprec hX hdim hLip hcoverF hmodF hmass hlarge hRrank hrank
  hcutoff hD hPdecay hdecay hδgrid hδgrid1 hgridmesh in

theorem allocatedFixedPath_sliced_ambient_rational_comparison_s2_oai :
    ‖(𝔼 u ∈ integerBox box, W.eval box nativePoly u *
        (κ * actualTarget nativePoly hmem u)) - rationalReference‖ ≤
      (2 * δnative + M * Real.exp (-Eprec)) +
        allocatedSlicedPhysicalAmbientGridError (B := B) (U := U) (basis := basis) (S := S)
          (E := E) (τ := τ) (ξ := ξ) (box := box) (integerFrame := integerFrame)
          (HG := HG) (hHG := hHG) (cG := cG) (stepG := stepG) (hstepG := hstepG)
          (e := e) (h0 := h0) (h1 := h1) (hδ := hδ) (o := o) (Lip := Lip)
          (cutoff := cutoff) (D := D) (δgrid := δgrid) := by
  let lowerP := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
    (c ⟨a, p⟩ : ℝ) / S.value
  let widthP := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
    (stepG : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
  let lowerG := fun g => (cG g : ℝ) / S.value
  let widthG := fun g => (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value
  let frame := allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame
  have hwGne : ∀ g, widthG g ≠ 0 := fun g => ne_of_gt
    (fixedSpatialKernelProgression_width_pos S.positive
      (show (0 : ℤ) < stepG by exact_mod_cast hstepG) (hHG g))
  have hδP : 0 < δ / 2 := div_pos hδ (by norm_num)
  have hPgeo := allocatedFixedPath_sliced_principal_geometry B U basis S
    stepG hstepG H c hH hδ hsubset hdense
  have hGgeo := allocatedFixedPath_sliced_kernel_geometry B U basis S
    HG hHG cG stepG hstepG hcontainedG
  have hframegeo := allocatedFixedPathKernelFrame_geometry B U basis S
    hτ hξ box hbox integerFrame hframe
  have hcomparison := fixedSpatialSliceNativeAmbientRationalMean_comparison_s2 B U basis hR hσ S
    actualLaw lowerP widthP sample xref actualActive actualOutput Ncrt gridVolume base box τ
    o hb bW W ν e budget (S.value : ℝ) frame lowerG widthG hwGne h0 h1 hB
    hs hδP hPgeo.1 hPgeo.2.1 hPgeo.2.2 hGgeo.1 hGgeo.2.1 hGgeo.2.2.1
    hσ1 radius hradius0 hradius3 hradius chartCap hchartCap hchart hchartBudget
    hframegeo.1 hframegeo.2.1 hframegeo.2.2.1 hframegeo.2.2.2 hτ hmargin htrimbase
    q hqN hm hperiod hcover hVpos F nativeCoeff δnative happrox nativePoly hdegree hmem
    hPambient hEprec hX hdim hLip hcoverF hmodF hmass hlarge hRrank hrank
    cutoff hcutoff hD hPdecay hdecay hδgrid hδgrid1 hgridmesh
  exact hcomparison

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_ambient_rational_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_ambient_rational_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
