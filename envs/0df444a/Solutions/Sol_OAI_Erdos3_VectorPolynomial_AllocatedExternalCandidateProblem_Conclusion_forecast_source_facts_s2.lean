-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.forecast_source_facts_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:54:35.344425+00:00
-- url     : https://prove2.me/submissions/e0ea74d2-c9ed-4412-ba76-f532544e519a

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B233
import Definitions.Def_OAIE3v2B304

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateSamplerFamily
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem law_support (z : A.Path) (hz : 0 < A.law.weight z) :
    columnResiduePattern stride z.2.val ∈ cells ∧
    0 < allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center z.1.val z.2.val :=
  selectedJointFiniteLaw_support (trimmedIntegerBox N (spatialTrimMargin τ N)) A.bases_nonempty
    stride cells (allocatedExternalCandidateWidths B U b S N τ ξ) A.widths_pos A.smooth_mass_pos
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) A.center_mass_pos z hz

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCenteredMeasurableFramedBadTail
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {c : ∀ j, U j} {a : X → ℤ}
variable {sample : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I E n B → ℤ}

theorem AllocatedCenteredRecoveredSampleReadAt.centeredJointFrame_read
    (h : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center c a sample read)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedReplaceReadNoise B z (allocatedJointFrameRead a (read z)) = read z := by
  funext i
  rcases i with i | i
  · exact (congrFun (h z).1 i).symm
  · rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateForecastComparisonSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable {qnum : ActualFixedSpatialSlicedForecastNumerics s}
variable (qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable (hδlate : qnum.δ = qLate.δ) (hHlate : qnum.Hchild = qLate.Hchild)
variable (hvlate : qnum.v = qLate.v) (hTaillate : qnum.Ptail = qLate.Ptail)
variable {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ δbase s.P s.Pbad PpresBase)

namespace AllocatedExternalCandidateProblem.Conclusion

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ)

variable {E Ptest : ℝ}
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)

variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Rrank : ℝ} (hEprec : 0 ≤ qLate.massLog + E + 8)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center path.center path.base sampleFn readFn)

variable (hcost : 0 ≤ cost) (hE : 0 ≤ E)
variable (hτ1 : τ ≤ 1)
variable (hEdata : E + 8 ≤ qLate.E)

variable {earlyPnative earlyMassLog earlyCapLog earlyEdata : ℝ}
variable (earlyData : ActualForecastData physicalN originalpoly
  earlyPnative earlyMassLog earlyCapLog earlyEdata)
variable (hEarlyCenter : earlyData.centerConstant = fun j => (path.center j).val)

variable (hprimes : path.primes = boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊)
variable (hexponent : path.exponent = fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)

variable {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ physicalN originalpoly hmem
      τ ξ stride cells center)
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {r d t : ℕ} {D : RationalFilteredNilmanifold L r d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {chartCost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := Eout) A D Fmark φ marked observable weight
      chartCost massThreshold scoreThreshold}
    {outputMass outputScore : ℝ}
    (out : P.Conclusion cost outputMass outputScore)
    (z : out.retained)
    (hkeep : ∀ k, (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔
      qnum.Hchild ≤ A.sides k)
    (hkernel : Nonempty G)
    (hcutoff : qnum.Hchild ≤ S.value)
    (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
    (hdensity : qnum.δ ≤ Real.exp (-cost))
    (hlog : cost + 1 ≤ qnum.v)
    (hprescribed : cost + 1 ≤ s.Ppres)
    (hstride : 2 * Real.exp cost ≤ qnum.Ptail)
    (hbase : path.base = z.val.1.val)
    (hnoise : path.noise = z.val.2.val)
    (hsample : path.sample = sampleFn z.val.2.val)
    (hread : path.read = allocatedReplaceReadNoise B z.val.2.val
      (allocatedJointFrameRead z.val.1.val (readFn z.val.2.val)))

include hnoise in
omit [Fintype Tsp] hcompact in
theorem forecast_noise_mem : path.noise ∈ rectangularWeightIndices 0
    (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
      (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1 := by
  rw [hnoise, ← allocatedExternalCandidateRootBudget_eq B U b S]
  exact z.val.2.property

include hbase in
omit [Fintype Tsp] hcompact in
theorem forecast_base_mem :
    path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN) := by
  rw [hbase]
  simpa only [trimmedIntegerBox, Finset.mem_image, mem_integerBox] using z.val.1.property

include hbase hnoise in
omit [Fintype Tsp] hcompact in
theorem forecast_density_ne_zero :
    allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
      center path.base path.noise ≠ 0 := by
  have hsupport : 0 < A.law.weight z.val := by
    have h := (P.chart ⟨z.val, out.subset z.property⟩).path_supported
    rwa [P.chart_path] at h
  rw [hbase, hnoise]
  exact ((A.law_support z.val hsupport).2).ne'

include hsample hnoise in
omit [Fintype Tsp] hcompact in
theorem forecast_sample_eq : sampleFn path.noise = path.sample := by
  rw [hnoise]
  exact hsample.symm

include hglobal hbase hnoise hread in
omit [Fintype Tsp] hcompact in
theorem forecast_read_eq : readFn path.noise = path.read := by
  rw [hread, ← hnoise, ← hbase]
  exact (hglobal.centeredJointFrame_read B U bW b hb o S hR hσ originalpoly hmem
    (allocatedShortAxis (I := I) U b S.value) spatial kernel block C path.noise).symm

include hglobal hbase hnoise hsample hread in
omit [Fintype Tsp] hcompact in
theorem forecast_source_facts_s2_oai :
    path.noise ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1 ∧
    path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN) ∧
    allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
      center path.base path.noise ≠ 0 ∧
    sampleFn path.noise = path.sample ∧ readFn path.noise = path.read := by
  exact ⟨forecast_noise_mem (s := s) (path := path) (hb := hb) (o := o) (originalpoly := originalpoly) (hmem := hmem) (ξ := ξ) (A := A) (out := out) (z := z) (hnoise := hnoise),
    forecast_base_mem (s := s) (path := path) (hb := hb) (o := o) (originalpoly := originalpoly) (hmem := hmem) (ξ := ξ) (A := A) (out := out) (z := z) (hbase := hbase),
    forecast_density_ne_zero (s := s) (path := path) (hb := hb) (o := o) (originalpoly := originalpoly) (hmem := hmem) (ξ := ξ) (A := A) (out := out) (z := z) (hbase := hbase) (hnoise := hnoise),
    forecast_sample_eq (s := s) (path := path) (hb := hb) (o := o) (originalpoly := originalpoly) (hmem := hmem) (ξ := ξ) (A := A) (out := out) (z := z) (hnoise := hnoise) (hsample := hsample),
    forecast_read_eq (s := s) (path := path) (hb := hb) (o := o) (originalpoly := originalpoly) (hmem := hmem) (ξ := ξ) (A := A) (out := out) (z := z) (bW := bW) (C := C) (hglobal := hglobal)
      (hbase := hbase) (hnoise := hnoise) (hread := hread)⟩

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.forecast_source_facts_s2_oai := @OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.forecast_source_facts_s2_oai
