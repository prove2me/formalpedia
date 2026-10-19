-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_native_ambient_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:13:11.31837+00:00
-- url     : https://prove2.me/submissions/182a037e-94e9-4ceb-b314-910866f8e205

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B266
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPath_sliced_ambient_rational_comparison_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPath_sliced_recovered_native_rational_comparison_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
namespace OAI

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
local notation "degree" => layerSamplerDegree I n

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedCompleteNativeCRTNeZero
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
local notation "Knative" => Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
local notation "actualDensity" => allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box
  integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c
local notation "projection" => allocatedOriginalSampleCongruenceProjection B U basis S sample
local notation "comparisonError" => allocatedSlicedPhysicalComparisonError B U basis S ξ HG
  (t := t) H q (ε := ε) (η := η) (Kφ := Knative)

attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedCompleteRecoveredCoverNeZero
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

include hR hσ hs ht hσbound hδ hsubset hdense hsizeG hsmallG hsize hsmall hε hmesh
  hδone b hη hA htail hp hV hτ hξ hbox hframe hmem hdegree hbase hsmallChart hread
  hm hperiod hcover hqN ν hlattice hcompact hσ1 hradius0 hradius3 hradius hchartCap hchart hchartBudget
  hmargin htrimbase hVpos happrox hPambient hEprec hX hdim hLip hcoverF hmodF hmass
  hlarge hRrank hrank hcutoff hD hPdecay hdecay hδgrid hδgrid1 hgridmesh in

theorem allocatedFixedPath_sliced_native_ambient_comparison_s2_oai :
    ‖allocatedSlicedNativeEvalMean B U basis S W base integerFrame box nativePoly
        HP stepP cP hinsideP hHP HG hHG cG stepG hcontainedG H c hH hsubset -
      (𝔼 u ∈ integerBox box, W.eval box nativePoly u *
        (κ * actualTarget nativePoly hmem u))‖ ≤
      comparisonError + ((2 * δnative + M * Real.exp (-Eprec)) +
        allocatedSlicedPhysicalAmbientGridError (B := B) (U := U) (basis := basis) (S := S)
          (E := E) (τ := τ) (ξ := ξ) (box := box) (integerFrame := integerFrame)
          (HG := HG) (hHG := hHG) (cG := cG) (stepG := stepG) (hstepG := hstepG)
          (e := e) (h0 := h0) (h1 := h1) (hδ := hδ) (o := o) (Lip := Lip)
          (cutoff := cutoff) (D := D) (δgrid := δgrid)) := by
  have hsource := allocatedFixedPath_sliced_recovered_native_rational_comparison_s2
    B U basis hR hσ S primes exponent HP stepP cP hinsideP hHP τ ξ hτ hξ box hbox
    integerFrame hframe HG hHG cG stepG hstepG hcontainedG e h0 h1 hB sample hs ht
    hσbound H c hH hδ hsubset hdense q hsizeG hsmallG hsize hsmall hε hmesh hδone
    b hη A hA htail hb o bW W hm hperiod hcover xref base read hp hcoprime hqN hV
    nativePoly hmem hdegree hbase hsmallChart hread
  have hamb := allocatedFixedPath_sliced_ambient_rational_comparison_s2
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ)
    (S := S) (primes := primes) (exponent := exponent) (HP := HP) (stepP := stepP)
    (cP := cP) (hinsideP := hinsideP) (hHP := hHP) (τ := τ) (ξ := ξ)
    (hτ := hτ) (hξ := hξ) (box := box) (hbox := hbox) (integerFrame := integerFrame)
    (hframe := hframe) (HG := HG) (hHG := hHG) (cG := cG) (stepG := stepG)
    (hstepG := hstepG) (hcontainedG := hcontainedG) (e := e) (h0 := h0) (h1 := h1)
    (hB := hB) (sample := sample) (hs := hs) (H := H) (c := c)
    (hH := hH) (hδ := hδ) (hsubset := hsubset) (hdense := hdense) (q := q)
    (hb := hb) (o := o) (bW := bW) (W := W) (hm := hm)
    (hperiod := hperiod) (hcover := hcover) (xref := xref) (base := base) (read := read)
    (hcoprime := hcoprime) (hqN := hqN) (nativePoly := nativePoly) (hmem := hmem) (hdegree := hdegree)
    (ν := ν) (hσ1 := hσ1) (radius := radius) (hradius0 := hradius0) (hradius3 := hradius3)
    (hradius := hradius) (chartCap := chartCap) (hchartCap := hchartCap) (hchart := hchart) (hchartBudget := hchartBudget)
    (hmargin := hmargin) (htrimbase := htrimbase) (hVpos := hVpos) (F := F) (nativeCoeff := nativeCoeff)
    (δnative := δnative) (happrox := happrox) (hPambient := hPambient) (hEprec := hEprec) (hX := hX)
    (hdim := hdim) (hLip := hLip) (hcoverF := hcoverF) (hmodF := hmodF) (hmass := hmass)
    (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank) (cutoff := cutoff) (hcutoff := hcutoff)
    (hD := hD) (hPdecay := hPdecay) (hdecay := hdecay) (hδgrid := hδgrid) (hδgrid1 := hδgrid1)
    (hgridmesh := hgridmesh)
  rw [norm_sub_rev] at hamb
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hsource hamb)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_native_ambient_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_native_ambient_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
