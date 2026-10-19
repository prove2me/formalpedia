-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.relativePatchSliceConclusion_of_normalized_prepared_degreeRule_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:22:48.354979+00:00
-- url     : https://prove2.me/submissions/9d9cd150-9d59-4962-a9c8-04d7af7110b7

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B262
import Definitions.Def_OAIE3v2B304
import Definitions.Def_OAIE3v2B264
import Definitions.Def_OAIE3v2B266
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedAdmissiblePath_relativePatchSliceConclusion_of_prepared_shear_score_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedExternalCandidateProblem_Conclusion_exists_actual_shear_buffered_forecast_score_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedExternalCandidateProblem_Conclusion_returned_modulus_le_exp_discount_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RetainedPatchCutoffChoice
namespace OAI

section

namespace Erdos3

theorem retainedPatchCutoffChoice_bounds {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    retainedPatchRelativeError ε ∈ Set.Icc (0 : ℝ) 1 ∧
    0 < retainedPatchCutoff ε ∧
    2 / (retainedPatchCutoff ε : ℝ) ≤ 1 / 2 ∧
    4 / (retainedPatchCutoff ε : ℝ) ≤ retainedPatchRelativeError ε ∧
    (1 + retainedPatchRelativeError ε) * (1 - ε) ≤ 1 - retainedPatchRelativeError ε ∧
    (retainedPatchCutoff ε : ℝ) ≤ 16 / ε + 1 ∧
    (retainedPatchCutoff ε : ℝ) ≤ 17 / ε := by
  have hlo : 16 / ε ≤ (retainedPatchCutoff ε : ℝ) := Nat.le_ceil _
  have hpos : 0 < retainedPatchCutoff ε := Nat.ceil_pos.mpr (by positivity)
  have hposr : (0 : ℝ) < retainedPatchCutoff ε := Nat.cast_pos.mpr hpos
  have hprod : 16 ≤ (retainedPatchCutoff ε : ℝ) * ε := (div_le_iff₀ hε).mp hlo
  have hsixteen : (16 : ℝ) ≤ retainedPatchCutoff ε :=
    ((le_div_iff₀ hε).mpr (by nlinarith)).trans hlo
  have hupp : (retainedPatchCutoff ε : ℝ) ≤ 16 / ε + 1 :=
    (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 16 / ε)).le
  refine ⟨⟨by unfold retainedPatchRelativeError; positivity,
    by unfold retainedPatchRelativeError; linarith⟩, hpos, ?_, ?_, ?_, hupp, ?_⟩
  · apply (div_le_iff₀ hposr).mpr
    linarith
  · apply (div_le_iff₀ hposr).mpr
    unfold retainedPatchRelativeError
    nlinarith only [hprod]
  · unfold retainedPatchRelativeError
    nlinarith [sq_nonneg ε]
  · apply hupp.trans
    apply (le_div_iff₀ hε).mpr
    have hcancel : (16 / ε : ℝ) * ε = 16 := div_mul_cancel₀ _ hε.ne'
    nlinarith only [hcancel, hεone]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.ZeroLayerPhysicalNiltestBudget
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct NNReal

theorem relativePatchComplexity_le_of_rank_lip
    {X : Type*} {s d : ℕ} (A : PolynomialPatch X s d) {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hLip : (A.kernel.lip : ℝ) ≤ Real.exp p) :
    relativePatchComplexity A ≤ 2 * p + 1 := by
  have he : 1 ≤ Real.exp p := Real.one_le_exp hp
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog : Real.log (1 + (A.kernel.lip : ℝ)) ≤ p + 1 := by
    apply (Real.log_le_iff_le_exp (by positivity : 0 < 1 + (A.kernel.lip : ℝ))).mpr
    calc
      1 + (A.kernel.lip : ℝ) ≤ 1 + Real.exp p := by linarith
      _ ≤ 2 * Real.exp p := by linarith
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right he1 (Real.exp_nonneg p)
      _ = Real.exp (p + 1) := by rw [← Real.exp_add]; congr 1; ring
  unfold relativePatchComplexity
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedShearForecastScoreBridge
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal Matrix

variable {X J₀ : Type} [Fintype X] [DecidableEq X]
variable {m : ℕ} (prep : RankPreparationFamily X J₀ m)
variable {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod selected τ δslice)
variable (qnum : ActualFixedSpatialSlicedForecastNumerics setup)

namespace ActualFixedSpatialSlicedAdmissiblePath

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) setup qnum)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))
variable {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)

variable {Y : Type} {degree returned : ℕ}
    (patch : PolynomialPatch Y degree returned)
    (g : (polynomialShearFiltration patch.weight degree patch.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) (fun j => (prep j).Coord)))
    (c : ∀ j, (prep j).space)
    (hcenter : c = member.slice.path.center)
    (hmem : ∀ j α, coefficients (prep j).poly α ∈ (prep j).space)
    (χ : PatchKernel tagCount) (f : (X → ℤ) → ℝ) (lam : ℝ)

include hcenter in

theorem prepared_shear_buffered_score_of_actual_target {score : ℝ}
    (hscore : score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (member.slice.target selected setup.hBactive o bW hb
        (fun j => (prep j).poly) hmem setup.κ x).re *
      bufferedScalarScore χ
        (fullTaggedBufferedCoordinates e (fun j => (prep j).poly) (fun j => (c j).val))
        (fun u β => (patch.ofTaggedWeightedShearOrbit e g).value
          (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ)))) f lam x.val) :
    score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (member.slice.targetAt selected setup.hBactive o bW hb
        (fun j => (prep j).poly) hmem setup.κ x.val).re *
      bufferedScalarScore χ
        (fullTaggedBufferedCoordinates e (fun j => (prep j).poly)
          (fun j => (member.slice.path.center j).val))
        (fun u β => (patch.ofTaggedWeightedShearOrbit e g).value
          (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ)))) f lam x.val := by
  subst c
  exact hscore

end ActualFixedSpatialSlicedAdmissiblePath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedSourceGeometryNormalizedPatchConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m : ℕ} {G X J₀ : Type} [Fintype G] [Fintype X]
variable (prep : RankPreparationFamily X J₀ m)
variable {preparationP : ℝ} {Rprep : ℕ}
variable (hprep : prep.PreparedHeights preparationP Rprep)
variable (hpPrep : 0 ≤ preparationP) (hRprep : 1 ≤ Rprep)
variable {I Eout : Fin m → Type} [∀ j, Fintype (I j)]
  [∀ j, Fintype (Eout j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {N : X → ℕ} {τ ξ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod (allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) τ (Real.exp (-cost) / 2))
variable (qnum qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j))
  (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))]
variable (ν : ∀ j, Measure (euclideanSubspace ((fun j : Fin m => (prep j).space) j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (EuclideanJetLayers (fun j : Fin m => (prep j).space) (fun _ : Fin m => Unit))]
variable {stride : X → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) (fun j : Fin m => (prep j).space)}
variable {A : AllocatedExternalCandidateSampler B (fun j : Fin m => (prep j).space) b S hb o hR hσ N (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
  τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem.Conclusion
local instance instNonemptySiteCoord_r684c0e_1 : Nonempty A.Site := A.site_nonempty
variable {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {degree d t : ℕ}
variable (patch : PolynomialPatch Y degree d) [Fintype (PolynomialShearIndex patch.weight)]
variable {Fmark : NilpotentLieFiltration M t}
variable {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
variable {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) (fun j : Fin m => (prep j).Coord))}
variable (f : (X → ℤ) → ℝ) (lam : ℝ)
variable {chartCost massThreshold scoreThreshold outputMass outputScore : ℝ}
variable {P : AllocatedExternalCandidateProblem (E := Eout) A
  (polynomialShearNilmanifold patch.weight degree patch.weight_le) Fmark φ marked
  (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
  chartCost massThreshold scoreThreshold}
variable (out : P.Conclusion cost outputMass outputScore)
variable {δbase PpresBase : ℝ}
variable (path : ∀ _z : out.retained, ActualFixedSpatialForecastPath (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S hR hσ Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B (fun j : Fin m => (prep j).space) b S (fun _ => 0)) (S.value : ℝ) N τ δbase s.P s.Pbad PpresBase)
variable (hkeep : ∀ z : out.retained, ∀ k,
  (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔ qnum.Hchild ≤ A.sides k)
variable (hkernel : Nonempty G) (hcutoff : qnum.Hchild ≤ S.value)
variable (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
variable (hdensity : qnum.δ ≤ Real.exp (-cost)) (hlog : cost + 1 ≤ qnum.v)
variable (hprescribed : cost + 1 ≤ s.Ppres) (hstride : 2 * Real.exp cost ≤ qnum.Ptail)

local notation "input" z => out.denseSliceInput s qnum z (hkeep z) (ActualFixedSpatialForecastPath.commonTuple (path z))
  hkernel hcutoff hlate hdensity le_rfl hlog hprescribed hstride
local notation "member" z => ActualFixedSpatialForecastPath.toDenseSliceMember (path z) (input z)

include ν hpPrep hRprep in

theorem relativePatchSliceConclusion_of_actual_prepared_candidate
    (hδlate : qnum.δ = qLate.δ) (hHlate : qnum.Hchild = qLate.Hchild)
    (hvlate : qnum.v = qLate.v) (hTaillate : qnum.Ptail = qLate.Ptail)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget precision C Ecompare Ptest Rrank Crecovered : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : qnum.capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ qnum.E)
    (hPrecision : actualForecastDataModelRequired localBudget qnum.Pnative qnum.massLog u p ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp qnum.capLog)))
    (hexcess : letI : Nonempty A.Site := A.site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcostSlice : cost ≤ pSlice) (hchartCost : chartCost ≤ pSlice)
    (htest : 2 ≤ pTest)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hσ1 : ∀ j, σ j ≤ 1)
    {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)
    {scoreLog massLogTransfer : ℝ}
    (hTransferMass : 0 ≤ massLogTransfer)
    (hscoreLower : Real.exp (-scoreLog) ≤ outputScore)
    (hmassLower : Real.exp (-massLogTransfer) ≤ outputMass)
    (hU : scoreLog + massLogTransfer + 6 ≤ u)
    (hEcompare : max (max localBudget (3 * qnum.Pnative + 3))
        (2 * u + 4 * p + max 0 qnum.massLog + 20) + 2 +
      massLogTransfer + scoreLog + 8 ≤ Ecompare)
    (hcommonTest : max localBudget (3 * qnum.Pnative + 3) ≤ Ptest)
    (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
      s.D (s.D + s.slicedComparisonSourceLog Ptest + 4) (cost + 1)
      (2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14) m))
    (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) (fun j : Fin m => (prep j).space) b R S.value
      (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) a).1)
        ((allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) a).2 : ℝ)) τ)
    (hEprec : 0 ≤ qLate.massLog + Ecompare + 8)
    (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (N i : ℝ))
    (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank ((fun j : Fin m => (prep j).space) j) ((fun j : Fin m => (prep j).poly) j))
    (sampleFn : out.retained → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (readFn : out.retained → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I Eout n B → ℤ)
    (hglobal : ∀ z : out.retained, AllocatedCenteredRecoveredSampleReadAt B (fun j : Fin m => (prep j).space) bW b hb o S hR hσ
      (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1) (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) spatial kernel block Crecovered
      center (path z).center (path z).base (sampleFn z) (readFn z))
    (hcost : 0 ≤ cost) (hE : 0 ≤ Ecompare) (hτ1 : τ ≤ 1)
    (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s
      (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) (2 * Ptest) Ecompare ≤ S.value)
    (hξsmall : ξ ≤ Real.exp (-(2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14)))
    (hEdata : Ecompare + 8 ≤ qLate.E)
    (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
      (Dmod + Fintype.card (Σ j, I j))
      (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
      (Ecompare + 4) (2 * Ptest) s.Pτ) ≤ (N i : ℝ))
    (hprimes : ∀ z, (path z).primes = boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊)
    (hexponent : ∀ z, (path z).exponent = fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
    (hbase : ∀ z, (path z).base = z.val.1.val)
    (hnoise : ∀ z, (path z).noise = z.val.2.val)
    (hsample : ∀ z, (path z).sample = sampleFn z z.val.2.val)
    (hread : ∀ z, (path z).read = allocatedReplaceReadNoise B z.val.2.val
      (allocatedJointFrameRead z.val.1.val (readFn z z.val.2.val)))
    (hcenter : ∀ z : out.retained, (path z).center = P.centerLift)
    (hcoord : ∀ j, (Fintype.card (prep j).Coord : ℝ) ≤ preparationP)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤
      Real.exp ((preparationP + 2) ^ preparedIntegralBasisExponent m))
    (patchCutoff : ℕ) (hPatchCutoff : 0 < patchCutoff)
    (hsmall : 2 / (patchCutoff : ℝ) ≤ 1 / 2)
    {qLog : ℝ}
    (hqLog : ∀ z : out.retained,
      ((member z).slice.path.referenceRetainedCRTModulus patchCutoff : ℝ) ≤ Real.exp qLog)
    {d₀ old removed : ℕ}
    (hm : m ≤ degree) (hprepared : (∑ j, (prep j).rank) ≤ m * removed)
    (hremoved : removed ≤ old) (hreturned : d ≤ d₀ + degree * (old - removed))
    {patchCost budget δ ε : ℝ}
    (hPatchCost : relativePatchComplexity patch ≤ patchCost)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (haccuracy : 4 / (patchCutoff : ℝ) ≤ δ)
    (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hFinalBudget : 1 ≤ budget)
    (hRankBudget : ((d₀ + degree * old : ℕ) : ℝ) ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hMatrixBudget : qLog + (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (hPatchCostBudget : patchCost ≤ budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
    (hScoreBudget : scoreLog ≤ budget)
    (hFinalLarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (N i : ℝ)) :
    RelativePatchSliceConclusion degree N f ((1 - ε) * lam) (d₀ + degree * old)
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  classical
  let : Nonempty A.Site := A.site_nonempty
  obtain ⟨z, hz⟩ := out.exists_actual_shear_buffered_forecast_score_s2
    (s := s) (qnum := qnum) (qLate := qLate) (bW := bW) (ν := ν)
    (patch := patch) (f := f) (lam := lam) (path := path)
    (hkeep := hkeep) (hkernel := hkernel) (hcutoff := hcutoff) (hlate := hlate)
    (hdensity := hdensity) (hlog := hlog) (hprescribed := hprescribed) (hstride := hstride)
    hδlate hHlate hvlate hTaillate hξone hmargin hu hp hbudget hSliceLog hC hCp hCap
    hAccuracy hPrecision hdirect hexcess hSlice hcostSlice hchartCost htest hf hlam
    hσ1 (fun j => (hprep j).1) e hTransferMass hscoreLower hmassLower hU hEcompare
    hcommonTest hσbound hκ hEprec hlarge hRrank hrank sampleFn readFn hglobal hcost hE
    hτ1 hfloor hξsmall hEdata hNgrid hprimes hexponent hbase hnoise hsample hread
  have hc : P.centerLift = (member z).slice.path.center := by
    rw [ActualFixedSpatialForecastPath.toDenseSliceMember_center]
    exact (hcenter z).symm
  have hs := (member z).prepared_shear_buffered_score_of_actual_target
    prep s qnum o bW hb e patch out.ambient P.centerLift hc (fun j => (hprep j).2.1)
    (majorPhasePlateauKernel tagCount) f lam hz
  have hFinalScore : Real.exp (-budget) ≤ outputScore :=
    (Real.exp_le_exp.mpr (neg_le_neg hScoreBudget)).trans hscoreLower
  exact (member z).relativePatchSliceConclusion_of_prepared_shear_score_s2
    prep s qnum o bW hb e hprep hpPrep hRprep hcoord hbW
    patchCutoff hPatchCutoff hsmall (hqLog z) hm hprepared hremoved hreturned
    patch out.ambient hPatchCost f hf hlam hδ haccuracy hε hdiscount hs
    hFinalBudget hRankBudget hDmodBudget hMatrixBudget hPatchCostBudget hcapLog hPnative
    hFinalScore hFinalLarge

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m : ℕ} {G X J₀ : Type} [Fintype G] [Fintype X]
variable (prep : RankPreparationFamily X J₀ m)
variable {preparationP : ℝ} {Rprep : ℕ}
variable (hprep : prep.PreparedHeights preparationP Rprep)
variable (hpPrep : 0 ≤ preparationP) (hRprep : 1 ≤ Rprep)
variable {I Eout : Fin m → Type} [∀ j, Fintype (I j)]
  [∀ j, Fintype (Eout j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {N : X → ℕ} {τ ξ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod (allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) τ (Real.exp (-cost) / 2))
variable (qnum qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j))
  (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))]
variable (ν : ∀ j, Measure (euclideanSubspace ((fun j : Fin m => (prep j).space) j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (EuclideanJetLayers (fun j : Fin m => (prep j).space) (fun _ : Fin m => Unit))]
variable {stride : X → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) (fun j : Fin m => (prep j).space)}
variable {A : AllocatedExternalCandidateSampler B (fun j : Fin m => (prep j).space) b S hb o hR hσ N (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
  τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem
local instance instNonemptySiteCoord_r684c0e_2 : Nonempty A.Site := A.site_nonempty
variable {Y : Type} {degree d : ℕ}
variable (patch : PolynomialPatch Y degree d) [Fintype (PolynomialShearIndex patch.weight)]
variable (f : (X → ℤ) → ℝ) (lam : ℝ)
variable {chartCost childCost normBudget : ℝ} {rankBound : ℕ}
variable {productive : Finset A.Path}
variable (P : AllocatedExternalCandidateProblem (E := Eout) A
  (polynomialShearNilmanifold patch.weight degree patch.weight_le)
  (RationalTorus.trivialFiltration degree) 0 1
  (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
  chartCost ((A.law.mass productive /
    ((min rankBound ⌊childCost⌋₊ + 1) * (degree + 1) ^ min rankBound ⌊childCost⌋₊ : ℕ)) *
    Real.exp (-normBudget)) (Real.exp (-normBudget)))
variable {gainLog gain pGlobal : ℝ} {netExponent : ℕ}
variable (hchild : 0 ≤ childCost) (hd : d ≤ min rankBound ⌊childCost⌋₊)
  (hchildBudget : childCost ≤ normBudget)
  (hcenters : ∀ i, realPolynomialMass (patch.form.center i) ≤ normBudget)
  (hLip : (patch.kernel.lip : ℝ) ≤ Real.exp normBudget)
  (hgain : Real.exp (-gainLog) ≤ gain)
  (hReady : gain / 16 < A.law.mass productive)
  (hregularityBudget : (normBudget + 2) ^
    allocatedNormalizedShearObservableExponent degree ≤ pGlobal)
  (hpGlobal : 0 ≤ pGlobal) (hchartGlobal : chartCost ≤ pGlobal)
  (hscoreGlobal : normBudget ≤ pGlobal)
  (hmassGlobal : gainLog + 16 + ((degree : ℝ) + 1) * childCost + normBudget ≤ pGlobal)
  (hfGlobal : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
  (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
  (rule : A.DegreeGlobalizationAt (E := Eout) (fun x => ((f x - lam : ℝ) : ℂ))
    degree netExponent pGlobal cost)
variable {δbase PpresBase : ℝ}
variable (path : ∀ _z : P.productive, ActualFixedSpatialForecastPath (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S hR hσ Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B (fun j : Fin m => (prep j).space) b S (fun _ => 0)) (S.value : ℝ) N τ δbase s.P s.Pbad PpresBase)
variable (hkeep : ∀ z : P.productive, ∀ k,
  (P.chart z).keep k ↔ qnum.Hchild ≤ A.sides k)
variable (hkernel : Nonempty G) (hcutoff : qnum.Hchild ≤ S.value)
variable (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
variable (hdensity : qnum.δ ≤ Real.exp (-cost)) (hlog : cost + 1 ≤ qnum.v)
variable (hprescribed : cost + 1 ≤ s.Ppres) (hstride : 2 * Real.exp cost ≤ qnum.Ptail)

include ν hpPrep hRprep hchild hd hchildBudget hcenters hLip hgain hReady
  hregularityBudget hpGlobal hchartGlobal hscoreGlobal hmassGlobal hfGlobal hlam rule
  hkeep hkernel hcutoff hlate hdensity hlog hprescribed hstride in

theorem relativePatchSliceConclusion_of_normalized_prepared_degreeRule_s2_oai
    (hδlate : qnum.δ = qLate.δ) (hHlate : qnum.Hchild = qLate.Hchild)
    (hvlate : qnum.v = qLate.v) (hTaillate : qnum.Ptail = qLate.Ptail)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget precision C Ecompare Ptest Rrank Crecovered : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : qnum.capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ qnum.E)
    (hPrecision : actualForecastDataModelRequired localBudget qnum.Pnative qnum.massLog u p ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp qnum.capLog)))
    (hexcess : letI : Nonempty A.Site := A.site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcostSlice : cost ≤ pSlice) (hchartCost : chartCost ≤ pSlice)
    (htest : 2 ≤ pTest)
    (hσ1 : ∀ j, σ j ≤ 1)
    {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)
    (hU : cost + cost + 6 ≤ u)
    (hEcompare : max (max localBudget (3 * qnum.Pnative + 3))
        (2 * u + 4 * p + max 0 qnum.massLog + 20) + 2 +
      cost + cost + 8 ≤ Ecompare)
    (hcommonTest : max localBudget (3 * qnum.Pnative + 3) ≤ Ptest)
    (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
      s.D (s.D + s.slicedComparisonSourceLog Ptest + 4) (cost + 1)
      (2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14) m))
    (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) (fun j : Fin m => (prep j).space) b R S.value
      (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) a).1)
        ((allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) a).2 : ℝ)) τ)
    (hEprec : 0 ≤ qLate.massLog + Ecompare + 8)
    (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (N i : ℝ))
    (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank ((fun j : Fin m => (prep j).space) j) ((fun j : Fin m => (prep j).poly) j))
    (sampleFn : P.productive → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (readFn : P.productive → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I Eout n B → ℤ)
    (hglobal : ∀ z : P.productive, AllocatedCenteredRecoveredSampleReadAt B (fun j : Fin m => (prep j).space) bW b hb o S hR hσ
      (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1) (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) spatial kernel block Crecovered
      center (path z).center (path z).base (sampleFn z) (readFn z))
    (hcost : 0 ≤ cost) (hE : 0 ≤ Ecompare) (hτ1 : τ ≤ 1)
    (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s
      (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) (2 * Ptest) Ecompare ≤ S.value)
    (hξsmall : ξ ≤ Real.exp (-(2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14)))
    (hEdata : Ecompare + 8 ≤ qLate.E)
    (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
      (Dmod + Fintype.card (Σ j, I j))
      (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
      (Ecompare + 4) (2 * Ptest) s.Pτ) ≤ (N i : ℝ))
    (hprimes : ∀ z, (path z).primes = boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊)
    (hexponent : ∀ z, (path z).exponent = fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
    (hbase : ∀ z, (path z).base = z.val.1.val)
    (hnoise : ∀ z, (path z).noise = z.val.2.val)
    (hsample : ∀ z, (path z).sample = sampleFn z z.val.2.val)
    (hread : ∀ z, (path z).read = allocatedReplaceReadNoise B z.val.2.val
      (allocatedJointFrameRead z.val.1.val (readFn z z.val.2.val)))
    (hcenter : ∀ z : P.productive, (path z).center = P.centerLift)
    (hcoord : ∀ j, (Fintype.card (prep j).Coord : ℝ) ≤ preparationP)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤
      Real.exp ((preparationP + 2) ^ preparedIntegralBasisExponent m))
    {ε crtBudget : ℝ} (hεpos : 0 < ε) (hεone : ε ≤ 1)
    (hCRTbudget : 1 ≤ crtBudget) (hCRTinv : ε⁻¹ ≤ crtBudget)
    (hCRTtest : Ptest ∈ Set.Icc 0 crtBudget)
    (hCRTbad : s.Pbad ∈ Set.Icc 0 crtBudget)
    (hCRTpres : s.Ppres ∈ Set.Icc 0 crtBudget)
    {d₀ old removed : ℕ}
    (hm : m ≤ degree) (hprepared : (∑ j, (prep j).rank) ≤ m * removed)
    (hremoved : removed ≤ old) (hreturned : d ≤ d₀ + degree * (old - removed))
    {budget : ℝ}
    (hFinalBudget : 1 ≤ budget)
    (hRankBudget : ((d₀ + degree * old : ℕ) : ℝ) ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hMatrixBudget : 2048 * crtBudget ^ 3 + (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (hPatchCostBudget : 2 * normBudget + 1 ≤ budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
    (hScoreBudget : cost ≤ budget)
    (hFinalLarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (N i : ℝ)) :
    RelativePatchSliceConclusion degree N f ((1 - ε) * lam) (d₀ + degree * old)
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  classical
  let out := P.normalizedShearDegreeConclusion patch
    hchild hd hchildBudget hcenters hLip hgain hReady hregularityBudget
    hpGlobal hchartGlobal hscoreGlobal hmassGlobal hfGlobal hlam rule
  let pathOut := fun z : out.retained => path ⟨z.val, out.subset z.property⟩
  have hkeepOut (z : out.retained) (k) :
      (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔ qnum.Hchild ≤ A.sides k :=
    hkeep ⟨z.val, out.subset z.property⟩ k
  have hNorm : 0 ≤ normBudget := hchild.trans hchildBudget
  have hRank : (d : ℝ) ≤ normBudget :=
    (Nat.cast_le.mpr (hd.trans (min_le_right _ _))).trans
      ((Nat.floor_le hchild).trans hchildBudget)
  have hPatchCost : relativePatchComplexity patch ≤ 2 * normBudget + 1 :=
    relativePatchComplexity_le_of_rank_lip patch hNorm hRank hLip
  obtain ⟨hδ, hcutoffPos, hsmall, haccuracy, hdiscount, _, _⟩ :=
    retainedPatchCutoffChoice_bounds hεpos hεone
  have hqLog := out.returned_modulus_le_exp_discount_s2
    (prep := prep) (hprep := hprep) (s := s) (qnum := qnum)
    (patch := patch) (f := f) (lam := lam)
    (path := pathOut) (hkeep := hkeepOut) (hkernel := hkernel)
    (hcutoff := hcutoff) (hlate := hlate) (hdensity := hdensity)
    (hlog := hlog) (hprescribed := hprescribed) (hstride := hstride)
    hεpos hεone hCRTbudget hCRTinv hCRTtest hCRTbad hCRTpres
    (fun z => hexponent ⟨z.val, out.subset z.property⟩)
  exact out.relativePatchSliceConclusion_of_actual_prepared_candidate
    (prep := prep) (hprep := hprep) (hpPrep := hpPrep) (hRprep := hRprep)
    (s := s) (qnum := qnum) (qLate := qLate) (bW := bW) (ν := ν)
    (patch := patch) (f := f) (lam := lam) (path := pathOut)
    (hkeep := hkeepOut) (hkernel := hkernel) (hcutoff := hcutoff) (hlate := hlate)
    (hdensity := hdensity) (hlog := hlog) (hprescribed := hprescribed) (hstride := hstride)
    (scoreLog := cost) (massLogTransfer := cost)
    hδlate hHlate hvlate hTaillate hξone hmargin hu hp hbudget hSliceLog hC hCp hCap
    hAccuracy hPrecision hdirect hexcess hSlice hcostSlice hchartCost htest
    (fun x _ => hfGlobal x) hlam hσ1 e hcost le_rfl le_rfl hU hEcompare
    hcommonTest hσbound hκ hEprec hlarge hRrank hrank
    (fun z => sampleFn ⟨z.val, out.subset z.property⟩)
    (fun z => readFn ⟨z.val, out.subset z.property⟩)
    (fun z => hglobal ⟨z.val, out.subset z.property⟩)
    hcost hE hτ1 hfloor hξsmall hEdata hNgrid
    (fun z => hprimes ⟨z.val, out.subset z.property⟩)
    (fun z => hexponent ⟨z.val, out.subset z.property⟩)
    (fun z => hbase ⟨z.val, out.subset z.property⟩)
    (fun z => hnoise ⟨z.val, out.subset z.property⟩)
    (fun z => hsample ⟨z.val, out.subset z.property⟩)
    (fun z => hread ⟨z.val, out.subset z.property⟩)
    (fun z => hcenter ⟨z.val, out.subset z.property⟩)
    hcoord hbW (retainedPatchCutoff ε) hcutoffPos hsmall hqLog
    hm hprepared hremoved hreturned hPatchCost hδ haccuracy ⟨hεpos.le, hεone⟩ hdiscount
    hFinalBudget hRankBudget hDmodBudget hMatrixBudget hPatchCostBudget hcapLog hPnative
    hScoreBudget hFinalLarge

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.relativePatchSliceConclusion_of_normalized_prepared_degreeRule_s2_oai := @OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.relativePatchSliceConclusion_of_normalized_prepared_degreeRule_s2_oai
