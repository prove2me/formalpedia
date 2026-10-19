-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.relativePatchSliceConclusion_of_normalized_ready_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:15:31.038288+00:00
-- url     : https://prove2.me/submissions/6c61377d-ca51-4c4b-a3f2-58a2cf8c9809

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B304
import Definitions.Def_OAIE3v2B264
import Definitions.Def_OAIE3v2B266
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedExternalCandidateProblem_relativePatchSliceConclusion_of_normalized_prepared_degreeRule_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem RelativePatchSliceConclusion.mono {X : Type*} [Fintype X] {s : ℕ}
    {N : X → ℕ} {f : (X → ℤ) → ℝ} {target : ℝ} {rankBound rankBound' : ℕ}
    {cost cost' : ℝ} (h : RelativePatchSliceConclusion s N f target rankBound cost)
    (hrank : rankBound ≤ rankBound') (hcost : cost ≤ cost') :
    RelativePatchSliceConclusion s N f target rankBound' cost' := by
  obtain ⟨q, hq, S, d, A, hlength, hd, hcomplexity, hscore⟩ := h
  have he : Real.exp (-cost') ≤ Real.exp (-cost) :=
    Real.exp_le_exp.mpr (neg_le_neg hcost)
  exact ⟨q, hq, S, d, A, fun i =>
    (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)).trans (hlength i),
    hd.trans hrank, hcomplexity.trans hcost, he.trans hscore⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedNormalizationPrimitiveBudget
namespace OAI

section

namespace Erdos3

theorem allocatedNormalizationExponent_ge_two (s : ℕ) :
    2 ≤ (exists_relative_finite_returned_fiber_normalization.{0, 0} s).choose :=
  (exists_relative_finite_returned_fiber_normalization.{0, 0} s).choose_spec.1

theorem allocatedNormalizedBudget_bounds (s cardVars : ℕ) {childCost : ℝ}
    (hchild : 0 ≤ childCost) :
    let E := (exists_relative_finite_returned_fiber_normalization.{0, 0} s).choose
    let B := ((childCost + (cardVars : ℝ) + 2) + 2) ^ E
    childCost ≤ B ∧ 0 ≤ B ∧ (cardVars : ℝ) ≤ B := by
  dsimp only
  have hE := allocatedNormalizationExponent_ge_two s
  have hcard : (0 : ℝ) ≤ cardVars := Nat.cast_nonneg cardVars
  have hbase : 1 ≤ (childCost + (cardVars : ℝ) + 2) + 2 := by linarith
  have hpower : (childCost + (cardVars : ℝ) + 2) + 2 ≤
      ((childCost + (cardVars : ℝ) + 2) + 2) ^
        (exists_relative_finite_returned_fiber_normalization.{0, 0} s).choose := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by omega : 1 ≤
      (exists_relative_finite_returned_fiber_normalization.{0, 0} s).choose)
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RelativeActualRankBudget
namespace OAI

section

namespace Erdos3

theorem relative_actual_rank_reconstruction_le
    {s d d₀ old removed : ℕ} (hremoved : removed ≤ old)
    (hreturned : d ≤ d₀ + s * (old - removed)) :
    d + s * removed ≤ d₀ + s * old := by
  calc
    d + s * removed ≤ d₀ + s * (old - removed) + s * removed :=
      Nat.add_le_add_right hreturned _
    _ = d₀ + s * old := by
      rw [Nat.add_assoc, ← Nat.mul_add, Nat.sub_add_cancel hremoved]

theorem relative_actual_rank_reconstruction_budget
    {s d removed bound : ℕ} {childCost p : ℝ}
    (hchild : 0 ≤ childCost) (hd : d ≤ min bound ⌊childCost⌋₊)
    (hremoved : (removed : ℝ) ≤ p) :
    ((d + s * removed : ℕ) : ℝ) ≤ childCost + (s : ℝ) * p := by
  have hdim : (d : ℝ) ≤ childCost :=
    (Nat.cast_le.mpr (hd.trans (min_le_right _ _))).trans (Nat.floor_le hchild)
  simpa only [Nat.cast_add, Nat.cast_mul] using
    add_le_add hdim (mul_le_mul_of_nonneg_left hremoved (Nat.cast_nonneg s))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedRetainedActualForecastFactory
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j ex, coefficients (poly j) ex ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

variable (z : A.Path) (centerLift : ∀ j, U j)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hrecovered : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      centerLift z.1.val z.2.val sample f)
    (Dmod : ℕ) {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
      (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (e : Fin 2 × X ↪ G) (Pdim gainLog Qstride : ℝ)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime) (depth : ℕ → ℕ)
    (hgood : letI := actualForecastPrimeNeZero primes hprime
      (∏ p ∈ primes, p ^ largestTestedBadDepth depth
        (allocatedActualPrimeBad (allocatedShortAxis (I := I) U b S.value)
          spatial kernel block primes (modularForecastRankConstant m Dmod : ℝ)) p f) ≤
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius (gainLog + 8)))
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card X : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdim)
    (hnX : 0 < Fintype.card X) (hgainLog : 0 ≤ gainLog) (hgainDim : gainLog ≤ Pdim)
    (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hdet : ∀ t : Fin 2,
      spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog) / 2 <
        |Matrix.det (fun i j : X => spatialMatrixNormalizedEntries e A.widths z.2.val (t,j,i))|)

variable {Selected : Type}
    {selected : Selected → Σ j : Fin m, Fin (n j)} {δslice : ℝ}
    (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := E)
      B U b S Dmod selected τ δslice)
    (hPmodel : preparedCenteredForecastSpatialLog Pdim ≤ setup.P)
    (hPbad : 2 * Fintype.card X * Qstride +
      (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11 ≤ setup.Pbad)

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in

theorem allocatedRecoveredGoodForecastPathForSetup_data :
    let path := allocatedRecoveredGoodForecastPathForSetup z centerLift sample f hrecovered Dmod spatial kernel block e Pdim gainLog Qstride
      primes hprime depth hgood hPdim hX hvars hnX hgainLog hgainDim hstride hdet
      setup hPmodel hPbad
    path.center = centerLift ∧ path.base = z.1.val ∧ path.noise = z.2.val ∧
      path.sample = sample ∧ path.read = allocatedReplaceReadNoise B z.2.val f ∧
      path.primes = primes ∧ path.exponent = depth ∧ path.prescribed = (fun _ => 0) ∧
      path.origin = (fun _ _ => 0) ∧ path.lower = (fun _ _ => 0) ∧ path.width = (fun _ _ => 1) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j ex, coefficients (poly j) ex ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

theorem exists_allocatedRetainedActualForecastFactory
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (centerLift : ∀ j, U j)
    (sampleFn : (X → ℤ) → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (readFn : (X → ℤ) → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (productive retained : Finset A.Path) (hsub : retained ⊆ productive)
    (Dmod : ℕ) {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
      (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (e : Fin 2 × X ↪ G) (Pdim gainLog Qstride Ptest Crecovered : ℝ)
    (hglobal : ∀ base, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
      poly hm (allocatedShortAxis (I := I) U b S.value) spatial kernel block Crecovered
      center centerLift base (sampleFn base) (readFn base))
    (hrecovered : ∀ z ∈ productive, AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
      poly hm centerLift z.1.val z.2.val (sampleFn z.1.val z.2.val)
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val)))
    (hgood : let primes := boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊
      letI := actualForecastPrimeNeZero primes (boundedPrimes_prime _)
      ∀ z ∈ productive,
      (∏ p ∈ primes, p ^ largestTestedBadDepth (fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
        (allocatedActualPrimeBad (allocatedShortAxis (I := I) U b S.value)
          spatial kernel block primes (modularForecastRankConstant m Dmod : ℝ)) p
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val))) ≤
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius (gainLog + 8)))
    (hdet : ∀ z ∈ productive, ∀ t : Fin 2,
      spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog) / 2 <
        |Matrix.det (fun i j : X => spatialMatrixNormalizedEntries e A.widths z.2.val (t,j,i))|)
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card X : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdim)
    (hnX : 0 < Fintype.card X) (hgainLog : 0 ≤ gainLog) (hgainDim : gainLog ≤ Pdim)
    (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    {Selected : Type} {selected : Selected → Σ j : Fin m, Fin (n j)} {δslice : ℝ}
    (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := E)
      B U b S Dmod selected τ δslice)
    (hPmodel : preparedCenteredForecastSpatialLog Pdim ≤ setup.P)
    (hPbad : 2 * Fintype.card X * Qstride +
      (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11 ≤ setup.Pbad) :
    AllocatedRetainedActualForecastFactoryConclusion bW centerLift sampleFn readFn retained
      Dmod spatial kernel block e Ptest Crecovered setup := by
  let path := fun z : retained => allocatedRecoveredGoodForecastPathForSetup
    (A := A) z.val centerLift (sampleFn z.val.1.val z.val.2.val)
    (allocatedJointFrameRead z.val.1.val (readFn z.val.1.val z.val.2.val))
    (hrecovered z.val (hsub z.property)) Dmod spatial kernel block e Pdim gainLog Qstride
    (boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊) (boundedPrimes_prime _)
    (fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊) (hgood z.val (hsub z.property))
    hPdim hX hvars hnX hgainLog hgainDim hstride (hdet z.val (hsub z.property))
    setup hPmodel hPbad
  have hdata (z : retained) := allocatedRecoveredGoodForecastPathForSetup_data
    (A := A) z.val centerLift (sampleFn z.val.1.val z.val.2.val)
    (allocatedJointFrameRead z.val.1.val (readFn z.val.1.val z.val.2.val))
    (hrecovered z.val (hsub z.property)) Dmod spatial kernel block e Pdim gainLog Qstride
    (boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊) (boundedPrimes_prime _)
    (fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊) (hgood z.val (hsub z.property))
    hPdim hX hvars hnX hgainLog hgainDim hstride (hdet z.val (hsub z.property))
    setup hPmodel hPbad
  refine ⟨path, ?_, (fun z => (hdata z).2.2.2.2.2.1),
    (fun z => (hdata z).2.2.2.2.2.2.1), (fun z => (hdata z).2.1),
    (fun z => (hdata z).2.2.1), (fun z => (hdata z).2.2.2.1),
    (fun z => (hdata z).2.2.2.2.1), (fun z => (hdata z).1)⟩
  intro z
  rw [(hdata z).1, (hdata z).2.1]
  exact hglobal z.val.1.val

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
variable (eSpatial : Fin 2 × X ↪ G)
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

local instance instNonemptySiteCoord_r8e7f43_1 : Nonempty A.Site := A.site_nonempty
variable {degree originalRank D E : ℕ}
variable (f : (X → ℤ) → ℝ) (lam : ℝ)
variable {chartCost childCost : ℝ} {productive : Finset A.Path}
variable {gainLog gain pGlobal : ℝ} {netExponent : ℕ}
variable (hchild : 0 ≤ childCost)
  (hgain : Real.exp (-gainLog) ≤ gain)
  (hReady : gain / 16 < A.law.mass productive)
  (hregularityBudget : ((((childCost + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 2) ^
    allocatedNormalizedShearObservableExponent degree ≤ pGlobal)
  (hpGlobal : 0 ≤ pGlobal) (hchartGlobal : chartCost ≤ pGlobal)
  (hscoreGlobal : (((childCost + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤ pGlobal)
  (hmassGlobal : gainLog + 16 + ((degree : ℝ) + 1) * childCost + (((childCost + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤ pGlobal)
  (hfGlobal : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
  (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
  (rule : A.DegreeGlobalizationAt (E := Eout) (fun x => ((f x - lam : ℝ) : ℂ))
    degree netExponent pGlobal cost)
variable (hkernel : Nonempty G) (hcutoff : qnum.Hchild ≤ S.value)
variable (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
variable (hdensity : qnum.δ ≤ Real.exp (-cost)) (hlog : cost + 1 ≤ qnum.v)
variable (hprescribed : cost + 1 ≤ s.Ppres) (hstride : 2 * Real.exp cost ≤ qnum.Ptail)

include ν hpPrep hRprep hchild hgain hReady
  hregularityBudget hpGlobal hchartGlobal hscoreGlobal hmassGlobal hfGlobal hlam rule
  hkernel hcutoff hlate hdensity hlog hprescribed hstride in

theorem relativePatchSliceConclusion_of_normalized_ready_s2_oai

    (centerLift : ∀ j, (prep j).space) (Hinitial : ℕ)
    (hInitialCutoff : Hinitial = qnum.Hchild)
    (hinit : AllocatedNormalizedCandidateConclusion (E := Eout) (A := A)
      degree (fun k => Hinitial ≤ A.sides k) centerLift productive childCost chartCost
      (originalRank + degree * E) f lam)
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
    (sampleFn : (X → ℤ) → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (readFn : (X → ℤ) → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I Eout n B → ℤ)
    (hglobal : ∀ base, AllocatedCenteredRecoveredSampleReadAt B (fun j : Fin m => (prep j).space)
      bW b hb o S hR hσ (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
      (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value)
      spatial kernel block Crecovered center centerLift base (sampleFn base) (readFn base))
    (hrecovered : ∀ z ∈ productive, AllocatedCenteredFramedRecoveredSampleAt
      B (fun j : Fin m => (prep j).space) b hb o S hR hσ
      (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
      centerLift z.1.val z.2.val (sampleFn z.1.val z.2.val)
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val)))
    (hgood : let primes := boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊
      letI := actualForecastPrimeNeZero primes (boundedPrimes_prime _)
      ∀ z ∈ productive,
      (∏ p ∈ primes, p ^ largestTestedBadDepth (fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
        (allocatedActualPrimeBad (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value)
          spatial kernel block primes (modularForecastRankConstant m Dmod : ℝ)) p
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val))) ≤
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius (gainLog + 8)))
    (hdet : ∀ z ∈ productive, ∀ t : Fin 2,
      spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog) / 2 <
        |Matrix.det (fun i j : X => spatialMatrixNormalizedEntries eSpatial A.widths z.2.val (t,j,i))|)
    {Pdim Qstride : ℝ}
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card X : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdim)
    (hnX : 0 < Fintype.card X) (hgainLog : 0 ≤ gainLog) (hgainDim : gainLog ≤ Pdim)
    (hstrideSource : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hPmodel : preparedCenteredForecastSpatialLog Pdim ≤ s.P)
    (hPbad : 2 * Fintype.card X * Qstride +
      (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11 ≤ s.Pbad)
    (hcost : 0 ≤ cost) (hE : 0 ≤ Ecompare) (hτ1 : τ ≤ 1)
    (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s
      (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) (2 * Ptest) Ecompare ≤ S.value)
    (hξsmall : ξ ≤ Real.exp (-(2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14)))
    (hEdata : Ecompare + 8 ≤ qLate.E)
    (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
      (Dmod + Fintype.card (Σ j, I j))
      (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
      (Ecompare + 4) (2 * Ptest) s.Pτ) ≤ (N i : ℝ))
    (hcoord : ∀ j, (Fintype.card (prep j).Coord : ℝ) ≤ preparationP)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤
      Real.exp ((preparationP + 2) ^ preparedIntegralBasisExponent m))
    {ε crtBudget : ℝ} (hεpos : 0 < ε) (hεone : ε ≤ 1)
    (hCRTbudget : 1 ≤ crtBudget) (hCRTinv : ε⁻¹ ≤ crtBudget)
    (hCRTtest : Ptest ∈ Set.Icc 0 crtBudget)
    (hCRTbad : s.Pbad ∈ Set.Icc 0 crtBudget)
    (hCRTpres : s.Ppres ∈ Set.Icc 0 crtBudget)
    (hm : m ≤ degree) (hprepared : (∑ j, (prep j).rank) ≤ m * D)
    {budget : ℝ}
    (hFinalBudget : 1 ≤ budget)
    (hRankBudget : childCost + (degree : ℝ) * D ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hMatrixBudget : 2048 * crtBudget ^ 3 + (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (hPatchCostBudget : 2 * (((childCost + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2) + 2) ^ (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 1 ≤ budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
    (hScoreBudget : cost ≤ budget)
    (hFinalLarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (N i : ℝ)) :
    RelativePatchSliceConclusion degree N f ((1 - ε) * lam) (originalRank + degree * (D + E))
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  classical
  obtain ⟨d, patch, hd, hreturned, hLip, hcenters, hP⟩ := hinit
  let := polynomialShearIndexFintype patch.weight (fun i => patch.weight_pos i)
  obtain ⟨P, hsub, hcenterP, hkeepP⟩ := hP
  obtain ⟨hchildBudget, _, _⟩ := allocatedNormalizedBudget_bounds degree
    (Fintype.card (LayerSamplerVariables G I n B)) hchild
  obtain ⟨path, hglobalPath, hprimes, hexponent, hbase, hnoise, hsample, hread, hcenterPath⟩ :=
    exists_allocatedRetainedActualForecastFactory (A := A) bW centerLift sampleFn readFn
      productive P.productive hsub Dmod spatial kernel block eSpatial Pdim gainLog Qstride
      Ptest Crecovered hglobal hrecovered hgood hdet hPdim hX hvars hnX hgainLog hgainDim
      hstrideSource s hPmodel hPbad
  have hkeep (z : P.productive) (k) :
      (P.chart z).keep k ↔ qnum.Hchild ≤ A.sides k := by
    rw [hkeepP z, hInitialCutoff]
  have hRank : ((d + degree * D : ℕ) : ℝ) ≤ budget :=
    (relative_actual_rank_reconstruction_budget hchild hd (le_refl (D : ℝ))).trans hRankBudget
  have hconclusion := P.relativePatchSliceConclusion_of_normalized_prepared_degreeRule_s2
    (prep := prep) (hprep := hprep) (hpPrep := hpPrep) (hRprep := hRprep)
    (s := s) (qnum := qnum) (qLate := qLate) (bW := bW) (ν := ν)
    (patch := patch) (f := f) (lam := lam) (hchild := hchild) (hd := hd)
    (hchildBudget := hchildBudget) (hcenters := hcenters) (hLip := hLip)
    (hgain := hgain) (hReady := hReady) (hregularityBudget := hregularityBudget)
    (hpGlobal := hpGlobal) (hchartGlobal := hchartGlobal) (hscoreGlobal := hscoreGlobal)
    (hmassGlobal := hmassGlobal) (hfGlobal := hfGlobal) (hlam := hlam) (rule := rule)
    (path := path) (hkeep := hkeep) (hkernel := hkernel) (hcutoff := hcutoff)
    (hlate := hlate) (hdensity := hdensity) (hlog := hlog)
    (hprescribed := hprescribed) (hstride := hstride)
    hδlate hHlate hvlate hTaillate hξone hmargin hu hp hbudget hSliceLog hC hCp hCap
    hAccuracy hPrecision hdirect hexcess hSlice hcostSlice hchartCost htest hσ1 e
    hU hEcompare hcommonTest hσbound hκ hEprec hlarge hRrank hrank
    (fun z => sampleFn z.val.1.val) (fun z => readFn z.val.1.val) hglobalPath
    hcost hE hτ1 hfloor hξsmall hEdata hNgrid hprimes hexponent hbase hnoise hsample hread
    (fun z => (hcenterPath z).trans hcenterP.symm) hcoord hbW
    hεpos hεone hCRTbudget hCRTinv hCRTtest hCRTbad hCRTpres
    (d₀ := d) (old := D) (removed := D) hm hprepared le_rfl (by simp)
    hFinalBudget hRank hDmodBudget hMatrixBudget hPatchCostBudget hcapLog hPnative
    hScoreBudget hFinalLarge
  apply hconclusion.mono _ le_rfl
  apply relative_actual_rank_reconstruction_le (removed := D) (by omega)
  simpa using hreturned

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.relativePatchSliceConclusion_of_normalized_ready_s2_oai := @OAI.Erdos3.VectorPolynomial.relativePatchSliceConclusion_of_normalized_ready_s2_oai
