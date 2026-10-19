-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.forecastFiber_ambient_bounded_original_twist_precision_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:15:30.265037+00:00
-- url     : https://prove2.me/submissions/95f38c8e-0de3-4b91-b67e-5800ae9763db

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B304
import Definitions.Def_OAIE3v2B266
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialForecastPath_denseFiber_ambient_original_twist_precision_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedExternalCandidateProblem_Conclusion_forecast_source_facts_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeDepthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem boundedPrimeProduct_captures {Q m : ℕ} (hm : 0 < m) (hmQ : m ≤ Q) :
    m ∣ boundedPrimeProduct Q := by
  have hQ : Q ≠ 0 := (hm.trans_le hmQ).ne'
  have hsub : m.primeFactors ⊆ boundedPrimes Q := by
    intro p hp
    have h := Nat.mem_primeFactors.mp hp
    exact (mem_boundedPrimes Q p).mpr ⟨h.1, (Nat.le_of_dvd hm h.2.1).trans hmQ⟩
  have hpow (p : ℕ) (hp : p ∈ m.primeFactors) :
      p ^ m.factorization p ∣ p ^ Nat.log p Q := by
    have hprime := (Nat.mem_primeFactors.mp hp).1
    apply Nat.pow_dvd_pow
    apply (Nat.le_log_iff_pow_le hprime.one_lt hQ).mpr
    exact (Nat.le_of_dvd hm (Nat.ordProj_dvd m p)).trans hmQ
  have hsmall : m ∣ ∏ p ∈ m.primeFactors, p ^ Nat.log p Q := by
    nth_rw 1 [Nat.prod_primeFactors_pow_factorization hm.ne']
    exact Finset.prod_dvd_prod_of_dvd _ _ hpow
  have hlarge := Finset.prod_dvd_prod_of_subset m.primeFactors (boundedPrimes Q)
    (fun p => p ^ Nat.log p Q) hsub
  have h := hsmall.trans hlarge
  have he : boundedPrimeProduct Q = ∏ p ∈ boundedPrimes Q, p ^ Nat.log p Q :=
    Finset.prod_coe_sort (boundedPrimes Q) (fun p => p ^ Nat.log p Q)
  rwa [he]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedTargetReal
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

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
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in

theorem referenceModulus_eq_boundedPrimeProduct (Q : ℕ)
    (hprimes : path.primes = boundedPrimes Q)
    (hexponent : path.exponent = fun p => Nat.log p Q) :
    path.referenceModulus = boundedPrimeProduct Q := by
  unfold referenceModulus
  rw [hexponent, hprimes]
  rfl

omit [Fintype Tsp] in

theorem dvd_referenceModulus_of_le_bound (Q : ℕ)
    (hprimes : path.primes = boundedPrimes Q)
    (hexponent : path.exponent = fun p => Nat.log p Q)
    {q : ℕ} (hq : 0 < q) (hqQ : q ≤ Q) :
    q ∣ path.referenceModulus := by
  rw [path.referenceModulus_eq_boundedPrimeProduct Q hprimes hexponent]
  exact boundedPrimeProduct_captures hq hqQ

end ActualFixedSpatialForecastPath
end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActualFiberSlicedBoundedTwistPrecision
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
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
variable (input : ActualFixedSpatialDenseSliceInput s qnum)
variable (hcost_match : input.cost = cost)

namespace ActualFixedSpatialForecastPath

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
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {E Ptest : ℝ}
variable (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
  s.D (s.D + (s.slicedComparisonSourceLog Ptest) + 4) (cost + 1) (2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14) m))
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Rrank : ℝ} (hEprec : 0 ≤ qLate.massLog + E + 8)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1)) (qLate.massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1)) (qLate.massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
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
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center path.base path.noise ≠ 0)
variable (hsampleAt : sampleFn path.noise = path.sample)
variable (hreadAt : readFn path.noise = path.read)

variable (hfinite : (integerBox physicalN).Nonempty)
variable (hcost : 0 ≤ cost) (hE : 0 ≤ E)
variable (hτ1 : τ ≤ 1)
variable (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) (2 * Ptest) E ≤ S.value)
variable (hξsmall : ξ ≤ Real.exp (-(2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14)))
variable (hEdata : E + 8 ≤ qLate.E)
variable (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
  (Dmod + Fintype.card (Σ j, I j)) (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
  (E + 4) (2 * Ptest) s.Pτ) ≤ (physicalN i : ℝ))

variable {earlyPnative earlyMassLog earlyCapLog earlyEdata : ℝ}
variable (earlyData : ActualForecastData physicalN originalpoly
  earlyPnative earlyMassLog earlyCapLog earlyEdata)
variable (hEarlyCenter : earlyData.centerConstant = fun j => (path.center j).val)
variable (hEarlyTarget : earlyData.target =
  (path.toDenseSliceMember input).slice.target (allocatedShortIntegerSelection U b S.value)
    s.hBactive o bW hb originalpoly hmem s.κ)

variable (hprimes : path.primes = boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊)
variable (hexponent : path.exponent = fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)

include hR hσ hdegree hξ hbox hframe hσbound
  ν hlattice hcompact hmargin htrimbase hκ hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hz hsampleAt hreadAt hfinite
  hcost hE hτ1 hfloor hξsmall hEdata hNgrid hcost_match hEarlyCenter hEarlyTarget
  hδlate hHlate hvlate hTaillate hprimes hexponent in

theorem denseFiber_ambient_bounded_original_twist_precision :
    ‖(input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun z => W.eval physicalN originalpoly
          (fun a => path.base a + integerPhysicalSite z.val path.noise a)) -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN originalpoly u.val * earlyData.target u)‖ ≤ Real.exp (-E) := by
  let q := W.modulus * W.cover
  have hqpos : 0 < q := Nat.mul_pos W.modulus_pos W.cover_pos
  let : NeZero q := ⟨hqpos.ne'⟩
  have hq : (q : ℝ) ≤ Real.exp (2 * Ptest) := by
    calc
      (q : ℝ) = (W.modulus : ℝ) * (W.cover : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp Ptest * Real.exp Ptest := mul_le_mul
        (W.modulus_bound.trans hpw) (W.cover_bound.trans hcw)
        (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * Ptest) := by rw [← Real.exp_add]; congr 1; ring
  have hqNat : q ≤ ⌈Real.exp (2 * Ptest)⌉₊ := by
    exact_mod_cast hq.trans (Nat.le_ceil _)
  have hqN : q ∣ path.referenceModulus :=
    path.dvd_referenceModulus_of_le_bound _ hprimes hexponent hqpos hqNat
  exact denseFiber_ambient_original_twist_precision_s2
    (s := s) (qLate := qLate) (hδlate := hδlate) (hHlate := hHlate)
    (hvlate := hvlate) (hTaillate := hTaillate)
    (path := path) (input := input) (hcost_match := hcost_match)
    (hb := hb) (o := o) (bW := bW) (W := W)
    (originalpoly := originalpoly) (hmem := hmem) (hdegree := hdegree)
    (ξ := ξ) (hξ := hξ) (hbox := hbox) (hframe := hframe)
    (hσbound := hσbound) (q := q)
    (hperiod := Nat.dvd_mul_right _ _) (hcover := Nat.dvd_mul_left _ _) (hqN := hqN)
    (ν := ν) (hmargin := hmargin) (htrimbase := htrimbase)
    (hκ := hκ) (hPtest := hPtest) (hLw := hLw) (hpw := hpw) (hcw := hcw)
    (hEprec := hEprec) (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank)
    (C := C) (hglobal := hglobal) (hz := hz) (hsampleAt := hsampleAt) (hreadAt := hreadAt)
    (hfinite := hfinite) (hcost := hcost) (hE := hE) (hτ1 := hτ1) (hq := hq)
    (hfloor := hfloor) (hξsmall := hξsmall) (hEdata := hEdata) (hNgrid := hNgrid)
    (earlyData := earlyData) (hEarlyCenter := hEarlyCenter) (hEarlyTarget := hEarlyTarget)

end ActualFixedSpatialForecastPath
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
variable (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
  s.D (s.D + (s.slicedComparisonSourceLog Ptest) + 4) (cost + 1) (2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14) m))
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
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1)) (qLate.massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1)) (qLate.massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
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
variable (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) (2 * Ptest) E ≤ S.value)
variable (hξsmall : ξ ≤ Real.exp (-(2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14)))
variable (hEdata : E + 8 ≤ qLate.E)
variable (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
  (Dmod + Fintype.card (Σ j, I j)) (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
  (E + 4) (2 * Ptest) s.Pτ) ≤ (physicalN i : ℝ))

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

include hR hσ hdegree hσbound ν hlattice hcompact hmargin hκ hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hcost hE hτ1 hfloor hξsmall hEdata hNgrid
  hEarlyCenter hδlate hHlate hvlate hTaillate hprimes hexponent
  hbase hnoise hsample hread in

theorem forecastFiber_ambient_bounded_original_twist_precision_s2_oai
    (input : ActualFixedSpatialDenseSliceInput s qnum)
    (hcost_match : input.cost = cost)
    (hTarget : earlyData.target = (path.toDenseSliceMember input).slice.target
      (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb originalpoly hmem s.κ) :
    ‖(input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun site => W.eval physicalN originalpoly
          (fun a => path.base a + integerPhysicalSite site.val path.noise a)) -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) A.integerBox_nonempty).complexMean
        (fun u => W.eval physicalN originalpoly u.val * earlyData.target u)‖ ≤ Real.exp (-E) := by

  obtain ⟨hframe, htrimbase, hz, hsampleAt, hreadAt⟩ := forecast_source_facts_s2 (s := s) (path := path) (hb := hb) (o := o) (originalpoly := originalpoly) (hmem := hmem) (ξ := ξ) (A := A) (out := out) (z := z)
    (bW := bW) (C := C) (hglobal := hglobal) (hbase := hbase) (hnoise := hnoise)
    (hsample := hsample) (hread := hread)
  exact ActualFixedSpatialForecastPath.denseFiber_ambient_bounded_original_twist_precision
    (m := m) (G := G) (I := I) (n := n) (B := B) (J := J) (U := U) (b := b)
    (R := R) (σ := σ) (S := S) (hR := hR) (hσ := hσ) (X := X) (Eout := Eout)
    (Dmod := Dmod) (Lrank := Lrank) (spatial := spatial) (kernel := kernel) (block := block)
    (Tsp := Tsp) (spatialEquiv := spatialEquiv) (physicalN := physicalN) (τ := τ)
    (cost := cost) (qnum := qnum) (δbase := δbase) (PpresBase := PpresBase)
    (periodCap := periodCap) (coverCap := coverCap) (Lip := Lip) (E := E) (Ptest := Ptest)
    (Rrank := Rrank) (center := center) (sampleFn := sampleFn) (readFn := readFn)
    (earlyPnative := earlyPnative) (earlyMassLog := earlyMassLog)
    (earlyCapLog := earlyCapLog) (earlyEdata := earlyEdata)
    (s := s) (qLate := qLate) (hδlate := hδlate) (hHlate := hHlate)
    (hvlate := hvlate) (hTaillate := hTaillate)
    (path := path) (input := input) (hcost_match := hcost_match)
    (hb := hb) (o := o) (bW := bW) (W := W)
    (originalpoly := originalpoly) (hmem := hmem) (hdegree := hdegree)
    (ξ := ξ) (hξ := A.narrow_pos) (hbox := A.size_pos) (hframe := hframe)
    (hσbound := hσbound) (ν := ν) (hmargin := hmargin) (htrimbase := htrimbase)
    (hκ := hκ) (hPtest := hPtest) (hLw := hLw) (hpw := hpw) (hcw := hcw)
    (hEprec := hEprec) (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank)
    (C := C) (hglobal := hglobal) (hz := hz)
    (hsampleAt := hsampleAt)
    (hreadAt := hreadAt)
    (hfinite := A.integerBox_nonempty) (hcost := hcost) (hE := hE) (hτ1 := hτ1)
    (hfloor := hfloor) (hξsmall := hξsmall) (hEdata := hEdata) (hNgrid := hNgrid)
    (earlyData := earlyData) (hEarlyCenter := hEarlyCenter) (hEarlyTarget := hTarget)
    (hprimes := hprimes) (hexponent := hexponent)

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.forecastFiber_ambient_bounded_original_twist_precision_s2_oai := @OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.forecastFiber_ambient_bounded_original_twist_precision_s2_oai
