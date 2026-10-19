-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedRelativePositiveForecastSource_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:40:37.896858+00:00
-- url     : https://prove2.me/submissions/6614d1cb-8a30-4df6-a94a-a28fe9f9c116

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B271
import Definitions.Def_OAIE3v2B308
import Definitions.Def_OAIE3v2B277

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorNativeBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedModularGeneralDetectorResources_nativeBudget_eq
    {α : Type*} [Semiring α] (K : PreparedModularCanonicalDetectorResourceConstants)
    (dim : ℕ) (P L L' : α) :
    (preparedModularGeneralDetectorResources K dim P L).nativeBudget =
      (preparedModularGeneralDetectorResources K dim P L').nativeBudget := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerFixedCenterExcess
namespace OAI

section

namespace Erdos3

theorem positiveProjectionAccuracy_le_of_le {p q : ℝ} (hpq : p ≤ q) :
    positiveProjectionAccuracy q ≤ positiveProjectionAccuracy p := by
  unfold positiveProjectionAccuracy
  apply Real.exp_le_exp.mpr
  linarith only [hpq]

namespace VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.fixedCenterEndpointSiteNonempty
theorem NativeDetection.forecast_of_exp_threshold
    {degree : ℕ} {u p pSlice pTest pNative C capLog : ℝ}
    (hdirect : A.NativeDetection degree pSlice pTest pNative
      (Real.exp (-(2 * u + 4 * p + 8))))
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : capLog ≤ p) :
    A.NativeDetection degree pSlice pTest pNative
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C
        (Real.exp capLog)) := by
  have hthreshold := (forecastAugmentedUnitThreshold_bounds hu hp (Real.exp_nonneg _)
    (zero_le_one.trans hC) (Real.exp_le_exp.mpr hSliceLog) hCp
    (Real.exp_le_exp.mpr hCap)).2.2
  intro Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices origin step length
    hstep hshape hdense hcomplex hnorm signal hsignal hsupp hlarge
  exact hdirect Ddetect Vdetect slices origin step length
    hstep hshape hdense hcomplex hnorm signal hsignal hsupp (hthreshold.trans hlarge)

theorem fixedCenter_excess_max_one_of_precision
    (hξsource hξtarget : ξ ≤ 1)
    (hmarginSource hmarginTarget : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    (hbox : (integerBox N).Nonempty) {rawCap E precision : ℝ}
    (hPrecision : precision ≤ E)
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
      (A.law.siteLaw (A.physicalBox hξsource hmarginSource)) rawCap ≤
        6 * positiveProjectionAccuracy E) :
    (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξtarget hmarginTarget)) (max 1 rawCap) ≤
        6 * positiveProjectionAccuracy precision := by
  exact ((FiniteProbabilityWeights.excessMass_max_one_le
    (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty)
    (A.law.siteLaw (A.physicalBox hξtarget hmarginTarget)) rawCap).trans hexcess).trans
      (mul_le_mul_of_nonneg_left (positiveProjectionAccuracy_le_of_le hPrecision) (by norm_num))

theorem fixedCenter_forecast_source_bounds
    (hξsource hξtarget : ξ ≤ 1)
    (hmarginSource hmarginTarget : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    (hbox : (integerBox N).Nonempty)
    {degree : ℕ} {u p pSlice pTest pNative rawCap capLog E precision : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hRawCap : rawCap ≤ Real.exp p) (hCap : capLog ≤ p)
    (hPrecision : precision ≤ E)
    (hdirect : A.NativeDetection degree pSlice pTest pNative
      (Real.exp (-(2 * u + 4 * p + 8))))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
      (A.law.siteLaw (A.physicalBox hξsource hmarginSource)) rawCap ≤
        6 * positiveProjectionAccuracy E) :
    1 ≤ max 1 rawCap ∧ max 1 rawCap ≤ Real.exp p ∧
      A.NativeDetection degree pSlice pTest pNative
        (forecastAugmentedUnitThreshold u p
          (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B)))
          (max 1 rawCap) (Real.exp capLog)) ∧
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
        (A.law.siteLaw (A.physicalBox hξtarget hmarginTarget)) (max 1 rawCap) ≤
          6 * positiveProjectionAccuracy precision := by
  have hcap := marginalCap_max_one_exp_bound hp hRawCap
  exact ⟨hcap.1, hcap.2,
    NativeDetection.forecast_of_exp_threshold A hdirect hu hp hSliceLog hcap.1 hcap.2 hCap,
    A.fixedCenter_excess_max_one_of_precision hξsource hξtarget hmarginSource hmarginTarget
      hbox hPrecision hexcess⟩

end AllocatedExternalCandidateSampler
end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedEndpointRequirement
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedNestedFrontProjectionEnvelope_endpoint_le
    {K : Type*} [Fintype K]
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth : ℕ)
    (outer inner : K → ℕ) (native : K → ℝ)
    {x gainLog stageLog : ℝ} (endpoint : ℝ)
    (hA : 2 ≤ A) (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    endpoint ≤ preparedNestedFrontProjectionEnvelope A constants innerDepth
      outer inner native x gainLog stageLog endpoint := by
  have hsum : 0 ≤ ∑ k : K, preparedFiniteForwardFrontProjectionPrecision
      (preparedFiniteForwardModelPrecision A constants (inner k)
        (candidateNestedForwardSeed A constants innerDepth (outer k) x) gainLog stageLog)
      (preparedFiniteForwardWork A constants (inner k)
        (candidateNestedForwardSeed A constants innerDepth (outer k) x)) (native k) := by
    apply Finset.sum_nonneg
    intro k _
    have hseed := le_candidateNestedForwardSeed A constants innerDepth (outer k) hA hx
    have hseed0 := candidateNestedForwardSeed_nonneg A constants innerDepth (outer k) hx
    exact preparedFiniteForwardFrontProjectionPrecision_nonneg
      (preparedFiniteForward_model_precision_bounds A constants (inner k) hseed0
        ⟨hg.1, hg.2.trans hseed⟩ ⟨hs.1, hs.2.trans hseed⟩).1
      (preparedFiniteForwardWork_nonneg A constants (inner k) hseed0)
  unfold preparedNestedFrontProjectionEnvelope
  linarith only [hsum]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarNestedPowerDetection
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

theorem preparedRelativePositiveTerminalDetection
    (s Aexp Cdirect Cslice : ℕ) (constants : ℕ → ℕ)
    (Bstruct gainLog stageLog Plate : ℝ)
    (Pmaster : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s → ℝ)
    (hdirect : ∀ k : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s,
      A.NativeDetection (preparedFiniteNestedForwardAllDegreeDegree k)
        ((preparedFiniteForwardParameter Aexp constants
          (preparedFiniteNestedForwardAllDegreeStage k).val
          (preparedFiniteNestedForwardAllDegreeSeed Aexp constants Bstruct k) + Cslice) ^ Cslice)
        ((preparedFiniteForwardDetectorPolynomial s).eval₂ (Nat.castRingHom ℝ)
          (allocatedModelTestLog
            (preparedFiniteForwardPairedSourcePrecision Aexp Cdirect constants
              (preparedFiniteNestedForwardAllDegreeStage k).val
              (preparedFiniteNestedForwardAllDegreeIsDirect k)
              (preparedFiniteNestedForwardAllDegreeSeed Aexp constants Bstruct k) gainLog stageLog)
            (preparedFiniteForwardWork Aexp constants
              (preparedFiniteNestedForwardAllDegreeStage k).val
              (preparedFiniteNestedForwardAllDegreeSeed Aexp constants Bstruct k))))
        (preparedModularGeneralDetectorResources
          (preparedModularGeneralDetectorConstants m (preparedFiniteNestedForwardAllDegreeDegree k))
          (preparedFiniteNestedForwardAllDegreeDegree k + 1) (Pmaster k) Plate).nativeBudget
        (preparedFiniteNestedForwardFixedCenterThreshold Aexp constants Bstruct gainLog stageLog k)) :
    let seed := candidateNestedForwardSeed Aexp constants (s + 1) (2 * s + 2) Bstruct
    let u := preparedFiniteForwardModelPrecision Aexp constants (s + 1) seed gainLog stageLog
    let p := preparedFiniteForwardWork Aexp constants (s + 1) seed
    let sliceLog := (preparedFiniteForwardParameter Aexp constants (s + 1) seed + Cslice) ^ Cslice
    let testLog := (preparedFiniteForwardDetectorPolynomial s).eval₂ (Nat.castRingHom ℝ)
      (allocatedModelTestLog
        (preparedFiniteForwardSourcePrecision Aexp constants (s + 1) seed gainLog stageLog) p)
    let native := (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m 0) 1
      (Pmaster (preparedFiniteNestedForwardAllDegreeAnchor (2 * s + 2) (s + 1) s)) Plate).nativeBudget
    A.NativeDetection 0 sliceLog testLog native (Real.exp (-(2 * u + 4 * p + 8))) := by
  simpa only [preparedFiniteNestedForwardFixedCenterThreshold,
    preparedFiniteNestedForwardAllDegreeAnchor, preparedFiniteNestedForwardAllDegreeDegree,
    preparedFiniteNestedForwardAllDegreeStage, preparedFiniteNestedForwardAllDegreeIsDirect,
    preparedFiniteNestedForwardAllDegreeSeed, preparedFiniteForwardPairedSourcePrecision_model,
    Fin.val_zero, Nat.zero_add]
    using hdirect (preparedFiniteNestedForwardAllDegreeAnchor (2 * s + 2) (s + 1) s)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedRelativePositiveForecastSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

attribute [local instance] OAI.Erdos3.VectorPolynomial.instNonemptySite
theorem preparedRelativePositiveForecastSource_s2_oai
    (s Aexp Cdirect Cslice : ℕ) (constants : ℕ → ℕ)
    (Bstruct gainLog stageLog Plate : ℝ)
    (Pmaster : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s → ℝ)
    (hdirect : ∀ k : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s,
      A.NativeDetection (preparedFiniteNestedForwardAllDegreeDegree k)
        ((preparedFiniteForwardParameter Aexp constants
          (preparedFiniteNestedForwardAllDegreeStage k).val
          (preparedFiniteNestedForwardAllDegreeSeed Aexp constants Bstruct k) + Cslice) ^ Cslice)
        ((preparedFiniteForwardDetectorPolynomial s).eval₂ (Nat.castRingHom ℝ)
          (allocatedModelTestLog
            (preparedFiniteForwardPairedSourcePrecision Aexp Cdirect constants
              (preparedFiniteNestedForwardAllDegreeStage k).val
              (preparedFiniteNestedForwardAllDegreeIsDirect k)
              (preparedFiniteNestedForwardAllDegreeSeed Aexp constants Bstruct k) gainLog stageLog)
            (preparedFiniteForwardWork Aexp constants
              (preparedFiniteNestedForwardAllDegreeStage k).val
              (preparedFiniteNestedForwardAllDegreeSeed Aexp constants Bstruct k))))
        (preparedModularGeneralDetectorResources
          (preparedModularGeneralDetectorConstants m (preparedFiniteNestedForwardAllDegreeDegree k))
          (preparedFiniteNestedForwardAllDegreeDegree k + 1) (Pmaster k) Plate).nativeBudget
        (preparedFiniteNestedForwardFixedCenterThreshold Aexp constants Bstruct gainLog stageLog k))
    (hAexp : 2 ≤ Aexp) (hB : 0 ≤ Bstruct)
    (hgain : gainLog ∈ Set.Icc 0 Bstruct) (hstage : stageLog ∈ Set.Icc 0 Bstruct)
    (hξsource hξtarget : ξ ≤ 1)
    (hmarginSource hmarginTarget : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    (knob rawCap capLog : ℝ) :
    let seed := candidateNestedForwardSeed Aexp constants (s + 1) (2 * s + 2) Bstruct
    let u := preparedFiniteForwardModelPrecision Aexp constants (s + 1) seed gainLog stageLog
    let p := preparedFiniteForwardWork Aexp constants (s + 1) seed
    let sliceLog := (preparedFiniteForwardParameter Aexp constants (s + 1) seed + Cslice) ^ Cslice
    let testLog := (preparedFiniteForwardDetectorPolynomial s).eval₂ (Nat.castRingHom ℝ)
      (allocatedModelTestLog
        (preparedFiniteForwardSourcePrecision Aexp constants (s + 1) seed gainLog stageLog) p)
    let native := (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m 0) 1
      (Pmaster (preparedFiniteNestedForwardAllDegreeAnchor (2 * s + 2) (s + 1) s)) 0).nativeBudget
    let Econditional := preparedNestedFrontProjectionEnvelope Aexp constants (s + 1)
      (fun k : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s => k.1.val)
      (fun k : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s => k.2.1.val)
      (fun k : PreparedFiniteNestedForwardAllDegreeSlot (2 * s + 2) (s + 1) s =>
        (preparedModularGeneralDetectorResources
          (preparedModularGeneralDetectorConstants m (preparedFiniteNestedForwardAllDegreeDegree k))
          (preparedFiniteNestedForwardAllDegreeDegree k + 1) (Pmaster k) Plate).nativeBudget)
      Bstruct gainLog stageLog knob
    sliceLog * Fintype.card (LayerSamplerVariables G I n B) ≤ p →
    rawCap ≤ Real.exp p → capLog ≤ p →
    (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξsource hmarginSource)) rawCap ≤
        6 * positiveProjectionAccuracy Econditional →
    1 ≤ max 1 rawCap ∧ max 1 rawCap ≤ Real.exp p ∧
      A.NativeDetection 0 sliceLog testLog native
        (forecastAugmentedUnitThreshold u p
          (Real.exp (sliceLog * Fintype.card (LayerSamplerVariables G I n B)))
          (max 1 rawCap) (Real.exp capLog)) ∧
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
        (A.law.siteLaw (A.physicalBox hξtarget hmarginTarget)) (max 1 rawCap) ≤
          6 * positiveProjectionAccuracy knob := by
  intro seed u p sliceLog testLog native Econditional hSliceLog hRawCap hCap hexcess
  have hseed0 : 0 ≤ seed :=
    candidateNestedForwardSeed_nonneg Aexp constants (s + 1) (2 * s + 2) hB
  have hseed : Bstruct ≤ seed :=
    le_candidateNestedForwardSeed Aexp constants (s + 1) (2 * s + 2) hAexp hB
  have hu : 0 ≤ u := (preparedFiniteForward_model_precision_bounds Aexp constants (s + 1)
    hseed0 ⟨hgain.1, hgain.2.trans hseed⟩ ⟨hstage.1, hstage.2.trans hseed⟩).1
  have hp : 0 ≤ p := preparedFiniteForwardWork_nonneg Aexp constants (s + 1) hseed0
  have hPrecision : knob ≤ Econditional :=
    preparedNestedFrontProjectionEnvelope_endpoint_le Aexp constants (s + 1)
      _ _ _ knob hAexp hB hgain hstage
  have hterminal := preparedRelativePositiveTerminalDetection A s Aexp Cdirect Cslice constants
    Bstruct gainLog stageLog Plate Pmaster hdirect
  have hnative := preparedModularGeneralDetectorResources_nativeBudget_eq
    (preparedModularGeneralDetectorConstants m 0) 1
    (Pmaster (preparedFiniteNestedForwardAllDegreeAnchor (2 * s + 2) (s + 1) s)) Plate (0 : ℝ)
  dsimp only at hterminal
  rw [hnative] at hterminal
  exact A.fixedCenter_forecast_source_bounds hξsource hξtarget hmarginSource hmarginTarget
    A.integerBox_nonempty hu hp hSliceLog hRawCap hCap hPrecision hterminal hexcess

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedRelativePositiveForecastSource_s2_oai := @OAI.Erdos3.VectorPolynomial.preparedRelativePositiveForecastSource_s2_oai
