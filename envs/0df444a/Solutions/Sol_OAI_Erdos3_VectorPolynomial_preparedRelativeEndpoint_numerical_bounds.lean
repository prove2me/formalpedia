-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedRelativeEndpoint_numerical_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T03:02:36.574167+00:00
-- url     : https://prove2.me/submissions/28a4bc86-57e4-4678-b448-4c47afa02d51

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1346
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedRelativeEndpointInputScale_setup_bounds

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointNumericalBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedRelativeEndpointUniformKnob_bounds (m : ℕ)
    {t seed childCost cost Ptest Ecompare D primitiveCap modelRequired nativeAmbient : ℝ}
    (ht : 0 ≤ t)
    (hseed : seed ≤ preparedRelativeEndpointGeometryScale m t)
    (hchild : childCost ≤ preparedRelativeEndpointGeometryScale m t)
    (hcost : cost ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hTest : Ptest ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hCompare : Ecompare ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hD : D ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hcap : primitiveCap ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hModel : modelRequired ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hAmbient : nativeAmbient ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t)) :
    let T := preparedRelativeEndpointGeometryScale m t
    let floorLog := (T + 10) ^ (2 * m + 20)
    let K := preparedRelativeEndpointUniformKnob m t
    1 ≤ K ∧ T ≤ K ∧
      preparedRelativeEndpointMinimumLog seed 0 childCost cost floorLog ≤ K ∧
      preparedRelativeEndpointGoodLog Ptest ≤ K ∧
      preparedRelativeEndpointSigmaLog D primitiveCap Ptest Ecompare cost m ≤ K ∧
      preparedRelativeEndpointCoarseLog D primitiveCap Ptest Ecompare ≤ K ∧
      preparedRelativeEndpointAmbientLog modelRequired nativeAmbient floorLog ≤ K := by
  intro T floorLog K
  have hT := (preparedRelativeEndpointGeometryScale_bounds m ht).1
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  let V := (T + preparedRelativeEndpointPerturbationExponent m) ^
    preparedRelativeEndpointPerturbationExponent m
  have hV0 : 0 ≤ V := by dsimp only [V]; positivity
  have hF0 : 0 ≤ floorLog := by dsimp only [floorLog]; positivity
  have hK : K = 4 * T + V + floorLog + 20 := rfl
  obtain ⟨hSigma, hCoarse⟩ :=
    (exists_preparedRelativeEndpointPerturbationLog_budget m).choose_spec.2
      hT0 hD hcap hTest hCompare hcost
  change preparedRelativeEndpointSigmaLog D primitiveCap Ptest Ecompare cost m ∈ Set.Icc 0 V at hSigma
  change preparedRelativeEndpointCoarseLog D primitiveCap Ptest Ecompare ∈ Set.Icc 0 V at hCoarse
  have hcommon : preparedSlicedForecastCommonFloorExponent 0 childCost cost floorLog ≤
      T + floorLog + 1 := by
    unfold preparedSlicedForecastCommonFloorExponent
    refine max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_)))
    · linarith only [hT0, hF0]
    · linarith only [hT0, hF0]
    · linarith only [hchild, hF0]
    · linarith only [hcost.2, hF0]
    · linarith only [hT0]
  have hMinimum : preparedRelativeEndpointMinimumLog seed 0 childCost cost floorLog ≤
      T + floorLog + 2 := by
    unfold preparedRelativeEndpointMinimumLog
    exact max_le (by linarith only [hseed, hF0]) (by linarith only [hcommon])
  have hGood : preparedRelativeEndpointGoodLog Ptest ≤ 2 * T + 1 := by
    unfold preparedRelativeEndpointGoodLog
    linarith only [hTest.2]
  have hEnd : preparedRelativeEndpointAmbientLog modelRequired nativeAmbient floorLog ≤
      T + floorLog := by
    unfold preparedRelativeEndpointAmbientLog
    exact max_le (by linarith only [hModel.2, hF0])
      (max_le (by linarith only [hAmbient.2, hF0]) (by linarith only [hT0]))
  exact ⟨by linarith only [hK, hT, hV0, hF0],
    by linarith only [hK, hT0, hV0, hF0],
    by linarith only [hMinimum, hK, hT0, hV0],
    by linarith only [hGood, hK, hT0, hV0, hF0],
    by linarith only [hSigma.2, hK, hT0, hF0],
    by linarith only [hCoarse.2, hK, hT0, hF0],
    by linarith only [hEnd, hK, hT0, hV0]⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

 theorem preparedRelativeEndpoint_numerical_bounds_oai
    (m earlyPower M nX Jalloc : ℕ)
    {B Pdim cost pRadius gainLog Qstride Pchart PF childCost u p budget seed : ℝ}
    (hB : 0 ≤ B)
    (hDbase : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ preparedRelativeEndpointInputBase earlyPower B)
    (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ preparedRelativeEndpointInputBase earlyPower B)
    (hPdim : Pdim ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hcost : cost ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hRadius : pRadius ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hGain : gainLog ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hStride : Qstride ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hChart : Pchart ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hPF : PF ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hChild : childCost ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hu : u ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hp : p ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hbudget : budget ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hseed : seed ≤ preparedRelativeEndpointInputBase earlyPower B) :
    let t := preparedRelativeEndpointInputScale m earlyPower B
    let T := preparedRelativeEndpointGeometryScale m t
    let K := preparedRelativeEndpointUniformKnob m t
    let Eearly := 2 * u + 4 * p + 12
    let nativeEarly := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride PF Pchart childCost Eearly
    let massEarly := preparedConcreteSlicedForecastMassLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride Pchart childCost Eearly
    let Ptest := preparedRelativeEndpointTestLog budget nativeEarly
    let Ecompare := preparedRelativeEndpointComparisonLog budget nativeEarly massEarly u p cost
    let nativeLate := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride PF Pchart childCost (Ecompare + 8)
    let massLate := preparedConcreteSlicedForecastMassLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride Pchart childCost (Ecompare + 8)
    let Pspatial := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
    let nativeAmbient := (max (max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1))
      (massLate + Ecompare + 8) + nativeForecastAmbientExponent m) ^ nativeForecastAmbientExponent m
    let modelRequired := actualForecastDataModelRequired budget nativeEarly massEarly u p
    let floorLog := (T + 10) ^ (2 * m + 20)
    1 ≤ T ∧ t ≤ T ∧ T ≤ K ∧ 1 ≤ K ∧
    Ptest ∈ Set.Icc 0 T ∧ Ecompare ∈ Set.Icc 0 T ∧
    nativeEarly ∈ Set.Icc 0 T ∧ massEarly ∈ Set.Icc 0 T ∧
    nativeLate ∈ Set.Icc 0 T ∧ massLate ∈ Set.Icc 0 T ∧
    modelRequired ∈ Set.Icc 0 T ∧ nativeAmbient ∈ Set.Icc 0 T ∧
    preparedRelativeEndpointMinimumLog seed 0 childCost cost floorLog ≤ K ∧
    preparedRelativeEndpointGoodLog Ptest ≤ K ∧
    preparedRelativeEndpointSigmaLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      preparedSlicedForecastPrimitiveCap Ptest Ecompare cost m ≤ K ∧
    preparedRelativeEndpointCoarseLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      preparedSlicedForecastPrimitiveCap Ptest Ecompare ≤ K ∧
    preparedRelativeEndpointAmbientLog modelRequired nativeAmbient floorLog ≤ K ∧ floorLog ≤ K := by
  intro t T K Eearly nativeEarly massEarly Ptest Ecompare nativeLate massLate Pspatial nativeAmbient modelRequired floorLog
  have hInput := preparedRelativeEndpointInputScale_bounds m earlyPower hB
  have ht : 0 ≤ t := zero_le_one.trans hInput.1
  have hGeo := preparedRelativeEndpointGeometryScale_bounds m ht
  have hbase : preparedRelativeEndpointInputBase earlyPower B ≤ t := hInput.2.1
  have lift {a : ℝ} (ha : a ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B)) :
      a ∈ Set.Icc 0 t := ⟨ha.1, ha.2.trans hbase⟩
  have liftT {a : ℝ} (ha : a ∈ Set.Icc 0 t) : a ∈ Set.Icc 0 T :=
    ⟨ha.1, ha.2.trans hGeo.2.1⟩
  obtain ⟨hSpatial, _, _, _, _, hD, hCap, _, _, _, _, _, _, _⟩ :=
    preparedRelativeEndpointInputScale_setup_bounds m earlyPower M nX Jalloc hB hDbase hDmod
      hPdim hcost hRadius hGain hStride hChart hPF hChild
  obtain ⟨hTest, hCompare, hnEarly, hmEarly, hnLate, hmLate, hModel, hAmbient⟩ :=
    (exists_preparedRelativeEndpointForecast_budget m).choose_spec.2 M nX Jalloc ht
      (hDbase.trans hbase) (hDmod.trans hbase) (lift hPdim) (lift hcost) (lift hRadius)
      (lift hGain) (lift hStride) (lift hPF) (lift hChart) (lift hChild) (lift hu)
      (lift hp) (lift hbudget) hSpatial
  have up {a : ℝ} (ha : a ∈ Set.Icc 0 ((t + preparedRelativeEndpointForecastExponent m) ^
      preparedRelativeEndpointForecastExponent m)) : a ∈ Set.Icc 0 T :=
    ⟨ha.1, ha.2.trans hGeo.2.2⟩
  have hTest' : Ptest ∈ Set.Icc 0 T := up hTest
  have hCompare' : Ecompare ∈ Set.Icc 0 T := up hCompare
  have hnEarly' : nativeEarly ∈ Set.Icc 0 T := up hnEarly
  have hmEarly' : massEarly ∈ Set.Icc 0 T := up hmEarly
  have hnLate' : nativeLate ∈ Set.Icc 0 T := up hnLate
  have hmLate' : massLate ∈ Set.Icc 0 T := up hmLate
  have hModel' : modelRequired ∈ Set.Icc 0 T := up hModel
  have hAmbient' : nativeAmbient ∈ Set.Icc 0 T := up hAmbient
  obtain ⟨hK, hTK, hMin, hGood, hSigma, hCoarse, hEnd⟩ :=
    preparedRelativeEndpointUniformKnob_bounds m ht
      (hseed.trans (hbase.trans hGeo.2.1))
      ((lift hChild).2.trans hGeo.2.1) (liftT (lift hcost)) hTest' hCompare'
      (liftT hD) (liftT hCap) hModel' hAmbient'
  have hFloor : floorLog ≤ K :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hEnd
  exact ⟨hGeo.1, hGeo.2.1, hTK, hK, hTest', hCompare', hnEarly', hmEarly', hnLate', hmLate',
    hModel', hAmbient', hMin, hGood, hSigma, hCoarse, hEnd, hFloor⟩

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedRelativeEndpoint_numerical_bounds_oai := @OAI.Erdos3.VectorPolynomial.preparedRelativeEndpoint_numerical_bounds_oai
