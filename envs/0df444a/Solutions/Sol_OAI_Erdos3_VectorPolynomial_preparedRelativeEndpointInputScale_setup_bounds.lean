-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointInputScale_setup_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T03:00:03.703963+00:00
-- url     : https://prove2.me/submissions/9e7edd8e-eac5-4b6a-8be6-fca900f6ac68

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1346

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointNumericalBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedRelativeEndpointInputScale_setup_bounds_oai (m earlyPower M nX Jalloc : ℕ)
    {B Pdim cost pRadius gainLog Qstride Pchart PF childCost : ℝ} (hB : 0 ≤ B)
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
    (hChild : childCost ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B)) :
    let t := preparedRelativeEndpointInputScale m earlyPower B
    preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ∈ Set.Icc 0 t ∧
    preparedSlicedForecastBadLog m nX Qstride gainLog ∈ Set.Icc 0 t ∧
    cost + 1 ∈ Set.Icc 0 t ∧ gainLog + nX + 8 ∈ Set.Icc 0 t ∧
    pRadius ∈ Set.Icc 0 t ∧
    allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ∈ Set.Icc 0 t ∧
    preparedSlicedForecastPrimitiveCap ∈ Set.Icc 0 t ∧
    (m : ℝ) ≤ t ∧ ((nX + m * M : ℕ) : ℝ) ≤ t ∧ (nX : ℝ) ≤ t ∧
    allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 ∈ Set.Icc 0 t ∧
    preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ∈ Set.Icc 0 t ∧
    PF ∈ Set.Icc 0 t ∧ childCost + 1 ∈ Set.Icc 0 t := by
  intro t
  have ha := (preparedRelativeEndpointInputBase_bounds earlyPower hB).1
  obtain ⟨hP, hBad, hPres, hτ, hK, hD, hCap, hm, hDim, hnX, hscale, hJac, hF, hchild⟩ :=
    (exists_preparedSlicedForecastScalarEnvelope m).choose_spec.2 M nX Jalloc
      (zero_le_one.trans ha) hDbase hDmod hPdim hcost hRadius hGain hStride hChart hPF hChild
  have hW := (preparedRelativeEndpointInputScale_bounds m earlyPower hB).2.2
  have lift {a : ℝ}
      (h : a ∈ Set.Icc 0 ((preparedRelativeEndpointInputBase earlyPower B +
        preparedRelativeEndpointPrimitiveExponent m) ^ preparedRelativeEndpointPrimitiveExponent m)) :
      a ∈ Set.Icc 0 t := ⟨h.1, h.2.trans hW⟩
  exact ⟨lift hP, lift hBad, lift hPres, lift hτ, lift hK, lift hD, lift hCap,
    hm.trans hW, hDim.trans hW, hnX.trans hW, lift hscale, lift hJac, lift hF, lift hchild⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointInputScale_setup_bounds_oai := @OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointInputScale_setup_bounds_oai
