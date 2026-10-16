-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointMinimumScale_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T03:23:05.429882+00:00
-- url     : https://prove2.me/submissions/6317bcc6-0f5a-40b4-a225-4def8ac2299e

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1327
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedSlicedForecastCommonFloor_bounds

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointSourceBounds
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical


namespace AllocatedExternalCandidateSampler

end AllocatedExternalCandidateSampler
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical


namespace AllocatedExternalCandidateSampler

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedRelativeEndpointMinimumScale_bounds_oai
    {seed : ℝ} (hseed : 0 ≤ seed) (periodLog childLog cost comparisonLog : ℝ) :
    let Lmin := preparedRelativeEndpointMinimumScale seed periodLog childLog cost comparisonLog
    let Pmin := preparedRelativeEndpointMinimumLog seed periodLog childLog cost comparisonLog
    0 ≤ Pmin ∧ 1 ≤ Lmin ∧ (Lmin : ℝ) ≤ Real.exp Pmin ∧
      ⌈Real.exp seed⌉₊ ≤ Lmin ∧
      preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog ≤ Lmin ∧
      preparedSlicedForecastChildSize childLog ≤ Lmin ∧
      2 * Real.exp cost ≤ (Lmin : ℝ) ∧
      (∀ T : ℕ, (T : ℝ) ≤ Real.exp periodLog → T ≤ Lmin) ∧
      (∀ Lcompare : ℕ, (Lcompare : ℝ) ≤ Real.exp comparisonLog → Lcompare ≤ Lmin) := by
  intro Lmin Pmin
  obtain ⟨hF, hL, hLexp, hchild, hcost, hperiod, hcompare⟩ :=
    preparedSlicedForecastCommonFloor_bounds periodLog childLog cost comparisonLog
  have hseedFloor : ⌈Real.exp seed⌉₊ ≤ Lmin := le_max_left _ _
  have hcommon : preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog ≤ Lmin :=
    le_max_right _ _
  have hseedP : seed + 1 ≤ Pmin := le_max_left _ _
  have hcommonP :
      preparedSlicedForecastCommonFloorExponent periodLog childLog cost comparisonLog + 1 ≤ Pmin :=
    le_max_right _ _
  refine ⟨by linarith only [hseed, hseedP],
    (one_le_ceil_exp seed).trans hseedFloor, ?_, hseedFloor, hcommon,
    hchild.trans hcommon, hcost.trans (Nat.cast_le.mpr hcommon),
    fun T hT => (hperiod T hT).trans hcommon,
    fun L hL => (hcompare L hL).trans hcommon⟩
  change ((max ⌈Real.exp seed⌉₊
    (preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_max]
  exact max_le ((ceil_exp_le_exp_add_one hseed).trans (Real.exp_le_exp.mpr hseedP))
    (hLexp.trans (Real.exp_le_exp.mpr hcommonP))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointMinimumScale_bounds_oai := @OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointMinimumScale_bounds_oai
