-- Prove2me | solution 1 for GlobalTheory.SW.PosSum.exists_repr_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:28:29.833728+00:00
-- url     : https://prove2.me/submissions/d9dd37ed-cea6-40fc-821f-bd446c26105a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableExpNegTraceTotallyPositiveHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.PosSum
namespace GlobalTheory.SW.PosSum
theorem _root_.solution (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : 𝓞 E) (j : Module.Free.ChooseBasisIndex ℤ (𝓞 E)),
      |(((RingOfIntegers.basis E).repr x j : ℤ) : ℝ)| ≤ C * house (x : E) := by
  let L := (canonicalEmbedding.latticeBasis E).equivFun.toLinearMap.toContinuousLinearMap
  refine ⟨‖L‖, norm_nonneg _, fun x j => ?_⟩
  have h1 := L.le_opNorm (canonicalEmbedding E x)
  have h2 := norm_le_pi_norm (L (canonicalEmbedding E x)) j
  have h3 : L (canonicalEmbedding E x) j = (((RingOfIntegers.basis E).repr x j : ℤ) : ℂ) := by
    have := canonicalEmbedding.integralBasis_repr_apply E (x : E) j
    rw [NumberField.integralBasis_repr_apply] at this
    simpa [L] using this
  rw [h3, Complex.norm_intCast] at h2
  exact h2.trans h1
end GlobalTheory.SW.PosSum
