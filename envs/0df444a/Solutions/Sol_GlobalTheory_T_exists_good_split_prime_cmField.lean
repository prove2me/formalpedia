-- Prove2me | solution 1 for GlobalTheory.T.exists_good_split_prime_cmField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:08:13.232806+00:00
-- url     : https://prove2.me/submissions/906b14cc-6b63-45a6-8c38-998678db38c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsGoodSplitPrimeCmField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsGoodSplitPrimeCmFieldStatement
import Theorems.Thm_GlobalTheory_SW_SplitPrime_exists_goodPrime


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (m : ℕ), 0 < m → ∃ (q : ℕ) (P : Ideal (𝓞 E)), GoodPrime m q P := by
  first | exact @GlobalTheory.SW.SplitPrime.exists_goodPrime | exact GlobalTheory.SW.SplitPrime.exists_goodPrime | (intros; apply GlobalTheory.SW.SplitPrime.exists_goodPrime <;> assumption)
end _root_.GlobalTheory.T
