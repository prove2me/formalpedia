-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.good_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:44:40.091792+00:00
-- url     : https://prove2.me/submissions/611d7f94-6521-4382-91a5-93e8ea7fe3a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Nbr_conjI_conjI
import Theorems.Thm_GlobalTheory_SW_Nbr_absNorm_conjI

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
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.SW.Nbr
theorem _root_.solution {M q : ℕ} {P : Ideal (𝓞 E)} (h : GoodPrime M q P) : GoodPrime M q (conjI P) :=
  ⟨h.1, h.2.1, (absNorm_conjI P).trans h.2.2.1, by rw [conjI_conjI]; exact h.2.2.2.1.symm, h.2.2.2.2⟩
end GlobalTheory.SW.Nbr
