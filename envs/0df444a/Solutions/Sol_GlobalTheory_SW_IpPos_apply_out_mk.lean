-- Prove2me | solution 1 for GlobalTheory.SW.IpPos.apply_out_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:21:10.497328+00:00
-- url     : https://prove2.me/submissions/8f81a935-1f34-40b1-8e6c-4c8cfc467228

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBounds
import Theorems.Thm_GlobalTheory_SW_HaarLevel_periodic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.IpPos
open NumberField
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
open Matrix Complex
open scoped ComplexConjugate Real
open NumberField
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
omit [NumberField K] [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.IpPos
namespace _root_.GlobalTheory.SW.IpPos
theorem _root_.solution {R : ℕ} {φ : Matrix κ ι K → ℂ}
    (h : _root_.GlobalTheory.SW.HasLevel R φ) (x : Matrix κ ι K) :
    φ (QuotientAddGroup.mk (s := _root_.GlobalTheory.SW.perSub K κ ι R) x).out = φ x := by
  have hmem := QuotientAddGroup.eq.mp
    (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (s := _root_.GlobalTheory.SW.perSub K κ ι R) x)).symm
  rw [← _root_.GlobalTheory.SW.HaarLevel.periodic h x _ hmem, add_neg_cancel_left]
end _root_.GlobalTheory.SW.IpPos
end GlobalTheory.SW.IpPos
