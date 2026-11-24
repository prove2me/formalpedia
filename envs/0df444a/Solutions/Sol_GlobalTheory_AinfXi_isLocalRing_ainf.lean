-- Prove2me | solution 1 for GlobalTheory.AinfXi.isLocalRing_ainf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:26:18.671413+00:00
-- url     : https://prove2.me/submissions/6ce739ca-ac1a-4238-a516-0df17f0f5092

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrder
import Theorems.Thm_GlobalTheory_AinfXi_witt_isUnit
import Theorems.Thm_GlobalTheory_AinfXi_isDomain_ainf
import Theorems.Thm_GlobalTheory_AinfXi_isLocalRing_preTilt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
open GlobalTheory GlobalTheory.AinfXi
open GlobalTheory.Sandwich
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
namespace GlobalTheory.AinfXi
theorem _root_.solution (hv : v.Integers O) : IsLocalRing (Ainf p O) := by
  haveI := isDomain_ainf (p := p) hv
  haveI := isLocalRing_preTilt (p := p) hv
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (constantCoeff a) with h | h
  · exact Or.inl (witt_isUnit a h)
  · exact Or.inr (witt_isUnit _ (by rwa [map_sub, map_one]))
end GlobalTheory.AinfXi
