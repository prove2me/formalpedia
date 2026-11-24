-- Prove2me | solution 1 for GlobalTheory.AinfXi.isLocalRing_preTilt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:41.810073+00:00
-- url     : https://prove2.me/submissions/f4555b65-8b81-46e2-90cf-ed172da6427f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrder
import Theorems.Thm_GlobalTheory_AinfXi_isUnit_of_coeff_zero
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_O_local
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_quot_nontrivial


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
theorem _root_.solution (hv : v.Integers O) : IsLocalRing (PreTilt O p) := by
  have : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  haveI : IsLocalRing O := ReciprocityTheory.PGsh.Ainf.O_local O hv
  haveI : Nontrivial (ModP O p) := ReciprocityTheory.PGsh.Ainf.quot_nontrivial _ (by
    rw [Ne, Ideal.span_singleton_eq_top]; exact Fact.out)
  haveI : IsLocalRing (ModP O p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (PreTilt.coeff 0 a) with h | h
  · exact Or.inl (isUnit_of_coeff_zero h)
  · exact Or.inr (isUnit_of_coeff_zero (by rwa [map_sub, map_one]))
end GlobalTheory.AinfXi
