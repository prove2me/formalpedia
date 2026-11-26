-- Prove2me | solution 1 for LowRankUnivariateSOS.hasPeelingWitness_of_factor_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:50.078659+00:00
-- url     : https://prove2.me/submissions/185ada87-adf9-488b-89d9-1c69d695051f

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
import Theorems.Thm_LowRankUnivariateSOS_rotatedPeelingData_of_factor_step
import Theorems.Thm_LowRankUnivariateSOS_hasPeelingWitness_of_rotated

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution {u u0 : UPair} {a gStart gNext : Poly}
    (hu : u = scalePair a u0)
    (hcop : IsCoprime u0.fst u0.snd)
    (hfg : QuadraticFactorStep u0 gStart gNext) :
    HasPeelingWitness u (scalePair gStart u0) (scalePair gNext u0) := by
  exact hasPeelingWitness_of_rotated (rotatedPeelingData_of_factor_step hu hcop hfg)
end LowRankUnivariateSOS
