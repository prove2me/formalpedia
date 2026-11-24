-- Prove2me | solution 1 for GroundTheory.PAdicHodge.monic_monicOfCoeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:07:03.150722+00:00
-- url     : https://prove2.me/submissions/d502c080-409c-4a1b-8c1c-9287ab379a79

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField C p]
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution (e : ℕ) (a : ℕ → 𝒪C♭) : (monicOfCoeffs e a).Monic := by
  refine Polynomial.monic_X_pow_add ?_
  refine (Polynomial.degree_sum_le _ _).trans_lt ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe e)).2 fun m hm => ?_
  refine (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt ?_
  exact WithBot.coe_lt_coe.2 (Finset.mem_range.1 hm)
end GroundTheory.PAdicHodge
