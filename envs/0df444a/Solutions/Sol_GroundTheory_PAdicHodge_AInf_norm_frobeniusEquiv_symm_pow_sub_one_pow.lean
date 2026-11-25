-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.norm_frobeniusEquiv_symm_pow_sub_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:11:29.039268+00:00
-- url     : https://prove2.me/submissions/8e8fcc34-37ad-49b9-860a-90b085f495d1

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaAInf
import Theorems.Thm_GroundTheory_PAdicHodge_frobeniusEquiv_symm_pow_apply_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
open _root_.WittVector
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution (ε : 𝒪♭) (N : ℕ) :
    ‖((_root_.frobeniusEquiv 𝒪♭ p).symm ^ N) ε - 1‖ ^ p ^ N = ‖ε - 1‖ := by
  rw [← norm_pow, sub_pow_char_pow, one_pow, frobeniusEquiv_symm_pow_apply_pow]
end GroundTheory.PAdicHodge.AInf
