-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.mem_jacobson_of_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:21:48.217178+00:00
-- url     : https://prove2.me/submissions/b0f8626a-99ec-44f8-a8ee-146828b564ca

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaPeriod

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
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution {x : ACris K p} {m : ℕ} (h : x ^ m ∈ 𝔭) :
    x ∈ (⊥ : Ideal (ACris K p)).jacobson :=
  Ideal.isRadical_jacobson ⊥ ⟨m, IsAdicComplete.le_jacobson_bot _ h⟩
end GroundTheory.PAdicHodge.ACris
