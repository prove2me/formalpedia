-- Prove2me | solution 1 for GroundTheory.PAdicHodge.iterate_frobeniusEquiv_symm_mem_integerTilt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:09:08.575411+00:00
-- url     : https://prove2.me/submissions/450aa7db-a320-4d17-ad66-f069bdd2ea2c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltDegree
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid

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
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution {N : IntermediateField K♭ C♭}
    [FiniteDimensional K♭ N] {a : 𝒪C♭} (ha : a ∈ integerTilt K C p N) (n : ℕ) :
    (frobeniusEquiv 𝒪C♭ p).symm^[n] a ∈ integerTilt K C p N := by
  induction n with
  | zero => exact ha
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact frobeniusEquiv_symm_mem_integerTilt ih
end GroundTheory.PAdicHodge
