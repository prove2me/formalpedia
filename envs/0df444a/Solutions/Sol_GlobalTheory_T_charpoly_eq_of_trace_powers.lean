-- Prove2me | solution 1 for GlobalTheory.T.charpoly_eq_of_trace_powers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:41:26.588462+00:00
-- url     : https://prove2.me/submissions/453dc8bd-c663-4f9d-b38b-31d89d5bf2da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyEqOfTracePowers
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyEqOfTracePowersStatement
import Theorems.Thm_GlobalTheory_TracePowCharpoly_charpoly_eq_of_trace_pow_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (f : Module.End ℂ V) (g : Module.End ℂ V'), (∀ k : ℕ, LinearMap.trace ℂ V (f ^ k) = LinearMap.trace ℂ V' (g ^ k)) → f.charpoly = g.charpoly := by
  first | exact @GlobalTheory.TracePowCharpoly.charpoly_eq_of_trace_pow_eq | exact GlobalTheory.TracePowCharpoly.charpoly_eq_of_trace_pow_eq | (intros; apply GlobalTheory.TracePowCharpoly.charpoly_eq_of_trace_pow_eq <;> assumption)
end _root_.GlobalTheory.T
