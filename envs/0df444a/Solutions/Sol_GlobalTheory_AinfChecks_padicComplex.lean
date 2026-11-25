-- Prove2me | solution 1 for GlobalTheory.AinfChecks.padicComplex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:08:33.368897+00:00
-- url     : https://prove2.me/submissions/1d4c8f87-c424-4e58-b096-952bc2459916

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_NonemptyAlgebra
import Theorems.Thm_GlobalTheory_PadicComplexHost_main
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_flatW__52449b1b4fd3
import Theorems.Thm_ReciprocityTheory_PGsh_exists_pflat
import Theorems.Thm_ReciprocityTheory_PGsh_kerTheta
import Theorems.Thm_ReciprocityTheory_PGsh_regular
import Theorems.Thm_ReciprocityTheory_PGsh_xiNu


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WittVector Ideal ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.AinfChecks
open WittVector Ideal
namespace GlobalTheory.AinfChecks
namespace _root_.GlobalTheory.AinfChecks
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    ∃ (_ : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p])) (_ : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]),
      (∃ pflat : PreTilt 𝓞_ℂ_[p] p, pflat.untilt = ((p : ℕ) : 𝓞_ℂ_[p])) ∧
      (∃ ε : PreTilt 𝓞_ℂ_[p] p,
        IsPrimitiveRoot (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε).untilt) p) ∧
      _root_.ReciprocityTheory.PGsh.KerThetaStatement p 𝓞_ℂ_[p] ∧ _root_.ReciprocityTheory.PGsh.XiNuStatement p ℂ_[p] Valued.v 𝓞_ℂ_[p] ∧
      _root_.ReciprocityTheory.PGsh.RegularStatement p 𝓞_ℂ_[p] ∧ _root_.ReciprocityTheory.PGsh.FlatW'Statement p 𝓞_ℂ_[p] := by
  obtain ⟨hunit, hcomp, ε, hv, hε⟩ := _root_.GlobalTheory.PadicComplexHost.main p
  have hker : _root_.ReciprocityTheory.PGsh.KerThetaStatement p 𝓞_ℂ_[p] := _root_.ReciprocityTheory.PGsh.kerTheta ℂ_[p] Valued.v hv
  refine ⟨hunit, hcomp, _root_.ReciprocityTheory.PGsh.exists_pflat ℂ_[p] Valued.v 𝓞_ℂ_[p] hv, ⟨ε, hε⟩, hker,
    _root_.ReciprocityTheory.PGsh.xiNu p ℂ_[p] Valued.v 𝓞_ℂ_[p] hker, ?_, _root_.ReciprocityTheory.PGsh.flatW' p 𝓞_ℂ_[p]⟩
  refine _root_.ReciprocityTheory.PGsh.regular p 𝓞_ℂ_[p] fun x hx => ?_
  have h : ((p : ℂ_[p]) * (x : ℂ_[p])) = 0 := by
    simpa using congrArg (fun y : 𝓞_ℂ_[p] => (y : ℂ_[p])) hx
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  · exact Subtype.ext h
end _root_.GlobalTheory.AinfChecks
end GlobalTheory.AinfChecks
