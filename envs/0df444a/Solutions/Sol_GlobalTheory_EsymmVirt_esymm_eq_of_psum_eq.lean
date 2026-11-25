-- Prove2me | solution 1 for GlobalTheory.EsymmVirt.esymm_eq_of_psum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:31:13.736588+00:00
-- url     : https://prove2.me/submissions/02537ba1-5e7e-4187-9369-cc8b634c06f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterEsymmRootsCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MultisetPowerSumNewtonIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EsymmMemVirtualCharactersOfPowerSumEigenvalues
import Theorems.Thm_P2M_GlobalTheory_EsymmVirt_esymm_zero__0112da44c67e
import Theorems.Thm_GlobalTheory_multiset_newton_psum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.EsymmVirt
namespace GlobalTheory.EsymmVirt
theorem _root_.solution (s t : Multiset ℂ)
    (h : ∀ j : ℕ, 0 < j → (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) (n : ℕ) :
    s.esymm n = t.esymm n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [esymm_zero', esymm_zero']
    have h1 := GlobalTheory.multiset_newton_psum s n hn
    have h2 := GlobalTheory.multiset_newton_psum t n hn
    have h3 : ∑ i ∈ Finset.Ioo 0 n, (-1) ^ i * s.esymm i * (s.map (· ^ (n - i))).sum
        = ∑ i ∈ Finset.Ioo 0 n, (-1) ^ i * t.esymm i * (t.map (· ^ (n - i))).sum := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_Ioo] at hi
      rw [ih i hi.2, h (n - i) (by omega)]
    have h4 : ((-1) ^ (n + 1) * (n : ℂ)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hn.ne')
    apply mul_left_cancel₀ h4
    linear_combination h2 - h1 + h n hn + h3
end GlobalTheory.EsymmVirt
