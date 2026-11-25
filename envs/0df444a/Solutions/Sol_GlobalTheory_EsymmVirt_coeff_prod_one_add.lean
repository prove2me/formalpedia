-- Prove2me | solution 1 for GlobalTheory.EsymmVirt.coeff_prod_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:31:11.993982+00:00
-- url     : https://prove2.me/submissions/2b5d5661-0205-4fea-b69b-214dbb0e3b57

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
import Theorems.Thm_GlobalTheory_EsymmVirt_esymm_cons_succ

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
theorem _root_.solution (s : Multiset ℂ) (n : ℕ) :
    ((s.map fun a => (1 + C a * X : ℂ[X])).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, coeff_add, coeff_C_mul]
    cases n with
    | zero => simp [ih, esymm_zero']
    | succ n => rw [coeff_X_mul, ih, ih, esymm_cons_succ]
end GlobalTheory.EsymmVirt
