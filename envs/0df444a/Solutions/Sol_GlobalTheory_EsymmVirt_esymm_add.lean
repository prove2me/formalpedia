-- Prove2me | solution 1 for GlobalTheory.EsymmVirt.esymm_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:41:50.206044+00:00
-- url     : https://prove2.me/submissions/16910bc9-8b7c-4bd8-a8af-39d2bd698082

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterEsymmRootsCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MultisetPowerSumNewtonIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EsymmMemVirtualCharactersOfPowerSumEigenvalues
import Theorems.Thm_GlobalTheory_EsymmVirt_coeff_prod_one_add

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
theorem _root_.solution (s t : Multiset ℂ) (n : ℕ) :
    (s + t).esymm n = ∑ i ∈ Finset.range (n + 1), s.esymm i * t.esymm (n - i) := by
  rw [← coeff_prod_one_add, Multiset.map_add, Multiset.prod_add, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_add]
end GlobalTheory.EsymmVirt
