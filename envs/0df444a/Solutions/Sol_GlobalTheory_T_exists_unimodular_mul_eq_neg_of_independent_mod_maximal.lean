-- Prove2me | solution 1 for GlobalTheory.T.exists_unimodular_mul_eq_neg_of_independent_mod_maximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:19:55.538153+00:00
-- url     : https://prove2.me/submissions/fbe12638-184e-456b-a7bc-c5e9fc563d57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsUnimodularMulEqNegOfIndependentModMaximal
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsUnimodularMulEqNegOfIndependentModMaximalStatement
import Theorems.Thm_GlobalTheory_exists_unimodular_mul_eq_neg_of_indepMod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (n n0 : ℕ) (Φ : Fin n → Fin n0 → C), (∀ b c, V.Ge 0 (Φ b c)) → IndepMod V (fun c b => Φ b c) → n0 ≤ n ∧ ∃ Y : Matrix (Fin n) (Fin n) C, (∀ b b', V.Ge 0 (Y b b')) ∧ V.v Y.det = 0 ∧ ∀ (b : Fin n) (c : Fin n0), b.val < n0 → ∑ b', Y b b' * Φ b' c = if b.val = c.val then -1 else 0 := by
  first | exact @GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod | exact GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod | (intros; apply GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod <;> assumption)
end _root_.GlobalTheory.T
