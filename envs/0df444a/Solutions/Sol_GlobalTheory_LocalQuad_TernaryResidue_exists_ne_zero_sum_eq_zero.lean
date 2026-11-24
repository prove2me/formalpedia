-- Prove2me | solution 1 for GlobalTheory.LocalQuad.TernaryResidue.exists_ne_zero_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:46:30.440456+00:00
-- url     : https://prove2.me/submissions/1fcac748-8255-418d-82b8-861bf3ada0cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNonzeroIsotropic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuedTernaryLtOne
import Theorems.Thm_GlobalTheory_NonzeroIsotropic_exists_nonzero_isotropic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.TernaryResidue
open MvPolynomial
namespace GlobalTheory.LocalQuad.TernaryResidue
theorem _root_.solution {k : Type*} [Field k] [Finite k] (a : Fin 3 → Fin 3 → k) :
    ∃ x : Fin 3 → k, x ≠ 0 ∧ ∑ i, ∑ j, a i j * x i * x j = 0 := by
  first
  | exact @_root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic
  | exact _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic
  | (apply _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic ..)
end GlobalTheory.LocalQuad.TernaryResidue
