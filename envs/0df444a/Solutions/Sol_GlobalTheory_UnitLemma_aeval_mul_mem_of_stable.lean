-- Prove2me | solution 1 for GlobalTheory.UnitLemma.aeval_mul_mem_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:03:43.946814+00:00
-- url     : https://prove2.me/submissions/2cce7a2d-c200-400c-a3d1-ba434047ac1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralClosureFgDvrOfSeparableCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqSubmoduleMulLeftImageIntegralClosureOfSeparablStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfMulLeftCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonDenominatorAevalOfFgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenSmulAndSelfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteUnitOrbitsStableLatticesSeparable
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma
theorem _root_.solution {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {g : A} {M : Submodule O A}
    (hM : ∀ y ∈ M, g * y ∈ M) (p : O[X]) {m : A} (hm : m ∈ M) : aeval g p * m ∈ M := by
  induction p using Polynomial.induction_on with
  | C a => simpa [Algebra.smul_def] using M.smul_mem a hm
  | add p q hp hq => simpa [add_mul] using M.add_mem hp hq
  | monomial n a ih =>
    have := hM _ ih
    have e : aeval g (Polynomial.C a * X ^ (n + 1)) * m = g * (aeval g (Polynomial.C a * X ^ n) * m) := by
      simp only [map_mul, aeval_C, aeval_X, map_pow, pow_succ]; ring
    rw [e]; exact this
end GlobalTheory.UnitLemma
