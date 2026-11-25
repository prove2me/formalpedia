-- Prove2me | solution 1 for GlobalTheory.LatOrb.Stab.polyStable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:35:58.45372+00:00
-- url     : https://prove2.me/submissions/17b1a2e9-abb8-4a5b-8ccb-97c1f44dab79

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCyclicVectorOfSeparableCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAevalEqAevalMapOfCoprimeCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqSubmoduleMulLeftImageIntegralClosureOfSeparabl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitEqOfStableLattices
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map
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
open Polynomial Matrix GlobalTheory.LatOrb
noncomputable section
open GlobalTheory GlobalTheory.LatOrb GlobalTheory.LatOrb.Stab
namespace GlobalTheory.LatOrb.Stab
theorem _root_.solution {O K : Type} [CommRing O] [Field K] [Algebra O K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K))
    (hM : ∀ v ∈ M, γ *ᵥ v ∈ M) (r : O[X]) :
    ∀ v ∈ M, aeval γ (r.map (algebraMap O K)) *ᵥ v ∈ M := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq =>
    intro v hv
    rw [Polynomial.map_add, map_add, Matrix.add_mulVec]
    exact M.add_mem (hp v hv) (hq v hv)
  | monomial k a =>
    intro v hv
    have hpow : ∀ v ∈ M, (γ ^ k) *ᵥ v ∈ M := by
      induction k with
      | zero => intro v hv; simpa using hv
      | succ k ih =>
        intro v hv
        rw [pow_succ, ← Matrix.mulVec_mulVec]
        exact ih _ (hM v hv)
    rw [Polynomial.map_monomial, aeval_monomial, ← Matrix.mulVec_mulVec,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
      algebraMap_smul]
    exact M.smul_mem a (hpow v hv)
end GlobalTheory.LatOrb.Stab
