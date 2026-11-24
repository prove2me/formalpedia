-- Prove2me | solution 1 for GlobalTheory.PrimTransc.exists_mul_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:54:46.289243+00:00
-- url     : https://prove2.me/submissions/b572551f-b258-485a-967f-9bdfe04e8e68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerRest
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveMonicSeparableSpecialization
import Theorems.Thm_GlobalTheory_TargetInequalityLemmas_target


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IntermediateField
noncomputable section
open GlobalTheory GlobalTheory.PrimTransc
namespace GlobalTheory.PrimTransc
theorem _root_.solution {R F K : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K] (θ z : K)
    (hz : z ∈ Algebra.adjoin F {θ}) :
    ∃ d : R, d ≠ 0 ∧ algebraMap R K d * z ∈ Algebra.adjoin R {θ} := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R F K h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 θ z hz; exact @_root_.GlobalTheory.TargetInequalityLemmas.target)
  | exact @_root_.GlobalTheory.TargetInequalityLemmas.target
  | exact _root_.GlobalTheory.TargetInequalityLemmas.target
  | (apply _root_.GlobalTheory.TargetInequalityLemmas.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetInequalityLemmas.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetInequalityLemmas.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetInequalityLemmas.target ..)
end GlobalTheory.PrimTransc
