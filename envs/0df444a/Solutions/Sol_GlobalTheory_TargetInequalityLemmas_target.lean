-- Prove2me | solution 1 for GlobalTheory.TargetInequalityLemmas.target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:40:11.686054+00:00
-- url     : https://prove2.me/submissions/bde6e30e-43e8-42c2-af0b-463d5fc21f91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerRest
import Theorems.Thm_GlobalTheory_TargetInequalityLemmas_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TargetInequalityLemmas
open Polynomial
namespace GlobalTheory.TargetInequalityLemmas
theorem _root_.solution : ∀ {R F K : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field F] [inst_3 : Algebra R F] [IsFractionRing R F] [inst_5 : Field K] [inst_6 : Algebra R K] [inst_7 : Algebra F K] [IsScalarTower R F K] (θ z : K), Membership.mem (Algebra.adjoin F (Singleton.singleton θ)) z → Exists fun (d : R) ↦ And (Ne d (0 : R)) (Membership.mem (Algebra.adjoin R (Singleton.singleton θ)) (HMul.hMul ((Algebra.algebraMap R K) d) z)) :=
  fun θ z hz => main θ z hz
end GlobalTheory.TargetInequalityLemmas
