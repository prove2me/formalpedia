-- Prove2me | solution 1 for GlobalTheory.eigDim_ker_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:03.69909+00:00
-- url     : https://prove2.me/submissions/68aa1de5-da1e-44e4-a09c-2d4f47fbd963

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {p q : K[X]} (h : IsCoprime p q) :
    Module.finrank K (LinearMap.ker (aeval T (p * q))) =
      Module.finrank K (LinearMap.ker (aeval T p)) +
        Module.finrank K (LinearMap.ker (aeval T q)) := by
  rw [← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime T h]
  have hd := Polynomial.disjoint_ker_aeval_of_isCoprime T h
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (aeval T p))
    (LinearMap.ker (aeval T q))
  rw [hd.eq_bot] at hs
  simpa using hs
end GlobalTheory
