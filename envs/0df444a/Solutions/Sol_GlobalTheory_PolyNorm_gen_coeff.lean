-- Prove2me | solution 1 for GlobalTheory.PolyNorm.gen_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:55.156342+00:00
-- url     : https://prove2.me/submissions/df0ad989-44ab-41e8-bd5e-2e255e7372da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm
namespace GlobalTheory.PolyNorm
theorem _root_.solution {r : ℕ} {K : Type} [CommRing K] (F : K[X]) (h : F.natDegree < r) :
    gen (fun i : Fin r => F.coeff i) = F := by
  unfold gen
  rw [Fin.sum_univ_eq_sum_range (fun i => monomial i (F.coeff i)) r]
  exact (as_sum_range' F r h).symm
end GlobalTheory.PolyNorm
