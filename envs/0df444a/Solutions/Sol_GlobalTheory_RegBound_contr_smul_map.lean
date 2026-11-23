-- Prove2me | solution 1 for GlobalTheory.RegBound.contr_smul_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:22.895822+00:00
-- url     : https://prove2.me/submissions/2ac6cc84-ca57-45a6-8a7b-d18849647445

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
variable {L : Type} [Field L] [Algebra K L]
namespace GlobalTheory.RegBound
theorem _root_.solution (φ : L →ₗ[K] K) (c : L) (F : MvPolynomial σ K) :
    contr φ (c • map (algebraMap K L) F) = φ c • F := by
  ext m
  rw [coeff_contr, coeff_smul, coeff_smul, coeff_map, smul_eq_mul, mul_comm, ← Algebra.smul_def,
    map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
end GlobalTheory.RegBound
