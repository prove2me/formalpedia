-- Prove2me | solution 1 for GlobalTheory.CNorm.herbPhi_arith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:06:51.206647+00:00
-- url     : https://prove2.me/submissions/711bf69a-2c5a-44a5-92e7-e2202368c8be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowPrimeRangeEqIteratedDifferenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionFiniteKerRangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormDifferenceIndexIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexRangeKerIterateEndomorphismStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution (q h0 h1 a t bI bT cI cT i c : ℕ) (hi : i ≠ 0) (hcT : cT ≠ 0)
    (e1 : a * bT * cT = bI * cI * t) (e2 : cI * c ^ q = i ^ q * cT)
    (e3 : h0 * i * bT = bI * h1 * c) :
    h0 ^ q * a * bT ^ (q + 1) = h1 ^ q * t * bI ^ (q + 1) := by
  have hne : i ^ q * cT ≠ 0 := mul_ne_zero (pow_ne_zero _ hi) hcT
  apply mul_right_cancel₀ hne
  calc h0 ^ q * a * bT ^ (q + 1) * (i ^ q * cT) = (h0 * i * bT) ^ q * (a * bT * cT) := by ring
    _ = (bI * h1 * c) ^ q * (bI * cI * t) := by rw [e1, e3]
    _ = h1 ^ q * t * bI ^ (q + 1) * (cI * c ^ q) := by ring
    _ = _ := by rw [e2]
end GlobalTheory.CNorm
