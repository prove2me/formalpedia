-- Prove2me | solution 1 for HlawkaCodex84SOSCache.small_certificates
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T06:28:49.426564+00:00
-- url     : https://prove2.me/submissions/f7508ba5-22e8-481e-9847-8cbd41825045

import Definitions.Def_HlawkaCodex84_SOSCertificateData
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open HlawkaCodex84SOSCache
theorem solution : (∀ i, 0 ≤ gramPivots i) ∧
(multiplier0 = multiplier0Lower * Matrix.diagonal multiplier0Pivots * multiplier0Lower.transpose) ∧
(∀ i, 0 ≤ multiplier0Pivots i) ∧
(multiplier1 = multiplier1Lower * Matrix.diagonal multiplier1Pivots * multiplier1Lower.transpose) ∧
(∀ i, 0 ≤ multiplier1Pivots i) ∧
(multiplier2 = multiplier2Lower * Matrix.diagonal multiplier2Pivots * multiplier2Lower.transpose) ∧
(∀ i, 0 ≤ multiplier2Pivots i) ∧
(multiplier3 = multiplier3Lower * Matrix.diagonal multiplier3Pivots * multiplier3Lower.transpose) ∧
(∀ i, 0 ≤ multiplier3Pivots i) ∧
(multiplier4 = multiplier4Lower * Matrix.diagonal multiplier4Pivots * multiplier4Lower.transpose) ∧
(∀ i, 0 ≤ multiplier4Pivots i) ∧
(multiplier5 = multiplier5Lower * Matrix.diagonal multiplier5Pivots * multiplier5Lower.transpose) ∧
(∀ i, 0 ≤ multiplier5Pivots i) ∧
(multiplier6 = multiplier6Lower * Matrix.diagonal multiplier6Pivots * multiplier6Lower.transpose) ∧
(∀ i, 0 ≤ multiplier6Pivots i) ∧
(multiplier7 = multiplier7Lower * Matrix.diagonal multiplier7Pivots * multiplier7Lower.transpose) ∧
(∀ i, 0 ≤ multiplier7Pivots i) ∧
(multiplier8 = multiplier8Lower * Matrix.diagonal multiplier8Pivots * multiplier8Lower.transpose) ∧
(∀ i, 0 ≤ multiplier8Pivots i) := by decide +kernel
#print axioms solution
