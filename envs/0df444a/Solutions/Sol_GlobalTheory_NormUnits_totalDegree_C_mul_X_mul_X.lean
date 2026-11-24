-- Prove2me | solution 1 for GlobalTheory.NormUnits.totalDegree_C_mul_X_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:14:38.70951+00:00
-- url     : https://prove2.me/submissions/916d05c8-47f0-48d2-985f-4940d3a9b48f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TotalDegreeCMulXMulX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NormUnits
open MvPolynomial
variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
namespace GlobalTheory.NormUnits
theorem _root_.solution {k : Type} [Field k] (r : k) (i j : Fin 3) :
    (C r * (X i * X j) : MvPolynomial (Fin 3) k).totalDegree ≤ 2 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_mul _ _).trans ?_
  simp [totalDegree_X]
end GlobalTheory.NormUnits
