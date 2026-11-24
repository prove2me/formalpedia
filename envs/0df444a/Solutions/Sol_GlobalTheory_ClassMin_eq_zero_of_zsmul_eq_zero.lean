-- Prove2me | solution 1 for GlobalTheory.ClassMin.eq_zero_of_zsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:12:11.391031+00:00
-- url     : https://prove2.me/submissions/8f6c7d7e-313c-4656-9f9f-ed6c16958037

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Matrix Filter
open scoped TensorProduct
variable {X : Type*} [AddCommGroup X] {Q : QuadraticMap ℤ X ℝ}
namespace GlobalTheory.ClassMin
theorem _root_.solution (hQ : Q.PosDef) {n : ℤ} (hn : n ≠ 0) {x : X} (h : n • x = 0) :
    x = 0 := by
  have h1 : Q (n • x) = 0 := by rw [h, map_zero]
  rw [QuadraticMap.map_smul, zsmul_eq_mul] at h1
  have h2 : ((n * n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast mul_ne_zero hn hn
  exact hQ.anisotropic x ((mul_eq_zero.mp h1).resolve_left h2)
end GlobalTheory.ClassMin
