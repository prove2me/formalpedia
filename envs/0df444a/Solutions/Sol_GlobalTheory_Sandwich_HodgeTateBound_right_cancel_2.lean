-- Prove2me | solution 2 for GlobalTheory.Sandwich.HodgeTateBound.right_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:31:33.52992+00:00
-- url     : https://prove2.me/submissions/fde349b3-bee5-41c8-b512-431e6ed36196

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.Sandwich.HodgeTateBound
variable {A O : Type} [CommRing A] [CommRing O] {h : ℕ}
namespace GlobalTheory.Sandwich.HodgeTateBound
theorem _root_.solution [IsDomain A] {F G : Matrix (Fin h) (Fin h) A} {μ : A} (hμ : μ ≠ 0)
    (hGF : G * F = μ • (1 : Matrix (Fin h) (Fin h) A)) {X Y : Matrix (Fin h) (Fin h) A}
    (hX : X * F = Y * F) : X = Y := by
  have hdet : F.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hGF
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hμ h1.symm
  have h2 : X * F * F.adjugate = Y * F * F.adjugate := by rw [hX]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.mul_one] at h2
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h3
  exact mul_left_cancel₀ hdet h3
end GlobalTheory.Sandwich.HodgeTateBound
