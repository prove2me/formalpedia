-- Prove2me | solution 1 for GlobalTheory.UnitaryZariskiDense.det_one_add_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:27.252151+00:00
-- url     : https://prove2.me/submissions/30ff730a-f8fe-4f39-af86-ea936db81692

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense
variable {ι : Type} {a : ℕ}
namespace GlobalTheory.UnitaryZariskiDense
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : Aᴴ = -A) :
    (1 + A).det ≠ 0 := by
  intro h0
  have hpd : (1 + Aᴴ * A).PosDef :=
    Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self A)
  have e : 1 + Aᴴ * A = (1 + A)ᴴ * (1 + A) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hA]
    noncomm_ring
  have := hpd.det_pos.ne'
  rw [e, Matrix.det_mul, h0, mul_zero] at this
  exact this rfl
end GlobalTheory.UnitaryZariskiDense
