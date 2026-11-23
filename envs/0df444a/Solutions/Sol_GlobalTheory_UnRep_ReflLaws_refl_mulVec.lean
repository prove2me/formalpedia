-- Prove2me | solution 1 for GlobalTheory.UnRep.ReflLaws.refl_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:06.608168+00:00
-- url     : https://prove2.me/submissions/39210960-eed9-492c-87e2-ce21f1e25313

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLaws
import Theorems.Thm_GlobalTheory_UnRep_ReflLaws_hermE_eq_dot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.ReflLaws
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E)
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.UnRep.ReflLaws
namespace _root_.GlobalTheory.UnRep.ReflLaws
theorem _root_.solution (x : Fin n → E) (u : E) (v : Fin n → E) :
    _root_.GlobalTheory.UnRep.refl c G x u *ᵥ v =
      v + ((u - 1) * _root_.GlobalTheory.UnRep.hermE c G v x /
        _root_.GlobalTheory.UnRep.hermE c G x x) • x := by
  unfold _root_.GlobalTheory.UnRep.refl
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    _root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot]
  congr 1
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    _root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot]
  ring
end _root_.GlobalTheory.UnRep.ReflLaws
end GlobalTheory.UnRep.ReflLaws
