-- Prove2me | solution 1 for GlobalTheory.DeligneSerre.eq_top_of_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:58:12.003161+00:00
-- url     : https://prove2.me/submissions/531d779e-c998-49e1-a36d-540511a1e587

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixExistsCommonEigenvectorMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteJointEigensystemsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatricesIntertwiningOfSemilinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormEigenvalueLeOneOfEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegralHeckeEigensystemDeligneSerre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.DeligneSerre
namespace GlobalTheory.DeligneSerre
theorem _root_.solution (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ)
    (σ : R →ₐ[O] Matrix (Fin n) (Fin n) O) (m : Ideal R) (hker : ∀ p, σ p = 0 → p ∈ m) (p : R)
    (hp : p ∈ m) (hu : IsUnit (σ p).det) : m = ⊤ := by
  set f := (σ p).charpoly with hf
  have hq : Polynomial.aeval p f ∈ m := by
    apply hker
    rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly]
  have h0 : algebraMap O R (f.coeff 0) ∈ m := by
    have h := hq
    rw [← Polynomial.X_mul_divX_add f, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
    exact (Submodule.add_mem_iff_right m (m.mul_mem_right _ hp)).1 h
  have hc : IsUnit (f.coeff 0) := by
    rw [Matrix.det_eq_sign_charpoly_coeff] at hu
    exact isUnit_of_mul_isUnit_right hu
  exact Ideal.eq_top_of_isUnit_mem m h0 (hc.map _)
end GlobalTheory.DeligneSerre
