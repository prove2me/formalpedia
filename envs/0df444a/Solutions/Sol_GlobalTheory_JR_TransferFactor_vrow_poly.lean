-- Prove2me | solution 1 for GlobalTheory.JR.TransferFactor.vrow_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:48:54.998863+00:00
-- url     : https://prove2.me/submissions/ef567103-311a-40d8-8dca-a26577706c70

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDet
import Theorems.Thm_GlobalTheory_JR_TransferFactor_vrow_succ_cast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.TransferFactor
variable {k : Type} [CommRing k] {r : ℕ}
namespace GlobalTheory.JR.TransferFactor
theorem _root_.solution (Y : Gl r k) (i : ℕ) : ∃ p : Polynomial k, p.coeff i = 1 ∧ (∀ N, i < N → p.coeff N = 0) ∧
    (fun l => vrow Y (i + 1) (Fin.castSucc l)) = Y.2.2.1 ᵥ* Polynomial.aeval Y.1 p := by
  induction i with
  | zero =>
    refine ⟨1, by simp, fun N hN => ?_, ?_⟩
    · rw [Polynomial.coeff_one]; simp; omega
    · funext l
      rw [vrow_succ_cast]
      simp [vrow, Pi.single_apply, Fin.castSucc_ne_last, Matrix.vecMul, dotProduct, Matrix.one_apply_ne' (Fin.castSucc_ne_last _), Matrix.one_apply]
  | succ i ih =>
    obtain ⟨p, h1, h2, h3⟩ := ih
    refine ⟨p * Polynomial.X + Polynomial.C (vrow Y (i + 1) (Fin.last r)), ?_, fun N hN => ?_, ?_⟩
    · rw [Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_C, h1]; simp
    · rw [Polynomial.coeff_add, Polynomial.coeff_C]
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      rw [Polynomial.coeff_mul_X, h2 M (by omega)]; simp
    · funext l
      rw [vrow_succ_cast, h3]
      simp [map_add, Polynomial.aeval_X, Polynomial.aeval_C, Matrix.vecMul_add, Matrix.vecMul_vecMul,
        Algebra.algebraMap_eq_smul_one, Matrix.vecMul_smul, mul_comm]
end GlobalTheory.JR.TransferFactor
