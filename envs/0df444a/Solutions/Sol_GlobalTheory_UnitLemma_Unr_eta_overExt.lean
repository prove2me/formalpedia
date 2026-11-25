-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.eta_overExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:54:24.714684+00:00
-- url     : https://prove2.me/submissions/11d35113-6aaf-4439-ae00-5b405f32c6bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddValNormUnramifiedInvolutionFieldExtEqMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBasisTraceInvolutionDetUnitUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetTraceGramBlockMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetInvAlgBaseChangeUnramifiedOdd
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_mul_of_ne
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_pow_of_ne
import Theorems.Thm_GlobalTheory_T_addVal_norm_unramifiedInvolutionFieldExt_eq_mul
import Theorems.Thm_GlobalTheory_T_det_trace_gram_block_eq_pow_mul_norm_det
import Theorems.Thm_GlobalTheory_T_exists_basis_trace_involution_det_unit_unramified
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_eta_gram


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → Odd d → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (x : B.Aˣ), B.σ (x : B.A) = x → K'.eta ((overExt φ B ψ hψ hσ).gramDet (x : B.A)) = K.eta (B.gramDet (x : B.A)) := by
  intro K K' d φ hU hd B ψ hψ hσ x _
  have hd0 : 0 < d := hd.pos
  obtain ⟨w, hw0, hwv⟩ := GlobalTheory.T.exists_basis_trace_involution_det_unit_unramified K K' d φ hU hd0
  letI : Algebra K.E K'.E := φ.toAlgebra
  haveI : Module.Finite K.E K'.E := Module.finite_of_finrank_pos (by rw [hU.2.2.2.2]; exact hd0)
  letI : Algebra K'.E B.A := ψ.toAlgebra
  haveI : IsScalarTower K.E K'.E B.A := IsScalarTower.of_algebraMap_eq fun e => (hψ e).symm
  haveI : Module.Finite K'.E B.A := (overExt φ B ψ hψ hσ).fd
  set u := Module.finBasis K'.E B.A with hu
  set H : Matrix (Fin (Module.finrank K'.E B.A)) (Fin (Module.finrank K'.E B.A)) K'.E :=
    Matrix.of fun i j => Algebra.trace K'.E B.A ((x : B.A) * u i * B.σ (u j)) with hH
  have h1 : (overExt φ B ψ hψ hσ).gramDet (x : B.A) = H.det := rfl
  set b0 := w.smulTower u with hb0
  set e := b0.indexEquiv (Module.finBasis K.E B.A) with he
  rw [h1, ← Orbit.eta_gram B _ (b0.reindex e)]
  have h2 : (Matrix.of fun i j => B.herm x ((b0.reindex e) i) ((b0.reindex e) j)) =
      (Matrix.of fun (p q : Fin d × Fin (Module.finrank K'.E B.A)) =>
        Algebra.trace K.E K'.E (w p.1 * H p.2 q.2 * K'.c (w q.1))).submatrix e.symm e.symm := by
    ext i j
    simp only [Module.Basis.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, hb0,
      Module.Basis.smulTower_apply, InvAlg.herm, hH]
    rw [← Algebra.trace_trace (S := K'.E)]
    refine congrArg (Algebra.trace K.E K'.E) ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul B.σ]
    have hc : ∀ y : K'.E, B.σ (algebraMap K'.E B.A y) = algebraMap K'.E B.A (K'.c y) := hσ
    rw [hc]
    have : (x : B.A) * (algebraMap K'.E B.A (w (e.symm i).1) * u (e.symm i).2) *
        (algebraMap K'.E B.A (K'.c (w (e.symm j).1)) * B.σ (u (e.symm j).2)) =
        (w (e.symm i).1 * K'.c (w (e.symm j).1)) • ((x : B.A) * u (e.symm i).2 * B.σ (u (e.symm j).2)) := by
      rw [Algebra.smul_def, map_mul]; ring
    rw [this, LinearMap.map_smul, smul_eq_mul]; ring
  rw [h2, Matrix.det_submatrix_equiv_self, GlobalTheory.T.det_trace_gram_block_eq_pow_mul_norm_det w H (fun l => K'.c (w l))]
  by_cases hH0 : H.det = 0
  · rw [hH0, Algebra.norm_zero, mul_zero]; simp [UQ.eta, val]
  have hN : Algebra.norm K.E H.det ≠ 0 := by
    rw [Ne, Algebra.norm_eq_zero_iff]; exact hH0
  unfold UQ.eta
  rw [val_mul_of_ne (pow_ne_zero _ hw0) hN, val_pow_of_ne hw0, hwv, GlobalTheory.T.addVal_norm_unramifiedInvolutionFieldExt_eq_mul K K' d φ hU hd0, mul_zero, zero_add,
    zpow_mul]
  rw [zpow_natCast, hd.neg_one_pow]
end GlobalTheory.UnitLemma.Unr
