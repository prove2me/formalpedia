-- Prove2me | solution 1 for GlobalTheory.HermUnimod.good_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:21:08.470801+00:00
-- url     : https://prove2.me/submissions/a9ec14f4-0c4d-42ad-b92d-c8f9185f72d7

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOne
import Theorems.Thm_GlobalTheory_HermUnimod_intg_mul
import Theorems.Thm_GlobalTheory_HermUnimod_intg_conjT
import Theorems.Thm_GlobalTheory_HermUnimod_norm_det_conjT
import Theorems.Thm_GlobalTheory_HermUnimod_good_sum
import Theorems.Thm_GlobalTheory_HermUnimod_sol_transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HermUnimod
variable {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]
namespace GlobalTheory.HermUnimod
theorem _root_.solution (hs : ∀ y : E, ‖star y‖ = ‖y‖)
    (piv : ∀ (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E), G.IsHermitian →
      Intg G → ‖G.det‖ = 1 → ∃ P : Matrix n n E, Intg P ∧ ‖P.det‖ = 1 ∧ ∃ k, (Pᴴ * G * P) k k = 1) :
    ∀ (m : ℕ) (n : Type) [Fintype n] [DecidableEq n], Fintype.card n = m → Good n E := by
  intro m
  induction m with
  | zero =>
    intro n _ _ hc G _ _ _
    haveI : IsEmpty n := Fintype.card_eq_zero_iff.1 hc
    refine ⟨1, fun i => isEmptyElim i, by simp, ?_⟩
    ext i
    exact isEmptyElim i
  | succ m ih =>
    intro n _ _ hc G hG hGi hGd
    haveI : Nonempty n := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨P, hPi, hPd, k, hk⟩ := piv n G hG hGi hGd
    have hM : (Pᴴ * G * P).IsHermitian := isHermitian_conjTranspose_mul_mul P hG
    have hMi : Intg (Pᴴ * G * P) := intg_mul (intg_mul (intg_conjT hs hPi) hGi) hPi
    have hMd : ‖(Pᴴ * G * P).det‖ = 1 := by
      rw [det_mul, det_mul, norm_mul, norm_mul, norm_det_conjT hs, hPd, hGd, one_mul, one_mul]
    let e : n ≃ {j // j ≠ k} ⊕ Unit :=
      (Equiv.optionSubtypeNe k).symm.trans (Equiv.optionEquivSumPUnit.{0, 0} _)
    have hc' : Fintype.card {j // j ≠ k} = m := by
      have := Fintype.card_congr (Equiv.optionSubtypeNe k)
      rw [Fintype.card_option] at this
      omega
    have hk' : reindex e e (Pᴴ * G * P) (Sum.inr ()) (Sum.inr ()) = 1 := by
      simpa [e, reindex_apply, Equiv.optionSubtypeNe] using hk
    obtain ⟨h, hi, hd, hh⟩ := good_sum hs (ih _ hc') (reindex e e (Pᴴ * G * P))
      (by simpa [reindex_apply] using hM.submatrix e.symm) (fun i j => hMi _ _)
      (by rw [det_reindex_self]; exact hMd) hk'
    obtain ⟨h₁, hi₁, hd₁, hh₁⟩ := sol_transfer hs e _ h hi hd hh
    refine ⟨P * h₁, intg_mul hPi hi₁, by rw [det_mul, norm_mul, hPd, hd₁, one_mul], ?_⟩
    rw [conjTranspose_mul, ← hh₁]
    simp only [Matrix.mul_assoc]
end GlobalTheory.HermUnimod
