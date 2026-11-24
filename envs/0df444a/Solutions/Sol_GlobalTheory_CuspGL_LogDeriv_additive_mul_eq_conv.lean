-- Prove2me | solution 1 for GlobalTheory.CuspGL.LogDeriv.additive_mul_eq_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:07:06.121033+00:00
-- url     : https://prove2.me/submissions/90cfbf4d-2cec-44f8-a9d9-36815b545649

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveMulEqVonMangoldtConvolution
import Theorems.Thm_GlobalTheory_CuspGL_LogDeriv_conv_congr_monic
import Theorems.Thm_GlobalTheory_CuspGL_LogDeriv_pow_mul_conv
import Theorems.Thm_GlobalTheory_CuspGL_LogDeriv_additive_mul_conv
import Theorems.Thm_GlobalTheory_CuspGL_LogDeriv_pow_natDegree_ne_one
import Theorems.Thm_GlobalTheory_CuspGL_LogDeriv_eq_zero_of_rec
import Theorems.Thm_GlobalTheory_CuspGL_LogDeriv_mangoldt_one
import Theorems.Thm_GlobalTheory_CuspGL_LogDeriv_conv_at_one
import Theorems.Thm_GlobalTheory_T_additive_eq_polynomialVonMangoldt_convolution_one
import Theorems.Thm_GlobalTheory_T_monicFactorizationConvolution_finite_comm_assoc_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.LogDeriv
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL.LogDeriv
theorem _root_.solution (F : Type) [Field F] (q : ℕ) (hq : 2 ≤ q) (s m : F[X] → ℂ)
    (hs : IsAdditive s) (_hm1 : m 1 = 1)
    (hm : ∀ P : F[X], P.Monic → (q : ℂ) ^ P.natDegree * m P = conv (fun _ => 1) m P)
    (P : F[X]) (hP : P.Monic) :
    s P * m P = conv (fun D => mangoldt s D / ((q : ℂ) ^ D.natDegree - 1)) m P := by
  set L : F[X] → ℂ := fun D => mangoldt s D / ((q : ℂ) ^ D.natDegree - 1) with hL
  set o : F[X] → ℂ := fun _ => 1 with ho
  have hs1 : s 1 = 0 := by
    have := hs 1 1 monic_one monic_one
    rw [mul_one] at this
    linear_combination -this
  have hσL : ∀ D : F[X], D.Monic → (q : ℂ) ^ D.natDegree * L D = (L + mangoldt s) D := by
    intro D hD
    by_cases h0 : D.natDegree = 0
    · rw [hD.natDegree_eq_zero.mp h0]
      simp [hL, mangoldt_one]
    · have := pow_natDegree_ne_one hq h0
      simp only [hL, Pi.add_apply]
      field_simp
      ring
  have hA : ∀ Q : F[X], Q.Monic → (q : ℂ) ^ Q.natDegree * (s Q * m Q) =
      conv (conv (mangoldt s) o) m Q + conv o (fun D => s D * m D) Q := by
    intro Q hQ
    rw [mul_left_comm, hm Q hQ, additive_mul_conv hs _ _ hQ]
    congr 1
    refine conv_congr_monic (fun D hD => ?_) (fun _ _ => rfl) Q
    rw [← (GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one F s hs).1 D hD]
    simp [ho]
  have hB : ∀ Q : F[X], Q.Monic → (q : ℂ) ^ Q.natDegree * conv L m Q =
      conv (conv (mangoldt s) o) m Q + conv o (conv L m) Q := by
    intro Q hQ
    have H := (GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add F Q hQ).2
    rw [pow_mul_conv _ _ _ hQ, conv_congr_monic hσL hm Q, (H L (mangoldt s) (conv o m)).2.2.1,
      (H (mangoldt s) o m).2.1, add_comm, ← (H L o m).2.1, ← (H o L m).2.1]
    congr 1
    exact conv_congr_monic (fun D hD => ((GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add F D hD).2 L o o).1) (fun _ _ => rfl) Q
  have hE := eq_zero_of_rec hq (E := (fun D => s D * m D) - conv L m)
    (by simp [hs1, conv_at_one, hL, mangoldt_one]) (fun Q hQ => by
      have H := (GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add F Q hQ).2
      rw [(H _ _ o).1, (H _ _ _).2.2.2, ← (H o _ o).1, ← (H o _ o).1, Pi.sub_apply, mul_sub,
        hA Q hQ, hB Q hQ]
      ring) P hP
  exact sub_eq_zero.mp hE
end GlobalTheory.CuspGL.LogDeriv
