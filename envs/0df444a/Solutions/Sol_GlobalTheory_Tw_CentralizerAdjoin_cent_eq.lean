-- Prove2me | solution 1 for GlobalTheory.Tw.CentralizerAdjoin.cent_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:04.478353+00:00
-- url     : https://prove2.me/submissions/6273ae4a-cae7-49ef-abdd-e7e7dc598005

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_mem_adjoin_of_commute
import Theorems.Thm_P2M_GlobalTheory_Tw_CentralizerAdjoin_isUnit_theta__778c4ab65804
import Theorems.Thm_GlobalTheory_Tw_Model_adj_eq
import Theorems.Thm_GlobalTheory_Tw_Model_theta_mul
import Theorems.Thm_GlobalTheory_Tw_Model_theta_theta


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.CentralizerAdjoin
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
open GlobalTheory.Tw.Model
namespace GlobalTheory.Tw.CentralizerAdjoin
theorem _root_.solution {δ : Matrix (Fin n) (Fin n) R} (hδ : Reg δ) :
    cent δ = {g | g ∈ Algebra.adjoin R {nrm δ} ∧ g * adj δ g = 1} := by
  have hu := hδ.1
  have hd := (Matrix.isUnit_iff_isUnit_det δ).mp hu
  ext g
  constructor
  · rintro ⟨hgU, hgd⟩
    have hc : g * nrm δ = nrm δ * g :=
      calc g * nrm δ = g * δ * theta δ := by rw [nrm, Matrix.mul_assoc]
        _ = δ * theta g * theta δ := by rw [hgd]
        _ = δ * theta (g * δ) := by rw [theta_mul, Matrix.mul_assoc]
        _ = δ * theta (δ * theta g) := by rw [hgd]
        _ = nrm δ * g := by rw [theta_mul, theta_theta hgU, nrm, Matrix.mul_assoc]
    refine ⟨mem_adjoin_of_commute _ g hδ.2 hc, ?_⟩
    rw [adj_eq hu hgU, ← hgd, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hgU)]
  · rintro ⟨-, h⟩
    have hgd := Matrix.isUnit_det_of_right_inverse h
    have hgU : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr hgd
    have hU1 : IsUnit (δ * theta g * δ⁻¹) :=
      (hu.mul (isUnit_theta' hgU)).mul (Matrix.isUnit_nonsing_inv_iff.mpr hu)
    have h2 : (δ * theta g * δ⁻¹)⁻¹ = g⁻¹ := by
      rw [← adj_eq hu hgU]; exact (Matrix.inv_eq_right_inv h).symm
    have e := congrArg Inv.inv h2
    rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU1),
      Matrix.nonsing_inv_nonsing_inv _ hgd] at e
    refine ⟨hgU, ?_⟩
    calc g * δ = δ * theta g * δ⁻¹ * δ := by rw [e]
      _ = δ * theta g := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
end GlobalTheory.Tw.CentralizerAdjoin
