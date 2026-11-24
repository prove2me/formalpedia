-- Prove2me | solution 1 for GlobalTheory.Tw.CentralizerAdjoin.adj_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:54:35.861749+00:00
-- url     : https://prove2.me/submissions/dd615780-22cf-4ec6-b69b-bae609cef06e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_inv_mem_adjoin_of_isUnit
import Theorems.Thm_P2M_GlobalTheory_Tw_CentralizerAdjoin_adj_mul__bed2d37a429b
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_adj_semi
import Theorems.Thm_P2M_GlobalTheory_Tw_CentralizerAdjoin_adj_one__bd9885609913
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_adj_algebraMap
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_isUnit_nrm
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_adj_nrm

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
theorem _root_.solution {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (g : Matrix (Fin n) (Fin n) R)
    (hg : g ∈ Algebra.adjoin R {nrm δ}) :
    adj δ g ∈ Algebra.adjoin R {nrm δ} ∧ adj δ (adj δ g) = g := by
  have hN := isUnit_nrm hδ
  have hNd := (Matrix.isUnit_iff_isUnit_det _).mp hN
  have hadd : ∀ x y : Matrix (Fin n) (Fin n) R, adj δ (x + y) = adj δ x + adj δ y := fun x y => by
    simpa using adj_semi δ 1 x y
  have hinvN : adj δ (nrm δ)⁻¹ = nrm δ := by
    have h1 : adj δ (nrm δ)⁻¹ * (nrm δ)⁻¹ = 1 := by
      calc adj δ (nrm δ)⁻¹ * (nrm δ)⁻¹ = adj δ (nrm δ)⁻¹ * adj δ (nrm δ) := by rw [adj_nrm hδ]
        _ = adj δ (nrm δ * (nrm δ)⁻¹) := (adj_mul' hδ _ _).symm
        _ = 1 := by rw [Matrix.mul_nonsing_inv _ hNd, adj_one' hδ]
    calc adj δ (nrm δ)⁻¹ = adj δ (nrm δ)⁻¹ * (nrm δ)⁻¹ * nrm δ := by
          rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hNd, Matrix.mul_one]
      _ = nrm δ := by rw [h1, Matrix.one_mul]
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx, adj_nrm hδ, hinvN]
    exact ⟨inv_mem_adjoin_of_isUnit hN, rfl⟩
  | algebraMap r =>
    rw [adj_algebraMap hδ, adj_algebraMap hδ, star_star]
    exact ⟨Subalgebra.algebraMap_mem _ _, rfl⟩
  | add x y _ _ hx hy =>
    rw [hadd, hadd, hx.2, hy.2]
    exact ⟨add_mem hx.1 hy.1, rfl⟩
  | mul x y _ _ hx hy =>
    rw [adj_mul' hδ, adj_mul' hδ, hx.2, hy.2]
    exact ⟨mul_mem hy.1 hx.1, rfl⟩
end GlobalTheory.Tw.CentralizerAdjoin
