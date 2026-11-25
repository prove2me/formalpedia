-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.part4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:39:33.96516+00:00
-- url     : https://prove2.me/submissions/bea7b88f-be94-4a0d-ad02-615d7a533988

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_pow_r_mulVec
import Theorems.Thm_GlobalTheory_JR_HermInv_comp_pow_ev
import Theorems.Thm_GlobalTheory_JR_HermInv_comp_pow_r
import Theorems.Thm_GlobalTheory_JR_HermInv_mom_sec_lt
import Theorems.Thm_GlobalTheory_JR_HermInv_hasInv_iff
import Theorems.Thm_GlobalTheory_JR_HermInv_gram
import Theorems.Thm_GlobalTheory_JR_HermInv_gram_hankel
import Theorems.Thm_GlobalTheory_JR_HermInv_det_unit
import Theorems.Thm_GlobalTheory_JR_HermInv_comp_map
import Theorems.Thm_GlobalTheory_JR_HermInv_HC_symm
import Theorems.Thm_P2M_GlobalTheory_JR_HermInv_conj_pow__9062d8b5e658
import Theorems.Thm_GlobalTheory_JR_HermInv_mulVec_ev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ}
namespace GlobalTheory.JR.HermInv
theorem _root_.solution [Unram F E] (a : Inv r F) (hΔ : Delta a ≠ 0) :
    (∃ X : Hn r F E, HasInv X a) ↔ ∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a).map (algebraMap F E) := by
  constructor
  · rintro ⟨X, hX⟩
    exact ⟨Bm X.toGl, gram_hankel X a hX⟩
  · rintro ⟨h, hh⟩
    have u := det_unit a hΔ h hh
    have hinv : h * h⁻¹ = 1 := mul_nonsing_inv _ u
    have hinv' : h⁻¹ * h = 1 := nonsing_inv_mul _ u
    set p : Fin r → E := fun i => algebraMap F E (a.1 i) with hp
    set CE := companion p with hCE
    have hCEm : CE = (companion a.1).map (algebraMap F E) := by rw [hCE, comp_map]
    have hCEH : CEᴴ = ((companion a.1)ᵀ).map (algebraMap F E) := by
      rw [hCEm]
      ext i j
      simp [conjTranspose_apply, star_algebraMap]
    have hM : CEᴴ * (hᴴ * h) = (hᴴ * h) * CE := by
      rw [hh, hCEH, hCEm, ← Matrix.map_mul, ← Matrix.map_mul, HC_symm]
    have hA : IsSelfAdjoint (h * CE * h⁻¹) := by
      show star (h * CE * h⁻¹) = h * CE * h⁻¹
      have e0 : star (h * CE * h⁻¹) = (h⁻¹)ᴴ * CEᴴ * hᴴ := by
        rw [star_eq_conjTranspose]; simp only [conjTranspose_mul, mul_assoc]
      rw [e0]
      calc (h⁻¹)ᴴ * CEᴴ * hᴴ = (h⁻¹)ᴴ * (CEᴴ * (hᴴ * h)) * h⁻¹ := by simp only [mul_assoc, hinv, mul_one]
        _ = (h⁻¹)ᴴ * ((hᴴ * h) * CE) * h⁻¹ := by rw [hM]
        _ = (h * h⁻¹)ᴴ * (h * CE * h⁻¹) := by rw [conjTranspose_mul]; simp only [mul_assoc]
        _ = h * CE * h⁻¹ := by rw [hinv, conjTranspose_one, one_mul]
    let X : Hn r F E := (⟨h * CE * h⁻¹, hA⟩, h *ᵥ ev r E 0, a.2.2)
    have hpow : ∀ k : ℕ, X.1.1 ^ k *ᵥ X.2.1 = h *ᵥ (CE ^ k *ᵥ ev r E 0) := by
      intro k
      show (h * CE * h⁻¹) ^ k *ᵥ (h *ᵥ ev r E 0) = _
      rw [conj_pow' h h⁻¹ CE hinv' hinv, mulVec_mulVec, mul_assoc, hinv', mul_one, ← mulVec_mulVec]
    have hBm : Bm X.toGl = h := by
      ext i j
      show (X.1.1 ^ (j : ℕ) *ᵥ X.2.1) i = h i j
      rw [hpow, hCE, comp_pow_ev p j j.2, mulVec_ev]
    have G := gram X
    rw [hBm, hh] at G
    refine ⟨X, (hasInv_iff X a).2 ⟨?_, ?_, rfl⟩⟩
    · have e1 := pow_r_mulVec X.toGl
      have e2 : X.1.1 ^ r *ᵥ X.2.1 = -(h *ᵥ p) := by
        rw [hpow, hCE, comp_pow_r, mulVec_neg]
      rw [show X.toGl.1 = X.1.1 from rfl, show X.toGl.2.1 = X.2.1 from rfl, e2, hBm, neg_inj] at e1
      have e3 := congrArg (fun v => h⁻¹ *ᵥ v) e1
      simp only [mulVec_mulVec, hinv', one_mulVec] at e3
      intro i
      exact (congrFun e3 i).symm
    · intro i
      have e4 := congrFun (congrFun G ⟨0, i.pos⟩) i
      simp only [map_apply, of_apply, hankel, Fin.val_mk, zero_add] at e4
      rw [← e4, mom_sec_lt]
end GlobalTheory.JR.HermInv
