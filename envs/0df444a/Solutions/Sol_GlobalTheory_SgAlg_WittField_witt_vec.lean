-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.witt_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:06:00.083319+00:00
-- url     : https://prove2.me/submissions/ce9e4c22-eb8f-4d4d-b61e-ee96f0372b0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
import Theorems.Thm_GlobalTheory_SgAlg_WittField_isUn_form
import Theorems.Thm_GlobalTheory_SgAlg_WittField_isUn_mul
import Theorems.Thm_GlobalTheory_SgAlg_WittField_isUn_one
import Theorems.Thm_GlobalTheory_SgAlg_WittField_step
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_dual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittField
variable {E : Type} [Field E] {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.SgAlg.WittField
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) (hdet : IsUnit J.det) {δ : E}
    (hδ : δ ≠ 0) (hσδ : σ δ = -δ) (h2 : (2 : E) ≠ 0) (a : ℕ) :
    ∀ (x x' ℓ ℓ' : Fin a → Fin n → E), (∀ i j, ℓ i ⬝ᵥ x j = if i = j then 1 else 0) →
      (∀ i j, ℓ' i ⬝ᵥ x' j = if i = j then 1 else 0) →
      (∀ i j, form σ J (x i) (x j) = form σ J (x' i) (x' j)) →
      ∃ g, IsUn σ J g ∧ ∀ j, g *ᵥ x j = x' j := by
  induction a with
  | zero => intro x x' ℓ ℓ' _ _ _; exact ⟨1, isUn_one, fun j => j.elim0⟩
  | succ a ih =>
    intro x x' ℓ ℓ' hℓ hℓ' hx
    obtain ⟨g₁, hg₁, hg₁x⟩ := ih (fun j => x j.castSucc) (fun j => x' j.castSucc)
      (fun i => ℓ i.castSucc) (fun i => ℓ' i.castSucc)
      (fun i j => by simp [hℓ, Fin.castSucc_inj]) (fun i j => by simp [hℓ', Fin.castSucc_inj])
      (fun i j => hx _ _)
    have hinv : (J⁻¹ * cT σ g₁ * J) * g₁ = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ g₁), hg₁, nonsing_inv_mul J hdet]
    set m := ℓ (Fin.last a) ᵥ* (J⁻¹ * cT σ g₁ * J) with hm
    have hm' : ∀ v, m ⬝ᵥ (g₁ *ᵥ v) = ℓ (Fin.last a) ⬝ᵥ v := by
      intro v; rw [hm, ← dotProduct_mulVec, mulVec_mulVec, hinv, one_mulVec]
    obtain ⟨h, hh, hhy, hhx⟩ := step hσ hJ hδ hσδ h2 (fun i => x' i.castSucc) (g₁ *ᵥ x (Fin.last a))
      (x' (Fin.last a))
      (fun i => by
        have := isUn_form hg₁ (x i.castSucc) (x (Fin.last a))
        rw [hg₁x i, hx] at this; exact this)
      (by rw [isUn_form hg₁, hx])
      (fun k => σ ((m ᵥ* J⁻¹) k)) (fun k => σ ((ℓ' (Fin.last a) ᵥ* J⁻¹) k))
      (fun i => by rw [form_dual hσ hdet, ← hg₁x i, hm', hℓ]; simp [(Fin.castSucc_lt_last i).ne'])
      (by rw [form_dual hσ hdet, hm', hℓ]; simp)
      (fun i => by rw [form_dual hσ hdet, hℓ']; simp [(Fin.castSucc_lt_last i).ne'])
      (by rw [form_dual hσ hdet, hℓ']; simp)
    refine ⟨h * g₁, isUn_mul hh hg₁, fun j => ?_⟩
    rw [← mulVec_mulVec]
    induction j using Fin.lastCases with
    | last => exact hhx
    | cast i => rw [hg₁x i, hhy i]
end GlobalTheory.SgAlg.WittField
