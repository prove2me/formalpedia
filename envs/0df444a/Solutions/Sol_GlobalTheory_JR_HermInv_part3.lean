-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.part3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:40:00.856649+00:00
-- url     : https://prove2.me/submissions/827fb3b0-726c-4e7f-9b6d-cf683bfa9552

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_hasInv_iff
import Theorems.Thm_GlobalTheory_JR_HermInv_mul_Bm
import Theorems.Thm_GlobalTheory_JR_HermInv_Bm_ev
import Theorems.Thm_GlobalTheory_JR_HermInv_gram_hankel
import Theorems.Thm_GlobalTheory_JR_HermInv_det_unit
import Theorems.Thm_GlobalTheory_JR_HermInv_pow_r_of
import Theorems.Thm_GlobalTheory_JR_HermInv_g_Bm

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
theorem _root_.solution (X₁ X₂ : Hn r F E) (a : Inv r F) (hΔ : Delta a ≠ 0) (h₁ : HasInv X₁ a) (h₂ : HasInv X₂ a) :
    ∃! g : Matrix.unitaryGroup (Fin r) E, actU g X₁ = X₂ := by
  have G₁ := gram_hankel X₁ a h₁
  have G₂ := gram_hankel X₂ a h₂
  have u₁ := det_unit a hΔ _ G₁
  have hB₁ : Bm X₁.toGl * (Bm X₁.toGl)⁻¹ = 1 := mul_nonsing_inv _ u₁
  have hB₁' : (Bm X₁.toGl)⁻¹ * Bm X₁.toGl = 1 := nonsing_inv_mul _ u₁
  set B₁ := Bm X₁.toGl with hB1def
  set B₂ := Bm X₂.toGl with hB2def
  have hstar : star (B₂ * B₁⁻¹) * (B₂ * B₁⁻¹) = 1 := by
    rw [star_eq_conjTranspose, conjTranspose_mul]
    calc (B₁⁻¹)ᴴ * B₂ᴴ * (B₂ * B₁⁻¹) = (B₁⁻¹)ᴴ * (B₂ᴴ * B₂) * B₁⁻¹ := by simp only [mul_assoc]
      _ = (B₁⁻¹)ᴴ * (B₁ᴴ * B₁) * B₁⁻¹ := by rw [G₁, G₂]
      _ = (B₁ * B₁⁻¹)ᴴ * (B₁ * B₁⁻¹) := by rw [conjTranspose_mul]; simp only [mul_assoc]
      _ = 1 := by rw [hB₁, conjTranspose_one, one_mul]
  have hmem : B₂ * B₁⁻¹ ∈ Matrix.unitaryGroup (Fin r) E := Matrix.mem_unitaryGroup_iff'.2 hstar
  have hmul : (B₂ * B₁⁻¹) * star (B₂ * B₁⁻¹) = 1 := Matrix.mem_unitaryGroup_iff.1 hmem
  have C₁ : X₁.1.1 * B₁ = B₁ * companion (fun i => algebraMap F E (a.1 i)) :=
    mul_Bm X₁.toGl _ (pow_r_of X₁ a h₁)
  have C₂ : X₂.1.1 * B₂ = B₂ * companion (fun i => algebraMap F E (a.1 i)) :=
    mul_Bm X₂.toGl _ (pow_r_of X₂ a h₂)
  have hs : (B₂ * B₁⁻¹) * X₁.1.1 = X₂.1.1 * (B₂ * B₁⁻¹) := by
    calc (B₂ * B₁⁻¹) * X₁.1.1 = B₂ * (B₁⁻¹ * X₁.1.1 * B₁) * B₁⁻¹ := by simp only [mul_assoc, hB₁, mul_one]
      _ = B₂ * companion (fun i => algebraMap F E (a.1 i)) * B₁⁻¹ := by
        rw [mul_assoc B₁⁻¹ X₁.1.1 B₁, C₁, ← mul_assoc B₁⁻¹ B₁, hB₁', one_mul]
      _ = X₂.1.1 * (B₂ * B₁⁻¹) := by rw [← C₂]; simp only [mul_assoc]
  obtain ⟨-, -, l₁⟩ := (hasInv_iff X₁ a).1 h₁
  obtain ⟨-, -, l₂⟩ := (hasInv_iff X₂ a).1 h₂
  refine ⟨⟨B₂ * B₁⁻¹, hmem⟩, ?_, ?_⟩
  · have e1 : (B₂ * B₁⁻¹) * X₁.1.1 * star (B₂ * B₁⁻¹) = X₂.1.1 := by rw [hs, mul_assoc, hmul, mul_one]
    have b1 : B₁ *ᵥ ev r E 0 = X₁.2.1 := Bm_ev X₁.toGl
    have b2 : B₂ *ᵥ ev r E 0 = X₂.2.1 := Bm_ev X₂.toGl
    have e2 : (B₂ * B₁⁻¹) *ᵥ X₁.2.1 = X₂.2.1 := by
      rw [← b1, mulVec_mulVec, mul_assoc, hB₁', mul_one, b2]
    exact Prod.ext (Subtype.ext e1) (Prod.ext e2 (l₁.trans l₂.symm))
  · intro g hg
    apply Subtype.ext
    have := g_Bm g X₁ X₂ hg
    rw [← hB1def, ← hB2def] at this
    show g.1 = B₂ * B₁⁻¹
    rw [← this, mul_assoc, hB₁, mul_one]
end GlobalTheory.JR.HermInv
