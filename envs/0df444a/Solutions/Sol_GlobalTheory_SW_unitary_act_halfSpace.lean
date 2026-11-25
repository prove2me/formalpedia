-- Prove2me | solution 1 for GlobalTheory.SW.unitary_act_halfSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:41:26.335795+00:00
-- url     : https://prove2.me/submissions/87a4f3b2-65ec-4a29-8d9c-c12d29d76502

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Theorems.Thm_GlobalTheory_SW_HAct_blocks
import Theorems.Thm_GlobalTheory_SW_HAct_det_ne
import Theorems.Thm_GlobalTheory_SW_HAct_im_act
import Theorems.Thm_P2M_GlobalTheory_SW_HAct_den__act_d7a6623b371e
import Theorems.Thm_P2M_GlobalTheory_SW_HAct_det_den__4c81421ae817
import Theorems.Thm_GlobalTheory_SW_HAct_posDef_of
import Theorems.Thm_GlobalTheory_SW_HAct_det_re
import Theorems.Thm_GlobalTheory_SW_HAct_mul_mem
import Theorems.Thm_GlobalTheory_SW_HAct_group_part
import Theorems.Thm_GlobalTheory_SW_HAct_map_blocks
import Theorems.Thm_GlobalTheory_SW_HAct_map_mem
import Theorems.Thm_GlobalTheory_SW_HAct_norm_det
import Theorems.Thm_GlobalTheory_SW_HAct_mul_blocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory.SW.HAct
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (N : ℕ) (γ : M2 E N), γ ∈ UU E N → (IsUnit γ.det ∧ γ⁻¹ ∈ UU E N ∧ ccT γ ∈ UU E N ∧ γ⁻¹ = -(Matrix.J (Fin N) E * ccT γ * Matrix.J (Fin N) E) ∧ ∀ γ' ∈ UU E N, γ' * γ ∈ UU E N) ∧ ∀ Z ∈ Hn Ψ N, (∀ τ, (hDen Ψ γ Z τ).det ≠ 0 ∧ (hDen' Ψ γ Z τ).det * τ.1 γ.det = (hDen Ψ γ Z τ).det ∧ ‖τ.1 γ.det‖ = 1 ∧ (hDen Ψ γ Z τ)ᴴ * imH (hAct Ψ γ Z τ) * hDen Ψ γ Z τ = imH (Z τ)) ∧ hAct Ψ γ Z ∈ Hn Ψ N ∧ detIm (hAct Ψ γ Z) * ∏ τ, ‖(hDen Ψ γ Z τ).det‖ ^ 2 = detIm Z ∧ ∀ γ' ∈ UU E N, hAct Ψ (γ' * γ) Z = hAct Ψ γ' (hAct Ψ γ Z) ∧ (∀ τ, hDen Ψ (γ' * γ) Z τ = hDen Ψ γ' (hAct Ψ γ Z) τ * hDen Ψ γ Z τ) ∧ ∀ τ, hDen' Ψ (γ' * γ) Z τ = hDen' Ψ γ Z τ * hDen' Ψ γ' (hAct Ψ γ Z) τ := by
  intro E _ _ _ Ψ N γ h
  obtain ⟨g1, g2, g3, g4⟩ := group_part h
  refine ⟨⟨g1, g2, g3, g4, fun γ' h' => mul_mem h h'⟩, fun Z hZ => ?_⟩
  have hb := fun τ : Ψ => blocks (map_blocks τ.1 γ ▸ map_mem τ.1 h)
  have hQ : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0 := fun τ =>
    det_ne (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (hZ τ)
  have hI : ∀ τ, (hDen Ψ γ Z τ)ᴴ * imH (hAct Ψ γ Z τ) * hDen Ψ γ Z τ = imH (Z τ) := fun τ =>
    im_act (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (hQ τ)
  refine ⟨fun τ => ⟨hQ τ, ?_, norm_det τ.1 h, hI τ⟩, fun τ => posDef_of (hQ τ) (hI τ) (hZ τ), ?_,
    fun γ' h' => ?_⟩
  · have := det_den' (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (hQ τ)
    rw [← map_blocks τ.1 γ] at this
    rw [RingHom.map_det]
    exact this
  · rw [detIm, detIm, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => det_re (hI τ)
  · have hW : ∀ τ, hAct Ψ γ Z τ * hDen Ψ γ Z τ =
        γ.toBlocks₁₁.map τ.1 * Z τ + γ.toBlocks₁₂.map τ.1 := fun τ => by
      rw [hAct, Matrix.mul_assoc, nonsing_inv_mul _ (Ne.isUnit (hQ τ)), Matrix.mul_one]
    have key : ∀ (τ : Ψ) (X Y : Matrix (Fin N) (Fin N) ℂ),
        (X * γ.toBlocks₁₁.map τ.1 + Y * γ.toBlocks₂₁.map τ.1) * Z τ +
          (X * γ.toBlocks₁₂.map τ.1 + Y * γ.toBlocks₂₂.map τ.1) =
        (X * hAct Ψ γ Z τ + Y) * hDen Ψ γ Z τ := fun τ X Y => by
      rw [Matrix.add_mul (X * hAct Ψ γ Z τ), Matrix.mul_assoc, hW, hDen]
      noncomm_ring
    have hD : ∀ τ, hDen Ψ (γ' * γ) Z τ = hDen Ψ γ' (hAct Ψ γ Z) τ * hDen Ψ γ Z τ := fun τ => by
      obtain ⟨-, -, m3, m4⟩ := mul_blocks τ.1 γ γ'
      rw [hDen, m3, m4, key]
      rfl
    refine ⟨funext fun τ => ?_, hD, fun τ => ?_⟩
    · obtain ⟨m1, m2, -, -⟩ := mul_blocks τ.1 γ γ'
      rw [hAct, hD, m1, m2, key, Matrix.mul_inv_rev, Matrix.mul_assoc,
        ← Matrix.mul_assoc (hDen Ψ γ Z τ), mul_nonsing_inv _ (Ne.isUnit (hQ τ)), Matrix.one_mul]
      rfl
    · obtain ⟨-, -, m3, m4⟩ := mul_blocks τ.1 γ γ'
      have hd : hDen' Ψ γ Z τ * hAct Ψ γ Z τ = _ :=
        den'_act (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (hQ τ)
      rw [hDen', m3, m4, hDen', hDen', Matrix.mul_add (_ + _), ← Matrix.mul_assoc (_ + _)]
      rw [hDen'] at hd
      rw [hd]
      simp only [conjTranspose_add, conjTranspose_mul]
      noncomm_ring
end GlobalTheory.SW
