-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuasiRefl.exists_unitary_carry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:37:23.59027+00:00
-- url     : https://prove2.me/submissions/9f0ebf86-9361-4621-8e84-376ce555d1e8

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GermConstantsEqAlongAffineSpaceSquare
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_QuasiRefl_hform_smul_right__8972bbbb794c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuasiRefl
open HeckeCharacterZeroLocus.SiegelWeilU
namespace GlobalTheory.CompanionTheory.SW.QuasiRefl
theorem _root_.solution (A : Type) [CommRing A] (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) A) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → A) (ε : A)
    (hxy : hform σ J x x = hform σ J y y) (hβ : IsUnit (hform σ J x x)) (hε : ε * σ ε = 1)
    (hu : IsUnit (hform σ J x x - σ ε * hform σ J y x)) :
    ∃ g ∈ UJ σ J, (g : Matrix (Fin M) (Fin M) A) *ᵥ x = y ∧
      ∀ z, hform σ J x z = 0 → hform σ J y z = 0 → (g : Matrix (Fin M) (Fin M) A) *ᵥ z = z := by
  obtain ⟨bi, hb⟩ := hβ.exists_right_inv
  obtain ⟨ui, hui⟩ := hu.exists_right_inv
  set β := hform σ J x x with hβdef
  set w := hform σ J y x with hw
  have hyy : hform σ J y y = β := hxy.symm
  have hxyw : hform σ J x y = σ w := by rw [hw, hform_conj_symm hσ hJ]
  have hσβ : σ β = β := hform_conj_symm hσ hJ x x
  have hσε : σ (σ ε) = ε := hσ ε
  have hσb : σ bi = bi := by
    have h1 : β * σ bi = 1 := by
      have := congrArg σ hb
      rwa [map_mul, hσβ, map_one] at this
    linear_combination bi * h1 - σ bi * hb
  have hσui : (β - ε * σ w) * σ ui = 1 := by
    have := congrArg σ hui
    rwa [map_mul, map_sub, map_mul, hσβ, hσε, map_one] at this
  set d : Fin M → A := x - ε • y with hd
  have hdx : hform σ J d x = β - σ ε * w := hform_sub_left x y x ε
  have hdy : hform σ J d y = σ w - σ ε * β := by
    rw [hd, hform_sub_left, hxyw, hyy]
  have hdd : hform σ J d d = (β - σ ε * w) + (β - ε * σ w) + (ε * σ ε - 1) * β := by
    rw [hform_sub_right, hdx, hdy]
    ring
  have hc₁ : (1 - σ ε) * bi + σ ((1 - σ ε) * bi)
      = (1 - σ ε) * bi * σ ((1 - σ ε) * bi) * hform σ J y y := by
    rw [map_mul, map_sub, map_one, hσε, hσb, hyy]
    linear_combination (-(1 - ε - σ ε + ε * σ ε) * bi) * hb + (-bi) * hε
  have hc₂ : ui + σ ui = ui * σ ui * hform σ J d d := by
    rw [hdd, hε]
    linear_combination (-σ ui) * hui + (-ui) * hσui
  refine ⟨((qr hσ hJ y _ hc₁ * qr hσ hJ d ui hc₂ : UJ σ J) : GL (Fin M) A), SetLike.coe_mem _, ?_, ?_⟩
  · have h2 : qrMat σ J d ui *ᵥ x = ε • y := by
      rw [qrMat_mulVec, hdx, mul_comm ui, hui, one_smul, hd]
      simp
    have h3 : qrMat σ J y ((1 - σ ε) * bi) *ᵥ (ε • y) = y := by
      rw [qrMat_mulVec, hform_smul_right', hyy]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination ((1 - σ ε) * ε * y i) * (-hb) + (y i) * hε
    show (qrMat σ J y ((1 - σ ε) * bi) * qrMat σ J d ui) *ᵥ x = y
    rw [← mulVec_mulVec, h2, h3]
  · intro z hxz hyz
    have hdz : hform σ J d z = 0 := by
      rw [hd, hform_sub_left, hxz, hyz]
      simp
    show (qrMat σ J y ((1 - σ ε) * bi) * qrMat σ J d ui) *ᵥ z = z
    have h2 : qrMat σ J d ui *ᵥ z = z := by
      rw [qrMat_mulVec, hdz, mul_zero, zero_smul, sub_zero]
    rw [← mulVec_mulVec, h2, qrMat_mulVec, hyz, mul_zero, zero_smul, sub_zero]
end GlobalTheory.CompanionTheory.SW.QuasiRefl
