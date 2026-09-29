-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6965b4f0-c00b-53d1-8f95-629dd1ae9e8d

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_RatIdele_Normalizer
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace IwasawaGL3

open Matrix

section Algebra

variable {F : Type*} [Field F]

def tv (i j : Fin 3) (h : i ≠ j) (c : F) : GL (Fin 3) F where
  val := Matrix.transvection i j c
  inv := Matrix.transvection i j (-c)
  val_inv := by rw [Matrix.transvection_mul_transvection_same i j h, add_neg_cancel, Matrix.transvection_zero]
  inv_val := by rw [Matrix.transvection_mul_transvection_same i j h, neg_add_cancel, Matrix.transvection_zero]

@[scoped simp] theorem coe_tv (i j : Fin 3) (h : i ≠ j) (c : F) :
    ((tv i j h c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.transvection i j c := rfl

@[scoped simp] theorem coe_inv_tv (i j : Fin 3) (h : i ≠ j) (c : F) :
    (((tv i j h c)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.transvection i j (-c) := rfl

theorem coe_mul_tv (g : GL (Fin 3) F) (i j : Fin 3) (h : i ≠ j) (c : F) (a b : Fin 3) :
    ((g * tv i j h c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) a b =
      if b = j then (g : Matrix (Fin 3) (Fin 3) F) a j + c * (g : Matrix (Fin 3) (Fin 3) F) a i
      else (g : Matrix (Fin 3) (Fin 3) F) a b := by
  rw [Units.val_mul, coe_tv]
  split_ifs with hb
  · subst hb
    exact Matrix.mul_transvection_apply_same i b a c _
  · exact Matrix.mul_transvection_apply_of_ne i j a b hb c _

theorem det_coe_ne_zero (g : GL (Fin 3) F) : (g : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
  have h := (Matrix.GeneralLinearGroup.det g).ne_zero
  rwa [Matrix.GeneralLinearGroup.val_det_apply] at h

theorem row_two_ne_zero (g : GL (Fin 3) F) :
    ¬ ((g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
        (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 0) := by
  rintro ⟨h0, h1, h2⟩
  apply det_coe_ne_zero g
  rw [Matrix.det_fin_three, h0, h1, h2]
  ring

theorem row_one_ne_zero (g : GL (Fin 3) F) (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    ¬ ((g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 1 = 0) := by
  rintro ⟨h0, h1⟩
  apply det_coe_ne_zero g
  rw [Matrix.det_fin_three, h0, h1, h20, h21]
  ring

theorem diag_ne_zero_of_upper (g : GL (Fin 3) F) (h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 1 ≠ 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
  have hdet := det_coe_ne_zero g
  rw [Matrix.det_fin_three, h10, h20, h21] at hdet
  have h : (g : Matrix (Fin 3) (Fin 3) F) 0 0 * (g : Matrix (Fin 3) (Fin 3) F) 1 1 *
      (g : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
    intro h0
    apply hdet
    linear_combination h0
  exact ⟨fun h0 => h (by rw [h0]; ring), fun h1 => h (by rw [h1]; ring), fun h2 => h (by rw [h2]; ring)⟩

def word (p : Fin 6 → F) : GL (Fin 3) F :=
  tv 0 2 (by decide) (p 0) * tv 1 2 (by decide) (p 1) * tv 2 0 (by decide) (p 2) *
    tv 2 1 (by decide) (p 3) * tv 0 1 (by decide) (p 4) * tv 1 0 (by decide) (p 5)

end Algebra

section Valued

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation F Γ₀)

theorem exists_pivot_three (a b c : F) (h : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    ∃ s₁ s₂ : F, w s₁ ≤ 1 ∧ w s₂ ≤ 1 ∧ c + s₁ * a + s₂ * b ≠ 0 ∧
      w a ≤ w (c + s₁ * a + s₂ * b) ∧ w b ≤ w (c + s₁ * a + s₂ * b) := by
  by_cases h1 : w a ≤ w c ∧ w b ≤ w c
  · refine ⟨0, 0, by simp, by simp, ?_⟩
    have he : c + 0 * a + 0 * b = c := by ring
    rw [he]
    refine ⟨fun hc => ?_, h1.1, h1.2⟩
    apply h
    rw [hc, map_zero, le_zero_iff, map_eq_zero] at h1
    rw [le_zero_iff, map_eq_zero] at h1
    exact ⟨h1.1, h1.2, hc⟩
  · by_cases h2 : w b ≤ w a
    · have hca : w c < w a := by
        by_contra hh
        push Not at hh
        exact h1 ⟨hh, h2.trans hh⟩
      refine ⟨1, 0, le_of_eq (map_one w), by simp, ?_⟩
      have he : c + 1 * a + 0 * b = c + a := by ring
      rw [he, w.map_add_eq_of_lt_right hca]
      refine ⟨fun h0 => ?_, le_rfl, h2⟩
      have := hca
      rw [← w.map_add_eq_of_lt_right hca, h0, map_zero] at this
      exact not_lt_zero this
    · push Not at h2
      have hcb : w c < w b := by
        by_contra hh
        push Not at hh
        exact h1 ⟨h2.le.trans hh, hh⟩
      refine ⟨0, 1, by simp, le_of_eq (map_one w), ?_⟩
      have he : c + 0 * a + 1 * b = c + b := by ring
      rw [he, w.map_add_eq_of_lt_right hcb]
      refine ⟨fun h0 => ?_, h2.le, le_rfl⟩
      have := hcb
      rw [← w.map_add_eq_of_lt_right hcb, h0, map_zero] at this
      exact not_lt_zero this

theorem exists_pivot_two (d e : F) (h : ¬ (d = 0 ∧ e = 0)) :
    ∃ s : F, w s ≤ 1 ∧ e + s * d ≠ 0 ∧ w d ≤ w (e + s * d) := by
  by_cases h1 : w d ≤ w e
  · refine ⟨0, by simp, ?_⟩
    have he : e + 0 * d = e := by ring
    rw [he]
    refine ⟨fun he0 => ?_, h1⟩
    apply h
    rw [he0, map_zero, le_zero_iff, map_eq_zero] at h1
    exact ⟨h1, he0⟩
  · push Not at h1
    refine ⟨1, le_of_eq (map_one w), ?_⟩
    have he : e + 1 * d = e + d := by ring
    rw [he, w.map_add_eq_of_lt_right h1]
    refine ⟨fun h0 => ?_, le_rfl⟩
    have := h1
    rw [← w.map_add_eq_of_lt_right h1, h0, map_zero] at this
    exact not_lt_zero this

theorem elim_coeff (a c : F) (hc : c ≠ 0) (h : w a ≤ w c) :
    w (-(a / c)) ≤ 1 ∧ a + -(a / c) * c = 0 := by
  refine ⟨?_, ?_⟩
  · rw [Valuation.map_neg, map_div₀]
    have hpos : 0 < w c := zero_lt_iff.mpr ((map_ne_zero w).mpr hc)
    exact (div_le_one₀ hpos).mpr h
  · rw [neg_mul, div_mul_cancel₀ a hc, add_neg_cancel]

theorem stepA (g : GL (Fin 3) F) : ∃ s₁ s₂ : F, w s₁ ≤ 1 ∧ w s₂ ≤ 1 ∧
    ∀ g' : GL (Fin 3) F, g' = g * tv 0 2 (by decide) s₁ * tv 1 2 (by decide) s₂ →
      (g' : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 ∧
      w ((g' : Matrix (Fin 3) (Fin 3) F) 2 0) ≤ w ((g' : Matrix (Fin 3) (Fin 3) F) 2 2) ∧
      w ((g' : Matrix (Fin 3) (Fin 3) F) 2 1) ≤ w ((g' : Matrix (Fin 3) (Fin 3) F) 2 2) := by
  obtain ⟨s₁, s₂, hs₁, hs₂, hne, ha, hb⟩ :=
    exists_pivot_three w ((g : Matrix (Fin 3) (Fin 3) F) 2 0) ((g : Matrix (Fin 3) (Fin 3) F) 2 1)
      ((g : Matrix (Fin 3) (Fin 3) F) 2 2) (row_two_ne_zero g)
  refine ⟨s₁, s₂, hs₁, hs₂, fun g' hg' => ?_⟩
  have h20 : (g' : Matrix (Fin 3) (Fin 3) F) 2 0 = (g : Matrix (Fin 3) (Fin 3) F) 2 0 := by
    rw [hg']; simp [coe_mul_tv]
  have h21 : (g' : Matrix (Fin 3) (Fin 3) F) 2 1 = (g : Matrix (Fin 3) (Fin 3) F) 2 1 := by
    rw [hg']; simp [coe_mul_tv]
  have h22 : (g' : Matrix (Fin 3) (Fin 3) F) 2 2 =
      (g : Matrix (Fin 3) (Fin 3) F) 2 2 + s₁ * (g : Matrix (Fin 3) (Fin 3) F) 2 0 +
        s₂ * (g : Matrix (Fin 3) (Fin 3) F) 2 1 := by
    rw [hg']; simp [coe_mul_tv]
  rw [h20, h21, h22]
  exact ⟨hne, ha, hb⟩

theorem stepB (g : GL (Fin 3) F) (hne : (g : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0)
    (ha : w ((g : Matrix (Fin 3) (Fin 3) F) 2 0) ≤ w ((g : Matrix (Fin 3) (Fin 3) F) 2 2))
    (hb : w ((g : Matrix (Fin 3) (Fin 3) F) 2 1) ≤ w ((g : Matrix (Fin 3) (Fin 3) F) 2 2)) :
    ∃ t₁ t₂ : F, w t₁ ≤ 1 ∧ w t₂ ≤ 1 ∧
    ∀ g' : GL (Fin 3) F, g' = g * tv 2 0 (by decide) t₁ * tv 2 1 (by decide) t₂ →
      (g' : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g' : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  obtain ⟨ht₁, he₁⟩ := elim_coeff w _ _ hne ha
  obtain ⟨ht₂, he₂⟩ := elim_coeff w _ _ hne hb
  refine ⟨_, _, ht₁, ht₂, fun g' hg' => ?_⟩
  have h20 : (g' : Matrix (Fin 3) (Fin 3) F) 2 0 =
      (g : Matrix (Fin 3) (Fin 3) F) 2 0 +
        -((g : Matrix (Fin 3) (Fin 3) F) 2 0 / (g : Matrix (Fin 3) (Fin 3) F) 2 2) *
          (g : Matrix (Fin 3) (Fin 3) F) 2 2 := by
    rw [hg']; simp [coe_mul_tv]
  have h21 : (g' : Matrix (Fin 3) (Fin 3) F) 2 1 =
      (g : Matrix (Fin 3) (Fin 3) F) 2 1 +
        -((g : Matrix (Fin 3) (Fin 3) F) 2 1 / (g : Matrix (Fin 3) (Fin 3) F) 2 2) *
          (g : Matrix (Fin 3) (Fin 3) F) 2 2 := by
    rw [hg']; simp [coe_mul_tv]
  rw [h20, h21]
  exact ⟨he₁, he₂⟩

theorem stepC (g : GL (Fin 3) F) (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    ∃ s : F, w s ≤ 1 ∧ ∀ g' : GL (Fin 3) F, g' = g * tv 0 1 (by decide) s →
      (g' : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g' : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
      (g' : Matrix (Fin 3) (Fin 3) F) 1 1 ≠ 0 ∧
      w ((g' : Matrix (Fin 3) (Fin 3) F) 1 0) ≤ w ((g' : Matrix (Fin 3) (Fin 3) F) 1 1) := by
  obtain ⟨s, hs, hne, hd⟩ :=
    exists_pivot_two w ((g : Matrix (Fin 3) (Fin 3) F) 1 0) ((g : Matrix (Fin 3) (Fin 3) F) 1 1)
      (row_one_ne_zero g h20 h21)
  refine ⟨s, hs, fun g' hg' => ?_⟩
  have e20 : (g' : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
    rw [hg']; simp [coe_mul_tv, h20]
  have e21 : (g' : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
    rw [hg']; simp [coe_mul_tv, h20, h21]
  have e10 : (g' : Matrix (Fin 3) (Fin 3) F) 1 0 = (g : Matrix (Fin 3) (Fin 3) F) 1 0 := by
    rw [hg']; simp [coe_mul_tv]
  have e11 : (g' : Matrix (Fin 3) (Fin 3) F) 1 1 =
      (g : Matrix (Fin 3) (Fin 3) F) 1 1 + s * (g : Matrix (Fin 3) (Fin 3) F) 1 0 := by
    rw [hg']; simp [coe_mul_tv]
  rw [e20, e21, e10, e11]
  exact ⟨rfl, rfl, hne, hd⟩

theorem stepD (g : GL (Fin 3) F) (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) (hne : (g : Matrix (Fin 3) (Fin 3) F) 1 1 ≠ 0)
    (hd : w ((g : Matrix (Fin 3) (Fin 3) F) 1 0) ≤ w ((g : Matrix (Fin 3) (Fin 3) F) 1 1)) :
    ∃ t : F, w t ≤ 1 ∧ ∀ g' : GL (Fin 3) F, g' = g * tv 1 0 (by decide) t →
      (g' : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (g' : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      (g' : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  obtain ⟨ht, he⟩ := elim_coeff w _ _ hne hd
  refine ⟨_, ht, fun g' hg' => ?_⟩
  have e10 : (g' : Matrix (Fin 3) (Fin 3) F) 1 0 =
      (g : Matrix (Fin 3) (Fin 3) F) 1 0 +
        -((g : Matrix (Fin 3) (Fin 3) F) 1 0 / (g : Matrix (Fin 3) (Fin 3) F) 1 1) *
          (g : Matrix (Fin 3) (Fin 3) F) 1 1 := by
    rw [hg']; simp [coe_mul_tv]
  have e20 : (g' : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
    rw [hg']; simp [coe_mul_tv, h20, h21]
  have e21 : (g' : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
    rw [hg']; simp [coe_mul_tv, h21]
  rw [e10, e20, e21]
  exact ⟨he, rfl, rfl⟩

theorem exists_word (g : GL (Fin 3) F) : ∃ p : Fin 6 → F, (∀ i, w (p i) ≤ 1) ∧
    ((g * word p : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
    ((g * word p : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
    ((g * word p : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  obtain ⟨s₁, s₂, hs₁, hs₂, hA⟩ := stepA w g
  obtain ⟨hAne, hAa, hAb⟩ := hA _ rfl
  obtain ⟨t₁, t₂, ht₁, ht₂, hB⟩ := stepB w _ hAne hAa hAb
  obtain ⟨hB0, hB1⟩ := hB _ rfl
  obtain ⟨s₃, hs₃, hC⟩ := stepC w _ hB0 hB1
  obtain ⟨hC0, hC1, hCne, hCd⟩ := hC _ rfl
  obtain ⟨t₃, ht₃, hD⟩ := stepD w _ hC0 hC1 hCne hCd
  obtain ⟨hD10, hD20, hD21⟩ := hD _ rfl
  refine ⟨![s₁, s₂, t₁, t₂, s₃, t₃], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hs₁
    · exact hs₂
    · exact ht₁
    · exact ht₂
    · exact hs₃
    · exact ht₃
  · have hw : g * word ![s₁, s₂, t₁, t₂, s₃, t₃] =
        g * tv 0 2 (by decide) s₁ * tv 1 2 (by decide) s₂ * tv 2 0 (by decide) t₁ *
          tv 2 1 (by decide) t₂ * tv 0 1 (by decide) s₃ * tv 1 0 (by decide) t₃ := by
      simp only [word, mul_assoc]
      rfl
    rw [hw]
    exact ⟨hD10, hD20, hD21⟩

end Valued

section Topology

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

theorem continuous_transvection (i j : Fin 3) : Continuous fun c : F => Matrix.transvection i j c := by
  refine continuous_matrix fun a b => ?_
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
  split_ifs
  · exact continuous_const.add continuous_id
  · exact continuous_const.add continuous_const

theorem continuous_tv (i j : Fin 3) (h : i ≠ j) : Continuous fun c : F => tv i j h c :=
  Units.continuous_iff.mpr
    ⟨continuous_transvection i j, (continuous_transvection i j).comp continuous_neg⟩

theorem continuous_word : Continuous fun p : Fin 6 → F => word p := by
  unfold word
  refine Continuous.mul (Continuous.mul (Continuous.mul (Continuous.mul (Continuous.mul ?_ ?_) ?_) ?_) ?_) ?_
  · exact (continuous_tv 0 2 (by decide)).comp (continuous_apply 0)
  · exact (continuous_tv 1 2 (by decide)).comp (continuous_apply 1)
  · exact (continuous_tv 2 0 (by decide)).comp (continuous_apply 2)
  · exact (continuous_tv 2 1 (by decide)).comp (continuous_apply 3)
  · exact (continuous_tv 0 1 (by decide)).comp (continuous_apply 4)
  · exact (continuous_tv 1 0 (by decide)).comp (continuous_apply 5)

theorem continuous_word_inv : Continuous fun p : Fin 6 → F => (word p)⁻¹ :=
  continuous_word.inv

end Topology

end IwasawaGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd.IwasawaGL3"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.psiLocal_eq_one_of_mem_integers"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_mul diagonal3_coe IsGL3PsiWhittakerFn upperUnipotent3 upperUnipotent3_coe localMaximalCompact3 LocalGL3"
namespace Core12
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

p2m_open "Matrix LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd.LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd.IwasawaGL3"

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => v.adicCompletion ℚ

theorem exists_eq_diagonal3_mul_upperUnipotent3 (u : LocalGL3 v)
    (h10 : (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0)
    (h20 : (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0) :
    ∃ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (x y z : v.adicCompletion ℚ),
      u = diagonal3 v a * upperUnipotent3 x y z := by
  obtain ⟨h0, h1, h2⟩ := diag_ne_zero_of_upper u h10 h20 h21
  refine ⟨![Units.mk0 _ h0, Units.mk0 _ h1, Units.mk0 _ h2],
    (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 / (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0,
    (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2 / (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1,
    (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2 / (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0,
    ?_⟩
  refine Units.ext ?_
  refine Matrix.ext fun i j => ?_
  rw [Units.val_mul, diagonal3_coe, upperUnipotent3_coe, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j
  · simp
  · simp [mul_div_cancel₀ _ h0]
  · simp [mul_div_cancel₀ _ h0]
  · simp [h10]
  · simp
  · simp [mul_div_cancel₀ _ h1]
  · simp [h20]
  · simp [h21]
  · simp

theorem diagonal3_mul_upperUnipotent3 (c : Fin 3 → (𝕂)ˣ) (x y z : 𝕂) :
    diagonal3 v c * upperUnipotent3 x y z =
      upperUnipotent3 ((c 0 : 𝕂) / (c 1 : 𝕂) * x) ((c 1 : 𝕂) / (c 2 : 𝕂) * y) ((c 0 : 𝕂) / (c 2 : 𝕂) * z) *
        diagonal3 v c := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_mul, Units.val_mul, diagonal3_coe, upperUnipotent3_coe, upperUnipotent3_coe, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  have h0 : ((c 0 : (𝕂)ˣ) : 𝕂) ≠ 0 := (c 0).ne_zero
  have h1 : ((c 1 : (𝕂)ˣ) : 𝕂) ≠ 0 := (c 1).ne_zero
  have h2 : ((c 2 : (𝕂)ˣ) : 𝕂) ≠ 0 := (c 2).ne_zero
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem diagonal3_comm (a c : Fin 3 → (𝕂)ˣ) : diagonal3 v a * diagonal3 v c = diagonal3 v c * diagonal3 v a := by
  rw [← diagonal3_mul, ← diagonal3_mul, mul_comm]

theorem valued_mul_le_of_right_integral {a b : Matrix (Fin 3) (Fin 3) 𝕂} {C : WithZero (Multiplicative ℤ)}
    (ha : ∀ i l, Valued.v (a i l) ≤ C) (hb : ∀ l j, Valued.v (b l j) ≤ 1) (i j : Fin 3) :
    Valued.v ((a * b) i j) ≤ C := by
  have hterm : ∀ l, Valued.v (a i l * b l j) ≤ C := fun l => by
    rw [map_mul]
    calc Valued.v (a i l) * Valued.v (b l j) ≤ Valued.v (a i l) * 1 := mul_le_mul_right (hb l j) _
      _ = Valued.v (a i l) := mul_one _
      _ ≤ C := ha i l
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

theorem valued_mul_le_of_left_integral {a b : Matrix (Fin 3) (Fin 3) 𝕂} {C : WithZero (Multiplicative ℤ)}
    (ha : ∀ i l, Valued.v (a i l) ≤ 1) (hb : ∀ l j, Valued.v (b l j) ≤ C) (i j : Fin 3) :
    Valued.v ((a * b) i j) ≤ C := by
  have hterm : ∀ l, Valued.v (a i l * b l j) ≤ C := fun l => by
    rw [map_mul]
    calc Valued.v (a i l) * Valued.v (b l j) ≤ 1 * Valued.v (b l j) := mul_le_mul_left (ha i l) _
      _ = Valued.v (b l j) := one_mul _
      _ ≤ C := hb l j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

theorem valued_transvection_le_one (i j : Fin 3) (c : 𝕂) (hc : Valued.v c ≤ 1) (a b : Fin 3) :
    Valued.v (Matrix.transvection i j c a b) ≤ 1 := by
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply]
  split_ifs <;> simp_all [Valuation.map_one, Valuation.map_zero]
  ·
    exact le_trans (Valuation.map_add _ _ _) (max_le (by rw [Valuation.map_one]) hc)

theorem valued_word_le_one (p : Fin 6 → 𝕂) (hp : ∀ i, Valued.v (p i) ≤ 1) :
    (∀ a b, Valued.v (((word p : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂) a b) ≤ 1) ∧
    (∀ a b, Valued.v ((((word p)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂) a b) ≤ 1) := by
  have htv : ∀ (i j : Fin 3) (h : i ≠ j) (c : 𝕂), Valued.v c ≤ 1 →
      (∀ a b, Valued.v (((tv i j h c : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂) a b) ≤ 1) ∧
      (∀ a b, Valued.v ((((tv i j h c)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂) a b) ≤ 1) := by
    intro i j h c hc
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [coe_tv]; exact valued_transvection_le_one v i j c hc a b
    · rw [coe_inv_tv]; exact valued_transvection_le_one v i j (-c) (by rwa [Valuation.map_neg]) a b
  have hmul : ∀ (g h : LocalGL3 v),
      ((∀ a b, Valued.v ((g : Matrix (Fin 3) (Fin 3) 𝕂) a b) ≤ 1) ∧
        (∀ a b, Valued.v (((g⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂) a b) ≤ 1)) →
      ((∀ a b, Valued.v ((h : Matrix (Fin 3) (Fin 3) 𝕂) a b) ≤ 1) ∧
        (∀ a b, Valued.v (((h⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂) a b) ≤ 1)) →
      ((∀ a b, Valued.v (((g * h : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂) a b) ≤ 1) ∧
        (∀ a b, Valued.v ((((g * h)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂) a b) ≤ 1)) := by
    intro g h hg hh
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [Units.val_mul]; exact valued_mul_le_of_right_integral v hg.1 hh.1 a b
    · rw [_root_.mul_inv_rev, Units.val_mul]; exact valued_mul_le_of_right_integral v hh.2 hg.2 a b
  unfold word
  refine hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (htv 0 2 _ _ (hp 0)) (htv 1 2 _ _ (hp 1)))
    (htv 2 0 _ _ (hp 2))) (htv 2 1 _ _ (hp 3))) (htv 0 1 _ _ (hp 4))) (htv 1 0 _ _ (hp 5))

theorem exists_valued_entry_le_of_isCompact (C : Set (LocalGL3 v)) (hC : IsCompact C) :
    ∃ M : ℕ, ∀ X ∈ C, ∀ i j,
      Valued.v ((X : Matrix (Fin 3) (Fin 3) 𝕂) i j) ≤ WithZero.exp (M : ℤ) ∧
      Valued.v (((X⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂) i j) ≤ WithZero.exp (M : ℤ) := by
  classical

  set π : 𝕂 := algebraMap ℚ (v.adicCompletion ℚ) ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℚ) with hπ
  have hvπ : Valued.v π = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans (RatIdele.valuation_natGenerator v)
  have hπ0 : π ≠ 0 := fun h => by rw [h, map_zero] at hvπ; exact WithZero.exp_ne_zero hvπ.symm
  have hnormπ : ‖π‖ < 1 := (Valued.toNormedField.norm_lt_one_iff).mpr (by rw [hvπ, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num))
  have hnormπinv : 1 < ‖π⁻¹‖ := by
    rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.mpr hπ0)).mpr hnormπ

  have hb : ∀ i j : Fin 3, ∃ R : ℝ, ∀ X ∈ C,
      ‖(X : Matrix (Fin 3) (Fin 3) 𝕂) i j‖ ≤ R ∧ ‖(((X⁻¹ : LocalGL3 v)) : Matrix (Fin 3) (Fin 3) 𝕂) i j‖ ≤ R := by
    intro i j
    have hc1 : Continuous fun X : LocalGL3 v => (X : Matrix (Fin 3) (Fin 3) 𝕂) i j :=
      (Units.continuous_val.matrix_elem i j)
    have hc2 : Continuous fun X : LocalGL3 v => (((X⁻¹ : LocalGL3 v)) : Matrix (Fin 3) (Fin 3) 𝕂) i j :=
      (Units.continuous_val.matrix_elem i j).comp continuous_inv
    obtain ⟨R₁, hR₁⟩ := hC.exists_bound_of_continuousOn hc1.continuousOn
    obtain ⟨R₂, hR₂⟩ := hC.exists_bound_of_continuousOn hc2.continuousOn
    exact ⟨max R₁ R₂, fun X hX => ⟨(hR₁ X hX).trans (le_max_left _ _), (hR₂ X hX).trans (le_max_right _ _)⟩⟩
  choose R hR using hb
  set R₀ : ℝ := Finset.univ.sum fun ij : Fin 3 × Fin 3 => |R ij.1 ij.2| with hR₀
  have hRle : ∀ i j, R i j ≤ R₀ := fun i j => by
    have := Finset.single_le_sum (f := fun ij : Fin 3 × Fin 3 => |R ij.1 ij.2|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ (i, j))
    exact (le_abs_self _).trans this
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt R₀ hnormπinv
  refine ⟨M, fun X hX i j => ?_⟩
  have hcmp : ∀ y : 𝕂, ‖y‖ ≤ R₀ → Valued.v y ≤ WithZero.exp (M : ℤ) := by
    intro y hy
    have h1 : ‖y‖ ≤ ‖(π⁻¹) ^ M‖ := by rw [norm_pow]; exact hy.trans hM.le
    have h2 := (Valued.toNormedField.norm_le_iff).mp h1
    rw [map_pow, map_inv₀, hvπ, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_nsmul] at h2
    simpa using h2
  exact ⟨hcmp _ ((hR i j X hX).1.trans (hRle i j)), hcmp _ ((hR i j X hX).2.trans (hRle i j))⟩

end LanglandsTunnell.CubicInduction.Core12
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd.IwasawaGL3"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd.IwasawaGL3"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd.IwasawaGL3"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.psiLocal_eq_one_of_mem_integers"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_mul diagonal3_coe IsGL3PsiWhittakerFn upperUnipotent3 upperUnipotent3_coe localMaximalCompact3 LocalGL3"
namespace Core12
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

p2m_open "Matrix LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd.LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd.IwasawaGL3"

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => v.adicCompletion ℚ

theorem diagonal3_one : diagonal3 v (1 : Fin 3 → (𝕂)ˣ) = 1 := by
  refine Units.ext ?_
  rw [diagonal3_coe, Units.val_one]
  simp

theorem diagonal3_inv (c : Fin 3 → (𝕂)ˣ) : (diagonal3 v c)⁻¹ = diagonal3 v c⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← diagonal3_mul, mul_inv_cancel, diagonal3_one]

theorem upperUnipotent3_inv (x y z : 𝕂) :
    (upperUnipotent3 x y z : LocalGL3 v)⁻¹ = upperUnipotent3 (-x) (-y) (x * y - z) := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, upperUnipotent3_coe, upperUnipotent3_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem word_conj_diagonal3_mem (p : Fin 6 → 𝕂) (hp : ∀ i, Valued.v (p i) ≤ 1) (c : Fin 3 → (𝕂)ˣ)
    (hc1 : ∀ i, Valued.v ((c i : (𝕂)ˣ) : 𝕂) = 1) (e : WithZero (Multiplicative ℤ)) (he : e ≤ 1)
    (hce : ∀ i, Valued.v (((c i : (𝕂)ˣ) : 𝕂) - 1) ≤ e) :
    word p * diagonal3 v c * (word p)⁻¹ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
    ∀ i j, Valued.v (((word p * diagonal3 v c * (word p)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂) i j -
      (1 : Matrix (Fin 3) (Fin 3) 𝕂) i j) ≤ e := by
  obtain ⟨hw, hwi⟩ := valued_word_le_one v p hp
  have hdiag : ∀ (f : Fin 3 → 𝕂) (B : WithZero (Multiplicative ℤ)), 0 ≤ B → (∀ i, Valued.v (f i) ≤ B) →
      ∀ i j, Valued.v (Matrix.diagonal f i j) ≤ B := by
    intro f B hB hf i j
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.diagonal_apply_eq]; exact hf i
    · rw [Matrix.diagonal_apply_ne _ hij, Valuation.map_zero]; exact hB
  have hc : ∀ i j, Valued.v ((diagonal3 v c : Matrix (Fin 3) (Fin 3) 𝕂) i j) ≤ 1 := by
    rw [diagonal3_coe]; exact hdiag _ 1 zero_le_one (fun i => (hc1 i).le)
  have hcinv : ∀ i j, Valued.v ((((diagonal3 v c)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂) i j) ≤ 1 := by
    rw [diagonal3_inv, diagonal3_coe]
    refine hdiag _ 1 zero_le_one (fun i => ?_)
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hc1 i, inv_one]
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact valued_mul_le_of_right_integral v (fun i l => valued_mul_le_of_right_integral v hw hc i l) hwi i j
  · have hinv : (word p * diagonal3 v c * (word p)⁻¹)⁻¹ = word p * (diagonal3 v c)⁻¹ * (word p)⁻¹ :=
      inv_eq_of_mul_eq_one_right (by simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, mul_inv_cancel])
    rw [hinv, Units.val_mul, Units.val_mul]
    exact valued_mul_le_of_right_integral v (fun i l => valued_mul_le_of_right_integral v hw hcinv i l) hwi i j
  · have hmat : ((word p * diagonal3 v c * (word p)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂) - 1 =
        ((word p : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂) *
          ((diagonal3 v c : Matrix (Fin 3) (Fin 3) 𝕂) - 1) * (((word p)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul,
        mul_inv_cancel, Units.val_one]
    have h := congrFun (congrFun hmat i) j
    rw [Matrix.sub_apply] at h
    rw [h]
    refine valued_mul_le_of_right_integral v (fun i l => valued_mul_le_of_left_integral v hw ?_ i l) hwi i j
    intro l j
    rw [diagonal3_coe, Matrix.sub_apply]
    rcases eq_or_ne l j with rfl | hlj
    · rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]; exact hce l
    · rw [Matrix.diagonal_apply_ne _ hlj, Matrix.one_apply_ne hlj, sub_zero, Valuation.map_zero]; exact zero_le'

end LanglandsTunnell.CubicInduction.Core12
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd.IwasawaGL3"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd.IwasawaGL3"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd.IwasawaGL3"

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd.LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))

    (W₀ : LocalGL3 v → ℂ)
    (hW₀law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W₀)
    (d : ℕ)
    (hW₀lev : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
      (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
      ∀ g : LocalGL3 v, W₀ (g * k) = W₀ g)

    (C : Set (LocalGL3 v)) (hC : IsCompact C) :
    ∃ N : ℕ, ∀ X ∈ C, ∀ a : Fin 3 → (v.adicCompletion ℚ)ˣ,
      Valued.v (((a 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) / ((a 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) ≤
        WithZero.exp (-(N : ℤ)) →
      ∀ s t : (v.adicCompletion ℚ)ˣ, s ∈ higherUnitsAt ℚ v d → t ∈ higherUnitsAt ℚ v d →
        W₀ (diagonal3 v a * diagonal3 v ![t, t, s] * X) = W₀ (diagonal3 v a * X) := by
  classical
  obtain ⟨M, hM⟩ := LanglandsTunnell.CubicInduction.Core12.exists_valued_entry_le_of_isCompact v C hC
  refine ⟨2 * M, fun X hX a ha s t hs ht => ?_⟩
  obtain ⟨hs1, hsd⟩ := (mem_higherUnitsAt_iff ℚ v).mp hs
  obtain ⟨ht1, htd⟩ := (mem_higherUnitsAt_iff ℚ v).mp ht

  have hsub1 : ∀ w : (v.adicCompletion ℚ)ˣ, Valued.v (w : v.adicCompletion ℚ) = 1 →
      Valued.v ((w : v.adicCompletion ℚ) - 1) ≤ 1 := fun w hw =>
    le_trans (Valuation.map_sub _ _ _) (max_le hw.le (by rw [Valuation.map_one]))
  have hse : Valued.v ((s : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(d : ℤ)) := by
    rcases hsd with h0 | h
    · rw [h0, Nat.cast_zero, neg_zero, WithZero.exp_zero]; exact hsub1 s hs1
    · exact h
  have hte : Valued.v ((t : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(d : ℤ)) := by
    rcases htd with h0 | h
    · rw [h0, Nat.cast_zero, neg_zero, WithZero.exp_zero]; exact hsub1 t ht1
    · exact h

  obtain ⟨p, hp, h10, h20, h21⟩ := IwasawaGL3.exists_word (Valued.v : Valuation (v.adicCompletion ℚ) _) X
  obtain ⟨δ, x, y, z, hδ⟩ :=
    LanglandsTunnell.CubicInduction.Core12.exists_eq_diagonal3_mul_upperUnipotent3 v (X * IwasawaGL3.word p) h10 h20 h21
  obtain ⟨hwint, hwinvint⟩ := LanglandsTunnell.CubicInduction.Core12.valued_word_le_one v p hp
  have hXdec : X = diagonal3 v δ * upperUnipotent3 x y z * (IwasawaGL3.word p)⁻¹ := by
    rw [← hδ, mul_inv_cancel_right]

  obtain ⟨c, hc⟩ : ∃ c : Fin 3 → (v.adicCompletion ℚ)ˣ, c = ![t, t, s] := ⟨_, rfl⟩
  rw [← hc]
  have hc0 : ((c 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = t := by subst hc; rfl
  have hc1' : ((c 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = t := by subst hc; rfl
  have hc2 : ((c 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = s := by subst hc; rfl
  have hc1 : ∀ i, Valued.v ((c i : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
    intro i
    fin_cases i
    · exact hc0.symm ▸ ht1
    · exact hc1'.symm ▸ ht1
    · exact hc2.symm ▸ hs1
  have hce : ∀ i, Valued.v (((c i : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(d : ℤ)) := by
    intro i
    fin_cases i
    · exact hc0.symm ▸ hte
    · exact hc1'.symm ▸ hte
    · exact hc2.symm ▸ hse
  obtain ⟨hkmem, hkcong⟩ := LanglandsTunnell.CubicInduction.Core12.word_conj_diagonal3_mem v p hp c hc1
    (WithZero.exp (-(d : ℤ))) (by rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by omega)) hce
  have hfix : ∀ g : LocalGL3 v, W₀ (g * (IwasawaGL3.word p * diagonal3 v c * (IwasawaGL3.word p)⁻¹)) = W₀ g :=
    hW₀lev _ hkmem hkcong

  have hψ := hW₀law
  obtain ⟨A, hA⟩ : ∃ A : Fin 3 → (v.adicCompletion ℚ)ˣ, A = a * δ := ⟨_, rfl⟩

  have hR : W₀ (diagonal3 v a * X) =
      (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹
        (((A 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) / ((A 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x +
          ((A 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) / ((A 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) *
        W₀ (diagonal3 v A * (IwasawaGL3.word p)⁻¹) := by
    rw [hXdec, ← mul_assoc, ← mul_assoc, ← diagonal3_mul, ← hA,
      LanglandsTunnell.CubicInduction.Core12.diagonal3_mul_upperUnipotent3, mul_assoc, hψ]

  have hL : W₀ (diagonal3 v a * diagonal3 v c * X) =
      (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹
        (((A 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) / ((A 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) *
            (((c 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) / ((c 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x) +
          ((A 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) / ((A 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) *
            (((c 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) / ((c 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y)) *
        W₀ (diagonal3 v A * (IwasawaGL3.word p)⁻¹) := by
    rw [hXdec]
    have hre : diagonal3 v a * diagonal3 v c * (diagonal3 v δ * upperUnipotent3 x y z * (IwasawaGL3.word p)⁻¹) =
        diagonal3 v A * (diagonal3 v c * upperUnipotent3 x y z) * (IwasawaGL3.word p)⁻¹ := by
      rw [hA, diagonal3_mul]
      simp only [mul_assoc]
      rw [← mul_assoc (diagonal3 v c) (diagonal3 v δ), LanglandsTunnell.CubicInduction.Core12.diagonal3_comm v c δ,
        mul_assoc]
    rw [hre, LanglandsTunnell.CubicInduction.Core12.diagonal3_mul_upperUnipotent3, ← mul_assoc,
      LanglandsTunnell.CubicInduction.Core12.diagonal3_mul_upperUnipotent3, mul_assoc, mul_assoc, hψ]
    congr 1

    have : diagonal3 v A * (diagonal3 v c * (IwasawaGL3.word p)⁻¹) =
        diagonal3 v A * (IwasawaGL3.word p)⁻¹ * (IwasawaGL3.word p * diagonal3 v c * (IwasawaGL3.word p)⁻¹) := by
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [this, hfix]
  rw [hL, hR]
  congr 1

  rw [hc0, hc1', hc2, div_self (t.ne_zero), one_mul]
  set α : v.adicCompletion ℚ := ((A 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) / ((A 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) with hα
  set β : v.adicCompletion ℚ := ((A 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) / ((A 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x with hβ
  have hsplit : β + α * ((t : v.adicCompletion ℚ) / (s : v.adicCompletion ℚ) * y) =
      (β + α * y) + α * ((t : v.adicCompletion ℚ) / (s : v.adicCompletion ℚ) - 1) * y := by ring
  rw [hsplit, AddChar.map_add_eq_mul]
  conv_rhs => rw [← mul_one ((NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (β + α * y))]
  congr 1
  rw [AddChar.inv_apply]
  apply LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_neg]

  have hA1 : ((A 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = (a 1 : v.adicCompletion ℚ) * (δ 1 : v.adicCompletion ℚ) := by
    simp [hA]
  have hA2 : ((A 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = (a 2 : v.adicCompletion ℚ) * (δ 2 : v.adicCompletion ℚ) := by
    simp [hA]

  have hu12 : ((X * IwasawaGL3.word p : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2 =
      (δ 1 : v.adicCompletion ℚ) * y := by
    rw [hδ, Units.val_mul, diagonal3_coe, upperUnipotent3_coe, Matrix.diagonal_mul]
    have : (!![(1 : v.adicCompletion ℚ), x, z; 0, 1, y; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2 = y := rfl
    rw [this]
  have hu22 : (((X * IwasawaGL3.word p)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 =
      ((δ 2 : v.adicCompletion ℚ))⁻¹ := by
    rw [hδ, _root_.mul_inv_rev, Units.val_mul]
    rw [LanglandsTunnell.CubicInduction.Core12.upperUnipotent3_inv, LanglandsTunnell.CubicInduction.Core12.diagonal3_inv,
      upperUnipotent3_coe, diagonal3_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 3) ≠ 2),
      Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 3) ≠ 2), Matrix.diagonal_apply_eq, mul_zero, mul_zero, zero_add,
      zero_add, Pi.inv_apply, Units.val_inv_eq_inv_val]
    have : (!![(1 : v.adicCompletion ℚ), -x, x * y - z; 0, 1, -y; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = 1 := rfl
    rw [this, one_mul]
  have hv12 : Valued.v ((δ 1 : v.adicCompletion ℚ) * y) ≤ WithZero.exp (M : ℤ) := by
    rw [← hu12, Units.val_mul]
    exact LanglandsTunnell.CubicInduction.Core12.valued_mul_le_of_right_integral v (fun i l => (hM X hX i l).1) hwint 1 2
  have hv22 : Valued.v (((δ 2 : v.adicCompletion ℚ))⁻¹) ≤ WithZero.exp (M : ℤ) := by
    rw [← hu22, _root_.mul_inv_rev, Units.val_mul]
    exact LanglandsTunnell.CubicInduction.Core12.valued_mul_le_of_left_integral v hwinvint (fun l j => (hM X hX l j).2) 2 2
  have hvst : Valued.v ((t : v.adicCompletion ℚ) / (s : v.adicCompletion ℚ) - 1) ≤ 1 := by
    rw [div_sub_one s.ne_zero, map_div₀, hs1, div_one]
    exact le_trans (Valuation.map_sub _ _ _) (max_le ht1.le hs1.le)
  have hrew : α * ((t : v.adicCompletion ℚ) / (s : v.adicCompletion ℚ) - 1) * y =
      ((a 1 : v.adicCompletion ℚ) / (a 2 : v.adicCompletion ℚ)) * (((δ 1 : v.adicCompletion ℚ) * y) *
        ((δ 2 : v.adicCompletion ℚ))⁻¹) * ((t : v.adicCompletion ℚ) / (s : v.adicCompletion ℚ) - 1) := by
    simp only [hα, hA1, hA2, div_eq_mul_inv, mul_inv]
    ring
  rw [hrew, map_mul, map_mul, map_mul]
  calc Valued.v ((a 1 : v.adicCompletion ℚ) / (a 2 : v.adicCompletion ℚ)) *
        (Valued.v ((δ 1 : v.adicCompletion ℚ) * y) * Valued.v (((δ 2 : v.adicCompletion ℚ))⁻¹)) *
        Valued.v ((t : v.adicCompletion ℚ) / (s : v.adicCompletion ℚ) - 1)
      ≤ WithZero.exp (-((2 * M : ℕ) : ℤ)) * (WithZero.exp (M : ℤ) * WithZero.exp (M : ℤ)) * 1 := by
        gcongr
    _ = 1 := by
        rw [mul_one, ← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_zero]
        congr 1
        push_cast
        ring

end S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd (solution)
