-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isOpen_forall_apply_mul_iotaGL_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1009edfa-dc7d-5dd8-93f7-8e1e97d38436

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq.IwasawaGL3"

namespace SmoothVectorTopology

theorem exists_open_forall_mem_compact_apply_mul_eq {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] {Z : Type*} {f : G → Z} (hf : IsLocallyConstant f) {C : Set G} (hC : IsCompact C) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ ∀ c ∈ C, ∀ r ∈ V, f (c * r) = f c := by
  have hF : IsLocallyConstant fun q : G × G => (f (q.1 * q.2), f q.1) :=
    (hf.comp_continuous continuous_mul).prodMk (hf.comp_continuous continuous_fst)
  have hn : IsOpen ((fun q : G × G => (f (q.1 * q.2), f q.1)) ⁻¹' {z : Z × Z | z.1 = z.2}) := hF _
  have hsub : C ×ˢ ({1} : Set G) ⊆
      ((fun q : G × G => (f (q.1 * q.2), f q.1)) ⁻¹' {z : Z × Z | z.1 = z.2}) := by
    rintro ⟨c, r⟩ ⟨-, hr⟩
    rw [Set.mem_singleton_iff] at hr
    subst hr
    show f (c * 1) = f c
    rw [mul_one]
  obtain ⟨U₁, V, -, hV, hCU, h1V, hUV⟩ := generalized_tube_lemma hC isCompact_singleton hn hsub
  refine ⟨V, hV, h1V (Set.mem_singleton 1), fun c hc r hr => ?_⟩
  exact hUV (Set.mk_mem_prod (hCU hc) hr)

def stab {G : Type*} [Group G] {Z : Type*} (f : G → Z) : Subgroup G where
  carrier := {u | ∀ g : G, f (g * u) = f g}
  one_mem' g := by rw [mul_one]
  mul_mem' {a b} ha hb g := by rw [← mul_assoc, hb, ha]
  inv_mem' {a} ha g := by
    have h := ha (g * a⁻¹)
    rw [inv_mul_cancel_right] at h
    exact h.symm

theorem mem_stab_iff {G : Type*} [Group G] {Z : Type*} {f : G → Z} {u : G} :
    u ∈ stab f ↔ ∀ g : G, f (g * u) = f g :=
  Iff.rfl

theorem isOpen_stab_of_nhds {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] {Z : Type*}
    {f : G → Z} {V : Set G} (hV : IsOpen V) (h1V : (1 : G) ∈ V) (hVf : ∀ g : G, ∀ r ∈ V, f (g * r) = f g) :
    IsOpen (stab f : Set G) :=
  Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hV.mem_nhds h1V) fun r hr g => hVf g r hr)

def conjInf {G : Type*} [Group G] (S : Subgroup G) (Y : Set G) : Subgroup G where
  carrier := {u | ∀ y ∈ Y, y⁻¹ * u * y ∈ S}
  one_mem' y hy := by
    rw [mul_one, inv_mul_cancel]
    exact one_mem S
  mul_mem' {a b} ha hb y hy := by
    have h := S.mul_mem (ha y hy) (hb y hy)
    rwa [show y⁻¹ * a * y * (y⁻¹ * b * y) = y⁻¹ * (a * b) * y by group] at h
  inv_mem' {a} ha y hy := by
    have h := S.inv_mem (ha y hy)
    rwa [show (y⁻¹ * a * y)⁻¹ = y⁻¹ * a⁻¹ * y by group] at h

theorem mem_conjInf_iff {G : Type*} [Group G] {S : Subgroup G} {Y : Set G} {u : G} :
    u ∈ conjInf S Y ↔ ∀ y ∈ Y, y⁻¹ * u * y ∈ S :=
  Iff.rfl

theorem isOpen_conjInf_image_union_image {X G : Type*} [TopologicalSpace X] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (S : Subgroup G) (hS : IsOpen (S : Set G)) {K : Set X} (hK : IsCompact K)
    {y₁ y₂ : X → G} (hy₁ : Continuous y₁) (hy₂ : Continuous y₂) :
    IsOpen (conjInf S (y₁ '' K ∪ y₂ '' K) : Set G) := by
  have hn : IsOpen {q : X × G | (y₁ q.1)⁻¹ * q.2 * y₁ q.1 ∈ S ∧ (y₂ q.1)⁻¹ * q.2 * y₂ q.1 ∈ S} := by
    refine IsOpen.inter ?_ ?_
    · exact hS.preimage ((((hy₁.comp continuous_fst).inv).mul continuous_snd).mul (hy₁.comp continuous_fst))
    · exact hS.preimage ((((hy₂.comp continuous_fst).inv).mul continuous_snd).mul (hy₂.comp continuous_fst))
  have hsub : K ×ˢ ({1} : Set G) ⊆
      {q : X × G | (y₁ q.1)⁻¹ * q.2 * y₁ q.1 ∈ S ∧ (y₂ q.1)⁻¹ * q.2 * y₂ q.1 ∈ S} := by
    rintro ⟨k, u⟩ ⟨-, hu⟩
    rw [Set.mem_singleton_iff] at hu
    subst hu
    refine ⟨?_, ?_⟩ <;>
    · show _ ∈ S
      rw [mul_one, inv_mul_cancel]
      exact one_mem S
  obtain ⟨U₁, V, -, hV, hKU, h1V, hUV⟩ := generalized_tube_lemma hK isCompact_singleton hn hsub
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hV.mem_nhds (h1V (Set.mem_singleton 1))) ?_)
  intro u hu y hy
  rcases hy with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact (hUV (Set.mk_mem_prod (hKU hk) hu)).1
  · exact (hUV (Set.mk_mem_prod (hKU hk) hu)).2

end SmoothVectorTopology
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq.IwasawaGL3"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 coefficientFn upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL LocalGL3"
namespace SmoothVector
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq.IwasawaGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq.SmoothVectorTopology"

variable (v : HeightOneSpectrum (𝓞 ℚ))

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

variable {v}

theorem exists_apply_upper_mul {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (u : LocalGL3 v)
    (h10 : (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0)
    (h20 : (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (u : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0) :
    ∃ c : ℂ, ∀ r : LocalGL3 v, f (u * r) = c * f r := by
  obtain ⟨a, x, y, z, rfl⟩ := exists_eq_diagonal3_mul_upperUnipotent3 v u h10 h20 h21
  refine ⟨torusChar3 v χ a * halfModulus3 v a, fun r => ?_⟩
  rw [mul_assoc (diagonal3 v a), apply_diagonal3_mul_of_mem_principalSeries3 hf,
    apply_upperUnipotent3_mul_of_mem_principalSeries3 hf]

theorem exists_apply_mul_eq_mul_apply_wordInv_mul {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) (g : LocalGL3 v) :
    ∃ (p : Fin 6 → v.adicCompletion ℚ) (c : ℂ), (∀ i, Valued.v (p i) ≤ 1) ∧
      ∀ r : LocalGL3 v, f (g * r) = c * f ((word p)⁻¹ * r) := by
  obtain ⟨p, hp, h10, h20, h21⟩ := exists_word (Valued.v : Valuation (v.adicCompletion ℚ) _) g
  obtain ⟨c, hc⟩ := exists_apply_upper_mul hf (g * word p) h10 h20 h21
  refine ⟨p, c, hp, fun r => ?_⟩
  rw [← hc, mul_assoc, mul_inv_cancel_left]

def wordInvSet (v : HeightOneSpectrum (𝓞 ℚ)) : Set (LocalGL3 v) :=
  (fun p : Fin 6 → v.adicCompletion ℚ => (word p)⁻¹) ''
    Set.pi Set.univ (fun _ => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))

theorem isCompact_wordInvSet (v : HeightOneSpectrum (𝓞 ℚ)) : IsCompact (wordInvSet v) := by
  refine IsCompact.image (isCompact_univ_pi fun _ => ?_) continuous_word_inv
  exact isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers ℚ)))

theorem wordInv_mem_wordInvSet {p : Fin 6 → v.adicCompletion ℚ} (hp : ∀ i, Valued.v (p i) ≤ 1) :
    (word p)⁻¹ ∈ wordInvSet v :=
  ⟨p, fun i _ => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (hp i), rfl⟩

theorem exists_nhds_forall_apply_mul_eq {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) :
    ∃ V : Set (LocalGL3 v), IsOpen V ∧ (1 : LocalGL3 v) ∈ V ∧ ∀ g : LocalGL3 v, ∀ r ∈ V, f (g * r) = f g := by
  obtain ⟨V, hV, h1V, hCV⟩ := exists_open_forall_mem_compact_apply_mul_eq
    (isLocallyConstant_of_mem_principalSeries3 hf) (isCompact_wordInvSet v)
  refine ⟨V, hV, h1V, fun g r hr => ?_⟩
  obtain ⟨p, c, hp, hgc⟩ := exists_apply_mul_eq_mul_apply_wordInv_mul hf g
  have h := hCV _ (wordInv_mem_wordInvSet hp) r hr
  rw [hgc r, h, ← mul_one (word p)⁻¹, ← hgc 1, mul_one]

theorem isOpen_stab {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) : IsOpen (stab f : Set (LocalGL3 v)) := by
  obtain ⟨V, hV, h1V, hVf⟩ := exists_nhds_forall_apply_mul_eq hf
  exact isOpen_stab_of_nhds hV h1V hVf

theorem coefficientFn_mul_mul_eq {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)) {y u : LocalGL3 v}
    (h : y⁻¹ * u * y ∈ stab (f : LocalGL3 v → ℂ)) (x : LocalGL3 v) :
    coefficientFn Λ f (x * u * y) = coefficientFn Λ f (x * y) := by
  unfold coefficientFn
  refine congrArg Λ (Subtype.ext (funext fun g => ?_))
  show (f : LocalGL3 v → ℂ) (g * (x * u * y)) = (f : LocalGL3 v → ℂ) (g * (x * y))
  rw [← h (g * (x * y))]
  simp only [mul_assoc, mul_inv_cancel_left]

theorem continuous_iotaGL :
    Continuous (iotaGL : GL (Fin 2) (v.adicCompletion ℚ) → LocalGL3 v) := by
  have hc : ∀ a b : Fin 2, Continuous fun h : GL (Fin 2) (v.adicCompletion ℚ) =>
      ((h : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) a b :=
    fun a b => Units.continuous_val.matrix_elem a b
  have hc' : ∀ a b : Fin 2, Continuous fun h : GL (Fin 2) (v.adicCompletion ℚ) =>
      ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) a b :=
    fun a b => Units.continuous_coe_inv.matrix_elem a b
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun h : GL (Fin 2) (v.adicCompletion ℚ) =>
      embedMat2 ((h : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j
    fin_cases i <;> fin_cases j <;> simp [embedMat2, hc, continuous_const]
  · refine continuous_matrix fun i j => ?_
    show Continuous fun h : GL (Fin 2) (v.adicCompletion ℚ) =>
      embedMat2 ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j
    fin_cases i <;> fin_cases j <;> simp [embedMat2, hc', continuous_const, -Matrix.coe_units_inv]

end LanglandsTunnell.CubicInduction.SmoothVector
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq.IwasawaGL3"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq.IwasawaGL3"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq.IwasawaGL3"

open AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse

open scoped nonZeroDivisors

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SmoothVector SmoothVectorTopology in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (W : LocalGL3 v → ℂ)
    (hW : ∃ (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)), W = coefficientFn Λ f)
    (b : ℕ) (g₃ : LocalGL3 v) (k₀ : GL (Fin 2) (v.adicCompletion ℚ)) :
    ∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b), ∀ k' ∈ U, ∀ x : LocalGL3 v,
        W (x * k' * (iotaGL (k₀ * k) * g₃)) = W (x * (iotaGL (k₀ * k) * g₃)) ∧
        W (x * k' * (iotaGL (AutomorphicForm.transposeInvN (Fin 2) k₀ * k) * g₃)) =
          W (x * (iotaGL (AutomorphicForm.transposeInvN (Fin 2) k₀ * k) * g₃)) := by
  obtain ⟨Λ, f, rfl⟩ := hW

  have hK : IsCompact
      (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) : Set (GL (Fin 2) (v.adicCompletion ℚ))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ v (v.asIdeal ^ b) (pow_ne_zero _ v.ne_bot)).1

  have hy₁ : Continuous fun k : GL (Fin 2) (v.adicCompletion ℚ) => iotaGL (k₀ * k) * g₃ :=
    (continuous_iotaGL.comp (continuous_const.mul continuous_id)).mul continuous_const
  have hy₂ : Continuous fun k : GL (Fin 2) (v.adicCompletion ℚ) =>
      iotaGL (AutomorphicForm.transposeInvN (Fin 2) k₀ * k) * g₃ :=
    (continuous_iotaGL.comp (continuous_const.mul continuous_id)).mul continuous_const

  refine ⟨conjInf (stab (f : LocalGL3 v → ℂ))
      ((fun k : GL (Fin 2) (v.adicCompletion ℚ) => iotaGL (k₀ * k) * g₃) ''
          (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∪
        (fun k : GL (Fin 2) (v.adicCompletion ℚ) => iotaGL (AutomorphicForm.transposeInvN (Fin 2) k₀ * k) * g₃) ''
          (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) : Set (GL (Fin 2) (v.adicCompletion ℚ)))),
    isOpen_conjInf_image_union_image _ (isOpen_stab f.2) hK hy₁ hy₂, ?_⟩
  intro k hk k' hk' x
  rw [mem_conjInf_iff] at hk'
  have h₁ : (iotaGL (k₀ * k) * g₃)⁻¹ * k' * (iotaGL (k₀ * k) * g₃) ∈ stab (f : LocalGL3 v → ℂ) :=
    hk' _ (Or.inl ⟨k, hk, rfl⟩)
  have h₂ : (iotaGL (AutomorphicForm.transposeInvN (Fin 2) k₀ * k) * g₃)⁻¹ * k' *
      (iotaGL (AutomorphicForm.transposeInvN (Fin 2) k₀ * k) * g₃) ∈ stab (f : LocalGL3 v → ℂ) :=
    hk' _ (Or.inr ⟨k, hk, rfl⟩)
  exact ⟨coefficientFn_mul_mul_eq Λ f h₁ x, coefficientFn_mul_mul_eq Λ f h₂ x⟩

end S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq (solution)
