-- Prove2me | solution 1 for HuWang2023.meanDMIGM_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:16:36.707299+00:00
-- url     : https://prove2.me/submissions/06edba3d-66d1-44ea-8351-d8ace3f611e6

import Mathlib
import Definitions.Def_HuWang2023_HubbleTension_Defs
open HuWang2023

namespace HuWangAux

lemma inner_ge_one (Ωm z : ℝ) (hΩ : 0 ≤ Ωm) (hz : 0 ≤ z) : 1 ≤ Ωm * (1 + z) ^ 3 + (1 - Ωm) := by
  have : 1 ≤ (1 + z) ^ 3 := one_le_pow₀ (by linarith)
  nlinarith

lemma flatE_pos (Ωm z : ℝ) (hΩ : 0 ≤ Ωm) (hz : 0 ≤ z) : 0 < flatE Ωm z := by
  unfold flatE
  exact Real.sqrt_pos.mpr (by linarith [inner_ge_one Ωm z hΩ hz])

lemma continuousOn_inv_flatE (Ωm : ℝ) (hΩ : 0 ≤ Ωm) :
    ContinuousOn (fun z => (flatE Ωm z)⁻¹) (Set.Ici 0) := by
  apply ContinuousOn.inv₀
  · unfold flatE; fun_prop
  · intro z hz; exact (flatE_pos Ωm z hΩ hz).ne'

lemma intervalIntegrable_inv_flatE (Ωm a b : ℝ) (hΩ : 0 ≤ Ωm) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun z => (flatE Ωm z)⁻¹) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_inv_flatE Ωm hΩ).mono
  intro z hz
  rw [Set.mem_uIcc] at hz
  simp only [Set.mem_Ici]
  rcases hz with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith

end HuWangAux

theorem solution (A Ωb H0 Ωm : ℝ) (fIGM fe : ℝ → ℝ)
    (hA : 0 < A) (hΩb : 0 < Ωb) (hH0 : 0 < H0) (hΩm0 : 0 ≤ Ωm)
    (hfIGM_cont : ContinuousOn fIGM (Set.Ici 0)) (hfe_cont : ContinuousOn fe (Set.Ici 0))
    (hfIGM_pos : ∀ z, 0 ≤ z → 0 < fIGM z) (hfe_pos : ∀ z, 0 ≤ z → 0 < fe z) :
    StrictMonoOn (meanDMIGM A Ωb H0 Ωm fIGM fe) (Set.Ici 0) := by
  set F : ℝ → ℝ := fun z' => fIGM z' * fe z' * (1 + z') / Real.sqrt (Ωm * (1 + z') ^ 3 + 1 - Ωm)
    with hF
  have hin : ∀ z : ℝ, 0 ≤ z → 0 < Ωm * (1 + z) ^ 3 + 1 - Ωm := by
    intro z hz
    have := HuWangAux.inner_ge_one Ωm z hΩm0 hz
    linarith
  have hcont : ContinuousOn F (Set.Ici 0) := by
    apply ContinuousOn.div
    · exact (hfIGM_cont.mul hfe_cont).mul (by fun_prop)
    · fun_prop
    · intro z hz; exact (Real.sqrt_pos.mpr (hin z hz)).ne'
  have hFpos : ∀ z : ℝ, 0 ≤ z → 0 < F z := by
    intro z hz
    have := hfIGM_pos z hz
    have := hfe_pos z hz
    have := Real.sqrt_pos.mpr (hin z hz)
    have : 0 < 1 + z := by linarith
    simp only [hF]; positivity
  have hII : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → IntervalIntegrable F MeasureTheory.volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    apply hcont.mono
    intro z hz
    rw [Set.mem_uIcc] at hz
    simp only [Set.mem_Ici]
    rcases hz with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  unfold meanDMIGM
  have hpre : 0 < A * Ωb * H0 ^ 2 / H0 := by positivity
  apply mul_lt_mul_of_pos_left _ hpre
  have hsplit := intervalIntegral.integral_interval_sub_left (hII 0 b le_rfl hb) (hII 0 a le_rfl ha)
  have hposI : 0 < ∫ z in a..b, F z :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hII a b ha hb)
      (fun z hz => hFpos z (by linarith [hz.1])) hab
  have : (∫ z in (0 : ℝ)..b, F z) - ∫ z in (0 : ℝ)..a, F z > 0 := by rw [hsplit]; exact hposI
  simp only [hF] at this ⊢
  linarith
