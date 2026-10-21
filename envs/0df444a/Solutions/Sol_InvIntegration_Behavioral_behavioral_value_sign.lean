-- Prove2me | solution 1 for InvIntegration.Behavioral.behavioral_value_sign
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T19:14:53.423409+00:00
-- url     : https://prove2.me/submissions/a7706098-6a3f-4323-a426-e1c8ff6c8c1e

import Mathlib
import Definitions.Def_InvIntegration_Behavioral_Model

namespace InvIntegration.Behavioral
open MeasureTheory ProbabilityTheory

lemma iib_G_vh (P : Params) (hS : P.Standing) : G P P.vh = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, hint, -, hsupp, -, h1, -⟩ := hS
  unfold G
  have h := integral_add_compl (s := Set.Iic P.vh) measurableSet_Iic hint
  rw [Set.compl_Iic] at h
  have h0 : ∫ t in Set.Ioi P.vh, P.g t = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    apply hsupp
    intro hx'
    exact absurd hx'.2 (not_lt.mpr (le_of_lt hx))
  linarith

lemma iib_one_sub_G (P : Params) (hS : P.Standing) (x : ℝ) :
    1 - G P x = ∫ t in Set.Ioi x, P.g t := by
  obtain ⟨-, -, -, -, -, -, -, -, hint, -, -, -, h1, -⟩ := hS
  unfold G
  have h := integral_add_compl (s := Set.Iic x) measurableSet_Iic hint
  rw [Set.compl_Iic] at h
  linarith

lemma iib_G_sub (P : Params) (hS : P.Standing) (a b : ℝ) (hab : a ≤ b) :
    G P b - G P a = ∫ t in Set.Ioc a b, P.g t := by
  obtain ⟨-, -, -, -, -, -, -, -, hint, -, -, -, -, -⟩ := hS
  unfold G
  rw [← Set.Iic_union_Ioc_eq_Iic hab, setIntegral_union (Set.Iic_disjoint_Ioc le_rfl)
    measurableSet_Ioc hint.integrableOn hint.integrableOn]
  ring

lemma iib_pos_of_sub (P : Params) (hS : P.Standing) (s a : Set ℝ) (hsub : s ⊆ a)
    (hpos : 0 < ∫ t in s, P.g t) : 0 < ∫ t in a, P.g t := by
  obtain ⟨-, -, -, -, -, -, -, -, hint, hnn, -, -, -, -⟩ := hS
  refine lt_of_lt_of_le hpos ?_
  apply setIntegral_mono_set hint.integrableOn
  · exact Filter.Eventually.of_forall (fun x => hnn x)
  · exact Filter.Eventually.of_forall hsub

lemma iib_G_strict (P : Params) (hS : P.Standing) (a b : ℝ) (ha : P.vl < a) (hab : a < b)
    (hb : b ≤ P.vh) : G P a < G P b := by
  have hsupp := hS.2.2.2.2.2.2.2.2.2.2.2.1
  rw [← sub_pos, iib_G_sub P hS a b hab.le]
  have hvh : a < P.vh := lt_of_lt_of_le hab hb
  set b' := min b ((a + P.vh) / 2)
  have h1 : a < b' := lt_min hab (by linarith)
  have h2 : b' < P.vh := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  apply iib_pos_of_sub P hS (Set.Ioo a b') _ _ (hsupp a b' ha h2 h1)
  intro x hx
  exact ⟨hx.1, le_trans hx.2.le (min_le_left _ _)⟩

lemma iib_Gbar_pos (P : Params) (hS : P.Standing) (v : ℝ) (hv : v < P.vh) (hvl : P.vl < v) :
    0 < Gbar P v := by
  have hsupp := hS.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Gbar
  rw [iib_one_sub_G P hS v]
  apply iib_pos_of_sub P hS (Set.Ioo v ((v + P.vh) / 2)) _ _
    (hsupp v ((v + P.vh) / 2) hvl (by linarith) (by linarith))
  intro x hx; exact hx.1

lemma iib_vstar_ge (P : Params) (hS : P.Standing) (ξ : ℝ) : P.p ≤ vstar P ξ := by
  have hpvh := hS.2.2.2.2.2.2.1
  unfold vstar
  split_ifs
  · exact hpvh.le
  · exact le_min hpvh.le (le_max_right _ _)

lemma iib_frac_le (P : Params) (hS : P.Standing) (ξ : ℝ) (hξ : ξ ≤ 0) :
    (P.p - ξ * P.s) / (1 - ξ * P.δ) ≤ P.p := by
  obtain ⟨-, -, hδ, -, hsδ, -⟩ := hS
  have h1 : 0 < 1 - ξ * P.δ := by nlinarith
  rw [div_le_iff₀ h1]
  nlinarith

lemma iib_frac_ge (P : Params) (hS : P.Standing) (ξ : ℝ) (hξ : 0 ≤ ξ) (h : ξ * P.δ < 1) :
    P.p ≤ (P.p - ξ * P.s) / (1 - ξ * P.δ) := by
  obtain ⟨-, -, hδ, -, hsδ, -⟩ := hS
  have h1 : 0 < 1 - ξ * P.δ := by linarith
  rw [le_div_iff₀ h1]
  nlinarith

lemma iib_vstar_nonpos (P : Params) (hS : P.Standing) (ξ : ℝ) (hξ : ξ ≤ 0) :
    vstar P ξ = P.p := by
  have hpvh := hS.2.2.2.2.2.2.1
  have hδ := hS.2.2.1
  unfold vstar
  rw [if_neg (by nlinarith), max_eq_right (iib_frac_le P hS ξ hξ), min_eq_right hpvh.le]

/-- Any equilibrium has `v < vh`. -/
lemma iib_eq_lt_vh (P : Params) (hS : P.Standing) (m sd q v ξ : ℝ) (hm : 0 ≤ m)
    (hE : IsEquilibrium P m sd q v ξ) : v < P.vh := by
  obtain ⟨hmax, hv, hξ⟩ := hE
  have hsc : P.s < P.c := hS.1
  have hcp : P.c < P.p := hS.2.1
  have hpvh := hS.2.2.2.2.2.2.1
  by_contra hcon
  have hvge : P.vh ≤ v := le_of_not_gt hcon
  have hvle : v ≤ P.vh := by
    rw [hv]; unfold vstar; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hveq : v = P.vh := le_antisymm hvle hvge
  have hGb : Gbar P v = 0 := by rw [hveq]; unfold Gbar; rw [iib_G_vh P hS]; ring
  -- profit is constant in x
  have hprof : ∀ q', profit P m sd v q' = (P.p - P.s) * min q' 0 - (P.c - P.s) * q' := by
    intro q'
    unfold profit demandLaw
    simp [hGb]
  have hq : q ≤ 0 := by
    have := hmax 0
    rw [hprof, hprof] at this
    by_contra hq; push Not at hq
    rw [min_eq_right hq.le] at this
    simp at this
    nlinarith
  have hξle : ξ ≤ 0 := by
    rw [hξ]; unfold fill2
    simp only []
    apply div_nonpos_of_nonpos_of_nonneg
    · apply integral_nonpos
      intro x
      simp only [hGb, zero_mul, sub_zero, max_eq_right hq]
      exact min_le_left _ _
    · exact mul_nonneg (le_max_right _ _) hm
  have := iib_vstar_nonpos P hS ξ hξle
  rw [← hv] at this
  linarith

end InvIntegration.Behavioral

open InvIntegration.Behavioral in
theorem solution (P : Params) (hS : P.Standing) (σ : ℝ) (hσ : 0 < σ)
    (hPi : 0 < Pi P P.μ σ) (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    (qm vm ξm qI vI ξI : ℝ) (hm : IsEquilibrium P P.μ σ qm vm ξm)
    (hI : IsEquilibrium P (2 * P.μ) (sdI σ ρ) qI vI ξI) :
    (vI < vm → 0 < behavioralValue P σ ρ vm vI) ∧
    (vm < vI → behavioralValue P σ ρ vm vI < 0) := by
  have hμ : 0 < P.μ := hS.2.2.2.2.2.2.2.1
  have hcp : P.c < P.p := hS.2.1
  have hvlp : P.vl < P.p := hS.2.2.2.2.2.1
  have hmlt := iib_eq_lt_vh P hS _ _ _ _ _ hμ.le hm
  have hIlt := iib_eq_lt_vh P hS _ _ _ _ _ (by linarith) hI
  have hmge : P.p ≤ vm := by rw [hm.2.1]; exact iib_vstar_ge P hS _
  have hIge : P.p ≤ vI := by rw [hI.2.1]; exact iib_vstar_ge P hS _
  have hGb : 0 < Gbar P vm := iib_Gbar_pos P hS vm hmlt (by linarith)
  -- positivity of the profit ratio
  have hsq0 : 0 ≤ Real.sqrt (2 * (1 + ρ)) := Real.sqrt_nonneg _
  have hsq2 : Real.sqrt (2 * (1 + ρ)) < 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 2)]
    nlinarith [hρ.2]
  have hPI : 0 < Pi P (2 * P.μ) (sdI σ ρ) := by
    unfold Pi sdI at *
    set K := (P.p - P.s) * lossN P + (P.c - P.s) * P.zh
    have e1 : (P.p - P.c) * P.μ - (P.p - P.s) * σ * lossN P - (P.c - P.s) * P.zh * σ
        = (P.p - P.c) * P.μ - K * σ := by ring
    have e2 : (P.p - P.c) * (2 * P.μ) - (P.p - P.s) * (Real.sqrt (2 * (1 + ρ)) * σ) * lossN P
        - (P.c - P.s) * P.zh * (Real.sqrt (2 * (1 + ρ)) * σ)
        = 2 * ((P.p - P.c) * P.μ) - K * (Real.sqrt (2 * (1 + ρ)) * σ) := by ring
    rw [e1] at hPi; rw [e2]
    rcases le_or_gt 0 K with hK | hK
    · have : K * (Real.sqrt (2 * (1 + ρ)) * σ) ≤ K * (2 * σ) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hK
      nlinarith
    · have : K * (Real.sqrt (2 * (1 + ρ)) * σ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hK.le (mul_nonneg hsq0 hσ.le)
      nlinarith
  have hratio : 0 < Pi P (2 * P.μ) (sdI σ ρ) / (2 * Pi P P.μ σ) := by positivity
  unfold behavioralValue
  constructor
  · intro h
    have := iib_G_strict P hS vI vm (by linarith) h hmlt.le
    apply mul_pos (div_pos (by linarith) hGb) hratio
  · intro h
    have := iib_G_strict P hS vm vI (by linarith) h hIlt.le
    apply mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith) hGb) hratio
