-- Prove2me | solution 1 for HackCosmologicalAQFT.big_bang
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:35:13.436365+00:00
-- url     : https://prove2.me/submissions/f154bde8-071c-4317-95c9-f794d259675c

import Mathlib
import Definitions.Def_hack_flrw_friedmann

open HackCosmologicalAQFT in
theorem solution (G : ℝ) (hG : 0 < G) (a ρ p : ℝ → ℝ)
    (ha_cont : Continuous a)
    (ha_diff : ContDiffOn ℝ 2 a {t | 0 < a t})
    (hF2 : SecondFriedmannEq G a ρ p {t | 0 < a t})
    (hSEC : ∀ t, 0 < a t → 0 < ρ t + 3 * p t)
    (t₁ : ℝ) (ha₁ : 0 < a t₁) (hexp : 0 < deriv a t₁) :
    ∃ t₀ < t₁, a t₀ = 0 ∧ ∀ t ∈ Set.Ioc t₀ t₁, 0 < a t := by
  have hπ := Real.pi_pos
  have hUo : IsOpen {t | 0 < a t} := isOpen_lt continuous_const ha_cont
  have hdd : ContDiffOn ℝ 1 (deriv a) {t | 0 < a t} :=
    ha_diff.deriv_of_isOpen hUo (by norm_num)
  have hneg : ∀ t, 0 < a t → deriv (deriv a) t < 0 := by
    intro t ht
    have h := hF2 t ht
    have h3 : -(4 * Real.pi * G / 3) * (ρ t + 3 * p t) < 0 := by
      have := hSEC t ht
      have : 0 < 4 * Real.pi * G / 3 := by positivity
      nlinarith
    rw [← h] at h3
    have : deriv (deriv a) t = deriv (deriv a) t / a t * a t := by field_simp
    rw [this]; exact mul_neg_of_neg_of_pos h3 ht
  have hderiv : ∀ x, 0 < a x → HasDerivAt a (deriv a x) x := fun x hx =>
    ((ha_diff.differentiableOn (by norm_num)).differentiableAt (hUo.mem_nhds hx)).hasDerivAt
  set v := deriv a t₁ with hv
  obtain ⟨T, hT⟩ : ∃ T, T = t₁ - a t₁ / v - 1 := ⟨_, rfl⟩
  have hTle : T ≤ t₁ := by
    have : 0 < a t₁ / v := div_pos ha₁ hexp
    linarith
  have hS : ∃ s ∈ Set.Icc T t₁, a s ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have hsub : Set.Icc T t₁ ⊆ {t | 0 < a t} := fun s hs => hcon s hs
    have hanti : AntitoneOn (deriv a) (Set.Icc T t₁) :=
      antitoneOn_of_deriv_nonpos (convex_Icc T t₁) (hdd.continuousOn.mono hsub)
        ((hdd.differentiableOn (by norm_num)).mono (interior_subset.trans hsub))
        (fun x hx => (hneg x (hsub (interior_subset hx))).le)
    have hmono : MonotoneOn (fun s => a s - v * s) (Set.Icc T t₁) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc T t₁)
      · exact (ha_cont.sub (continuous_const.mul continuous_id)).continuousOn
      · intro x hx
        exact ((hderiv x (hsub (interior_subset hx))).sub
          ((hasDerivAt_id x).const_mul v)).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' := interior_subset hx
        have hx2 : HasDerivAt (fun s => a s - v * s) (deriv a x - v) x := by
          have := (hderiv x (hsub hx')).sub ((hasDerivAt_id x).const_mul v)
          simp only [mul_one] at this
          exact this
        rw [hx2.deriv]
        have := hanti hx' (Set.right_mem_Icc.mpr hTle) hx'.2
        linarith
    have h := hmono (Set.left_mem_Icc.mpr hTle) (Set.right_mem_Icc.mpr hTle) hTle
    simp only at h
    have hvT : v * T = v * t₁ - a t₁ - v := by
      rw [hT]; field_simp
    have := hcon T (Set.left_mem_Icc.mpr hTle)
    linarith
  set S := Set.Iic t₁ ∩ {t | a t ≤ 0} with hSdef
  have hclosed : IsClosed S := isClosed_Iic.inter (isClosed_le ha_cont continuous_const)
  have hne : S.Nonempty := by
    obtain ⟨s, hs, has⟩ := hS
    exact ⟨s, hs.2, has⟩
  have hbdd : BddAbove S := ⟨t₁, fun s hs => hs.1⟩
  have hmem : sSup S ∈ S := hclosed.csSup_mem hne hbdd
  have hle : sSup S ≤ t₁ := hmem.1
  have hlt : sSup S < t₁ := by
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso; have := hmem.2; simp only [Set.mem_setOf_eq] at this; rw [h] at this; linarith
  refine ⟨sSup S, hlt, ?_, ?_⟩
  · obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hle ha_cont.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (a (sSup S)) (a t₁) from ⟨hmem.2, ha₁.le⟩)
    have hcS : c ∈ S := ⟨hc.2, by simp [hc0]⟩
    have := le_csSup hbdd hcS
    have hceq : c = sSup S := le_antisymm this hc.1
    rw [← hceq, hc0]
  · intro t ht
    by_contra hcon
    push_neg at hcon
    have := le_csSup hbdd (show t ∈ S from ⟨ht.2, hcon⟩)
    linarith [ht.1]
