-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_mixture
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:33:00.774995+00:00
-- url     : https://prove2.me/submissions/d6b5f4e7-e7d5-458b-9622-ab296021a817

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory
theorem h44_persp (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    y * Real.negMulLog (x / y) = Real.negMulLog x + x * Real.log y := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · subst h0; simp
  · have hy : 0 < y := lt_of_lt_of_le hpos hxy
    simp only [Real.negMulLog]
    rw [Real.log_div hpos.ne' hy.ne']
    field_simp
    ring

theorem h44_psi_sup {ι : Type*} (t : Finset ι) (x y : ι → ℝ) (Y : ℝ)
    (hx : ∀ i ∈ t, 0 ≤ x i) (hxy : ∀ i ∈ t, x i ≤ y i) (hY : ∑ i ∈ t, y i ≤ Y) :
    ∑ i ∈ t, (Real.negMulLog (x i) + x i * Real.log (y i)) ≤
      Real.negMulLog (∑ i ∈ t, x i) + (∑ i ∈ t, x i) * Real.log Y := by
  set S := ∑ i ∈ t, y i with hS
  set X := ∑ i ∈ t, x i with hX
  have hy0 : ∀ i ∈ t, 0 ≤ y i := fun i hi => (hx i hi).trans (hxy i hi)
  have hX0 : 0 ≤ X := Finset.sum_nonneg hx
  have hXS : X ≤ S := Finset.sum_le_sum hxy
  have hS0 : 0 ≤ S := Finset.sum_nonneg hy0
  rcases eq_or_lt_of_le hS0 with hS0' | hSpos
  · have hyz : ∀ i ∈ t, y i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hy0).mp hS0'.symm
    have hxz : ∀ i ∈ t, x i = 0 := fun i hi =>
      le_antisymm ((hxy i hi).trans (hyz i hi).le) (hx i hi)
    have : X = 0 := Finset.sum_eq_zero hxz
    rw [this, Finset.sum_eq_zero (fun i hi => by rw [hxz i hi]; simp)]
    simp
  · have e1 : ∀ i ∈ t, Real.negMulLog (x i) + x i * Real.log (y i) =
        S * ((y i / S) * Real.negMulLog (x i / y i)) := by
      intro i hi
      rw [← h44_persp _ _ (hx i hi) (hxy i hi)]
      field_simp
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
    have hJ := Real.concaveOn_negMulLog.le_map_sum (t := t) (w := fun i => y i / S)
      (p := fun i => x i / y i) (fun i hi => div_nonneg (hy0 i hi) hSpos.le)
      (by rw [← Finset.sum_div, div_self hSpos.ne'])
      (fun i hi => Set.mem_Ici.mpr (div_nonneg (hx i hi) (hy0 i hi)))
    simp only [smul_eq_mul] at hJ
    have e2 : ∑ i ∈ t, y i / S * (x i / y i) = X / S := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      rcases eq_or_ne (y i) 0 with h | h
      · have : x i = 0 := le_antisymm ((hxy i hi).trans h.le) (hx i hi)
        simp [h, this]
      · field_simp
    rw [e2] at hJ
    have h3 := mul_le_mul_of_nonneg_left hJ hSpos.le
    rw [h44_persp _ _ hX0 hXS] at h3
    refine h3.trans ?_
    gcongr

theorem h44_psi_smul (w x y : ℝ) (hw : 0 ≤ w) (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.negMulLog (w * x) + w * x * Real.log (w * y) =
      w * (Real.negMulLog x + x * Real.log y) := by
  rcases eq_or_lt_of_le hw with h0 | hwp
  · subst h0; simp
  rcases eq_or_lt_of_le hx with h0 | hxp
  · subst h0; simp
  have hy : 0 < y := lt_of_lt_of_le hxp hxy
  rw [Real.negMulLog_mul, Real.log_mul hwp.ne' hy.ne']
  simp only [Real.negMulLog]; ring

theorem h44_cond_psi {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) :
    conditionalEntropy s p f g = ∑ x ∈ s.image (fun a => (f a, g a)),
      (Real.negMulLog (mass s p (fun a => (f a, g a)) x) +
        mass s p (fun a => (f a, g a)) x * Real.log (mass s p g x.2)) := by
  classical
  unfold conditionalEntropy observableEntropy entropy
  rw [Finset.sum_add_distrib]
  have h := sum_mass_mul (s.image (fun a => (f a, g a))) (s.image g)
    (mass s p (fun a => (f a, g a))) Prod.snd (fun c => Real.log (mass s p g c))
    (fun x hx => by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image_of_mem g ha)
  beta_reduce at h
  rw [← h]
  have e : ∀ c, mass (s.image (fun a => (f a, g a))) (mass s p (fun a => (f a, g a)))
      Prod.snd c = mass s p g c := fun c => mass_comp s p _ Prod.snd c
  simp only [e, Real.negMulLog]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem h44_mass_le {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (hp : ∀ a ∈ s, 0 ≤ p a) (F : α → β) (G : α → γ) (x : β) (y : γ)
    (hFG : ∀ a ∈ s, F a = x → G a = y) : mass s p F x ≤ mass s p G y := by
  unfold mass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    obtain ⟨has, hax⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨has, hFG a has hax⟩
  · intro a ha _; exact hp a (Finset.mem_filter.mp ha).1

theorem solution {ι : Type uι} {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq ι] [DecidableEq β] [DecidableEq γ]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) (g : α → γ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hp : ∀ i ∈ t, ∀ a ∈ s, 0 ≤ p i a)
    (hp1 : ∀ i ∈ t, ∑ a ∈ s, p i a = 1) :
    (∑ i ∈ t, w i*conditionalEntropy s (p i) f g) ≤
      conditionalEntropy s (fun a => ∑ i ∈ t, w i*p i a) f g := by
  classical
  have hlin1 : ∀ x, mass s (fun a => ∑ i ∈ t, w i*p i a) (fun a => (f a, g a)) x =
      ∑ i ∈ t, w i * mass s (p i) (fun a => (f a, g a)) x := by
    intro x; unfold mass; simp only [Finset.mul_sum]; rw [Finset.sum_comm]
  have hlin2 : ∀ x, mass s (fun a => ∑ i ∈ t, w i*p i a) g x =
      ∑ i ∈ t, w i * mass s (p i) g x := by
    intro x; unfold mass; simp only [Finset.mul_sum]; rw [Finset.sum_comm]
  rw [h44_cond_psi s (fun a => ∑ i ∈ t, w i*p i a) f g]
  have e : ∀ i ∈ t, w i * conditionalEntropy s (p i) f g =
      ∑ x ∈ s.image (fun a => (f a, g a)),
        (Real.negMulLog (w i * mass s (p i) (fun a => (f a, g a)) x) +
          w i * mass s (p i) (fun a => (f a, g a)) x * Real.log (w i * mass s (p i) g x.2)) := by
    intro i hi
    rw [h44_cond_psi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact (h44_psi_smul _ _ _ (hw i hi) (mass_nonneg s (p i) _ (hp i hi) x)
      (h44_mass_le s (p i) (hp i hi) _ _ x x.2 (fun a _ hax => by rw [← hax]))).symm
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [hlin1, hlin2]
  exact h44_psi_sup t (fun i => w i * mass s (p i) (fun a => (f a, g a)) x)
    (fun i => w i * mass s (p i) g x.2) _
    (fun i hi => mul_nonneg (hw i hi) (mass_nonneg s (p i) _ (hp i hi) x))
    (fun i hi => mul_le_mul_of_nonneg_left
      (h44_mass_le s (p i) (hp i hi) _ _ x x.2 (fun a _ hax => by rw [← hax])) (hw i hi))
    le_rfl

