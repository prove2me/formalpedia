-- Prove2me | solution 1 for MaxCutSample2027.Coreset.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-26T23:56:23.637484+00:00
-- url     : https://prove2.me/submissions/be9bab70-c8ca-4675-920b-20edab2523dc

import Definitions.Def_MaxCutSample2027_Coreset_fractional
open scoped BigOperators

set_option autoImplicit false

open MaxCutSample2027
open MaxCutSample2027.Coreset

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (r : V → ℝ) (hr : ∀ v, 0 ≤ r v) :
    ∃ a ∈ Z r, bilinear (K A p) a (r - a) = FK (K A p) r ∧
      ∀ v, a v = 0 ∨ a v = r v := by
  classical
  let f (a : V → ℝ) := bilinear (K A p) a (r - a)
  have hbox : Z r = Set.Icc (0 : V → ℝ) r := by
    ext a
    change (∀ v, 0 ≤ a v ∧ a v ≤ r v) ↔ (∀ v, 0 ≤ a v) ∧ ∀ v, a v ≤ r v
    exact forall_and
  have continuous_f : Continuous f := by
    unfold f bilinear
    simp only [Pi.sub_apply]
    fun_prop
  obtain ⟨a, ha, hmax⟩ := (hbox ▸ isCompact_Icc : IsCompact (Z r)).exists_isMaxOn
      ⟨0, fun v => ⟨le_rfl, hr v⟩⟩ continuous_f.continuousOn
  have diagonal (v : V) : K A p v v = 0 := by simp [K, hA.2.1]
  have improve (b : V → ℝ) (hb : b ∈ Z r) (v : V) : ∃ c ∈ Z r,
      f b ≤ f c ∧ (c v = 0 ∨ c v = r v) ∧ ∀ i, i ≠ v → c i = b i := by
    have update_mem (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ r v) : Function.update b v t ∈ Z r := by
      intro i
      by_cases hi : i = v
      · subst i
        simpa only [Function.update_self] using And.intro ht0 ht1
      · simpa only [Function.update_of_ne hi] using hb i
    rcases (hr v).eq_or_lt with hzero | hpos
    · exact ⟨b, hb, le_rfl, Or.inl (le_antisymm ((hb v).2.trans hzero.ge) (hb v).1), fun _ _ => rfl⟩
    let b₀ := Function.update b v 0
    let b₁ := Function.update b v (r v)
    have interpolate : r v * f b = (r v - b v) * f b₀ + b v * f b₁ := by
      unfold f bilinear
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Pi.sub_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hi : i = v <;> by_cases hj : j = v
      · subst i j
        simp [diagonal]
      · subst i
        simp only [b₀, b₁, Function.update_self, Function.update_of_ne hj]
        ring
      · subst j
        simp only [b₀, b₁, Function.update_self, Function.update_of_ne hi]
        ring
      · simp only [b₀, b₁, Function.update_of_ne hi, Function.update_of_ne hj]
        ring
    by_cases h : f b₀ ≤ f b₁
    · refine ⟨b₁, update_mem _ (hr v) le_rfl, ?_, Or.inr (Function.update_self _ _ _), ?_⟩
      · apply le_of_mul_le_mul_left _ hpos
        rw [interpolate]
        calc
          _ ≤ (r v - b v) * f b₁ + b v * f b₁ :=
            add_le_add (mul_le_mul_of_nonneg_left h (sub_nonneg.mpr (hb v).2)) le_rfl
          _ = _ := by ring
      · intro i hi
        exact Function.update_of_ne hi _ _
    · refine ⟨b₀, update_mem 0 le_rfl (hr v), ?_, Or.inl (Function.update_self _ _ _), ?_⟩
      · apply le_of_mul_le_mul_left _ hpos
        rw [interpolate]
        calc
          _ ≤ (r v - b v) * f b₀ + b v * f b₀ :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_of_not_ge h) (hb v).1)
          _ = _ := by ring
      · intro i hi
        exact Function.update_of_ne hi _ _
  have rounded (s : Finset V) : ∃ b ∈ Z r, IsMaxOn f (Z r) b ∧
      ∀ v ∈ s, b v = 0 ∨ b v = r v := by
    induction s using Finset.induction_on with
    | empty => exact ⟨a, ha, hmax, by simp⟩
    | @insert v s hv ih =>
      obtain ⟨b, hb, hopt, hdone⟩ := ih
      obtain ⟨c, hc, hbetter, hvertex, hrest⟩ := improve b hb v
      refine ⟨c, hc, isMaxOn_iff.mpr (fun x hx => (hopt hx).trans hbetter), ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hvertex
      · rw [hrest i (fun hieq => hv (hieq ▸ hi))]
        exact hdone i hi
  obtain ⟨b, hb, hbest, hcorners⟩ := rounded Finset.univ
  refine ⟨b, hb, ?_, fun v => hcorners v (Finset.mem_univ v)⟩
  change f b = sSup (f '' Z r)
  exact le_antisymm (le_csSup hbest.bddAbove ⟨b, hb, rfl⟩)
    (csSup_le ⟨_, b, hb, rfl⟩ (by rintro _ ⟨x, hx, rfl⟩; exact hbest hx))
