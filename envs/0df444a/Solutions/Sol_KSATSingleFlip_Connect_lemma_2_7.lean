-- Prove2me | solution 1 for KSATSingleFlip.Connect.lemma_2_7
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:21:51.247502+00:00
-- url     : https://prove2.me/submissions/06b5aec2-5715-42dd-951d-adec9e054b65

import Theorems.Thm_KSATSingleFlip_Connect_lemma_2_7_ball_bounds
import Theorems.Thm_KSATSingleFlip_Connect_lemma_2_7_changed_balls

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- A sum of [0,1]-valued observables changes by at most the number of
coordinates whose inputs change. -/
theorem audit_changed_coordinate_sum {A B : Type} [Fintype A] (u v : A → B)
    (f : A → B → ℝ) (hf : ∀ a b, 0 ≤ f a b ∧ f a b ≤ 1) :
    |(∑ a, f a (u a)) - ∑ a, f a (v a)| ≤
      ((Finset.univ.filter fun a => u a ≠ v a).card : ℝ) := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ a, (f a (u a) - f a (v a))| ≤ ∑ a, |f a (u a) - f a (v a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, if u a ≠ v a then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : u a = v a
      · simp [h]
      · rw [if_pos h]
        apply abs_le.mpr
        constructor <;> linarith [(hf a (u a)).1, (hf a (u a)).2, (hf a (v a)).1, (hf a (v a)).2]
    _ = _ := by simp [Finset.card_filter]

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

theorem solution {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) (k r D : ℕ)
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k) (hC : (vbl C).card ≤ k) :
    (∀ v, LocallyTree Φ v r D →
      (ballVars Φ v r).card + (ballIdx Φ v r).card ≤
        ∑ h ∈ Finset.range (r + 2), (k * D)^h) ∧
    (∀ u, (Finset.univ.filter fun v : Fin n =>
      LocallyTree Φ v r D ∧ u ∈ ballVars Φ v r).card ≤
        ∑ h ∈ Finset.range (r + 2), (k * D)^h) ∧
    ((Finset.univ.filter fun v : Fin n =>
      trimmedBall Φ v r D ≠ trimmedBall (Φ ++ [C]) v r D).card ≤
        2 * k * ∑ h ∈ Finset.range (r + 2), (k * D)^h) ∧
    (∀ f : Fin n → Option (Finset (Fin n) × Finset ℕ × GFormula (Fin n)) → ℝ,
      (∀ v b, 0 ≤ f v b ∧ f v b ≤ 1) →
      |(∑ v, f v (trimmedBall Φ v r D)) -
        (∑ v, f v (trimmedBall (Φ ++ [C]) v r D))| ≤
        (2 * k * ∑ h ∈ Finset.range (r + 2), (k * D)^h : ℕ)) := by
  have hballs := lemma_2_7_ball_bounds Φ k r D hk hr hD hwidth
  have hchanged := lemma_2_7_changed_balls Φ C k r D hk hr hD hwidth hC
  refine ⟨hballs.1, hballs.2, hchanged, ?_⟩
  intro f hf
  have hsum := audit_changed_coordinate_sum (fun v => trimmedBall Φ v r D)
    (fun v => trimmedBall (Φ ++ [C]) v r D) f hf
  exact hsum.trans (Nat.cast_le.mpr hchanged)

#print axioms solution
