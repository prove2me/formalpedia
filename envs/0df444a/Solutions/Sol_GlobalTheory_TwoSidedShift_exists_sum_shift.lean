-- Prove2me | solution 1 for GlobalTheory.TwoSidedShift.exists_sum_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:58:11.084803+00:00
-- url     : https://prove2.me/submissions/b53fc871-ea13-402b-9326-3b908568ecfb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwoSidedShiftSeriesHasSum
import Theorems.Thm_GlobalTheory_TwoSidedShift_mem_pow_span_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TwoSidedShift
namespace GlobalTheory.TwoSidedShift
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A]
    [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (c : ℤ → A),
    (∀ n : ℤ, (l : A) ^ n.natAbs ∣ c n) → (∀ n : ℤ, φ^[h] (c n) = (l : A) * c (n + 1)) →
    ∃ w : A, φ^[h] w = (l : A) * w ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) →
      HasSum (fun n : ℤ => Θ (c n)) (Θ w) := by
  intro l _ A _ _ φ h c hc hsh
  set ψ : A →+* A := φ ^ h with hψdef
  have hψ : ∀ x, φ^[h] x = ψ x := fun x => by rw [hψdef, RingHom.coe_pow]
  have hsh' : ∀ n : ℤ, ψ (c n) = (l : A) * c (n + 1) := fun n => by rw [← hψ]; exact hsh n
  set T : ℕ → A := fun N => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, c n with hT
  have hIcc : ∀ N : ℕ, Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ)
      = insert (-((N + 1 : ℕ) : ℤ)) (insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) N)) := by
    intro N; ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
  have hstep : ∀ N : ℕ, T (N + 1) = T N + c ((N + 1 : ℕ) : ℤ) + c (-((N + 1 : ℕ) : ℤ)) := by
    intro N
    simp only [hT]
    rw [hIcc N, Finset.sum_insert, Finset.sum_insert]
    · ring
    · simp only [Finset.mem_Icc]; push_cast; omega
    · simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega
  have hdstep : ∀ N : ℕ, (l : A) ^ (N + 1) ∣ T (N + 1) - T N := by
    intro N
    rw [hstep N, show T N + c ((N + 1 : ℕ) : ℤ) + c (-((N + 1 : ℕ) : ℤ)) - T N
      = c ((N + 1 : ℕ) : ℤ) + c (-((N + 1 : ℕ) : ℤ)) by ring]
    refine dvd_add ?_ ?_
    · have := hc ((N + 1 : ℕ) : ℤ)
      rwa [show (((N + 1 : ℕ) : ℤ)).natAbs = N + 1 by omega] at this
    · have := hc (-((N + 1 : ℕ) : ℤ))
      rwa [show (-((N + 1 : ℕ) : ℤ)).natAbs = N + 1 by omega] at this
  have hcauchy : ∀ m n : ℕ, m ≤ n → (l : A) ^ m ∣ T n - T m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [show T (n + 1) - T m = (T (n + 1) - T n) + (T n - T m) by ring]
      exact dvd_add ((pow_dvd_pow _ (by omega)).trans (hdstep n)) ih
  obtain ⟨w, hw⟩ := IsPrecomplete.prec (I := Ideal.span {(l : A)}) inferInstance (f := T)
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_pow_span_iff]
      rw [← dvd_neg, neg_sub]; exact hcauchy m n hmn)
  have hwT : ∀ N : ℕ, (l : A) ^ N ∣ w - T N := by
    intro N
    have := hw N
    rw [SModEq.sub_mem, mem_pow_span_iff] at this
    rw [← dvd_neg, neg_sub]; exact this

  have hE : ∀ N : ℕ, ψ (T N) - (l : A) * T N = (l : A) * (c ((N : ℤ) + 1) - c (-(N : ℤ))) := by
    intro N
    induction N with
    | zero => simp [hT, hsh']; ring
    | succ N ih =>
      rw [hstep N, map_add, map_add, hsh', hsh']
      have e1 : (-((N + 1 : ℕ) : ℤ) + 1) = -(N : ℤ) := by push_cast; ring
      have e2 : (((N + 1 : ℕ) : ℤ) + 1) = ((N + 1 : ℕ) : ℤ) + 1 := rfl
      rw [e1]
      push_cast at ih ⊢
      linear_combination ih
  have hEd : ∀ N : ℕ, (l : A) ^ N ∣ ψ (T N) - (l : A) * T N := by
    intro N
    rw [hE N]
    have h1 : (l : A) ^ (N + 1) ∣ c ((N : ℤ) + 1) := by
      have := hc ((N : ℤ) + 1)
      rwa [show ((N : ℤ) + 1).natAbs = N + 1 by omega] at this
    have h2 : (l : A) ^ N ∣ c (-(N : ℤ)) := by simpa using hc (-(N : ℤ))
    exact dvd_mul_of_dvd_right (dvd_sub ((pow_dvd_pow _ (by omega)).trans h1) h2) _
  refine ⟨w, ?_, ?_⟩
  · rw [hψ, ← sub_eq_zero]
    refine IsHausdorff.haus (I := Ideal.span {(l : A)}) inferInstance _ (fun N => ?_)
    rw [SModEq.sub_mem, sub_zero, mem_pow_span_iff]
    rw [show ψ w - (l : A) * w = ψ (w - T N) + (ψ (T N) - (l : A) * T N) - (l : A) * (w - T N) by
      rw [map_sub]; ring]
    refine dvd_sub (dvd_add ?_ (hEd N)) (dvd_mul_of_dvd_right (hwT N) _)
    have := map_dvd ψ (hwT N)
    simpa [map_pow, map_natCast] using this
  · intro Θ hΘ
    set r : ℝ := ‖(l : ℂ_[l])‖ with hr
    have hr1 : r < 1 := by
      have h := PadicComplex.norm_extends' l (l : ℚ_[l])
      have h2 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
      rw [← h] at h2
      simpa using h2
    have hr0 : 0 ≤ r := norm_nonneg _
    have hbound : ∀ (n : ℕ) (a : A), (l : A) ^ n ∣ a → ‖Θ a‖ ≤ r ^ n := by
      intro n a ⟨b, hb⟩
      rw [hb, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (pow_nonneg hr0 _) (hΘ b)
    change Filter.Tendsto (fun s : Finset ℤ => ∑ b ∈ s, Θ (c b)) Filter.atTop (nhds (Θ w))
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hr1
    refine ⟨Finset.Icc (-(N : ℤ)) N, fun s hs => ?_⟩
    rw [dist_eq_norm, ← Finset.sum_sdiff hs]
    have hrest : ‖∑ n ∈ s \ Finset.Icc (-(N : ℤ)) N, Θ (c n)‖ ≤ r ^ N := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _) fun n hn => ?_
      have hn' : n ∉ Finset.Icc (-(N : ℤ)) N := (Finset.mem_sdiff.1 hn).2
      rw [Finset.mem_Icc] at hn'
      refine (hbound _ _ (hc n)).trans (pow_le_pow_of_le_one hr0 hr1.le (by omega))
    have hhead : ‖∑ n ∈ Finset.Icc (-(N : ℤ)) N, Θ (c n) - Θ w‖ ≤ r ^ N := by
      rw [← map_sum, ← map_sub]
      refine hbound N _ ?_
      rw [← dvd_neg, neg_sub]; exact hwT N
    rw [add_sub_assoc]
    exact lt_of_le_of_lt ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hrest hhead)) hN
end GlobalTheory.TwoSidedShift
