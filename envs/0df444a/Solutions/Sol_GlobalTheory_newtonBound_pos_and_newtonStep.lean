-- Prove2me | solution 1 for GlobalTheory.newtonBound_pos_and_newtonStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:05:20.406614+00:00
-- url     : https://prove2.me/submissions/a9ec1708-11b6-4374-96ea-9eddb7f10d4d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NewtonBoundPosAndNewtonStep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_intCast_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.L2.FormalSeriesBounds
namespace GlobalTheory
private lemma sum_range_succ_choose_mul_eq_add_shift {C : Type} [Field C] (f : ℕ → C) (y : ℕ) :
    ∑ s ∈ Finset.range (y + 1 + 1), ((y + 1).choose s : C) * f s =
      ∑ s ∈ Finset.range (y + 1), (y.choose s : C) * f s +
        ∑ s ∈ Finset.range (y + 1), (y.choose s : C) * f (s + 1) := by
  rw [Finset.sum_range_succ' (fun s => ((y + 1).choose s : C) * f s)]
  simp_rw [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun s => (y.choose s : C) * f s),
    Finset.sum_range_succ (fun s => (y.choose (s + 1) : C) * f (s + 1)), Nat.choose_succ_self]
  simp
  ring
end GlobalTheory
end

set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
open GlobalTheory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : _root_.Formalism.L2.FormalSeriesBounds.NewtonBoundPositive ∧ _root_.Formalism.L2.FormalSeriesBounds.P7 := by
  refine ⟨?_, ?_⟩
  · unfold _root_.Formalism.L2.FormalSeriesBounds.NewtonBoundPositive
    intro l hl i n0 s hi hn hs
    unfold _root_.Formalism.L2.FormalSeriesBounds.S0 at hs
    have hl' : (5:ℝ) ≤ l := by exact_mod_cast hl
    have hN : (1:ℝ) ≤ n0 := by exact_mod_cast hn
    have hi' : (1:ℝ) ≤ i := by exact_mod_cast hi
    have hlogl : 1 ≤ Real.log l := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    have hlbN1 : 0 ≤ Real.logb l ((n0:ℝ) + 1) := Real.logb_nonneg (by linarith) (by linarith)
    have hsK : 64 * (n0:ℝ) ^ 2 * ((i:ℝ) + 3 + 3 * Real.logb l ((n0:ℝ) + 1)) ≤ (s:ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hs)
    have hN2 : 0 < 64 * (n0:ℝ) ^ 2 := by positivity
    set t : ℝ := (s:ℝ) / (64 * (n0:ℝ) ^ 2) with ht
    have hst : (s:ℝ) = t * 64 * (n0:ℝ) ^ 2 := by rw [ht]; field_simp
    have htK : (i:ℝ) + 3 + 3 * Real.logb l ((n0:ℝ) + 1) ≤ t := by
      rw [ht, le_div_iff₀ hN2]; linarith
    have ht0 : 0 < t := by linarith
    have hlogs : Real.logb l s = Real.logb l t + Real.logb l 64 + 2 * Real.logb l n0 := by
      rw [hst, Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by norm_num),
        Real.logb_pow]
      push_cast
      ring
    have hlbt : Real.logb l t ≤ t - 1 := by
      have h1 := Real.log_le_sub_one_of_pos ht0
      have h2 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
      rw [Real.logb, div_le_iff₀ (by linarith)]
      nlinarith
    have hlb64 : Real.logb l 64 ≤ 3 := by
      have h3 : Real.logb l ((l:ℝ) ^ 3) = 3 := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by linarith)]
        norm_num
      rw [← h3]
      apply Real.logb_le_logb_of_le (by linarith) (by norm_num)
      have hcube : (5:ℝ) ^ 3 ≤ (l:ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hl' 3
      linarith
    have hlbN : Real.logb l n0 ≤ Real.logb l ((n0:ℝ) + 1) :=
      Real.logb_le_logb_of_le (by linarith) (by linarith) (by linarith)
    have key : 3 * Real.logb l n0 + 2 * Real.logb l s + i + 3 < 8 * t := by
      rw [hlogs]
      nlinarith
    have hs8 : (s:ℝ) / 8 = 8 * t * (n0:ℝ) ^ 2 := by rw [hst]; ring
    rw [hs8]
    have hpos : 0 < (n0:ℝ) ^ 2 := by positivity
    nlinarith [mul_lt_mul_of_pos_left key hpos]
  · unfold _root_.Formalism.L2.FormalSeriesBounds.P7
    intro C _ v S a hS ha0 hpos Y0
    by_contra hcon
    push_neg at hcon
    have hadd : ∀ x y : C, 0 < v x → 0 < v y → 0 < v (x + y) := fun x y hx hy =>
      lt_of_lt_of_le (lt_min hx hy) (v.map_add x y)
    have hsub : ∀ x y : C, 0 < v x → 0 < v y → 0 < v (x - y) := fun x y hx hy => by
      rw [sub_eq_add_neg]
      exact hadd _ _ hx (by rwa [v.map_neg])
    have hnat : ∀ (c : ℕ) (x : C), 0 < v x → 0 < v ((c : C) * x) := fun c x hx => by
      rw [v.map_mul]
      have h := _root_.ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.intCast_nonneg v (c : ℤ)
      rw [Int.cast_natCast] at h
      exact lt_of_lt_of_le hx (le_add_of_nonneg_left h)
    have hsum : ∀ (s : Finset ℕ) (f : ℕ → C), (∀ j ∈ s, 0 < v (f j)) → 0 < v (∑ j ∈ s, f j) := by
      intro s f hf
      induction s using Finset.induction_on with
      | empty => simp
      | insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact hadd _ _ (hf j (Finset.mem_insert_self _ _))
          (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))
    set B : ℕ → ℕ → C := fun k y => ∑ s ∈ Finset.range (y + 1), (y.choose s : C) * a (s + k) with hB
    have hpascal : ∀ k y, B (k + 1) y = B k (y + 1) - B k y := by
      intro k y
      simp only [hB]
      rw [sum_range_succ_choose_mul_eq_add_shift (fun s => a (s + k)) y]
      have : ∀ s, a (s + 1 + k) = a (s + (k + 1)) := fun s => by rw [add_assoc, add_comm 1 k]
      simp only [this]
      ring
    have hup : ∀ k, k < S → ∀ y, Y0 ≤ y → y + k < Y0 + S → 0 < v (B k y) := by
      intro k
      induction k with
      | zero =>
        intro _ y h1 h2
        simpa [hB] using hcon y h1 (by omega)
      | succ k ih =>
        intro hk y h1 h2
        rw [hpascal]
        exact hsub _ _ (ih (by omega) (y + 1) (by omega) (by omega)) (ih (by omega) y h1 (by omega))
    have hbig : ∀ k, S ≤ k → ∀ y, 0 < v (B k y) := fun k hk y =>
      hsum _ _ fun s _ => hnat _ _ (hpos _ (by omega))
    have hdown : ∀ d, d ≤ Y0 → ∀ k, 0 < v (B k (Y0 - d)) := by
      intro d
      induction d with
      | zero =>
        intro _ k
        by_cases hk : k < S
        · exact hup k hk Y0 le_rfl (by simpa using hk)
        · exact hbig k (by omega) _
      | succ d ih =>
        intro hd
        have hy : Y0 - d = Y0 - (d + 1) + 1 := by omega
        have main : ∀ m k, S ≤ k + m → 0 < v (B k (Y0 - (d + 1))) := by
          intro m
          induction m with
          | zero => intro k hk; exact hbig k (by omega) _
          | succ m ihm =>
            intro k hk
            have e := hpascal k (Y0 - (d + 1))
            have : B k (Y0 - (d + 1)) = B k (Y0 - (d + 1) + 1) - B (k + 1) (Y0 - (d + 1)) := by
              rw [e]; ring
            rw [this, ← hy]
            exact hsub _ _ (ih (by omega) k) (ihm (k + 1) (by omega))
        exact fun k => main S k (by omega)
    have h0 := hdown Y0 le_rfl 0
    simp [hB, ha0] at h0
end _root_.GlobalTheory
end GlobalTheory
