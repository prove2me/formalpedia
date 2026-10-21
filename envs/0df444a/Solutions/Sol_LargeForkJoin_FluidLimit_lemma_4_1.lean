-- Prove2me | solution 1 for LargeForkJoin.FluidLimit.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:59:44.563691+00:00
-- url     : https://prove2.me/submissions/44fb88bc-1cba-4c39-bc32-5945e45faf17

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace FJLemma41Aux
open LargeForkJoin.FluidLimit

lemma Rtil_eq {Ω : Type*} (M : ForkJoin Ω) (α : ℝ) (N i n : ℕ) (ω : Ω) :
    Rtil M α N i n ω = (arr M N n ω - srv M N i n ω) / scale N := by
  unfold Rtil Atil Stil scale
  rw [← div_div]
  congr 1
  ring

lemma queueEmpty_eq {Ω : Type*} (M : ForkJoin Ω) (N i n : ℕ) (ω : Ω) :
    queueEmpty M N i n ω = (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => (arr M N n ω - srv M N i n ω) - (arr M N k ω - srv M N i k ω)) := by
  unfold queueEmpty
  congr 1
  funext k
  ring

lemma bdd {Ω : Type*} (M : ForkJoin Ω) (N n : ℕ) (ω : Ω) :
    BddAbove (Set.range fun i : Fin N => queueEmpty M N i n ω) :=
  (Set.finite_range _).bddAbove

lemma queueEmpty_nonneg {Ω : Type*} (M : ForkJoin Ω) (N i n : ℕ) (ω : Ω) :
    0 ≤ queueEmpty M N i n ω := by
  rw [queueEmpty_eq]
  refine le_trans ?_ (Finset.le_sup' _ (Finset.self_mem_range_succ n))
  simp

end FJLemma41Aux

open LargeForkJoin.FluidLimit FJLemma41Aux in
theorem solution {Ω : Type*} (M : ForkJoin Ω) (α : ℝ) (N : ℕ) (ω : Ω) (t δ : ℝ)
    (hN : 0 < N) (ht : 0 < t) (hδ : 0 < δ) (a b : ℝ)
    (ha : ∀ s ∈ Set.Icc t (t + δ), ∀ i : Fin N,
      Rtil M α N i (tau N s) ω - Rtil M α N i (tau N t) ω ≤ a)
    (hb : ∀ s ∈ Set.Icc t (t + δ), ∀ i : Fin N,
      Rtil M α N i (tau N t) ω - Rtil M α N i (tau N s) ω ≤ b) :
    ∀ s ∈ Set.Icc t (t + δ),
      |maxQueueEmpty M N (tau N s) ω / scale N - maxQueueEmpty M N (tau N t) ω / scale N| ≤
        a + 2 * b := by
  intro s hs
  have i0 : Fin N := ⟨0, hN⟩
  have htmem : t ∈ Set.Icc t (t + δ) := ⟨le_rfl, by linarith⟩
  have ha0 : 0 ≤ a := by have := ha t htmem i0; simpa using this
  have hb0 : 0 ≤ b := by have := hb t htmem i0; simpa using this
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hD0 : 0 ≤ scale N := by unfold scale; positivity
  rcases hD0.eq_or_lt with hD | hD
  · rw [← hD]; simp; linarith
  -- D > 0
  have hlogpos : 0 < Real.log N := by
    unfold scale at hD
    rcases hlog.eq_or_lt with h | h
    · rw [← h] at hD; simp at hD
    · exact h
  set D := scale N with hDdef
  set c : ℝ := (N : ℝ) ^ 3 * Real.log N with hc
  have hcpos : 0 < c := by positivity
  have htau : ∀ x : ℝ, tau N x = ⌊x * c⌋₊ := by
    intro x; unfold tau; rw [hc]; ring_nf
  set m := tau N t with hm
  set n := tau N s with hn
  have hmn : m ≤ n := by
    rw [hm, hn, htau, htau]
    exact Nat.floor_mono (by nlinarith [hs.1])
  -- unscaled netput
  set f : Fin N → ℕ → ℝ := fun i k => arr M N k ω - srv M N i k ω with hf
  have hA : ∀ s' ∈ Set.Icc t (t + δ), ∀ i : Fin N, f i (tau N s') - f i m ≤ a * D := by
    intro s' hs' i
    have := ha s' hs' i
    rw [Rtil_eq, Rtil_eq, ← sub_div, div_le_iff₀ hD] at this
    simpa [hf] using this
  have hB : ∀ s' ∈ Set.Icc t (t + δ), ∀ i : Fin N, f i m - f i (tau N s') ≤ b * D := by
    intro s' hs' i
    have := hb s' hs' i
    rw [Rtil_eq, Rtil_eq, ← sub_div, div_le_iff₀ hD] at this
    simpa [hf] using this
  have hQ : ∀ (i : Fin N) (k : ℕ), queueEmpty M N i k ω = (Finset.range (k + 1)).sup'
      Finset.nonempty_range_add_one (fun j => f i k - f i j) := by
    intro i k; rw [queueEmpty_eq]
  have : Nonempty (Fin N) := ⟨i0⟩
  have hle : ∀ (i : Fin N) (k : ℕ), queueEmpty M N i k ω ≤ maxQueueEmpty M N k ω :=
    fun i k => le_ciSup (bdd M N k ω) i
  have hQm0 : 0 ≤ maxQueueEmpty M N m ω :=
    le_trans (queueEmpty_nonneg M N i0 m ω) (hle i0 m)
  -- upper bound
  have hup : maxQueueEmpty M N n ω ≤ maxQueueEmpty M N m ω + (a + b) * D := by
    refine ciSup_le fun i => ?_
    rw [hQ]
    refine Finset.sup'_le _ _ fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 := hA s hs i
    by_cases hkm : k ≤ m
    · have h2 : f i m - f i k ≤ queueEmpty M N i m ω := by
        rw [hQ]
        exact Finset.le_sup' (fun j => f i m - f i j)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hkm))
      have h3 := hle i m
      have : 0 ≤ b * D := mul_nonneg hb0 hD.le
      nlinarith
    · push Not at hkm
      -- k = tau N s' for s' = k / c
      set s' : ℝ := (k : ℝ) / c with hs'
      have htk : tau N s' = k := by
        rw [htau, hs', div_mul_cancel₀ _ hcpos.ne']
        exact Nat.floor_natCast k
      have hs'mem : s' ∈ Set.Icc t (t + δ) := by
        constructor
        · rw [hs', le_div_iff₀ hcpos]
          have : t * c < (m : ℝ) + 1 := by
            rw [hm, htau]; exact Nat.lt_floor_add_one _
          have : (m : ℝ) + 1 ≤ k := by exact_mod_cast hkm
          linarith
        · rw [hs', div_le_iff₀ hcpos]
          have hsc : (n : ℝ) ≤ s * c := by
            rw [hn, htau]; exact Nat.floor_le (by nlinarith [hs.1])
          have : (k : ℝ) ≤ n := by exact_mod_cast hkn
          nlinarith [hs.2]
      have h2 := hB s' hs'mem i
      rw [htk] at h2
      nlinarith
  -- lower bound
  have hlo : maxQueueEmpty M N m ω ≤ maxQueueEmpty M N n ω + b * D := by
    refine ciSup_le fun i => ?_
    rw [hQ]
    refine Finset.sup'_le _ _ fun k hk => ?_
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 := hB s hs i
    have h2 : f i n - f i k ≤ queueEmpty M N i n ω := by
      rw [hQ]
      exact Finset.le_sup' (fun j => f i n - f i j)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_trans hkm hmn)))
    have h3 := hle i n
    linarith
  rw [← sub_div, abs_div, abs_of_pos hD, div_le_iff₀ hD, abs_le]
  constructor <;> nlinarith [mul_nonneg ha0 hD.le, mul_nonneg hb0 hD.le]
