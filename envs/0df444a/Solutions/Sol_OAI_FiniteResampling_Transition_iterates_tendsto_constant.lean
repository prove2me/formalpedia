-- Prove2me | solution 1 for OAI.FiniteResampling.Transition.iterates_tendsto_constant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:49:22.638709+00:00
-- url     : https://prove2.me/submissions/98bdab4d-bdcf-49cd-99b6-7d8f7cac3d4a

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling

open OAI OAI.FiniteResampling OAI.FiniteResampling.Transition
universe uI
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
open scoped ENNReal
open scoped BigOperators Matrix
open Filter
variable {I : Type uI} [Fintype I] [Nonempty I]
variable (K : Transition I)
theorem hc_lower_le {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) (j : I) : lower f ≤ f j :=
  Finset.inf'_le _ (Finset.mem_univ j)

theorem hc_le_upper {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) (j : I) : f j ≤ upper f :=
  Finset.le_sup' _ (Finset.mem_univ j)

theorem hc_act_sub {I : Type*} [Fintype I] (K : Transition I) (f : I → ℝ) (c : ℝ) (i : I) :
    K.act f i - c = ∑ j, K.weight i j * (f j - c) := by
  simp only [act, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, K.total, one_mul]

theorem hc_atom_bounds {I : Type*} [Fintype I] [Nonempty I] (K : Transition I)
    (z : I) (a : ℝ) (ha : ∀ i, a ≤ K.weight i z)
    (f : I → ℝ) (i : I) :
    a * f z + (1-a) * lower f ≤ K.act f i ∧
      K.act f i ≤ a * f z + (1-a) * upper f := by
  constructor
  · have h1 := hc_act_sub K f (lower f) i
    have h2 : K.weight i z * (f z - lower f) ≤ ∑ j, K.weight i j * (f j - lower f) :=
      Finset.single_le_sum (f := fun j => K.weight i j * (f j - lower f))
        (fun j _ => mul_nonneg (K.nonneg i j) (sub_nonneg.mpr (hc_lower_le f j))) (Finset.mem_univ z)
    have h3 : a * (f z - lower f) ≤ K.weight i z * (f z - lower f) :=
      mul_le_mul_of_nonneg_right (ha i) (sub_nonneg.mpr (hc_lower_le f z))
    nlinarith
  · have h1 := hc_act_sub K f (upper f) i
    have h2 : ∑ j, K.weight i j * (f j - upper f) ≤ K.weight i z * (f z - upper f) := by
      have := Finset.single_le_sum (f := fun j => K.weight i j * (upper f - f j))
        (fun j _ => mul_nonneg (K.nonneg i j) (sub_nonneg.mpr (hc_le_upper f j))) (Finset.mem_univ z)
      simp only [mul_sub, Finset.sum_sub_distrib] at this ⊢
      linarith
    have h3 : K.weight i z * (f z - upper f) ≤ a * (f z - upper f) :=
      mul_le_mul_of_nonpos_right (ha i) (sub_nonpos.mpr (hc_le_upper f z))
    nlinarith

theorem hc_iter_const {I : Type*} [Fintype I] [Nonempty I] (K : Transition I)
    (z : I) (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (ha : ∀ i, a ≤ K.weight i z) (f : I → ℝ) :
    ∃ c : ℝ, lower f ≤ c ∧ c ≤ upper f ∧
      ∀ i, Tendsto (fun n : ℕ => ((K.act)^[n] f) i) atTop (nhds c) := by
  have hlo : ∀ g : I → ℝ, a * g z + (1-a) * lower g ≤ lower (K.act g) := fun g =>
    Finset.le_inf' _ _ (fun i _ => (hc_atom_bounds K z a ha g i).1)
  have hup : ∀ g : I → ℝ, upper (K.act g) ≤ a * g z + (1-a) * upper g := fun g =>
    Finset.sup'_le _ _ (fun i _ => (hc_atom_bounds K z a ha g i).2)
  let fn : ℕ → I → ℝ := fun n => (K.act)^[n] f
  have hsucc : ∀ n, fn (n+1) = K.act (fn n) := fun n => Function.iterate_succ_apply' _ _ _
  let L : ℕ → ℝ := fun n => lower (fn n)
  let U : ℕ → ℝ := fun n => upper (fn n)
  have hLU : ∀ n, L n ≤ U n := fun n => (hc_lower_le (fn n) (Classical.arbitrary I)).trans
    (hc_le_upper (fn n) _)
  have hLmono : Monotone L := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    show lower (fn n) ≤ lower (fn (n+1))
    rw [hsucc]
    have := hlo (fn n)
    have := hc_lower_le (fn n) z
    nlinarith
  have hUanti : Antitone U := by
    refine antitone_nat_of_succ_le (fun n => ?_)
    show upper (fn (n+1)) ≤ upper (fn n)
    rw [hsucc]
    have := hup (fn n)
    have := hc_le_upper (fn n) z
    nlinarith
  have hgap : ∀ n, U n - L n ≤ (1-a)^n * (U 0 - L 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      show upper (fn (n+1)) - lower (fn (n+1)) ≤ _
      rw [hsucc]
      have h1 := hlo (fn n)
      have h2 := hup (fn n)
      have : upper (K.act (fn n)) - lower (K.act (fn n)) ≤ (1-a) * (U n - L n) := by
        simp only [U, L]; nlinarith
      calc _ ≤ (1-a) * (U n - L n) := this
        _ ≤ (1-a) * ((1-a)^n * (U 0 - L 0)) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ = _ := by ring
  have hLU' : ∀ m n, L m ≤ U n := fun m n =>
    (hLmono (le_max_left m n)).trans ((hLU _).trans (hUanti (le_max_right m n)))
  have hbdd : BddAbove (Set.range L) := ⟨U 0, by rintro _ ⟨m, rfl⟩; exact hLU' m 0⟩
  let c := ⨆ n, L n
  have hLc : Tendsto L atTop (nhds c) := tendsto_atTop_ciSup hLmono hbdd
  have hgap0 : Tendsto (fun n => U n - L n) atTop (nhds 0) := by
    have hp : Tendsto (fun n : ℕ => (1-a)^n * (U 0 - L 0)) atTop (nhds 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0:ℝ) ≤ 1-a) (by linarith : 1-a < 1)).mul_const (U 0 - L 0)
      simpa using this
    exact squeeze_zero (fun n => sub_nonneg.mpr (hLU n)) hgap hp
  have hUc : Tendsto U atTop (nhds c) := by
    have := hLc.add hgap0
    simp only [add_zero, add_sub_cancel] at this
    exact this
  refine ⟨c, ?_, ?_, fun i => ?_⟩
  · exact le_ciSup hbdd 0
  · exact ciSup_le (fun m => hLU' m 0)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le hLc hUc
      (fun n => hc_lower_le (fn n) i) (fun n => hc_le_upper (fn n) i)

theorem solution (z : I) (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (ha : ∀ i, a ≤ K.weight i z) (f : I → ℝ) :
    ∃ c : ℝ, lower f ≤ c ∧ c ≤ upper f ∧
      ∀ i, Tendsto (fun n : ℕ => ((K.act)^[n] f) i) atTop (nhds c) := by
  exact hc_iter_const K z a ha0 ha1 ha f

