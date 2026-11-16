-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.adaptive_stages_l1
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:26:44.194438+00:00
-- url     : https://prove2.me/submissions/1c080d75-c5c2-4de2-8766-a5bcbf02c5ed

import Definitions.Def_InfoLossLAR_LoadedBatchBundle_05

set_option autoImplicit false
open scoped BigOperators
open AFT
noncomputable section

private theorem l1_source_contract {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : FiniteDist X) (k : X → FiniteDist Y) :
    (∑ y, |(p.mix k).weight y - (q.mix k).weight y|) ≤
      ∑ x, |p.weight x-q.weight x| := by
  simp only [FiniteDist.mix_weight, ← Finset.sum_sub_distrib, ← sub_mul]
  calc
    _ ≤ ∑ y, ∑ x, |p.weight x-q.weight x| * (k x).weight y := by
      apply Finset.sum_le_sum
      intro y _
      have h := Finset.abs_sum_le_sum_abs (fun x => (p.weight x-q.weight x)*(k x).weight y) Finset.univ
      simpa only [abs_mul, abs_of_nonneg ((k _).nonneg _)] using h
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, FiniteDist.sum_one, mul_one]

private theorem l1_kernel_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteDist X) (k l : X → FiniteDist Y) (e : ℝ)
    (h : ∀ x, (∑ y, |(k x).weight y-(l x).weight y|) ≤ e) :
    (∑ y, |(p.mix k).weight y-(p.mix l).weight y|) ≤ e := by
  simp only [FiniteDist.mix_weight, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ y, ∑ x, p.weight x*|(k x).weight y-(l x).weight y| := by
      apply Finset.sum_le_sum
      intro y _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro x _
      rw [← mul_sub, abs_mul, abs_of_nonneg (p.nonneg x)]
    _ = ∑ x, p.weight x*(∑ y, |(k x).weight y-(l x).weight y|) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ x, p.weight x*e := Finset.sum_le_sum (fun x _ =>
      mul_le_mul_of_nonneg_left (h x) (p.nonneg x))
    _ = e := by rw [← Finset.sum_mul, p.sum_one, one_mul]

private theorem l1_triangle {X : Type*} [Fintype X] (p q r : FiniteDist X) :
    (∑ x, |p.weight x-r.weight x|) ≤
      (∑ x, |p.weight x-q.weight x|) + (∑ x, |q.weight x-r.weight x|) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun x _ => abs_sub_le _ _ _)

/-- A full state can retain the entire shared pool and all prior randomness.
Uniform conditional step errors compose without a cross-stage independence
assumption. All bounds here are for complete joint distributions. -/
theorem solution {State : Type*} [Fintype State]
    (actual ideal : ℕ → FiniteDist State)
    (actualStep idealStep : ℕ → State → FiniteDist State)
    (δ : ℝ) (error : ℕ → ℝ)
    (hstart : (∑ x, |(actual 0).weight x-(ideal 0).weight x|) ≤ δ)
    (hactual : ∀ i, actual (i+1) = (actual i).mix (actualStep i))
    (hideal : ∀ i, ideal (i+1) = (ideal i).mix (idealStep i))
    (hstep : ∀ i state, (∑ x, |(actualStep i state).weight x-(idealStep i state).weight x|) ≤ error i) :
    ∀ n, (∑ x, |(actual n).weight x-(ideal n).weight x|) ≤ δ + ∑ i ∈ Finset.range n, error i := by
  intro n
  induction n with
  | zero => simpa using hstart
  | succ n ih =>
      rw [hactual n, hideal n, Finset.sum_range_succ]
      have htriangle := l1_triangle ((actual n).mix (actualStep n))
        ((ideal n).mix (actualStep n)) ((ideal n).mix (idealStep n))
      have hleft := (l1_source_contract (actual n) (ideal n) (actualStep n)).trans ih
      have hright := l1_kernel_bound (ideal n) (actualStep n) (idealStep n) (error n) (hstep n)
      linarith

end

#print axioms solution
