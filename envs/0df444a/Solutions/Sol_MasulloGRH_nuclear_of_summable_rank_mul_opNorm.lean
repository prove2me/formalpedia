-- Prove2me | solution 1 for MasulloGRH.nuclear_of_summable_rank_mul_opNorm
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:33:10.167192+00:00
-- url     : https://prove2.me/submissions/39c06c7a-459c-43b4-80b7-72e4c93de872

import Definitions.Def_MasulloGRH_HilbertNuclear
import Theorems.Thm_MasulloGRH_operatorTrace_of_nuclear_series

set_option autoImplicit false
set_option maxHeartbeats 800000
open MasulloGRH
open scoped BigOperators

private lemma finite_row {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (d : ℕ) (f : ℕ → E) (hf : ∀ i, d ≤ i → f i = 0) :
    HasSum f (∑ i : Fin d, f i.val) := by
  rw [Fin.sum_univ_eq_sum_range]
  exact hasSum_sum_of_ne_finset_zero (fun i hi => hf i (Nat.le_of_not_gt (by simpa using hi)))

private lemma assemble_rows {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ℕ → H →L[ℂ] H) (T : H →L[ℂ] H) (x y : ℕ → ℕ → H)
    (hc : Summable fun p : ℕ × ℕ => ‖x p.1 p.2‖ * ‖y p.1 p.2‖)
    (hrc : ∀ n, Summable (fun i => ‖x n i‖ * ‖y n i‖))
    (hrow : ∀ u n, HasSum (fun i => inner ℂ (x n i) u • y n i) (A n u))
    (hT : ∀ u, HasSum (fun n => A n u) (T u)) :
    IsNuclearOperator T ∧ HasSum (fun n => operatorTrace (A n)) (operatorTrace T) := by
  let f (u : H) (p : ℕ × ℕ) := inner ℂ (x p.1 p.2) u • y p.1 p.2
  let cost (p : ℕ × ℕ) := ‖x p.1 p.2‖ * ‖y p.1 p.2‖
  have hcost : Summable cost := hc
  have hfs (u : H) : Summable (f u) := by
    apply Summable.of_norm_bounded (hcost.mul_right ‖u‖)
    intro p
    calc
      ‖f u p‖ = ‖inner ℂ (x p.1 p.2) u‖ * ‖y p.1 p.2‖ := norm_smul _ _
      _ ≤ (‖x p.1 p.2‖ * ‖u‖) * ‖y p.1 p.2‖ :=
        mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
      _ = cost p * ‖u‖ := by dsimp [cost]; ring
  have hf (u : H) : HasSum (f u) (T u) := by
    have h := (hfs u).hasSum
    exact (h.prod_fiberwise (hrow u)).unique (hT u) ▸ h
  let e := Nat.pairEquiv.symm
  let X (m : ℕ) := x (e m).1 (e m).2
  let Y (m : ℕ) := y (e m).1 (e m).2
  have hc' : Summable (fun m => ‖X m‖ * ‖Y m‖) := by
    change Summable (cost ∘ e)
    exact (e.summable_iff (f := cost)).mpr hcost
  have hf' (u : H) : HasSum (fun m => inner ℂ (X m) u • Y m) (T u) := by
    change HasSum (f u ∘ e) (T u)
    exact (e.hasSum_iff (f := f u) (a := T u)).mpr (hf u)
  refine ⟨⟨X, Y, hc', hf'⟩, ?_⟩
  let g (p : ℕ × ℕ) := inner ℂ (x p.1 p.2) (y p.1 p.2)
  have hg : Summable g := Summable.of_norm_bounded hcost fun p => norm_inner_le_norm _ _
  have htr (n : ℕ) : HasSum (fun i => g (n,i)) (operatorTrace (A n)) := by
    rw [operatorTrace_of_nuclear_series (A n) (x n) (y n) (hrc n) (fun u => hrow u n)]
    exact (Summable.of_norm_bounded (hrc n) (fun i => norm_inner_le_norm (x n i) (y n i))).hasSum
  have htot : operatorTrace T = ∑' p, g p := by
    rw [operatorTrace_of_nuclear_series T X Y hc' hf']
    change (∑' m, g (e m)) = ∑' p, g p
    exact e.tsum_eq g
  rw [htot]
  exact hg.hasSum.prod_fiberwise htr

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ℕ → H →L[ℂ] H) (S : ℕ → Submodule ℂ H) [∀ n, FiniteDimensional ℂ (S n)]
    (hAS : ∀ n u, A n u ∈ S n)
    (hc : Summable (fun n => (Module.finrank ℂ (S n) : ℝ) * ‖A n‖))
    (T : H →L[ℂ] H) (hT : ∀ u, HasSum (fun n => A n u) (T u)) :
    IsNuclearOperator T ∧ HasSum (fun n => operatorTrace (A n)) (operatorTrace T) := by
  classical
  let d (n : ℕ) := Module.finrank ℂ (S n)
  let b (n : ℕ) := stdOrthonormalBasis ℂ (S n)
  let y (n i : ℕ) : H := if h : i < d n then (b n ⟨i, h⟩ : H) else 0
  let x (n i : ℕ) : H := (A n).adjoint (y n i)
  have hy (n : ℕ) (i : Fin (d n)) : y n i.val = (b n i : H) := by simp [y, i.isLt]
  have hy0 {n i} (hi : d n ≤ i) : y n i = 0 := by simp [y, Nat.not_lt.mpr hi]
  have unit (n : ℕ) (i : Fin (d n)) : ‖y n i.val‖ = 1 := by
    rw [hy]; exact (b n).norm_eq_one i
  let cost (p : ℕ × ℕ) := ‖x p.1 p.2‖ * ‖y p.1 p.2‖
  have hcost_row (n : ℕ) : HasSum (fun i => cost (n,i)) (∑ i : Fin (d n), cost (n,i.val)) :=
    finite_row _ _ fun i hi => by simp [cost, hy0 hi]
  have hcost_le (n : ℕ) : ∑ i : Fin (d n), cost (n, i.val) ≤ d n * ‖A n‖ := by
    calc
      _ ≤ ∑ _ : Fin (d n), ‖A n‖ := by
        apply Finset.sum_le_sum
        intro i _
        have hi := (A n).adjoint.le_opNorm (y n i.val)
        simpa only [cost, x, unit, mul_one, ContinuousLinearMap.adjoint.norm_map] using hi
      _ = _ := by simp
  have hcost : Summable cost := by
    apply (summable_prod_of_nonneg (f := cost) (fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
    refine ⟨fun n => (hcost_row n).summable, ?_⟩
    apply Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))) _ hc
    intro n
    exact (hcost_row n).tsum_eq.le.trans (hcost_le n)
  let f (u : H) (p : ℕ × ℕ) := inner ℂ (x p.1 p.2) u • y p.1 p.2
  have hrow (u : H) (n : ℕ) : HasSum (fun i => f u (n,i)) (A n u) := by
    have hfinite := finite_row (d n) (fun i => f u (n,i)) (fun i hi => by simp [f, hy0 hi])
    convert hfinite using 1
    let v : S n := ⟨A n u, hAS n u⟩
    have h := congrArg (S n).subtype ((b n).sum_repr' v)
    rw [map_sum] at h
    simp only [map_smul, Submodule.subtype_apply] at h
    simp only [f, x, ContinuousLinearMap.adjoint_inner_left, hy]
    exact h.symm
  exact assemble_rows A T x y hcost (fun n => (hcost_row n).summable) hrow hT
