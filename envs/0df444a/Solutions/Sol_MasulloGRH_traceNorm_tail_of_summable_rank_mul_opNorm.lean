-- Prove2me | solution 1 for MasulloGRH.traceNorm_tail_of_summable_rank_mul_opNorm
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:44:48.765696+00:00
-- url     : https://prove2.me/submissions/b64988a8-8161-432c-ba43-17fc7a46fb77

import Definitions.Def_MasulloGRH_HilbertNuclear
import Theorems.Thm_MasulloGRH_traceNorm_le_nuclear_series

set_option autoImplicit false
set_option maxHeartbeats 800000
open MasulloGRH
open scoped BigOperators Topology
open Filter

private lemma finite_row {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (d : ℕ) (f : ℕ → E) (hf : ∀ i, d ≤ i → f i = 0) :
    HasSum f (∑ i : Fin d, f i.val) := by
  rw [Fin.sum_univ_eq_sum_range]
  exact hasSum_sum_of_ne_finset_zero (fun i hi => hf i (Nat.le_of_not_gt (by simpa using hi)))

private lemma assemble_rows {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ℕ → H →L[ℂ] H) (T : H →L[ℂ] H) (x y : ℕ → ℕ → H)
    (hc : Summable fun p : ℕ × ℕ => ‖x p.1 p.2‖ * ‖y p.1 p.2‖)
    (hrow : ∀ u n, HasSum (fun i => inner ℂ (x n i) u • y n i) (A n u))
    (hT : ∀ u, HasSum (fun n => A n u) (T u)) :
    traceNorm T ≤ ∑' p : ℕ × ℕ, ‖x p.1 p.2‖ * ‖y p.1 p.2‖ := by
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
  exact (traceNorm_le_nuclear_series T X Y hc' hf').trans_eq (e.tsum_eq cost)

private lemma rank_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ℕ → H →L[ℂ] H) (S : ℕ → Submodule ℂ H) [∀ n, FiniteDimensional ℂ (S n)]
    (hAS : ∀ n u, A n u ∈ S n)
    (hc : Summable (fun n => (Module.finrank ℂ (S n) : ℝ) * ‖A n‖))
    (T : H →L[ℂ] H) (hT : ∀ u, HasSum (fun n => A n u) (T u)) :
    traceNorm T ≤ ∑' n, (Module.finrank ℂ (S n) : ℝ) * ‖A n‖ := by
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
  calc
    traceNorm T ≤ ∑' p, cost p := assemble_rows A T x y hcost hrow hT
    _ = ∑' n, ∑' i, cost (n,i) := hcost.tsum_prod
    _ ≤ _ := ((summable_prod_of_nonneg (f := cost) (fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hcost).2.tsum_le_tsum
      (fun n => (hcost_row n).tsum_eq.le.trans (hcost_le n)) hc

private lemma trace_norm_nonneg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H) : 0 ≤ traceNorm T := by
  have hpos : (operatorAbs T).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg _)
  unfold traceNorm operatorTrace
  by_cases h : Summable (fun i => inner ℂ (chosenHilbertBasis H i) (operatorAbs T (chosenHilbertBasis H i)))
  · rw [Complex.re_tsum h]
    exact tsum_nonneg fun i => hpos.re_inner_nonneg_right _
  · rw [tsum_eq_zero_of_not_summable h, Complex.zero_re]

private lemma delete_finite {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] (f : ι → E) (s : Finset ι) {t : E} (h : HasSum f t) :
    HasSum (fun n => if n ∈ s then 0 else f n) (t - ∑ n ∈ s, f n) := by
  have hfin : HasSum (fun n => if n ∈ s then f n else 0) (∑ n ∈ s, f n) := by
    convert (hasSum_sum_of_ne_finset_zero (s := s) (f := fun n => if n ∈ s then f n else 0)
      (fun n hn => by simp [hn])) using 1
    · exact Finset.sum_congr rfl (fun n hn => by simp [hn])
    · infer_instance
  convert h.sub hfin using 1
  ext n
  split_ifs <;> simp

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : ℕ → H →L[ℂ] H) (S : ℕ → Submodule ℂ H) [∀ n, FiniteDimensional ℂ (S n)]
    (hAS : ∀ n u, A n u ∈ S n)
    (hc : Summable (fun n => (Module.finrank ℂ (S n) : ℝ) * ‖A n‖))
    (T : H →L[ℂ] H) (hT : ∀ u, HasSum (fun n => A n u) (T u)) :
    (∀ s : Finset ℕ, traceNorm (T - ∑ n ∈ s, A n) ≤
      (∑' n, (Module.finrank ℂ (S n) : ℝ) * ‖A n‖) -
      ∑ n ∈ s, (Module.finrank ℂ (S n) : ℝ) * ‖A n‖) ∧
    Tendsto (fun s : Finset ℕ => traceNorm (T - ∑ n ∈ s, A n)) atTop (𝓝 0) := by
  classical
  let c (n : ℕ) := (Module.finrank ℂ (S n) : ℝ) * ‖A n‖
  have htail (s : Finset ℕ) : traceNorm (T - ∑ n ∈ s, A n) ≤ (∑' n, c n) - ∑ n ∈ s, c n := by
    let B (n : ℕ) : H →L[ℂ] H := if n ∈ s then 0 else A n
    have hBS (n : ℕ) (u : H) : B n u ∈ S n := by
      by_cases hn : n ∈ s <;> simp [B, hn, hAS]
    have hbc (n : ℕ) : (Module.finrank ℂ (S n) : ℝ) * ‖B n‖ = if n ∈ s then 0 else c n := by
      by_cases hn : n ∈ s <;> simp [B,c,hn]
    have hcost : HasSum (fun n => (Module.finrank ℂ (S n) : ℝ) * ‖B n‖) ((∑' n, c n) - ∑ n ∈ s, c n) := by
      simpa only [hbc] using delete_finite c s hc.hasSum
    apply (rank_bound B S hBS hcost.summable _ _).trans_eq hcost.tsum_eq
    intro u
    have h := delete_finite (fun n => A n u) s (hT u)
    simpa [B, apply_ite (fun (L : H →L[ℂ] H) => L u), sum_apply] using h
  refine ⟨htail,?_⟩
  apply squeeze_zero (fun s => trace_norm_nonneg _) htail
  have hc' : Summable c := hc
  simpa using (tendsto_const_nhds (x := ∑' n, c n)).sub hc'.hasSum
