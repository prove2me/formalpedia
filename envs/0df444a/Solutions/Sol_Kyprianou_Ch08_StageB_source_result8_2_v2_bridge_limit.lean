-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:28:55.823933+00:00
-- url     : https://prove2.me/submissions/1bd892b4-10e6-4786-bd8f-76100dbc0310

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_1_v2
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
set_option autoImplicit false
-- Infrastructure retry only: candidate 46186 reached terminal ERROR when the platform import parser timed out before Lean elaboration; the proof body is unchanged.
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped BigOperators NNReal ENNReal
section
variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {D : SpectrallyNegativeModel Ω P} {ψ : ℝ → ℝ} {q : ℝ} {n : Measure ℝ}
theorem scaleBridgeLimitAux (hq : 0 ≤ q) (hLaw : HasActualQExcursionHeightLaw P D ψ q n) (hLow : ∀ l d : ℝ, 0 < l → 0 < d → Real.exp (-(d * (Phi ψ q + (n (Ici l)).toReal))) ≤ upBeforeDownExpectation P D.X q l (l + d)) (hUp : ∀ l d : ℝ, 0 < l → 0 < d → upBeforeDownExpectation P D.X q l (l + d) ≤ Real.exp (-(d * (Phi ψ q + (n (Ici (l + d + d))).toReal)))) : ∀ x a : ℝ, 0 < x → x < a → upBeforeDownExpectation P D.X q x a = Real.exp (-(∫ t in x..a, Phi ψ q + (n (Ici t)).toReal)) := by
  intro x a hx hxa
  let u : ℝ → ℝ → ℝ := fun y z => upBeforeDownExpectation P D.X q y z;  let f : ℝ → ℝ := fun t => Phi ψ q + (n (Ici t)).toReal
  let I : ℝ := ∫ t in x..a, f t;  let L : ℝ := Real.log (u x a)
  let C : ℝ := f x;  let slopeDiff : ℝ := f x - f a
  obtain ⟨_, W, _, _, _, _, _, hupper⟩ := source_result8_1_v2 Ω P D
  have hW y hy : 0 < W q y := (hupper q y y hq hy le_rfl).1
  have huPos (y z : ℝ) (hy : 0 < y) (hyz : y ≤ z) : 0 < u y z := by
    simp only [u];      rw [(hupper q y z hq (lt_of_lt_of_le hy hyz) hyz).2.1];      exact div_pos (hW y hy) (hW z (lt_of_lt_of_le hy hyz))
  have hlog (y z : ℝ) (hy : 0 < y) (hyz : y ≤ z) : Real.log (u y z) = Real.log (W q y) - Real.log (W q z) := by
    simp only [u];      rw [(hupper q y z hq (lt_of_lt_of_le hy hyz) hyz).2.1, Real.log_div (ne_of_gt (hW y hy)) (ne_of_gt (hW z (lt_of_lt_of_le hy hyz)))]
  have hf0 t : 0 ≤ f t := by     dsimp [f]; exact add_nonneg hLaw.1.2.1.1 ENNReal.toReal_nonneg
  have hfanti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : f t ≤ f s := by
    have hfin : n (Ici s) ≠ ⊤ := ne_of_lt ((hLaw.2 1 s zero_lt_one hs).1)
    dsimp [f]; exact add_le_add_right (ENNReal.toReal_mono hfin (measure_mono (fun y hy => le_trans hst hy))) (Phi ψ q)
  let δ : ℕ → ℝ := fun m => (a - x) / (((m + 1 : ℕ) : ℝ))
  let g : ℕ → ℕ → ℝ := fun m k => δ m * (k : ℝ) + x
  have hseq : ∀ m : ℕ, (-I - δ m * slopeDiff ≤ L) ∧ (L ≤ -I + δ m * (C + slopeDiff)) := by
    intro m
    let N : ℕ := m + 1;    let d : ℝ := δ m
    let Ffun : ℝ → ℝ := fun t => f (d * t + x);    let Fv : ℕ → ℝ := fun k => f (g m k)
    let T : ℕ → ℝ := fun k => Real.log (u (g m k) (g m (k + 1)));    let A : ℕ → ℝ := fun k => Real.log (W q (g m k))
    let S : ℕ → ℝ := fun j => ∑ k ∈ Finset.range N, Fv (k + j);    let J : ℝ := ∫ t in (0 : ℝ)..(N : ℝ), Ffun t
    have hNpos : 0 < (((m + 1 : ℕ) : ℝ)) := by exact_mod_cast Nat.succ_pos m
    have hd : 0 < d := by dsimp [d, δ]; exact div_pos (sub_pos.mpr hxa) hNpos
    have hg0 : 0 < g m 0 := by simpa [g] using hx
    have hgstep k : g m k < g m (k + 1) := by dsimp [g, d]; norm_num; nlinarith [hd]
    have hgpos k : 0 < g m k := by dsimp [g, d]; positivity
    have hgadd k : g m k + d = g m (k + 1) := by dsimp [g, d]; norm_num; ring
    have hgadd2 k : g m k + d + d = g m (k + 2) := by dsimp [g, d]; norm_num; ring
    have hgN : g m N = a := by
      dsimp [g, δ, N]
      field_simp [ne_of_gt hNpos]
      ring
    have hsumlog : (∑ k ∈ Finset.range N, T k) = L := by
      calc
        _ = ∑ k ∈ Finset.range N, (A k - A (k + 1)) := Finset.sum_congr rfl (fun k hk => hlog (g m k) (g m (k + 1)) (hgpos k) (le_of_lt (hgstep k)))
        _ = A 0 - A N := Finset.sum_range_sub' A N
        _ = L := by simpa [A, L, g, hgN] using (hlog x a hx hxa.le).symm
    have hpos k : 0 < u (g m k) (g m (k + 1)) := huPos (g m k) (g m (k + 1)) (hgpos k) (le_of_lt (hgstep k))
    have hlo k : -(d * Fv k) ≤ T k := by dsimp [T]; exact Real.exp_le_exp.mp (by rw [Real.exp_log (hpos k)]; simpa [u, Fv, f, hgadd k, d] using hLow (g m k) d (hgpos k) hd)
    have hhi k : T k ≤ -(d * Fv (k + 2)) := by dsimp [T]; exact Real.exp_le_exp.mp (by rw [Real.exp_log (hpos k)]; have h := hUp (g m k) d (hgpos k) hd; rw [hgadd2 k, hgadd k] at h; simpa [u, Fv, f, d] using h)
    have hslo : -(d * S 0) ≤ L := by
      rw [← hsumlog];      dsimp [S];      simpa [Finset.mul_sum, Finset.sum_neg_distrib] using Finset.sum_le_sum (fun k hk => hlo k)
    have hshi : L ≤ -(d * S 2) := by
      rw [← hsumlog]; dsimp [S]; simpa [Finset.mul_sum, Finset.sum_neg_distrib] using Finset.sum_le_sum (fun k hk => hhi k)
    have hanti : AntitoneOn Ffun (Icc (0 : ℝ) (0 + (N : ℝ))) := by
      intro s hs t ht hst;      dsimp [Ffun]
      exact hfanti (by have hp : 0 ≤ d * s := mul_nonneg hd.le hs.1; linarith) (add_le_add_left (mul_le_mul_of_nonneg_left hst hd.le) x)
    have hsub : d * J = I := by
      dsimp [J, Ffun];      rw [intervalIntegral.mul_integral_comp_mul_add];      simpa [I, d, g, hgN]
    have hcompLo : d * S 1 ≤ I := by
      have h := mul_le_mul_of_nonneg_left (hanti.sum_le_integral (x₀ := (0 : ℝ)) (a := N)) hd.le
      have h' : d * S 1 ≤ d * J := by simpa [S, Fv, Ffun, g, d, J] using h
      exact h'.trans (le_of_eq hsub)
    have hcompHi : I ≤ d * S 0 := by
      have h := mul_le_mul_of_nonneg_left (hanti.integral_le_sum (x₀ := (0 : ℝ)) (a := N)) hd.le
      have h' : d * J ≤ d * S 0 := by simpa [S, Fv, Ffun, g, d, J] using h
      exact (le_of_eq hsub.symm).trans h'
    have hS01 : S 1 = S 0 - slopeDiff := by
      have h := Finset.sum_range_sub' Fv N
      rw [Finset.sum_sub_distrib] at h;      dsimp [S] at h ⊢
      simp [slopeDiff, Fv, g, hgN] at h ⊢
      linarith
    have hS12 : S 2 = S 1 - (Fv 1 - Fv (N + 1)) := by
      have h := Finset.sum_range_sub' (fun k => Fv (k + 1)) N
      rw [Finset.sum_sub_distrib] at h;      dsimp [S] at h ⊢
      linarith
    have hdiff : d * (Fv 1 - Fv (N + 1)) ≤ d * C := by
      apply mul_le_mul_of_nonneg_left _ hd.le
      have h := hfanti hg0 (le_of_lt (hgstep 0))
      have hn := hf0 (g m (N + 1))
      dsimp [Fv, C] at h hn ⊢
      simp [g] at h hn ⊢
      linarith
    rw [hS01] at hcompLo;    rw [hS12] at hshi
    constructor
    · have hl : -I - d * slopeDiff ≤ L := by nlinarith [hslo, hcompLo]
      simpa only [d] using hl
    · have hu' : L ≤ -I + d * (C + slopeDiff) := by nlinarith
      simpa only [d] using hu'
  have hδ : Tendsto δ atTop (𝓝 0) := by simpa [δ] using (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)).const_div_atTop (a - x)
  have hzero c : Tendsto (fun m : ℕ => δ m * c) atTop (𝓝 0) := by simpa using hδ.mul_const c
  have hLeq : L = -I := tendsto_nhds_unique tendsto_const_nhds
    (tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using tendsto_const_nhds.sub (hzero slopeDiff))
      (by simpa using tendsto_const_nhds.add (hzero (C + slopeDiff)))
      (Filter.Eventually.of_forall (fun m => (hseq m).1))
      (Filter.Eventually.of_forall (fun m => (hseq m).2)))
  change u x a = Real.exp (-I)
  rw [← hLeq]
  simpa [L] using (Real.exp_log (huPos x a hx hxa.le)).symm
end
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) (q : ℝ) (hq : 0 ≤ q) (n : Measure ℝ)
    (hLaw : HasActualQExcursionHeightLaw P D ψ q n)
    (hLow : ∀ l d : ℝ, 0 < l → 0 < d → Real.exp (-(d * (Phi ψ q + (n (Set.Ici l)).toReal))) ≤ upBeforeDownExpectation P D.X q l (l + d))
    (hUp : ∀ l d : ℝ, 0 < l → 0 < d → upBeforeDownExpectation P D.X q l (l + d) ≤ Real.exp (-(d * (Phi ψ q + (n (Set.Ici (l + d + d))).toReal)))) :
    ∀ x a : ℝ, 0 < x → x < a → upBeforeDownExpectation P D.X q x a = Real.exp (-(∫ t in x..a, Phi ψ q + (n (Set.Ici t)).toReal)) := scaleBridgeLimitAux hq hLaw hLow hUp
