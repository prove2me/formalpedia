-- Prove2me | solution 1 for MassiveChannels.GCE.holevoQuantity_le_entropy_mean
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:12:29.554918+00:00
-- url     : https://prove2.me/submissions/30f83d68-b619-4450-a483-4cea028b9246

import Mathlib
import Definitions.Def_MassiveChannels_GCE_Model

namespace X5HQ

open Matrix QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P07

lemma tr_cfc {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    (f : ℝ → ℝ) : (cfc f X).trace = ∑ i, ((f (hX.eigenvalues i) : ℝ) : ℂ) := by
  rw [hX.cfc_eq]
  unfold IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply]
  set U := (hX.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (hX.eigenvectorUnitary).2
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]
  rfl

lemma vn_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ}
    (hX : QAlgorithms.IsDensityMatrix X) : 0 ≤ vnEntropy X := by
  have hH := hX.1.1
  unfold vnEntropy
  rw [tr_cfc hH, Complex.re_sum]
  have hs : ∑ i, hH.eigenvalues i = 1 := by
    have h := hX.2
    rw [hH.trace_eq_sum_eigenvalues] at h
    have := congrArg Complex.re h
    simpa using this
  have h0 : ∀ i, 0 ≤ hH.eigenvalues i := hX.1.eigenvalues_nonneg
  have h1 : ∀ i, hH.eigenvalues i ≤ 1 := fun i => by
    rw [← hs]; exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
  rw [← neg_nonpos, neg_neg]
  refine Finset.sum_nonpos fun i _ => ?_
  simp only [Complex.ofReal_re]
  exact mul_nonpos_of_nonneg_of_nonpos (h0 i) (Real.logb_nonpos (by norm_num) (h0 i) (h1 i))

theorem hq {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q] (e : CQData X Q)
    (he : e.Valid) : ensembleInformation e ≤ vnEntropy (ensembleMean e) := by
  unfold ensembleInformation QAlgorithms.Papers.Independent.Information100.P27.labelInformation
  have hnn : 0 ≤ ∑ i, e.prob i * vnEntropy (e.state i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (he.1 i) (by convert vn_nonneg (he.2.2 i))
  convert sub_le_self (vnEntropy (ensembleMean e)) hnn using 2
  · unfold ensembleMean; congr 1
  · congr 1; funext i; congr 2

end X5HQ

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P07 in
theorem solution {X Q : Type} [Fintype X] [Fintype Q]
    [DecidableEq Q] [Nonempty Q] (e : CQData X Q) (he : e.Valid) :
    ensembleInformation e ≤ vnEntropy (ensembleMean e) := X5HQ.hq e he
