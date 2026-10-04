-- Prove2me | solution 1 for KKBinPacking.GeometricGrouping.alg2_iterations_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-02T12:10:35.357973+00:00
-- url     : https://prove2.me/submissions/e96b7f2a-43fc-4061-a627-e7a78cc24166
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Reduction (sketch) of Algorithm 2's iteration bound to its size recurrence.
-- The imported platform recurrence remains Open; the proof below contains no holes.
-- Karmarkar--Karp, FOCS 1982, p. 316.
import Theorems.Thm_KKBinPacking_GeometricGrouping_alg2_size_recursion

set_option autoImplicit false

open KKBinPacking.GeometricGrouping

theorem solution (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (I : Multiset ℝ) (hI : IsInstance I) (tr : Alg2Trace k g I) (ht : 1 ≤ tr.t) :
    (tr.t : ℝ) ≤ Real.log (SIZE (tr.inst 0)) / Real.log k + 1 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hkone : (1 : ℝ) < k := by linarith
  have hden : 0 < 1 - 1 / (k : ℝ) := by
    have : 1 / (k : ℝ) < 1 := (div_lt_one hkpos).2 hkone
    linarith
  have hlog : 0 ≤ Real.log (1 / g) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hg0).2 (by simpa using hg1)
  let C : ℝ := Real.log (1 / g) / (1 - 1 / (k : ℝ))
  have hC : 0 ≤ C := div_nonneg hlog hden.le
  have hfixed : C * (1 - 1 / (k : ℝ)) = Real.log (1 / g) :=
    div_mul_cancel₀ _ hden.ne'
  have hCeq : C / (k : ℝ) + Real.log (1 / g) = C := by
    rw [← hfixed]
    ring
  have hgeom : ∀ i ≤ tr.t, SIZE (tr.inst i) ≤ SIZE (tr.inst 0) / (k : ℝ) ^ i + C := by
    intro i
    induction i with
    | zero => intro hi; simp only [pow_zero, div_one]; linarith
    | succ i ih =>
      intro hi
      have hi' : i < tr.t := by omega
      have hprev := ih (by omega)
      have hrec := (alg2_size_recursion k hk g hg0 hg1 I hI tr i hi').2.2.2.2
      have hdiv := div_le_div_of_nonneg_right hprev hkpos.le
      calc
        SIZE (tr.inst (i + 1)) ≤ SIZE (tr.inst i) / k + Real.log (1 / g) := hrec
        _ ≤ (SIZE (tr.inst 0) / (k : ℝ) ^ i + C) / k + Real.log (1 / g) :=
          by linarith only [hdiv]
        _ = SIZE (tr.inst 0) / (k : ℝ) ^ (i + 1) + C := by
          rw [add_div, div_div, ← pow_succ, add_assoc, hCeq]
  have hm : tr.t - 1 < tr.t := by omega
  have hrun := tr.loop_run (tr.t - 1) hm
  have hbound := hgeom (tr.t - 1) (by omega)
  have hthreshold : alg2Threshold k g = 1 + C := by
    simp [alg2Threshold, C, div_eq_mul_inv, mul_comm]
  rw [hthreshold] at hrun
  have hquot : 1 < SIZE (tr.inst 0) / (k : ℝ) ^ (tr.t - 1) := by linarith
  have hpowpos := pow_pos hkpos (tr.t - 1)
  have hpow : (k : ℝ) ^ (tr.t - 1) < SIZE (tr.inst 0) := by
    simpa using (lt_div_iff₀ hpowpos).1 hquot
  have hlogbound := Real.log_lt_log hpowpos hpow
  rw [Real.log_pow] at hlogbound
  have hklog : 0 < Real.log (k : ℝ) := Real.log_pos hkone
  have hratio : ((tr.t - 1 : ℕ) : ℝ) < Real.log (SIZE (tr.inst 0)) / Real.log k :=
    (lt_div_iff₀ hklog).2 hlogbound
  have hcast : ((tr.t - 1 : ℕ) : ℝ) + 1 = (tr.t : ℝ) := by
    exact_mod_cast (show tr.t - 1 + 1 = tr.t by omega)
  linarith
