-- Prove2me | solution 1 for NumberField.exists_nonneg_abscissa_le_hasSum_tsum_mul_absNorm_cpow_eq_lseries_of_le_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/012f6487-a25a-5916-9827-d4fb0d2347f7

import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_nonneg_abscissa_le_hasSum_tsum_mul_absNorm_cpow_eq_lseries_of_le_mul_pow

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField IsDedekindDomain

noncomputable section

namespace NFLogDirichletSol

variable {K : Type} [Field K] [NumberField K]

abbrev nrm (v : HeightOneSpectrum (𝓞 K)) : ℕ := Ideal.absNorm v.asIdeal

theorem nrm_ne_zero (v : HeightOneSpectrum (𝓞 K)) : nrm v ≠ 0 := by
  rw [Ne, nrm, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot

theorem two_le_nrm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ nrm v := by
  have h0 := nrm_ne_zero v
  have h1 : nrm v ≠ 1 := by
    rw [Ne, nrm, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  unfold nrm at *
  omega

theorem nrm_pos (v : HeightOneSpectrum (𝓞 K)) : 0 < nrm v := Nat.pos_of_ne_zero (nrm_ne_zero v)

theorem nrm_real_pos (v : HeightOneSpectrum (𝓞 K)) : (0 : ℝ) < (nrm v : ℝ) :=
  Nat.cast_pos.mpr (nrm_pos v)

theorem two_le_nrm_real (v : HeightOneSpectrum (𝓞 K)) : (2 : ℝ) ≤ (nrm v : ℝ) := by
  exact_mod_cast two_le_nrm v

def idx (p : HeightOneSpectrum (𝓞 K) × ℕ) : ℕ := nrm p.1 ^ p.2

variable (K) in

abbrev Fib (n : ℕ) : Type := ↥((idx (K := K)) ⁻¹' {n})

theorem idx_eq_of_fib {n : ℕ} (q : Fib K n) : nrm q.1.1 ^ q.1.2 = n :=
  Set.mem_singleton_iff.mp (Set.mem_preimage.mp q.2)

theorem idx_ne_zero (p : HeightOneSpectrum (𝓞 K) × ℕ) : idx p ≠ 0 :=
  pow_ne_zero _ (nrm_ne_zero p.1)

scoped instance isEmpty_fib_zero : IsEmpty (Fib K 0) :=
  ⟨fun q => idx_ne_zero q.1 (idx_eq_of_fib q)⟩

theorem ne_zero_of_fib {n : ℕ} (q : Fib K n) : n ≠ 0 := by
  rw [← idx_eq_of_fib q]; exact idx_ne_zero q.1

theorem rpow_pow_eq_of_fib {n : ℕ} (q : Fib K n) (σ : ℝ) :
    (((nrm q.1.1 : ℕ) : ℝ) ^ (-σ)) ^ q.1.2 = ((n : ℕ) : ℝ) ^ (-σ) := by
  rw [Real.rpow_pow_comm (Nat.cast_nonneg _), ← Nat.cast_pow, idx_eq_of_fib q]

theorem natCast_pow_cpow_neg (q : ℕ) (s : ℂ) (m : ℕ) :
    (((q ^ m : ℕ) : ℂ)) ^ (-s) = (((q : ℂ)) ^ (-s)) ^ m := by
  rw [Nat.cast_pow, ← Complex.cpow_nat_mul, Complex.cpow_nat_mul']
  · simp [Complex.natCast_arg, Real.pi_pos]
  · simp [Complex.natCast_arg, Real.pi_pos.le]

theorem cpow_pow_eq_of_fib {n : ℕ} (q : Fib K n) (s : ℂ) :
    ((((nrm q.1.1 : ℕ) : ℂ)) ^ (-s)) ^ q.1.2 = ((n : ℕ) : ℂ) ^ (-s) := by
  rw [← natCast_pow_cpow_neg, idx_eq_of_fib q]

section Real

variable (c : HeightOneSpectrum (𝓞 K) → ℕ → ℝ)

def H (σ : ℝ) (p : HeightOneSpectrum (𝓞 K) × ℕ) : ℝ :=
  c p.1 p.2 * (((nrm p.1 : ℕ) : ℝ) ^ (-σ)) ^ p.2

theorem H_apply (σ : ℝ) (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    H c σ (v, m) = c v m * (((nrm v : ℕ) : ℝ) ^ (-σ)) ^ m := rfl

variable {c}
variable (hc0 : ∀ v : HeightOneSpectrum (𝓞 K), c v 0 = 0)
  (hc : ∀ (v : HeightOneSpectrum (𝓞 K)) (m : ℕ), 0 ≤ c v m)
  (B : ℝ) (hcB : ∀ (v : HeightOneSpectrum (𝓞 K)) (m : ℕ), c v m ≤ B * (((nrm v : ℕ) : ℝ)) ^ m)

include hc in
theorem H_nonneg (σ : ℝ) (p : HeightOneSpectrum (𝓞 K) × ℕ) : 0 ≤ H c σ p :=
  mul_nonneg (hc _ _) (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _)

def ratio (σ : ℝ) (v : HeightOneSpectrum (𝓞 K)) : ℝ := ((nrm v : ℕ) : ℝ) ^ (1 - σ)

theorem ratio_nonneg (σ : ℝ) (v : HeightOneSpectrum (𝓞 K)) : 0 ≤ ratio σ v :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem ratio_eq (σ : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    ratio σ v = ((nrm v : ℕ) : ℝ) * ((nrm v : ℕ) : ℝ) ^ (-σ) := by
  rw [ratio, sub_eq_add_neg, Real.rpow_add (nrm_real_pos v), Real.rpow_one]

theorem ratio_eq_neg (σ : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    ratio σ v = ((nrm v : ℕ) : ℝ) ^ (-(σ - 1)) := by
  rw [ratio, neg_sub]

theorem ratio_le_half {σ : ℝ} (hσ : 2 ≤ σ) (v : HeightOneSpectrum (𝓞 K)) : ratio σ v ≤ 1 / 2 := by
  have h1 : ratio σ v ≤ ((nrm v : ℕ) : ℝ) ^ (-1 : ℝ) := by
    unfold ratio
    apply Real.rpow_le_rpow_of_exponent_le
    · linarith [two_le_nrm_real v]
    · linarith
  have h2 : ((nrm v : ℕ) : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (two_le_nrm_real v) (by norm_num)
  have h3 : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by
    rw [Real.rpow_neg_one]; norm_num
  exact h1.trans (h2.trans_eq h3)

theorem pow_mul_rpow_pow (σ : ℝ) (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    ((nrm v : ℕ) : ℝ) ^ m * (((nrm v : ℕ) : ℝ) ^ (-σ)) ^ m = ratio σ v ^ m := by
  rw [← mul_pow, ← ratio_eq]

def M (B' σ : ℝ) (p : HeightOneSpectrum (𝓞 K) × ℕ) : ℝ :=
  2 * B' * ratio σ p.1 * (1 / 2 : ℝ) ^ p.2

include hc0 hc hcB in

theorem H_le_M {σ : ℝ} (hσ : 2 ≤ σ) (p : HeightOneSpectrum (𝓞 K) × ℕ) :
    H c σ p ≤ M (max B 0) σ p := by
  obtain ⟨v, m⟩ := p
  have hB' : 0 ≤ max B 0 := le_max_right _ _
  have hr0 := ratio_nonneg σ v
  have hrh := ratio_le_half hσ v
  cases m with
  | zero =>
    simp only [H, M, hc0 v, pow_zero, mul_one]
    positivity
  | succ k =>
    have hx : (0 : ℝ) ≤ ((nrm v : ℕ) : ℝ) ^ (k + 1) := pow_nonneg (Nat.cast_nonneg _) _
    have hw : (0 : ℝ) ≤ (((nrm v : ℕ) : ℝ) ^ (-σ)) ^ (k + 1) :=
      pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _
    calc H c σ (v, k + 1)
        = c v (k + 1) * (((nrm v : ℕ) : ℝ) ^ (-σ)) ^ (k + 1) := rfl
      _ ≤ (max B 0 * ((nrm v : ℕ) : ℝ) ^ (k + 1)) * (((nrm v : ℕ) : ℝ) ^ (-σ)) ^ (k + 1) := by
          apply mul_le_mul_of_nonneg_right _ hw
          exact (hcB v (k + 1)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hx)
      _ = max B 0 * ratio σ v ^ (k + 1) := by
          rw [mul_assoc, pow_mul_rpow_pow]
      _ = max B 0 * ratio σ v * ratio σ v ^ k := by ring
      _ ≤ max B 0 * ratio σ v * (1 / 2 : ℝ) ^ k := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB' hr0)
          exact pow_le_pow_left₀ hr0 hrh k
      _ = M (max B 0) σ (v, k + 1) := by
          simp only [M, pow_succ]
          ring

theorem summable_M_inner (B' σ : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    Summable fun m : ℕ => M B' σ (v, m) := by
  show Summable fun m : ℕ => 2 * B' * ratio σ v * (1 / 2 : ℝ) ^ m
  exact (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left _

theorem tsum_M_inner (B' σ : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    ∑' m : ℕ, M B' σ (v, m) = 4 * B' * ratio σ v := by
  show ∑' m : ℕ, 2 * B' * ratio σ v * (1 / 2 : ℝ) ^ m = _
  rw [tsum_mul_left, tsum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)]
  ring

include hc0 hc hcB in

theorem summable_H {σ : ℝ} (hσ : 2 < σ) : Summable (H c σ) := by
  have hnn : 0 ≤ H c σ := fun p => H_nonneg hc σ p
  have hB' : 0 ≤ max B 0 := le_max_right _ _
  have hle : ∀ p, H c σ p ≤ M (max B 0) σ p := fun p => H_le_M hc0 hc B hcB hσ.le p
  have hinner : ∀ v : HeightOneSpectrum (𝓞 K), Summable fun m : ℕ => H c σ (v, m) := fun v =>
    Summable.of_nonneg_of_le (fun m => hnn (v, m)) (fun m => hle (v, m)) (summable_M_inner _ σ v)
  refine (summable_prod_of_nonneg hnn).mpr ⟨hinner, ?_⟩

  have hout : Summable fun v : HeightOneSpectrum (𝓞 K) => 4 * max B 0 * ratio σ v := by
    have h1 : (1 : ℝ) < σ - 1 := by linarith
    have hs := NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K h1
    refine (hs.mul_left (4 * max B 0)).congr fun v => ?_
    rw [ratio_eq_neg]
  refine Summable.of_nonneg_of_le (fun v => tsum_nonneg fun m => hnn (v, m)) (fun v => ?_) hout
  rw [← tsum_M_inner]
  exact (hinner v).tsum_le_tsum (fun m => hle (v, m)) (summable_M_inner _ σ v)

end Real

section Coeff

variable (c : HeightOneSpectrum (𝓞 K) → ℕ → ℝ)

def coeff (n : ℕ) : ℝ := ∑' q : Fib K n, c q.1.1 q.1.2

variable {c}
variable (hc0 : ∀ v : HeightOneSpectrum (𝓞 K), c v 0 = 0)
  (hc : ∀ (v : HeightOneSpectrum (𝓞 K)) (m : ℕ), 0 ≤ c v m)
  (B : ℝ) (hcB : ∀ (v : HeightOneSpectrum (𝓞 K)) (m : ℕ), c v m ≤ B * (((nrm v : ℕ) : ℝ)) ^ m)

include hc in
theorem coeff_nonneg (n : ℕ) : 0 ≤ coeff c n := tsum_nonneg fun q => hc _ _

theorem H_of_fib {n : ℕ} (σ : ℝ) (q : Fib K n) :
    H c σ q.1 = c q.1.1 q.1.2 * ((n : ℕ) : ℝ) ^ (-σ) := by
  rw [H, rpow_pow_eq_of_fib q σ]

include hc0 hc hcB in

theorem summable_fib (n : ℕ) : Summable fun q : Fib K n => c q.1.1 q.1.2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact (hasSum_empty : HasSum (fun q : Fib K 0 => c q.1.1 q.1.2) 0).summable
  · have h3 : (2 : ℝ) < 3 := by norm_num
    have hs := (summable_H hc0 hc B hcB h3).subtype ((idx (K := K)) ⁻¹' {n})
    have hs' : Summable fun q : Fib K n => c q.1.1 q.1.2 * ((n : ℕ) : ℝ) ^ (-(3 : ℝ)) := by
      refine hs.congr fun q => ?_
      simp only [Function.comp_apply]
      exact H_of_fib 3 q
    have hn0 : ((n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≠ 0 :=
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) _).ne'
    refine (hs'.mul_right (((n : ℕ) : ℝ) ^ (-(3 : ℝ)))⁻¹).congr fun q => ?_
    rw [mul_assoc, mul_inv_cancel₀ hn0, mul_one]

include hc0 hc hcB in
theorem hasSum_fib (n : ℕ) : HasSum (fun q : Fib K n => c q.1.1 q.1.2) (coeff c n) :=
  (summable_fib hc0 hc B hcB n).hasSum

include hc0 hc hcB in
theorem hasSum_fib_complex (n : ℕ) :
    HasSum (fun q : Fib K n => ((c q.1.1 q.1.2 : ℝ) : ℂ)) ((coeff c n : ℝ) : ℂ) :=
  Complex.hasSum_ofReal.mpr (hasSum_fib hc0 hc B hcB n)

include hc0 hc hcB in

theorem tsum_fib_H {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∑' q : Fib K n, H c σ q.1 = coeff c n * ((n : ℕ) : ℝ) ^ (-σ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [tsum_empty, Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hσ.ne'), mul_zero]
  · simp_rw [H_of_fib σ]
    rw [tsum_mul_right, coeff]

include hc0 hc hcB in

theorem hasSum_fib_term (s : ℂ) (n : ℕ) :
    HasSum (fun q : Fib K n =>
        ((c q.1.1 q.1.2 : ℝ) : ℂ) * ((((nrm q.1.1 : ℕ) : ℂ)) ^ (-s)) ^ q.1.2)
      (LSeries.term (fun k => ((coeff c k : ℝ) : ℂ)) s n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero]
    exact hasSum_empty
  · have h1 := (hasSum_fib_complex hc0 hc B hcB n).mul_right (((n : ℕ) : ℂ) ^ (-s))
    rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
    refine h1.congr_fun fun q => ?_
    rw [cpow_pow_eq_of_fib q s]

end Coeff

section Abscissa

variable {c : HeightOneSpectrum (𝓞 K) → ℕ → ℝ}
variable (hc0 : ∀ v : HeightOneSpectrum (𝓞 K), c v 0 = 0)
  (hc : ∀ (v : HeightOneSpectrum (𝓞 K)) (m : ℕ), 0 ≤ c v m)
  (B : ℝ) (hcB : ∀ (v : HeightOneSpectrum (𝓞 K)) (m : ℕ), c v m ≤ B * (((nrm v : ℕ) : ℝ)) ^ m)

include hc0 hc hcB in
theorem lseriesSummable_coeff {σ : ℝ} (hσ : 2 < σ) :
    LSeriesSummable (fun n => ((coeff c n : ℝ) : ℂ)) (σ : ℂ) := by
  have hH := summable_H hc0 hc B hcB hσ

  have hfib : Summable fun n : ℕ => ∑' q : Fib K n, H c σ q.1 :=
    (hH.hasSum.tsum_fiberwise (idx (K := K))).summable
  have hσ0 : 0 < σ := by linarith
  have hfib' : Summable fun n : ℕ => coeff c n * ((n : ℕ) : ℝ) ^ (-σ) :=
    hfib.congr fun n => tsum_fib_H hc0 hc B hcB hσ0 n
  refine Summable.of_norm ?_
  refine hfib'.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [if_pos rfl, Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hσ0.ne'), mul_zero]
  · rw [if_neg hn, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg (coeff_nonneg hc n),
      Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

include hc0 hc hcB in
theorem abscissa_le_two :
    LSeries.abscissaOfAbsConv (fun n => ((coeff c n : ℝ) : ℂ)) ≤ ((2 : ℝ) : EReal) :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun _ hy =>
    lseriesSummable_coeff hc0 hc B hcB hy

end Abscissa

section Cplx

variable {c : HeightOneSpectrum (𝓞 K) → ℕ → ℝ}
variable (hc0 : ∀ v : HeightOneSpectrum (𝓞 K), c v 0 = 0)
  (hc : ∀ (v : HeightOneSpectrum (𝓞 K)) (m : ℕ), 0 ≤ c v m)
  (B : ℝ) (hcB : ∀ (v : HeightOneSpectrum (𝓞 K)) (m : ℕ), c v m ≤ B * (((nrm v : ℕ) : ℝ)) ^ m)

def F (c : HeightOneSpectrum (𝓞 K) → ℕ → ℝ) (s : ℂ) (p : HeightOneSpectrum (𝓞 K) × ℕ) : ℂ :=
  ((c p.1 p.2 : ℝ) : ℂ) * ((((nrm p.1 : ℕ) : ℂ)) ^ (-s)) ^ p.2

include hc in
theorem norm_F (s : ℂ) (p : HeightOneSpectrum (𝓞 K) × ℕ) : ‖F c s p‖ = H c s.re p := by
  rw [F, H, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hc _ _),
    Complex.norm_natCast_cpow_of_pos (nrm_pos p.1), Complex.neg_re]

include hc0 hc hcB in
theorem summable_F {s : ℂ} (hs : 2 < s.re) : Summable (F c s) := by
  refine Summable.of_norm ?_
  have h := summable_H hc0 hc B hcB hs
  exact h.congr fun p => (norm_F hc s p).symm

include hc0 hc hcB in

theorem hasSum_F {s : ℂ} (hs : 2 < s.re) :
    HasSum (F c s) (LSeries (fun n => ((coeff c n : ℝ) : ℂ)) s) := by
  have hF := summable_F hc0 hc B hcB hs
  have h1 : HasSum (fun n : ℕ => ∑' q : Fib K n, F c s q.1) (∑' p, F c s p) :=
    hF.hasSum.tsum_fiberwise (idx (K := K))
  have h2 : ∀ n : ℕ, ∑' q : Fib K n, F c s q.1 = LSeries.term (fun k => ((coeff c k : ℝ) : ℂ)) s n :=
    fun n => (hasSum_fib_term hc0 hc B hcB s n).tsum_eq
  simp_rw [h2] at h1
  have h3 : LSeries (fun n => ((coeff c n : ℝ) : ℂ)) s = ∑' p, F c s p := h1.tsum_eq
  rw [h3]
  exact hF.hasSum

end Cplx

end NFLogDirichletSol
p2m_reactivate "P2MW.S_NumberField_exists_nonneg_abscissa_le_hasSum_tsum_mul_absNorm_cpow_eq_lseries_of_le_mul_pow.NFLogDirichletSol"

end
p2m_reactivate "P2MW.S_NumberField_exists_nonneg_abscissa_le_hasSum_tsum_mul_absNorm_cpow_eq_lseries_of_le_mul_pow.NFLogDirichletSol"

open NFLogDirichletSol in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (c : HeightOneSpectrum (𝓞 K) → ℕ → ℝ)
    (hc0 : ∀ v : HeightOneSpectrum (𝓞 K), c v 0 = 0)
    (hc : ∀ (v : HeightOneSpectrum (𝓞 K)) (m : ℕ), 0 ≤ c v m)
    (B : ℝ) (hcB : ∀ (v : HeightOneSpectrum (𝓞 K)) (m : ℕ),
      c v m ≤ B * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ)) ^ m) :
    ∃ d : ℕ → ℝ, (∀ n : ℕ, 0 ≤ d n) ∧
      LSeries.abscissaOfAbsConv (fun n => (d n : ℂ)) ≤ ((2 : ℝ) : EReal) ∧
      ∀ s : ℂ, 2 < s.re →
        (∀ v : HeightOneSpectrum (𝓞 K),
          Summable (fun m : ℕ => (c v m : ℂ) * ((((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ^ (-s)) ^ m)) ∧
        HasSum (fun v : HeightOneSpectrum (𝓞 K) =>
            ∑' m : ℕ, (c v m : ℂ) * ((((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ^ (-s)) ^ m)
          (LSeries (fun n => (d n : ℂ)) s) := by
  refine ⟨coeff c, coeff_nonneg hc, abscissa_le_two hc0 hc B hcB, fun s hs => ?_⟩
  have hF := summable_F hc0 hc B hcB hs
  refine ⟨fun v => hF.prod_factor v, ?_⟩
  exact (hasSum_F hc0 hc B hcB hs).prod_fiberwise fun v => (hF.prod_factor v).hasSum

end S_NumberField_exists_nonneg_abscissa_le_hasSum_tsum_mul_absNorm_cpow_eq_lseries_of_le_mul_pow
end P2MW
export P2MW.S_NumberField_exists_nonneg_abscissa_le_hasSum_tsum_mul_absNorm_cpow_eq_lseries_of_le_mul_pow (solution)
