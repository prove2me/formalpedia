-- Prove2me | solution 1 for MasulloRH.prime_shell_tests_require_independent_radial_profiles
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:35:26.48632+00:00
-- url     : https://prove2.me/submissions/ace6f1c8-65f2-462f-ae9e-ebb60fdd8f99

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Filter MeasureTheory
open scoped Topology
open Set

theorem MasulloRH.exists_prime_shell_bump (q : Nat.Primes) :
    ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Set.Ioi 1 ∧ ∀ (p : Nat.Primes) (k : ℤ),
        f ((p : ℝ)^k) = if p = q ∧ k = 1 then 1 else 0 := by
  let b : ContDiffBump (q : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩
  have hq : 2 ≤ (q : ℝ) := by exact_mod_cast q.prop.two_le
  have hs : tsupport (fun t : ℝ => b t) ⊆ Set.Ioi 1 := by
    rw [b.tsupport_eq]
    intro t ht
    change dist t (q : ℝ) ≤ 1/2 at ht
    rw [Real.dist_eq, abs_le] at ht
    change 1 < t
    linarith [ht.1]
  have hval (n : ℕ) (hne : n ≠ (q : ℕ)) : b n = 0 := by
    apply b.zero_of_le_dist
    change 1/2 ≤ dist (n : ℝ) (q : ℝ)
    rw [Real.dist_eq]
    rcases lt_or_gt_of_ne hne with h | h
    · have h' : (n : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast h
      linarith [neg_le_abs ((n:ℝ)-(q:ℝ))]
    · have h' : (q : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h
      linarith [le_abs_self ((n:ℝ)-(q:ℝ))]
  refine ⟨b, b.contDiff, b.hasCompactSupport, hs, ?_⟩
  intro p k
  cases k with
  | ofNat n =>
    by_cases h : (p : ℕ)^n = (q:ℕ)
    · obtain ⟨hp,hn⟩ := q.prop.pow_eq_iff.mp h
      have hp' : p = q := Subtype.ext hp
      subst p
      subst n
      simpa using b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    · have hh : ¬ (p = q ∧ n = 1) := by
        rintro ⟨rfl, rfl⟩
        simp at h
      simpa [hh] using hval ((p:ℕ)^n) h
  | negSucc n =>
    have hp : 1 ≤ (p:ℝ) := by exact_mod_cast p.prop.one_lt.le
    have ht : (p:ℝ)^(Int.negSucc n) ≤ 1 :=
      zpow_le_one_of_nonpos₀ hp (by omega)
    have hz : b ((p:ℝ)^(Int.negSucc n)) = 0 := by
      apply b.zero_of_le_dist
      change 1/2 ≤ dist ((p:ℝ)^(Int.negSucc n)) (q:ℝ)
      rw [Real.dist_eq]
      linarith [neg_le_abs (((p:ℝ)^(Int.negSucc n))-(q:ℝ))]
    simpa using hz

theorem MasulloRH.prime_shell_bump_evaluation (p q : Nat.Primes) (a : ℝ) (f : ℝ → ℝ)
    (hf : ∀ (p : Nat.Primes) (k : ℤ), f ((p : ℝ)^k) = if p = q ∧ k = 1 then 1 else 0) :
    (∑' k : ℤ, (((p : ℝ)^(-k))^a) * f ((p : ℝ)^(-k))) = if p = q then (p:ℝ)^a else 0 := by
  rw [tsum_eq_single (-1)]
  · rw [hf p (-(-1:ℤ))]
    by_cases he : p = q <;> simp [he]
  · intro k hk
    have h : -k ≠ 1 := by omega
    rw [hf p (-k), if_neg (fun hp => h hp.2), mul_zero]

theorem solution :
    ∃ f : Nat.Primes → ℝ → ℝ,
      (∀ q, ContDiff ℝ (⊤ : ℕ∞) (f q) ∧ HasCompactSupport (f q) ∧ tsupport (f q) ⊆ Set.Ioi 1) ∧
      (∀ (p q : Nat.Primes) (a : ℝ), (∑' k : ℤ, (((p : ℝ)^(-k))^a) * f q ((p : ℝ)^(-k))) = if p = q then (p:ℝ)^a else 0) ∧
      ∀ (N : ℕ) (p : Fin N ↪ Nat.Primes) (a : ℝ) (ι : Type*) (L : Filter ι)
        (M : ι → Matrix (Fin N) (Fin N) ℂ),
        (∀ i j, Tendsto (fun u => M u i j) L
          (𝓝 (((Real.log (p i : ℝ)) * ∑' k : ℤ, (((p i : ℝ)^(-k))^a) * f (p j) ((p i : ℝ)^(-k)) : ℝ) : ℂ))) →
        ∀ᶠ u in L,
          (∀ (d : ℕ) (A : Matrix (Fin N) (Fin d) ℂ) (B : Matrix (Fin d) (Fin N) ℂ),
            M u = A * B → N ≤ d) ∧
          ∀ (μ : Measure ℝ) (W V : Fin N → ℝ → ℂ),
            (∀ i j, Integrable (fun t => W i t * V j t) μ) →
            (∀ i j, M u i j = ∫ t, W i t * V j t ∂μ) →
            ∀ c : Fin N → ℂ, (∀ᵐ t ∂μ, ∑ i, c i * W i t = 0) → c = 0 := by
  choose f hf using MasulloRH.exists_prime_shell_bump
  have hs (p q : Nat.Primes) (a : ℝ) : (∑' k : ℤ, (((p : ℝ)^(-k))^a) * f q ((p : ℝ)^(-k))) = if p = q then (p:ℝ)^a else 0 := by
    exact MasulloRH.prime_shell_bump_evaluation p q a (f q) (hf q).2.2.2
  refine ⟨f, fun q => ⟨(hf q).1,(hf q).2.1,(hf q).2.2.1⟩, hs, ?_⟩
  intro N p a ι L M hlim
  let D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => ((Real.log (p i : ℝ) * (p i : ℝ)^a : ℝ) : ℂ))
  have hentry (i j : Fin N) :
      (((Real.log (p i : ℝ)) * ∑' k : ℤ, (((p i : ℝ)^(-k))^a) * f (p j) ((p i : ℝ)^(-k)) : ℝ) : ℂ) = D i j := by
    classical
    rw [hs (p i) (p j) a]
    by_cases h : i = j
    · subst j; simp [D]
    · simp [D, h, p.injective.ne h]
  have hmat : Tendsto (fun u => M u) L (𝓝 D) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [hentry] using hlim i j
  have hid : D.det ≠ 0 := by
    rw [show D.det = ∏ i, ((Real.log (p i : ℝ) * (p i : ℝ)^a : ℝ) : ℂ) by simp [D]]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ =>
      Complex.ofReal_ne_zero.mpr (mul_ne_zero (Real.log_pos (by exact_mod_cast (p i).prop.one_lt)).ne' (Real.rpow_pos_of_pos (by exact_mod_cast (p i).prop.pos) a).ne'))
  have hd := (continuous_id.matrix_det (n := Fin N) (R := ℂ)).continuousAt.tendsto.comp hmat
  filter_upwards [hd.eventually_ne hid] with u hu
  change (M u).det ≠ 0 at hu
  constructor
  · intro d A B hab
    rw [hab] at hu
    have hfull := Matrix.rank_of_det_ne_zero (A := A * B) hu
    have hle := (Matrix.rank_mul_le_left A B).trans A.rank_le_width
    simpa [hfull] using hle
  intro μ W V hint hpair c hzero
  apply Matrix.eq_zero_of_vecMul_eq_zero hu
  funext j
  rw [Matrix.vecMul_apply_eq_sum]
  change ∑ i, c i * M u i j = 0
  simp_rw [hpair, ← MeasureTheory.integral_const_mul]
  rw [← MeasureTheory.integral_finsetSum Finset.univ (fun i _ => (hint i j).const_mul (c i))]
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards [hzero] with t ht
  change (∑ i, c i * (W i t * V j t)) = 0
  simp only [← mul_assoc, ← Finset.sum_mul, ht, zero_mul]
