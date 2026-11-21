-- Prove2me | solution 1 for NymanBeurling.damped_moebius_approximation_on_each_fixed_prefix
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T01:01:36.979749+00:00
-- url     : https://prove2.me/submissions/e1d1822a-2264-4f6b-b9fd-6333b6c1ec06

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace DampedPrefix

open Filter
open scoped Topology

private theorem damped_moebius_hasSum {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + ε))
      ((riemannZeta ((1 + ε : ℝ) : ℂ))⁻¹).re := by
  let s : ℂ := ((1 + ε : ℝ) : ℂ)
  have hs : 1 < s.re := by simpa [s] using hε
  have h := (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum
  have hprod := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at hprod
  rw [← inv_eq_of_mul_eq_one_right hprod] at h
  apply (Complex.hasSum_re h).congr_fun
  intro n
  rw [LSeries.term_def₀ (by simp) s n]
  rw [Complex.cpow_neg, ← div_eq_mul_inv]
  change _ = ((ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ ((1 + ε : ℝ) : ℂ)).re
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n), ← Complex.ofReal_intCast,
    ← Complex.ofReal_div, Complex.ofReal_re]

private theorem damped_zeta_inv_tendsto_zero :
    Tendsto (fun ε : ℝ ↦ ((riemannZeta ((1+ε : ℝ) : ℂ))⁻¹).re) (𝓝[>] 0) (𝓝 0) := by
  have hnum : Tendsto (fun s : ℂ ↦ s-1) (𝓝[≠] 1) (𝓝 0) := by
    simpa using (tendsto_id.sub_const (1 : ℂ)).mono_left
      (nhdsWithin_le_nhds (a := (1 : ℂ)) (s := {1}ᶜ))
  have hquot := hnum.div riemannZeta_residue_one one_ne_zero
  simp only [zero_div] at hquot
  have hrec : Tendsto (fun s : ℂ ↦ (riemannZeta s)⁻¹) (𝓝[≠] 1) (𝓝 0) := by
    apply hquot.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hne : z-1 ≠ 0 := sub_ne_zero.mpr hz
    change (z-1) / ((z-1)*riemannZeta z) = _
    rw [div_mul_eq_div_div, div_self hne, one_div]
  have ht : Tendsto (fun ε : ℝ ↦ ((1+ε : ℝ) : ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcont : Continuous (fun ε : ℝ ↦ ((1+ε : ℝ) : ℂ)) := by fun_prop
      simpa using (hcont.continuousAt.continuousWithinAt (x := (0 : ℝ)) (s := Set.Ioi 0)).tendsto
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change ((1+ε : ℝ) : ℂ) ≠ 1
      exact_mod_cast (by linarith [show 0 < ε from hε] : 1+ε ≠ 1)
  simpa [Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp (hrec.comp ht)

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

private theorem damped_floor_identity (m : ℕ) (hm : 0 < m) :
    (∑ k ∈ Finset.range (m+1), (ArithmeticFunction.moebius k : ℝ) * (m / k : ℕ)) = 1 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [sum_range_succ]
  | succ m hm ih =>
    have hdiff (k : ℕ) :
        (moebius k : ℝ) * (((m+1)/k : ℕ) : ℝ) =
          (moebius k : ℝ) * ((m/k : ℕ) : ℝ) +
            (if k ∣ m+1 then (moebius k : ℝ) else 0) := by
      by_cases hk : k ∣ m+1
      · rw [Nat.succ_div_of_dvd hk, Nat.cast_add_one, mul_add, mul_one, if_pos hk]
      · rw [Nat.succ_div_of_not_dvd hk, if_neg hk, add_zero]
    have he : ∑ k ∈ (m+1).divisors, (moebius k : ℝ) = 0 := by
      change (∑ k ∈ (m+1).divisors, ((moebius : ArithmeticFunction ℝ) k)) = 0
      rw [← coe_mul_zeta_apply, coe_moebius_mul_coe_zeta, one_apply_ne]
      omega
    simp_rw [hdiff, sum_add_distrib]
    rw [← sum_filter, Nat.filter_dvd_eq_divisors (by omega), he, add_zero, sum_range_succ]
    simpa [Nat.div_eq_of_lt (Nat.lt_succ_self m)] using ih

open Finset

private theorem damp_residual_cut_sum (ε : ℝ) (m N : ℕ) (hmN : m ≤ N) :
    1 + ∑ k : Fin N, ((ArithmeticFunction.moebius (k.val+2) : ℝ) / (k.val+2 : ℝ)^ε) *
      (((m % (k.val+2) : ℕ) : ℝ)) / (k.val+2 : ℝ) =
    1 + (m:ℝ) * (∑ d ∈ Finset.range (N+2), (ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^(1+ε)) -
      ∑ d ∈ Finset.range (m+1), ((ArithmeticFunction.moebius d : ℝ) / (d:ℝ)^ε) * ((m / d : ℕ) : ℝ) := by
  let u (d : ℕ) : ℝ := ArithmeticFunction.moebius d
  let r (d : ℕ) := u d / (d:ℝ)^ε * ((m%d : ℕ) : ℝ) / (d:ℝ)
  let b (d : ℕ) := u d / (d:ℝ)^(1+ε)
  let z (d : ℕ) := u d / (d:ℝ)^ε * ((m/d : ℕ) : ℝ)
  have elem (d : ℕ) : r d = (m:ℝ)*b d - z d := by
    by_cases hd : d=0
    · simp [hd,r,b,z,u]
    have hd0 : (0:ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hw := Real.rpow_pos_of_pos hd0 ε
    have hdiv : ((m%d : ℕ):ℝ)+(d:ℝ)*((m/d : ℕ):ℝ) = (m:ℝ) := by exact_mod_cast Nat.mod_add_div m d
    have hrem : ((m%d : ℕ):ℝ)/(d:ℝ)=(m:ℝ)/(d:ℝ)-((m/d : ℕ):ℝ) := by
      field_simp
      linarith
    calc r d = u d/(d:ℝ)^ε*(((m%d : ℕ):ℝ)/(d:ℝ)) := by dsimp [r]; ring
         _ = _ := by rw [hrem]; dsimp [b,z]; rw [Real.rpow_add hd0,Real.rpow_one]; ring
  have h0 : r 0 = 0 := by simp [r]
  have h1 : r 1 = 0 := by simp [r,Nat.mod_one]
  have liftSum : ∑ k : Fin N, r (k.val+2) = ∑ d ∈ range (N+2), r d := by
    rw [Fin.sum_univ_eq_sum_range (fun i => r (i+2)) N, Nat.add_comm N 2, sum_range_add]
    simp [sum_range_succ,h0,h1,Nat.add_comm]
  have hfloor : ∑ d ∈ range (m+1), z d = ∑ d ∈ range (N+2), z d := by
    refine sum_subset (range_mono (by omega)) ?_
    intro d _ hd
    have hlt : m < d := by have := mt mem_range.mpr hd; omega
    simp [z,Nat.div_eq_of_lt hlt]
  have hL : (∑ k : Fin N, (↑(ArithmeticFunction.moebius (k.val+2)) : ℝ) / ((k:ℝ)+2)^ε *
      ((m%(k.val+2):ℕ):ℝ) / ((k:ℝ)+2)) =
      ∑ k : Fin N, r (k.val+2) := by simp [r,u]
  rw [hL,liftSum]
  change 1+∑ d ∈ range (N+2),r d = 1+(m:ℝ)*∑ d ∈ range (N+2), b d - ∑ d ∈ range (m+1), z d
  simp_rw [elem]
  rw [sum_sub_distrib,←mul_sum,hfloor]
  ring

open Filter Topology

private noncomputable def row (m N : ℕ) (ε : ℝ) : ℝ :=
  1 + ∑ k : Fin N, ((ArithmeticFunction.moebius (k.val+2) : ℝ) / (k.val+2 : ℝ)^ε) *
    (((m % (k.val+2) : ℕ) : ℝ)) / (k.val+2 : ℝ)

private noncomputable def correction (m : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ Finset.range (m+1), ((ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^ε) * ((m / d : ℕ):ℝ)

private noncomputable def rowLimit (m : ℕ) (ε : ℝ) : ℝ :=
  1 + (m:ℝ)*((riemannZeta ((1+ε:ℝ):ℂ))⁻¹).re - correction m ε

private lemma row_converges (m : ℕ) (ε : ℝ) (he : 0 < ε) :
    Tendsto (fun N : ℕ => row m N ε) atTop (𝓝 (rowLimit m ε)) := by
  have hp := (damped_moebius_hasSum he).tendsto_sum_nat.comp (tendsto_add_atTop_nat 2)
  have h := ((hp.const_mul (m:ℝ)).const_add 1).sub_const (correction m ε)
  apply h.congr'
  filter_upwards [eventually_ge_atTop m] with N hN
  exact (damp_residual_cut_sum ε m N hN).symm

private lemma rowLimit_converges (m : ℕ) (hm : 0 < m) :
    Tendsto (rowLimit m) (𝓝[>] 0) (𝓝 0) := by
  have hd (d : ℕ) : ContinuousAt
      (fun ε : ℝ => ((ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^ε) * ((m/d:ℕ):ℝ)) 0 := by
    by_cases h : d = 0
    · subst d; simpa using (continuousAt_const (x := (0:ℝ)) (y := (0:ℝ)))
    · exact (continuousAt_const.div (Real.continuousAt_const_rpow (by exact_mod_cast h))
        (by simp)).mul continuousAt_const
  have hc : ContinuousAt (correction m) 0 := by
    exact tendsto_finsetSum _ (fun d _ => (hd d).tendsto)
  have hc0 : correction m 0 = 1 := by
    simpa only [correction, Real.rpow_zero, div_one] using damped_floor_identity m hm
  have hl := ((damped_zeta_inv_tendsto_zero.const_mul (m:ℝ)).const_add 1).sub hc.continuousWithinAt
  change Tendsto (fun x : ℝ => 1 + (m:ℝ)*((riemannZeta ((1+x:ℝ):ℂ))⁻¹).re - correction m x) _ _
  simpa only [hc0, mul_zero, add_zero, sub_self] using hl

private noncomputable def normSum (H : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range H, (v (i+1))^2 / (((i:ℝ)+1)*((i:ℝ)+2))

private lemma normSum_lim {α : Type} {l : Filter α} (H : ℕ) (v : α → ℕ → ℝ) (w : ℕ → ℝ)
    (hv : ∀ m : ℕ, 0 < m → Tendsto (fun x => v x m) l (𝓝 (w m))) :
    Tendsto (fun x => normSum H (v x)) l (𝓝 (normSum H w)) := by
  exact tendsto_finsetSum _ (fun i _ => ((hv (i+1) (by omega)).pow 2).div_const _)

end DampedPrefix

open Filter Topology DampedPrefix

theorem solution (H : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1/2 ∧
      ∀ᶠ N : ℕ in atTop, ∀ h : ℕ, h ≤ H →
        (∑ n ∈ Finset.range h,
          (1 + ∑ k : Fin N,
            ((ArithmeticFunction.moebius (k.val+2) : ℝ) / (k.val+2 : ℝ)^ε) *
              (((n+1) % (k.val+2) : ℕ) : ℝ) / (k.val+2 : ℝ))^2 /
          ((n+1 : ℝ)*(n+2 : ℝ))) < δ := by
  have hz : normSum H (fun _ => 0) = 0 := by simp [normSum]
  have ho := normSum_lim H (fun e m => rowLimit m e) (fun _ => 0) rowLimit_converges
  rw [hz] at ho
  filter_upwards [ho.eventually_lt_const hδ, self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0:ℝ) < 1/2 by norm_num)).filter_mono nhdsWithin_le_nhds] with ε hL he hhalf
  refine ⟨he, hhalf, ?_⟩
  have hi := normSum_lim H (fun N m => row m N ε) (fun m => rowLimit m ε)
    (fun m _ => row_converges m ε he)
  filter_upwards [hi.eventually_lt_const hL] with N hNh
  intro h hh
  apply lt_of_le_of_lt _ hNh
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hh) (fun n _ _ => by positivity)
