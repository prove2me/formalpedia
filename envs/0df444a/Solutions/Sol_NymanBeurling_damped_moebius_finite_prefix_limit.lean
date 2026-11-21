-- Prove2me | solution 1 for NymanBeurling.damped_moebius_finite_prefix_limit
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:02:28.627103+00:00
-- url     : https://prove2.me/submissions/89168ba6-2d6e-4014-8066-95fcf732cc1b

import Mathlib

open Filter Topology Finset ArithmeticFunction
open scoped Moebius
noncomputable section

private def w (ε : ℝ) (k : ℕ) : ℝ := (μ k : ℝ)/(k:ℝ)^ε
private def moment (N : ℕ) (ε : ℝ) := ∑ k ∈ Ioc 0 N, w ε k/(k:ℝ)
private def floorSum (m : ℕ) (ε : ℝ) := ∑ k ∈ Ioc 0 m, w ε k*(m/k : ℕ)
private def residue (N m : ℕ) (ε : ℝ) := 1+∑ k ∈ Ioc 0 N, w ε k*(m%k : ℕ)/(k:ℝ)
private def zinv (ε : ℝ) : ℝ := (riemannZeta (1+(ε:ℂ)))⁻¹.re

private theorem moments (ε : ℝ) (hε : 0<ε) : Tendsto (fun N => moment N ε) atTop (𝓝 (zinv ε)) := by
  let s := (1+(ε:ℂ))
  have hs : 1<s.re := by simp [s,hε]
  have hmul := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs] at hmul
  have hinv : LSeries (fun n => (μ n : ℂ)) s = (riemannZeta s)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rwa [mul_comm])
  have hserie := (LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum
  rw [hinv] at hserie
  have hsum := (Complex.reCLM.hasSum hserie).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  apply hsum.congr
  intro N
  change (∑ k ∈ range (N+1), (LSeries.term (fun n => (μ n:ℂ)) s k).re) = _
  have heq : range (N+1) = insert 0 (Ioc 0 N) := by ext i; simp
  rw [heq,sum_insert (by simp),LSeries.term_zero,Complex.zero_re,zero_add]
  apply sum_congr rfl
  intro d hd
  obtain ⟨hd0,_⟩ := mem_Ioc.mp hd
  have hdp : (0:ℝ)<d := by exact_mod_cast hd0
  have hpow : (d:ℂ)^s = (((d:ℝ)^ε*(d:ℝ):ℝ):ℂ) := by
    have he : s = (((ε+1:ℝ):ℝ):ℂ) := by simp [s,add_comm]
    rw [he,←Complex.ofReal_natCast,←Complex.ofReal_cpow hdp.le,Real.rpow_add hdp,Real.rpow_one]
  rw [LSeries.term_of_ne_zero (Nat.ne_of_gt hd0) _ _,hpow]
  have hr : (μ d : ℂ) = ((μ d : ℝ):ℂ) := by norm_cast
  rw [hr,←Complex.ofReal_div,Complex.ofReal_re]
  dsimp [w]; ring

private theorem zinv_limit : Tendsto zinv (𝓝[>] 0) (𝓝 0) := by
  have hε : Tendsto (fun ε : ℝ => (ε:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    by simpa only [Complex.ofReal_zero] using ((Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
  have hs : Tendsto (fun ε : ℝ => (1:ℂ)+ε) (𝓝[>] 0) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using tendsto_const_nhds.add hε,?_⟩
    filter_upwards [self_mem_nhdsWithin (s := Set.Ioi 0)] with ε h
    simp [ne_of_gt (show 0<ε from h)]
  have hres := riemannZeta_residue_one.comp hs
  have hh := hε.div hres (by norm_num : (1:ℂ) ≠ 0)
  have hi : Tendsto (fun ε : ℝ => (riemannZeta (1+(ε:ℂ)))⁻¹) (𝓝[>] 0) (𝓝 0) := by
    rw [zero_div] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin (s := Set.Ioi 0)] with ε h
    have he : (ε:ℂ)≠0 := by exact_mod_cast (ne_of_gt (show 0<ε from h))
    change (ε:ℂ) / ((1+ε-1)*riemannZeta (1+ε)) = (riemannZeta (1+ε))⁻¹
    simp [he,div_eq_mul_inv,mul_left_comm,mul_comm,mul_assoc]
  exact (Complex.continuous_re.tendsto (0:ℂ)).comp hi


private theorem floor_zero (m : ℕ) (hm : 0 < m) : floorSum m 0 = 1 := by
  have hh := sum_Ioc_mul_zeta_eq_sum (R := ℝ) (μ : ArithmeticFunction ℝ) m
  rw [coe_moebius_mul_coe_zeta] at hh
  simpa [floorSum,w,ArithmeticFunction.one_apply,show 1 ≤ m by omega] using hh.symm

private theorem floor_lim (m : ℕ) (hm : 0 < m) : Tendsto (floorSum m) (𝓝[>] 0) (𝓝 1) := by
  rw [←floor_zero m hm]
  apply Tendsto.mono_left _ nhdsWithin_le_nhds
  apply tendsto_finsetSum
  intro d hd
  have ha : (d:ℝ)≠0 := by exact_mod_cast (mem_Ioc.mp hd).1.ne'
  exact ((continuousAt_const.div (Real.continuous_const_rpow ha).continuousAt (by simp)).mul continuousAt_const)

private theorem residue_formula {m N : ℕ} (hm : m≤N) (ε : ℝ) :
    residue N m ε = 1+(m:ℝ)*moment N ε-floorSum m ε := by
  have sub : Ioc 0 m ⊆ Ioc 0 N := Ioc_subset_Ioc_right hm
  have hfloor : floorSum m ε = ∑ k ∈ Ioc 0 N, w ε k*(m/k : ℕ) := by
    apply sum_subset sub
    intro k hk hkm
    have hlt : m<k := by have := mem_Ioc.mp hk; contrapose! hkm;exact mem_Ioc.mpr ⟨this.1,hkm⟩
    simp [Nat.div_eq_of_lt hlt]
  rw [hfloor]
  simp only [residue,moment,mul_sum]
  rw [add_sub_assoc,←sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast (mem_Ioc.mp hk).1.ne'
  have hh : (m%k:ℕ) + (k:ℝ)*(m/k:ℕ) = m := by exact_mod_cast Nat.mod_add_div m k
  field_simp
  linear_combination w ε k * hh

private theorem coordinate (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ᶠ N : ℕ in atTop, |residue N m ε| < δ := by
  have hlim : Tendsto (fun ε => 1+(m:ℝ)*zinv ε-floorSum m ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).add (zinv_limit.const_mul (m:ℝ))).sub (floor_lim m hm)
  have hsmall := hlim.eventually (Metric.ball_mem_nhds (0:ℝ) hδ)
  filter_upwards [hsmall,self_mem_nhdsWithin (s := Set.Ioi (0:ℝ))] with ε hε hpos
  have hn : Tendsto (fun N => residue N m ε) atTop (𝓝 (1+(m:ℝ)*zinv ε - floorSum m ε)) := by
    apply Tendsto.congr' (f₁ := fun N => 1+(m:ℝ)*moment N ε-floorSum m ε) ?_
      ((tendsto_const_nhds.add ((moments ε hpos).const_mul _)).sub tendsto_const_nhds)
    filter_upwards [eventually_ge_atTop m] with N hN using (residue_formula hN ε).symm
  simpa [Real.dist_eq] using hn.eventually (Metric.isOpen_ball.mem_nhds hε)

theorem solution (M : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᶠ N : ℕ in atTop, ∀ m ∈ Finset.Ioc 0 M,
      |1 + ∑ d ∈ Finset.Ioc 0 N, ((ArithmeticFunction.moebius d : ℝ)/(d:ℝ)^ε) * ((m%d:ℕ):ℝ)/(d:ℝ)| < δ := by
  have hh := (Finset.eventually_all (Ioc 0 M)).mpr (fun m hm => coordinate m (mem_Ioc.mp hm).1 δ hδ)
  filter_upwards [hh] with ε hε
  exact (Finset.eventually_all (Ioc 0 M)).mpr hε
