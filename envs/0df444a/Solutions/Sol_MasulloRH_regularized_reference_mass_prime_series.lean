-- Prove2me | solution 1 for MasulloRH.regularized_reference_mass_prime_series
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:49:17.094848+00:00
-- url     : https://prove2.me/submissions/c17ed8da-bf58-4846-b29f-24d884c8d50c

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib

open Set Filter Topology MeasureTheory
open MasulloRH

private theorem arch_value : regularizedArch 3 =
    ((1 - Real.log 2 / 2 - Real.pi / 4 : ℝ) : ℂ) := by
  let u (t : ℝ) := (Real.sqrt t)⁻¹
  let F (x : ℝ) := x^2 - 2*x + Real.log (1+x) - Real.log (1+x^2)/2 + Real.arctan x
  let D (t : ℝ) := - (u t)^7 / ((1+u t)*(1+(u t)^2))
  have hF (x : ℝ) (hx : 0 ≤ x) : HasDerivAt F
      (2*x^4/((1+x)*(1+x^2))) x := by
    have h1 : 0 < 1+x := by linarith
    have h2 : 0 < 1+x^2 := by positivity
    have id' := hasDerivAt_id x
    have hlog1 := (Real.hasDerivAt_log h1.ne').comp x (id'.const_add 1)
    have hlog2 := (Real.hasDerivAt_log h2.ne').comp x ((id'.pow 2).const_add 1)
    have d := (((((id'.pow 2).sub (id'.const_mul 2)).add hlog1).sub
      (hlog2.div_const 2)).add (Real.hasDerivAt_arctan x))
    convert d using 1 <;> try rfl
    all_goals dsimp [F] <;> field_simp <;> ring
  have hu (t : ℝ) (ht : 0 < t) : HasDerivAt u (-(u t)^3/2) t := by
    have hrt := Real.sqrt_pos.mpr ht
    convert (Real.hasDerivAt_sqrt ht.ne').inv hrt.ne' using 1 <;> try rfl
    all_goals dsimp [u] <;> field_simp <;> ring
  have hd (t : ℝ) (ht : t ∈ Ici (1:ℝ)) : HasDerivAt (F ∘ u) (D t) t := by
    have hp : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have hut : 0 ≤ u t := inv_nonneg.mpr (Real.sqrt_nonneg _)
    convert (hF _ hut).comp t (hu _ hp) using 1 <;> try rfl
    all_goals dsimp [D] <;> ring
  have hsign (t : ℝ) (_ : t ∈ Ioi (1:ℝ)) : D t ≤ 0 := by
    have h0 : 0 ≤ u t := inv_nonneg.mpr (Real.sqrt_nonneg _)
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (pow_nonneg h0 7)) (by positivity)
  have htu : Tendsto u atTop (𝓝 0) := tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have htF : Tendsto (F ∘ u) atTop (𝓝 (F 0)) := ((hF 0 le_rfl).continuousAt.tendsto).comp htu
  have hI := integral_Ioi_of_hasDerivAt_of_nonpos' hd hsign htF
  have hval : ∫ t in Ioi (1:ℝ), D t = 1-Real.log 2/2-Real.pi/4 := by
    rw [hI]
    norm_num [F,u,Function.comp_apply,Real.arctan_one]
    ring
  have he (t : ℝ) (ht : 1 < t) :
      (((t:ℂ) ^ (1/2-(3:ℂ)) - (t:ℂ) ^ (-2:ℂ)) *
      ((Real.sqrt t / (t^2-1):ℝ):ℂ)) = (D t : ℂ) := by
    have ht0 := zero_lt_one.trans ht
    let r := Real.sqrt t
    have hr : 1 < r := by simpa [r] using (Real.sqrt_lt_sqrt (show 0 ≤ (1:ℝ) by norm_num) ht)
    have hr0 : r ≠ 0 := (zero_lt_one.trans hr).ne'
    have hrs : r^2 = t := Real.sq_sqrt ht0.le
    have htp (n : ℕ) : (t:ℂ)^(((-(n:ℝ)/2:ℝ)):ℂ) = (((r^n)⁻¹ : ℝ):ℂ) := by
      rw [←Complex.ofReal_cpow ht0.le]
      apply congrArg Complex.ofReal
      rw [show -(n:ℝ)/2 = -((1/2:ℝ)*(n:ℝ)) by ring,Real.rpow_neg ht0.le,
        Real.rpow_mul ht0.le,←Real.sqrt_eq_rpow,Real.rpow_natCast]
    have hfive : (t:ℂ)^(1/2-(3:ℂ)) = (((r^5)⁻¹:ℝ):ℂ) := by convert htp 5 using 2 <;> norm_num
    have hfour : (t:ℂ)^(-2:ℂ) = (((r^4)⁻¹:ℝ):ℂ) := by convert htp 4 using 2 <;> norm_num
    rw [hfive,hfour]
    norm_cast
    change ((r^5)⁻¹-(r^4)⁻¹)*(r/(t^2-1)) = -(r⁻¹)^7/((1+r⁻¹)*(1+(r⁻¹)^2))
    have hr4 : (r^2)^2-1 ≠ 0 := by rw [hrs]; nlinarith [mul_self_lt_mul_self (by norm_num : (0:ℝ) ≤ 1) ht]
    have hpoly : -1+r^4 ≠ 0 := by
      intro h
      apply hr4
      calc (r^2)^2-1 = -1+r^4 := by ring
           _ = _ := h
    rw [←hrs]
    field_simp [hr0,hr4]
    ring_nf
    field_simp [hpoly]
    ring
  unfold regularizedArch
  calc _ = ∫ t in Ioi (1:ℝ), ((D t:ℝ):ℂ) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht using he t ht
       _ = _ := by rw [integral_complex_ofReal,hval]

private theorem regularized_reference_mass_at_three :
    (zetaLogDeriv 3).re - (zetaLogDeriv (5/2) + regularizedArch 3 - regularizedPolar 3).re =
    (zetaLogDeriv 3).re - (zetaLogDeriv (5/2)).re + Real.log 2 / 2 + Real.pi / 4 - 37 / 30 := by
  rw [arch_value]
  have hP : regularizedPolar 3 = (-7/30:ℂ) := by norm_num [regularizedPolar]
  rw [hP,Complex.sub_re,Complex.add_re,Complex.ofReal_re]
  norm_num [Complex.div_re,Complex.normSq_apply]
  ring

private theorem mangoldt_series_hasSum {x : ℝ} (hx : 1 < x) :
    HasSum (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n:ℝ)^x)
      (-(zetaLogDeriv (x:ℂ)).re) := by
  have hs : 1 < (x:ℂ).re := hx
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).hasSum
  have hv := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  change LSeries _ (x:ℂ) = _ at hv
  change HasSum _ (LSeries _ (x:ℂ)) at h
  rw [hv,neg_div] at h
  have hR := Complex.hasSum_re h
  convert hR using 1
  · ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · change _ = (LSeries.term (fun k : ℕ => (ArithmeticFunction.vonMangoldt k:ℂ)) (x:ℂ) n).re
      rw [LSeries.term_of_ne_zero hn]
      simp only [← Complex.ofReal_natCast n, ← Complex.ofReal_cpow n.cast_nonneg,
        ← Complex.ofReal_div, Complex.ofReal_re]
  · simp [zetaLogDeriv]

theorem solution :
    HasSum (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n:ℝ)^(5/2:ℝ) -
      ArithmeticFunction.vonMangoldt n / (n:ℝ)^(3:ℝ))
      ((zetaLogDeriv 3).re - (zetaLogDeriv (5/2) + regularizedArch 3 - regularizedPolar 3).re -
        Real.log 2 / 2 - Real.pi / 4 + 37 / 30) := by
  have hp := (mangoldt_series_hasSum (x:=5/2) (by norm_num)).sub
    (mangoldt_series_hasSum (x:=3) (by norm_num))
  rw [regularized_reference_mass_at_three]
  push_cast at hp
  rw [show (zetaLogDeriv 3).re - (zetaLogDeriv (5/2)).re + Real.log 2 / 2 +
      Real.pi / 4 - 37 / 30 - Real.log 2 / 2 - Real.pi / 4 + 37 / 30 =
      -(zetaLogDeriv (5/2)).re - -(zetaLogDeriv 3).re by ring]
  exact hp

