-- Prove2me | solution 1 for MasulloRH.corrected_prime_shell_mellin_limits
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T01:31:31.553484+00:00
-- url     : https://prove2.me/submissions/4e4a9bb4-06f6-44d2-bd5c-d39d6c0c212f

import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
section

open Filter Finset
open scoped Topology

/-- Omitting finitely many primes does not prevent the partial Euler product from
vanishing in the strip with real exponent between zero and one, including one. -/
theorem MasulloRH.tendsto_sieved_euler_product_zero (S : Finset ℕ) {a : ℝ}
    (ha : 0 < a) (ha₁ : a ≤ 1) :
    Tendsto (fun B : ℕ ↦ ∏ l ∈ (range (B+1)).filter (fun l ↦ l.Prime ∧ l ∉ S),
      (1 - (l : ℝ)^(-a))) atTop (𝓝 0) := by
  let f (n : ℕ) : ℝ := if n.Prime ∧ n ∉ S then (n : ℝ)^(-a) else 0
  have hf (n : ℕ) : 0 ≤ f n := by dsimp [f]; split_ifs <;> positivity
  have hf₁ (n : ℕ) : f n ≤ 1 := by
    dsimp [f]
    split_ifs with h
    · exact (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast h.1.one_lt) (neg_neg_of_pos ha)).le
    · norm_num
  have hns : ¬ Summable f := by
    intro h
    have hsum : Summable (fun n : ℕ ↦ if n.Prime then (n : ℝ)^(-a) else 0) :=
      h.congr_cofinite (by
        filter_upwards [S.finite_toSet.compl_mem_cofinite] with n hn
        have hn' : n ∉ S := hn
        simp only [f, hn', not_false_eq_true, and_true])
    have hbad := Nat.Primes.summable_rpow.mp <|
      (Nat.Primes.summable_iff_summable_ite (fun n : ℕ ↦ (n : ℝ)^(-a))).mpr hsum
    linarith
  have htop := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf).mp hns
  have htop' : Tendsto (fun B : ℕ ↦ ∑ i ∈ range (B+1), f i) atTop atTop :=
    htop.comp (tendsto_add_atTop_nat 1)
  have hzero := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp htop')
  have hprod (B : ℕ) : (∏ l ∈ (range (B+1)).filter (fun l ↦ l.Prime ∧ l ∉ S),
        (1 - (l : ℝ)^(-a))) = ∏ l ∈ range (B+1), (1-f l) := by
    rw [prod_filter]
    apply prod_congr rfl
    intro l hl
    by_cases h : l.Prime ∧ l ∉ S <;> simp [f, h]
  simp_rw [hprod]
  apply squeeze_zero (fun _ ↦ prod_nonneg (fun n _ ↦ sub_nonneg.mpr (hf₁ n))) _
    (show Tendsto (fun B : ℕ ↦ Real.exp (-(∑ i ∈ range (B+1), f i))) atTop (𝓝 0) from hzero)
  intro B
  rw [← sum_neg_distrib, Real.exp_sum]
  apply prod_le_prod (fun n _ ↦ sub_nonneg.mpr (hf₁ n))
  intro n hn
  linarith [Real.add_one_le_exp (-f n)]

end

section

open Complex MeasureTheory Set ENNReal
open scoped ENNReal

private lemma weighted_dilation_norm (ψ : ℝ → ℂ) (a b : ℝ) (hb : 0 < b) :
    (∫ t : ℝ in Ioi 0, ‖(t:ℂ)^((a:ℂ)-1) * ψ (b*t)‖) =
      b^(-a) * ∫ t : ℝ in Ioi 0, ‖(t:ℂ)^((a:ℂ)-1) * ψ t‖ := by
  let g (t : ℝ) := ‖(t:ℂ)^((a:ℂ)-1) * ψ t‖
  calc
    _ = ∫ t : ℝ in Ioi 0, b^(1-a) * g (b*t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      dsimp only [g]
      simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
        Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hb ht0), sub_re, ofReal_re, one_re,
        Real.mul_rpow hb.le ht0.le]
      have he : b^(1-a)*b^(a-1)=1 := by
        rw [← Real.rpow_add hb]; ring_nf; exact Real.rpow_zero b
      calc _ = (b^(1-a)*b^(a-1))*(t^(a-1)*‖ψ (b*t)‖) := by rw [he,one_mul]
           _ = _ := by ring
    _ = b^(1-a) * (b⁻¹ * ∫ t : ℝ in Ioi 0, g t) := by
      rw [integral_const_mul,integral_comp_mul_left_Ioi g 0 hb,mul_zero,smul_eq_mul]
    _ = _ := by
      rw [← mul_assoc, ← Real.rpow_neg_one b, ← Real.rpow_add hb]
      congr 2; ring

private lemma complex_tsum_integrable_of_summable_norm_integrals {F : ℕ → ℝ → ℂ}
    {ν : Measure ℝ} (hF : ∀ j, Integrable (F j) ν) (h : Summable (fun j => ∫ t, ‖F j t‖ ∂ν)) :
    Integrable (fun t => ∑' j, F j t) ν := by
  refine ⟨AEStronglyMeasurable.tsum (fun j => (hF j).aestronglyMeasurable),?_⟩
  have hlam (j : ℕ) : ∫⁻ t, ‖F j t‖ₑ ∂ν = ‖∫ t, ‖F j t‖ ∂ν‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF j).norm, coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg (F j t)))]
    simp only [coe_nnnorm]
  have hfin : (∑' j, ∫⁻ t, ‖F j t‖ₑ ∂ν) ≠ ⊤ := by
    rw [funext hlam]; exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 h.abs)
  change (∫⁻ t, ‖∑' j, F j t‖ₑ ∂ν) < ⊤
  calc _ ≤ ∫⁻ t, ∑' j, ‖F j t‖ₑ ∂ν := lintegral_mono fun _ => enorm_tsum_le_tsum_enorm
       _ = ∑' j, ∫⁻ t, ‖F j t‖ₑ ∂ν := lintegral_tsum fun j => (hF j).aestronglyMeasurable.enorm
       _ < ⊤ := hfin.lt_top

theorem MasulloAudit.mellin_prime_power_dilation_sum (p a : ℝ) (hp : 1<p) (ha : 0<a)
    (ψ : ℝ → ℂ) (hψ : MellinConvergent ψ (a:ℂ)) :
    HasMellin (fun t : ℝ => ∑' j : ℕ, ψ (p^(j+1)*t)) (a:ℂ)
      (mellin ψ (a:ℂ)/((p^a-1:ℝ):ℂ)) := by
  let D (j : ℕ) : ℝ := p^(j+1)
  have hp0 : 0<p := lt_trans zero_lt_one hp
  have hD (j : ℕ) : 0<D j := pow_pos hp0 _
  let q := (p^a)⁻¹
  have hpa := Real.one_lt_rpow hp ha
  have hpapos := Real.rpow_pos_of_pos hp0 a
  have hq0 : 0<q := inv_pos.mpr hpapos
  have hq : ‖q‖ < 1 := by rw [Real.norm_eq_abs,abs_of_pos hq0]; exact inv_lt_one_of_one_lt₀ hpa
  have hgeom := hasSum_geometric_of_norm_lt_one hq
  have hpow (j : ℕ) : (D j)^(-a) = q^(j+1) := by
    dsimp only [D,q]
    rw [← Real.rpow_natCast_mul hp0.le,mul_comm,Real.rpow_mul_natCast hp0.le,Real.rpow_neg hp0.le]
  let F (j : ℕ) (t : ℝ) := (t:ℂ)^((a:ℂ)-1) * ψ (D j*t)
  let ν := volume.restrict (Ioi (0:ℝ))
  have hF (j : ℕ) : Integrable (F j) ν := (MellinConvergent.comp_mul_left (hD j)).mpr hψ
  have hs : Summable (fun j => ∫ t, ‖F j t‖ ∂ν) := by
    let L := ∫ t : ℝ in Ioi 0, ‖(t:ℂ)^((a:ℂ)-1) * ψ t‖
    have hi (j : ℕ) : (∫ t, ‖F j t‖ ∂ν) = q^(j+1)*L :=
      (weighted_dilation_norm ψ a (D j) (hD j)).trans (by rw [hpow])
    simp_rw [hi]
    exact ((summable_nat_add_iff 1).mpr hgeom.summable).mul_right L
  have hpoint (t : ℝ) : (t:ℂ)^((a:ℂ)-1) * (∑' j : ℕ, ψ (D j*t)) = ∑' j : ℕ, F j t :=
    tsum_mul_left.symm
  constructor
  · change Integrable (fun t : ℝ => (t:ℂ)^((a:ℂ)-1) * (∑' j : ℕ, ψ (D j*t))) ν
    simp_rw [hpoint]; exact complex_tsum_integrable_of_summable_norm_integrals hF hs
  · change (∫ t : ℝ, ((t:ℂ)^((a:ℂ)-1)) * (∑' j : ℕ, ψ (D j*t)) ∂ν) = _
    simp_rw [hpoint]
    rw [← integral_tsum_of_summable_integral_norm hF hs]
    have hline (j : ℕ) : (∫ t, F j t ∂ν) = (q^(j+1):ℝ)*mellin ψ (a:ℂ) := by
      have hr : ((D j:ℝ):ℂ)^(-(a:ℂ)) = ((q^(j+1):ℝ):ℂ) := by
        rw [←Complex.ofReal_neg,←Complex.ofReal_cpow (hD j).le,hpow]
      simpa only [mellin,smul_eq_mul,hr] using mellin_comp_mul_left ψ (a:ℂ) (hD j)
    simp_rw [hline]
    rw [tsum_mul_right,←Complex.ofReal_tsum]
    have hseries : (∑' j : ℕ, q^(j+1)) = 1 / (p^a-1) := by
      simp_rw [pow_succ]
      rw [tsum_mul_right,hgeom.tsum_eq]
      dsimp [q]
      field_simp
    rw [hseries]
    push_cast; ring
end

section

open Finset MeasureTheory Filter Set
open scoped Topology

private theorem weighted_mellin_sum {ι : Type*} (S : Finset ι) (G : ι → ℝ → ℂ) (z : ℂ)
    (H : ∀ i ∈ S, MellinConvergent (G i) z) :
    HasMellin (fun t => ∑ i ∈ S, G i t) z (∑ i ∈ S, mellin (G i) z) := by
  constructor
  · simpa only [MellinConvergent, Finset.smul_sum] using!
      (integrable_finsetSum S H)
  · simp only [mellin, Finset.smul_sum]
    exact integral_finsetSum S H

private theorem finite_sieve_transform (T : Finset ℕ) (hT : ∀ l ∈ T, 0 < l)
    (p a : ℝ) (hp : 0 < p) (F : ℝ → ℂ) (hF : MellinConvergent F (a : ℂ)) :
    HasMellin
      (fun t : ℝ => ∑ U ∈ T.powerset, (-1:ℂ)^U.card * F ((p * ∏ l ∈ U, (l:ℝ))*t))
      (a : ℂ) (((∏ l ∈ T, (1-(l:ℝ)^(-a)) : ℝ) : ℂ) *
        (((p^(-a):ℝ):ℂ) * mellin F (a:ℂ))) := by
  let scale (U : Finset ℕ) := p*∏ l ∈ U,(l:ℝ)
  let G (U : Finset ℕ) (t : ℝ) := (-1:ℂ)^U.card * F (scale U*t)
  have hs (U : Finset ℕ) (hU : U ∈ T.powerset) : 0 < scale U :=
    mul_pos hp (prod_pos fun l hl => by exact_mod_cast hT l (mem_powerset.mp hU hl))
  have hG (U : Finset ℕ) (hU : U ∈ T.powerset) : MellinConvergent (G U) (a : ℂ) :=
    ((MellinConvergent.comp_mul_left (hs U hU)).mpr hF).const_smul ((-1:ℂ)^U.card)
  have hval (U : Finset ℕ) (hU : U ∈ T.powerset) : mellin (G U) (a:ℂ) =
      ((∏ l ∈ U,-(l:ℝ)^(-a):ℝ):ℂ) * (((p^(-a):ℝ):ℂ) * mellin F (a:ℂ)) := by
    change mellin (fun t => ((-1:ℂ)^U.card) • F (scale U*t)) _ = _
    rw [mellin_const_smul, mellin_comp_mul_left F (a:ℂ) (hs U hU)]
    simp only [smul_eq_mul, ←Complex.ofReal_neg, ←Complex.ofReal_cpow (hs U hU).le]
    have hreal : (-1:ℝ)^U.card*(scale U)^(-a) =
        (∏ l ∈ U,-(l:ℝ)^(-a))*p^(-a) := by
      dsimp only [scale]
      rw [prod_neg, Real.finsetProd_rpow U (fun l : ℕ => (l:ℝ)) (fun _ _ => Nat.cast_nonneg _),
        Real.mul_rpow hp.le (prod_nonneg fun l _ => Nat.cast_nonneg l)]
      ring
    calc
      _ = ((((-1:ℝ)^U.card * scale U^(-a) : ℝ):ℂ) * mellin F a) := by push_cast; ring
      _ = _ := by rw [hreal]; push_cast; ring
  have h := weighted_mellin_sum T.powerset G (a:ℂ) hG
  refine ⟨h.1,h.2.trans ?_⟩
  rw [sum_congr rfl hval, ←sum_mul, ←Complex.ofReal_sum, ←prod_one_add]
  simp [sub_eq_add_neg]
end

section
open Finset Filter MeasureTheory
open scoped Topology

theorem solution (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1)
    (ψ : ℝ → ℂ) (hψ : MellinConvergent ψ (a:ℂ))
    (hF : (∀ t : ℝ, 0 < t → Summable (fun n : ℕ => ψ (((n:ℝ)+1)*t))) ∧
      MellinConvergent (fun t : ℝ => ∑' n : ℕ, ψ (((n:ℝ)+1)*t)) (a:ℂ)) :
    let F (t : ℝ) := ∑' n : ℕ, ψ (((n:ℝ)+1)*t)
    let Q (B : ℕ) := (range (B+1)).filter (fun l : ℕ => l.Prime ∧ l ≠ p)
    let G (B : ℕ) (t : ℝ) := ∑ U ∈ (Q B).powerset,
      (-1:ℂ)^U.card * F (((p:ℝ)*∏ l ∈ U, (l:ℝ))*t)
    let shell (t : ℝ) := ∑' j : ℕ, ψ ((p:ℝ)^(j+1)*t)
    (∀ B : ℕ, HasMellin (G B) (a:ℂ)
      (((∏ l ∈ Q B, (1-(l:ℝ)^(-a)) : ℝ):ℂ) * ((((p:ℝ)^(-a):ℝ):ℂ) * mellin F (a:ℂ)))) ∧
    Tendsto (fun B : ℕ => mellin (G B) (a:ℂ)) atTop (𝓝 0) ∧
    HasMellin shell (a:ℂ) (mellin ψ (a:ℂ) / ((((p:ℝ)^a-1):ℝ):ℂ)) ∧
    (mellin ψ (a:ℂ) ≠ 0 → ¬Tendsto (fun B : ℕ => mellin (G B) (a:ℂ)) atTop
      (𝓝 (mellin shell (a:ℂ)))) := by
  intro F Q G shell
  have hp1 : 1 < (p:ℝ) := by exact_mod_cast hp.one_lt
  have finite (B : ℕ) := finite_sieve_transform (Q B) (fun l hl => (mem_filter.mp hl).2.1.pos)
    (p:ℝ) a (by positivity) F hF.2
  have hprod : Tendsto (fun B : ℕ => ∏ l ∈ Q B, (1-(l:ℝ)^(-a))) atTop (𝓝 0) := by
    simpa only [Q, mem_singleton] using MasulloRH.tendsto_sieved_euler_product_zero {p} ha ha₁
  have hlim : Tendsto (fun B : ℕ => mellin (G B) (a:ℂ)) atTop (𝓝 0) := by
    have h1 := (Complex.continuous_ofReal.continuousAt.tendsto.comp hprod).mul_const
      ((((p:ℝ)^(-a):ℝ):ℂ) * mellin F (a:ℂ))
    simp only [Complex.ofReal_zero, zero_mul, Function.comp_def] at h1
    exact h1.congr (fun B => (finite B).2.symm)
  have hpow := MasulloAudit.mellin_prime_power_dilation_sum (p:ℝ) a hp1 ha ψ hψ
  refine ⟨finite,hlim,hpow,?_⟩
  intro hn hbad
  have hden : 0 < (p:ℝ)^a-1 := sub_pos.mpr (Real.one_lt_rpow hp1 ha)
  have hdenC : ((((p:ℝ)^a-1):ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hden.ne'
  exact (div_ne_zero hn hdenC) (hpow.2.symm.trans (tendsto_nhds_unique hbad hlim))
end
