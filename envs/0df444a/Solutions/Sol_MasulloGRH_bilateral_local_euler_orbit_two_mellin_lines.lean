-- Prove2me | solution 1 for MasulloGRH.bilateral_local_euler_orbit_two_mellin_lines
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:46:01.218085+00:00
-- url     : https://prove2.me/submissions/bc7e1527-1c6f-489b-8cc0-d343e5d44ae0

import Definitions.Def_MasulloGRH_MellinRpos
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Set MeasureTheory

namespace MasulloGRH

theorem c11_reciprocal_dyadic_bump : ∃ ψ : ℝ → ℂ, HasExpDecay ψ ∧
    (∀ k : ℤ, ψ ((2:ℝ)^k) = if k = -1 then 1 else 0) ∧
    MellinConvergent ψ 1 ∧ (∀ x : ℝ, 0 < x → ContinuousAt ψ x) ∧
    IsSchwartzRpos (powMul 1 ψ) := by
  let L := Real.log 2
  have hL : 0 < L := Real.log_pos (by norm_num)
  let b : ContDiffBump (-L) := ⟨L/4, L/2, by positivity, by linarith⟩
  let g (u : ℝ) : ℂ := (b u : ℂ)
  let ψ (t : ℝ) : ℂ := g (Real.log t)
  have hgc : ContDiff ℝ (⊤ : ℕ∞) g := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hgs : HasCompactSupport g := b.hasCompactSupport.comp_left (show (↑(0 : ℝ) : ℂ) = 0 by simp)
  have he (u : ℝ) : ψ (Real.exp u) = g u := by simp [ψ]
  have hψc (x : ℝ) (hx : 0 < x) : ContinuousAt ψ x :=
    hgc.continuous.continuousAt.comp (Real.continuousAt_log hx.ne')
  refine ⟨ψ, ⟨⟨hgs.toSchwartzMap hgc, fun x => (he x).symm⟩, ?_⟩, ?_, ?_, hψc, ?_⟩
  · intro N k
    simp_rw [he]
    have hk : HasCompactSupport (iteratedDeriv k g) := by
      induction k with
      | zero => simpa using hgs
      | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
    let H (x : ℝ) := Real.exp (N * |x|) * ‖iteratedDeriv k g x‖
    have hH : Continuous H := (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
      ((hgc.continuous_iteratedDeriv k (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)) ).norm)
    have hHC : HasCompactSupport H := hk.norm.mul_left (f := fun x : ℝ => Real.exp (N * |x|))
    obtain ⟨B,hB⟩ := hHC.exists_bound_of_continuousOn hH.continuousOn
    refine ⟨max 0 B, fun x => ?_⟩
    by_cases hx : x ∈ tsupport H
    · exact (le_abs_self (H x)).trans ((hB x hx).trans (le_max_right _ _))
    · change H x ≤ _
      rw [image_eq_zero_of_notMem_tsupport hx]
      exact le_max_left _ _
  · intro k
    change (b (Real.log ((2 : ℝ)^k)) : ℂ) = _
    rw [Real.log_zpow]
    change (b ((k : ℝ)*L) : ℂ) = _
    by_cases heq : k = -1
    · subst k
      simpa using congrArg (fun r : ℝ => (r : ℂ)) (b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le))
    · rw [if_neg heq, b.zero_of_le_dist]
      · simp
      · rw [Real.dist_eq, show (k:ℝ)*L - -L = ((k:ℝ)+1)*L by ring, abs_mul, abs_of_pos hL]
        have hp : (1:ℝ) ≤ |(k:ℝ)+1| := by
          exact_mod_cast (Int.one_le_abs (show k+1 ≠ 0 by omega))
        change L/2 ≤ _
        nlinarith
  · have hz (t : ℝ) (ht : 1 ≤ t) : ψ t = 0 := by
      change (b (Real.log t) : ℂ) = 0
      rw [b.zero_of_le_dist]; simp
      rw [Real.dist_eq]
      change L/2 ≤ _
      linarith [Real.log_nonneg ht, le_abs_self (Real.log t - -L)]
    have hb (t : ℝ) : ‖ψ t‖ ≤ 1 := by
      change ‖(b (Real.log t) : ℂ)‖ ≤ _
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg] using (b.le_one (x := Real.log t))
    have hint : IntegrableOn ψ (Ioi 0) := by
      apply Integrable.mono' (g := (Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)))
      · exact (integrableOn_const (C := (1:ℝ)) (s := Ioc 0 1) (μ := volume) (by simp)).integrable_indicator measurableSet_Ioc |>.integrableOn
      · exact (hgc.continuous.measurable.comp Real.measurable_log).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
        by_cases h1 : t ≤ 1
        · simpa [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨ht,h1⟩)] using hb t
        · simp [hz t (le_of_not_ge h1), Set.indicator_of_notMem (show t ∉ Ioc (0:ℝ) 1 from fun e => h1 e.2)]
    simpa [MellinConvergent] using hint
  · let G (x : ℝ) : ℂ := (Real.exp x : ℂ) * g x
    have hc : ContDiff ℝ (⊤ : ℕ∞) G := (Complex.ofRealCLM.contDiff.comp Real.contDiff_exp).mul hgc
    have hs : HasCompactSupport G := hgs.mul_left (f := fun x : ℝ => (Real.exp x : ℂ))
    exact ⟨hs.toSchwartzMap hc, fun x => by change G x = _; simp [G,powMul,he]⟩
end MasulloGRH
namespace MasulloGRH

open Complex FourierTransform

private theorem nf_mellin_slice (ϕ : ℝ → ℂ) (σ : ℝ)
    (hσ : IsSchwartzRpos (powMul σ ϕ)) :
    ∃ g : SchwartzMap ℝ ℂ, ∀ y : ℝ, g y = mellin ϕ (σ + y * Complex.I) := by
  obtain ⟨ψ,hψ⟩ := hσ
  let negEquiv : ℝ ≃L[ℝ] ℝ := (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv
  let reflected : SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ negEquiv ψ
  let dilation := ContinuousLinearEquiv.unitsEquivAut ℝ
    (Units.mk0 (2 * Real.pi)⁻¹ (by positivity))
  let F : SchwartzMap ℝ ℂ := 𝓕 reflected
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ dilation F, ?_⟩
  intro y
  have hfun : (reflected : ℝ → ℂ) =
      (fun u : ℝ => Real.exp (-σ * u) • ϕ (Real.exp (-u))) := by
    funext u
    change ψ (-u) = _
    rw [hψ, powMul, Complex.real_smul, ← Real.exp_mul]
    rw [show -u * σ = -σ * u by ring]
  change F (y * (2 * Real.pi)⁻¹) = _
  rw [mellin_eq_fourier]
  change (𝓕 (reflected : ℝ → ℂ)) (y * (2 * Real.pi)⁻¹) = _
  rw [hfun]
  simp [div_eq_mul_inv]
end MasulloGRH

open Real Complex MeasureTheory Set Filter

private theorem nf_euler_tail (q a : ℝ) (hq0 : 0 < q) (hr : q ^ (-a) < 1)
    (u : ℂ) (hu : ‖u‖ = 1) (k : ℕ)
    (f : ℝ → ℂ) (hconv : MellinConvergent f a)
    (hM : VerticalIntegrable (mellin f) a)
    (hf : ∀ n : ℕ, ContinuousAt f (q^(n+k))) :
    HasSum (fun n : ℕ => u^(n+k)*f (q^(n+k)))
      ((1 / (2 * Real.pi) : ℝ) • ∫ y : ℝ,
        ((u*(q:ℂ)^(-((a:ℂ)+(y:ℂ)*I)))^k*mellin f ((a:ℂ)+(y:ℂ)*I))/(1-u*(q:ℂ)^(-((a:ℂ)+(y:ℂ)*I)))) := by
  let s (y : ℝ) : ℂ := a + y*I
  let r := q ^ (-a)
  let R (y : ℝ) := u*(q:ℂ)^(-s y)
  let M (y : ℝ) := mellin f (s y)
  let T (n : ℕ) (y : ℝ) := (R y)^(n+k) * M y
  have hqc : (q:ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hR (y : ℝ) : ‖R y‖ = r := by simp [R, r, s, hu, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  have hr0 : 0 < r := Real.rpow_pos_of_pos hq0 _
  have hRcont : Continuous R := by
    let : NeZero (q:ℂ) := ⟨hqc⟩
    apply continuous_const.mul
    apply (continuous_const_cpow (q:ℂ)).comp
    dsimp [s]
    fun_prop
  have hMint : Integrable M := hM
  have hTnorm n y : ‖T n y‖ = r^(n+k)*‖M y‖ := by simp only [T,norm_mul,norm_pow,hR]
  have hT (n : ℕ) : Integrable (T n) := by
    apply (hMint.norm.const_mul (r^(n+k))).mono' (((hRcont.pow _).aestronglyMeasurable).mul hMint.aestronglyMeasurable)
    exact .of_forall fun y => (hTnorm n y).le
  have hS : Summable (fun n : ℕ => ∫ y : ℝ, ‖T n y‖) := by
    simp_rw [hTnorm, integral_const_mul]
    apply Summable.mul_right
    simpa only [pow_add] using (summable_geometric_of_lt_one hr0.le hr).mul_right (r^k)
  have hSum (y : ℝ) : ∑' n : ℕ, T n y = (R y)^k*M y/(1-R y) := by
    have hgeom := hasSum_geometric_of_norm_lt_one ((hR y).trans_lt hr)
    have h := (hgeom.mul_right ((R y)^k)).mul_right (M y)
    simp only [← pow_add] at h
    rw [show (∑' n : ℕ, T n y) = (1-R y)⁻¹*(R y)^k*M y from h.tsum_eq]
    ring
  have hInt := (hasSum_integral_of_summable_integral_norm hT hS).const_smul (1/(2*Real.pi) : ℝ)
  simp_rw [hSum] at hInt
  apply hInt.congr_fun
  intro n
  rw [← mellinInv_mellin_eq a f (x := q^(n+k)) (pow_pos hq0 _) hconv hM (hf n)]
  dsimp [mellinInv]
  rw [mul_left_comm (u^(n+k)),
    ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  simp only [T, R, M, s, Complex.ofReal_pow, mul_pow, mul_assoc]
  congr 2
  rw [Complex.cpow_def_of_ne_zero (pow_ne_zero _ hqc), ← Complex.ofReal_pow,
    ← Complex.ofReal_log (pow_pos hq0 _).le,Real.log_pow,Complex.cpow_def_of_ne_zero hqc,
    ← Complex.ofReal_log hq0.le, ← Complex.exp_nat_mul]
  push_cast
  ring_nf
open MeasureTheory Set Filter Complex

private noncomputable def nf_eulerIntegral (q : ℝ) (u : ℂ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℝ) • ∫ y : ℝ, mellin f (a+y*I)/(1-u⁻¹*(q:ℂ)^((a:ℂ)+y*I))

private theorem nf_euler_positive (q a : ℝ) (hq : 1 < q) (ha : 0 < a) (u : ℂ) (hu : ‖u‖ = 1)
    (f : ℝ → ℂ) (hconv : MellinConvergent f a) (hM : VerticalIntegrable (mellin f) a)
    (hf : ∀ x : ℝ, 0 < x → ContinuousAt f x) :
    HasSum (fun n : ℕ => u^(n+1)*f (q^(n+1))) (-nf_eulerIntegral q u f a) := by
  have hp := zero_lt_one.trans hq
  have hu0 : u ≠ 0 := by intro hz; simp [hz] at hu
  have hqc : (q:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have H := nf_euler_tail q a hp (Real.rpow_lt_one_of_one_lt_of_neg hq (neg_lt_zero.mpr ha))
    u hu 1 f hconv hM (fun n => hf _ (pow_pos hp _))
  convert H using 1
  unfold nf_eulerIntegral
  rw [← smul_neg, ←integral_neg]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  let s : ℂ := a+y*I
  have hne : (q:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl hqc)
  have habs : 1 < ‖(q:ℂ)^s‖ := by simp [Complex.norm_cpow_eq_rpow_re_of_pos hp,s,Real.one_lt_rpow hq ha]
  have hnu : (q:ℂ)^s ≠ u := by intro e; rw [e,hu] at habs; exact (lt_irrefl _ habs)
  change -(mellin f s/(1-u⁻¹*(q:ℂ)^s)) = (u*(q:ℂ)^(-s))^1*mellin f s/(1-u*(q:ℂ)^(-s))
  rw [Complex.cpow_neg,pow_one]
  field_simp
  ring

private theorem nf_euler_nonpositive (q b : ℝ) (hq : 1 < q) (hb : b < 0) (u : ℂ) (hu : ‖u‖ = 1)
    (f : ℝ → ℂ) (hconv : MellinConvergent f b) (hM : VerticalIntegrable (mellin f) b)
    (hf : ∀ x : ℝ, 0 < x → ContinuousAt f x) :
    HasSum (fun n : ℕ => (u⁻¹)^n * f ((q⁻¹)^n)) (nf_eulerIntegral q u f b) := by
  have hp := zero_lt_one.trans hq
  have hq' : q⁻¹ < 1 := (inv_lt_one₀ hp).mpr hq
  have harg : (q:ℂ).arg ≠ Real.pi := by simp [Complex.arg_ofReal_of_nonneg hp.le, Real.pi_ne_zero.symm]
  have H := nf_euler_tail q⁻¹ b (inv_pos.mpr hp)
    (Real.rpow_lt_one (inv_pos.mpr hp).le hq' (neg_pos.mpr hb))
    u⁻¹ (by simp [hu]) 0 f hconv hM (fun n => hf _ (pow_pos (inv_pos.mpr hp) _))
  have he (s : ℂ) : ((q⁻¹ : ℝ) : ℂ)^(-s) = (q:ℂ)^s := by
    rw [Complex.ofReal_inv,Complex.inv_cpow _ _ harg,Complex.cpow_neg,inv_inv]
  simpa only [nf_eulerIntegral,he,pow_zero,one_mul,add_zero] using H

private theorem nf_euler_bilateral (q a b : ℝ) (hq : 1 < q) (ha : 0 < a) (hb : b < 0)
    (u : ℂ) (hu : ‖u‖=1) (f : ℝ → ℂ)
    (hca : MellinConvergent f a) (hcb : MellinConvergent f b)
    (hva : VerticalIntegrable (mellin f) a) (hvb : VerticalIntegrable (mellin f) b)
    (hf : ∀ x : ℝ, 0 < x → ContinuousAt f x) :
    HasSum (fun k : ℤ => u^k*f (q^k)) (nf_eulerIntegral q u f b - nf_eulerIntegral q u f a) := by
  have H₁ := nf_euler_nonpositive q b hq hb u hu f hcb hvb hf
  have H₂ := nf_euler_positive q a hq ha u hu f hca hva hf
  apply (Equiv.neg ℤ).hasSum_iff.mp
  change HasSum (fun k : ℤ => u^(-k)*f (q^(-k))) _
  rw [sub_eq_add_neg]
  apply HasSum.of_nat_of_neg_add_one
  · simpa [inv_pow] using H₁
  · simpa only [neg_neg, ← Nat.cast_one (R:=ℤ), ← Nat.cast_add, zpow_natCast] using H₂
open MasulloGRH

theorem solution :
    (∀ (q a b : ℝ), 1 < q → 0 < a → b < 0 → ∀ u : ℂ, ‖u‖ = 1 → ∀ f : ℝ → ℂ,
      MellinConvergent f a → MellinConvergent f b →
      VerticalIntegrable (mellin f) a → VerticalIntegrable (mellin f) b →
      (∀ x : ℝ, 0 < x → ContinuousAt f x) →
      let J := fun d : ℝ => (1 / (2 * Real.pi) : ℝ) •
        ∫ y : ℝ, mellin f (d+y*I) / (1-u⁻¹*(q : ℂ)^((d:ℂ)+y*I))
      HasSum (fun k : ℤ => u^k * f (q^k)) (J b - J a)) ∧
    (∃ ψ : ℝ → ℂ, HasExpDecay ψ ∧
      (∀ k : ℤ, ψ ((2:ℝ)^k) = if k = -1 then 1 else 0) ∧
      (∑' k : ℤ, ψ ((2:ℝ)^k)) = 1 ∧ VerticalIntegrable (mellin ψ) 1 ∧
      ((1 / (2 * Real.pi) : ℝ) • ∫ y : ℝ, mellin ψ (1+y*I) / (1-(2 : ℂ)^(1+(y:ℂ)*I)))=0) := by
  constructor
  · intro q a b hq ha hb u hu f hca hcb hva hvb hf
    exact nf_euler_bilateral q a b hq ha hb u hu f hca hcb hva hvb hf
  obtain ⟨ψ,hexp,hvals,hconv,hcont,hsch⟩ := c11_reciprocal_dyadic_bump
  obtain ⟨g,hg⟩ := nf_mellin_slice ψ 1 hsch
  have hM : VerticalIntegrable (mellin ψ) 1 := by
    change Integrable (fun y : ℝ => mellin ψ ((1:ℝ)+y*I))
    simpa only [← funext hg] using g.integrable
  refine ⟨ψ, hexp, hvals, ?_, hM, ?_⟩
  · simp_rw [hvals]
    simp
  · have H := nf_euler_positive 2 1 (by norm_num) (by norm_num) 1 norm_one ψ hconv hM hcont
    have hz (n : ℕ) : ψ ((2:ℝ)^(n+1)) = 0 := by
      have h := hvals (n+1 : ℕ)
      have hnonneg : 0 ≤ ((n+1:ℕ):ℤ) := by positivity
      have hn : ((n+1:ℕ):ℤ) ≠ -1 := by linarith
      simpa only [zpow_natCast,if_neg hn] using h
    have H' := H.tsum_eq
    simpa [nf_eulerIntegral,hz] using H'.symm