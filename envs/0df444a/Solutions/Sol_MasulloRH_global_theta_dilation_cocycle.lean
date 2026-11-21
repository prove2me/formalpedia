-- Prove2me | solution 1 for MasulloRH.global_theta_dilation_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T03:37:35.194178+00:00
-- url     : https://prove2.me/submissions/a2a76077-6744-423b-b89a-7e95c85c1b9d

import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory Set

namespace MasulloRH

/-- Translating a half-line cutoff changes its signed integral by the translation; adding
an integrable perturbation does not change this value. -/
theorem total_cutoff_translation (r : ℝ → ℝ) (hr : Integrable r) (s : ℝ) :
    let ρ (u : ℝ) := (if u ≤ 0 then 1 else 0) + r u
    Integrable (fun u => ρ (u-s) - ρ u) ∧ (∫ u, ρ (u-s)-ρ u) = s := by
  intro ρ
  let slab (a b x : ℝ) := (if x ≤ b then (1:ℝ) else 0) - (if x ≤ a then 1 else 0)
  have hpos {a b : ℝ} (hab : a ≤ b) : Integrable (slab a b) ∧ (∫ x, slab a b x) = b-a := by
    have hsl : slab a b = (Ioc a b).indicator (fun _ => (1:ℝ)) := by
      funext x
      simp only [slab,Set.indicator_apply,mem_Ioc]
      split_ifs <;> simp_all <;> linarith
    rw [hsl]
    exact ⟨(integrableOn_const (C := (1:ℝ)) measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc,
      by rw [integral_indicator_const _ measurableSet_Ioc, Real.volume_real_Ioc, smul_eq_mul,
             mul_one, max_eq_left (sub_nonneg.mpr hab)]⟩
  have hslab : Integrable (slab 0 s) ∧ (∫ u, slab 0 s u) = s := by
    rcases le_total 0 s with h | h
    · simpa only [sub_zero] using hpos h
    · have hneg : slab 0 s = fun x => -slab s 0 x := by funext x; simp [slab]
      have H := hpos h
      rw [hneg]
      exact ⟨H.1.neg,by rw [integral_neg,H.2]; ring⟩
  have ht : Integrable (fun u => r (u-s)) := by simpa only [sub_eq_add_neg] using hr.comp_add_right (-s)
  have he (u : ℝ) : ρ (u-s)-ρ u = slab 0 s u + (r (u-s) - r u) := by
    simp only [ρ,slab,sub_nonpos]; ring
  simp_rw [he]
  refine ⟨hslab.1.add (ht.sub hr),?_⟩
  have hd : Integrable (fun u : ℝ => r (u-s) - r u) := ht.sub hr
  rw [integral_add hslab.1 hd,integral_sub ht hr,integral_sub_right_eq_self r s,hslab.2]
  ring

end MasulloRH

/-- The first log moment of the positive prime-power translates in half-density normalization. -/
theorem MasulloRH.shifted_half_density_first_moment (p s : ℝ) (hp : 1 < p) :
    HasSum (fun j : ℕ => (s - ((j:ℝ)+1)*Real.log p) *
      Real.exp ((s - ((j:ℝ)+1)*Real.log p)/2))
      (Real.exp (s/2) * (s/(Real.sqrt p-1) - Real.log p*Real.sqrt p/(Real.sqrt p-1)^2)) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hsqrt : 1 < Real.sqrt p := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt zero_le_one hp
  let q := (Real.sqrt p)⁻¹
  have hq : 0 < q := inv_pos.mpr (Real.sqrt_pos.mpr hp0)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ hsqrt
  have hbase : Real.exp (-(Real.log p / 2)) = q := by
    rw [Real.exp_neg, Real.exp_half, Real.exp_log hp0]
  have hgeom := hasSum_geometric_of_lt_one hq.le hq1
  have hfirst := hasSum_coe_mul_geometric_of_norm_lt_one (r := q)
    (by simpa only [Real.norm_eq_abs, abs_of_pos hq] using hq1)
  have H := (hgeom.mul_left ((s-Real.log p)*Real.exp (s/2)*q)).sub
    (hfirst.mul_left (Real.log p*Real.exp (s/2)*q))
  convert! H using 1
  · funext j
    rw [show (s-((j:ℝ)+1)*Real.log p)/2 = s/2 + (-(Real.log p/2)) + (j:ℝ)*(-(Real.log p/2)) by ring,
      Real.exp_add, Real.exp_add, Real.exp_nat_mul, hbase]
    ring
  · dsimp only [q]
    field_simp [(Real.sqrt_pos.mpr hp0).ne', (sub_pos.mpr hsqrt).ne']
    ring

open MeasureTheory Set

/-- Pulling an integrable real function back by the logarithm preserves its integral
when the positive real axis is equipped with multiplicative Haar measure. -/
theorem MasulloRH.log_haar_integral (f : ℝ → ℝ) (hf : Integrable f) :
    IntegrableOn (fun t : ℝ => f (Real.log t)/t) (Ioi 0) ∧
      (∫ t in Ioi (0:ℝ), f (Real.log t)/t) = ∫ u : ℝ, f u := by
  let g (t : ℝ) := f (Real.log t)/t
  have he : Real.exp '' univ = Ioi (0:ℝ) := by rw [image_univ, Real.range_exp]
  have hd (x : ℝ) (_ : x ∈ (univ : Set ℝ)) :
      HasDerivWithinAt Real.exp (Real.exp x) univ x := (Real.hasDerivAt_exp x).hasDerivWithinAt
  have h (u : ℝ) : |Real.exp u| • g (Real.exp u) = f u := by
    simp [g, abs_of_pos (Real.exp_pos _), smul_eq_mul, mul_comm (Real.exp u), div_mul_cancel₀ _ (Real.exp_ne_zero u)]
  constructor
  · rw [← he]
    apply (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd Real.exp_injective.injOn g).2
    simpa only [h, integrableOn_univ] using hf
  · rw [← he]
    simpa only [h, setIntegral_univ] using
      integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd Real.exp_injective.injOn g

open MeasureTheory Set

namespace MasulloRH

private theorem theta_cocycle_core (ρ : ℝ → ℝ) (h : ℝ → ℝ) (hi : IntegrableOn h (Ioi 0)) (s : ℝ) :
    let m (g : ℝ → ℝ) := ∫ t in Ioi (0:ℝ), g t
    let θ (g : ℝ → ℝ) (t : ℝ) := ∑' n : ℕ, g (((n:ℝ)+1)*t)
    let U (g : ℝ → ℝ) (t : ℝ) := Real.exp (-s/2) * g (Real.exp (-s)*t)
    let R (g : ℝ → ℝ) (t : ℝ) := θ g t - m g * ρ (Real.log t) / t
    IntegrableOn (U h) (Ioi 0) ∧ m (U h) = Real.exp (s/2)*m h ∧
    ∀ t : ℝ, 0<t →
      (Summable (fun n:ℕ => U h (((n:ℝ)+1)*t)) ↔
        Summable (fun n:ℕ => h (((n:ℝ)+1)*(Real.exp (-s)*t)))) ∧
      R (U h) t - U (R h) t =
        m h * (Real.exp (s/2) * (ρ (Real.log t-s)-ρ (Real.log t))/t) := by
  intro m θ U R
  have hi' : IntegrableOn (fun t => h (Real.exp (-s)*t)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff h 0 (Real.exp_pos (-s))).mpr (by simpa using hi)
  have hfactor : Real.exp (-s/2) / Real.exp (-s) = Real.exp (s/2) := by
    rw [← Real.exp_sub]; congr 1; ring
  have hm : m (U h) = Real.exp (s/2)*m h := by
    dsimp [m,U]
    rw [integral_const_mul,integral_comp_mul_left_Ioi h 0 (Real.exp_pos (-s)),mul_zero, smul_eq_mul,
      ← mul_assoc, ← div_eq_mul_inv, hfactor]
  refine ⟨hi'.const_mul _,hm,?_⟩
  intro t ht
  have hb (n : ℕ) : U h (((n:ℝ)+1)*t) = Real.exp (-s/2)*h (((n:ℝ)+1)*(Real.exp (-s)*t)) := by
    dsimp [U]; congr 2; ring
  have hth : θ (U h) t = Real.exp (-s/2) * θ h (Real.exp (-s)*t) := by
    dsimp only [θ]
    simp_rw [hb]
    exact tsum_mul_left
  constructor
  · simp_rw [hb]
    constructor
    · intro hs
      have H := hs.mul_left (Real.exp (-s/2))⁻¹
      simpa only [←mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero _),one_mul] using H
    · exact fun hs => hs.mul_left _
  · change (θ (U h) t - m (U h) * ρ (Real.log t) / t) -
      Real.exp (-s/2) * (θ h (Real.exp (-s)*t) - m h * ρ (Real.log (Real.exp (-s)*t)) / (Real.exp (-s)*t)) = _
    rw [hth,hm,Real.log_mul (Real.exp_ne_zero _) ht.ne',Real.log_exp,
      show -s+Real.log t = Real.log t-s by ring]
    have hfac : Real.exp (-s/2) = Real.exp (s/2)*Real.exp (-s) := (div_eq_iff (Real.exp_ne_zero _)).mp hfactor
    rw [hfac]
    field_simp [ht.ne',Real.exp_ne_zero]
    ring

end MasulloRH
open MeasureTheory Set

private theorem theta_global_cocycle (r : ℝ → ℝ) (hr : Integrable r) :
    let ρ (u : ℝ) := (if u≤0 then (1:ℝ) else 0) + r u
    let m (g : ℝ → ℝ) := ∫ t in Ioi (0:ℝ), g t
    let θ (g : ℝ → ℝ) (t : ℝ) := ∑' n : ℕ, g (((n:ℝ)+1)*t)
    let U (s : ℝ) (g : ℝ → ℝ) (t : ℝ) := Real.exp (-s/2) * g (Real.exp (-s)*t)
    let R (g : ℝ → ℝ) (t : ℝ) := θ g t - m g * ρ (Real.log t) / t
    let d (b t : ℝ) := Real.exp (b/2)*(ρ (Real.log t-b)-ρ (Real.log t))/t
    (∀ (h : ℝ → ℝ) (s : ℝ), IntegrableOn h (Ioi 0) →
      IntegrableOn (U s h) (Ioi 0) ∧ m (U s h) = Real.exp (s/2)*m h ∧
      (∀ t : ℝ, 0<t →
        (Summable (fun n : ℕ => U s h (((n:ℝ)+1)*t)) ↔
          Summable (fun n : ℕ => h (((n:ℝ)+1)*(Real.exp (-s)*t)))) ∧
        R (U s h) t - U s (R h) t = m h * d s t) ∧
      IntegrableOn (fun t => R (U s h) t - U s (R h) t) (Ioi 0) ∧
      m (fun t => R (U s h) t - U s (R h) t) = m h * (s*Real.exp (s/2))) ∧
    (∀ s : ℝ, IntegrableOn (d s) (Ioi 0) ∧ m (d s) = s*Real.exp (s/2)) ∧
    (∀ p s : ℝ, 1<p →
      HasSum (fun j : ℕ => m (d (s-((j:ℝ)+1)*Real.log p)))
        (Real.exp (s/2)*(s/(Real.sqrt p-1) - Real.log p*Real.sqrt p/(Real.sqrt p-1)^2))) := by
  intro ρ m θ U R d
  have hmass (s : ℝ) : IntegrableOn (d s) (Ioi 0) ∧ m (d s) = s*Real.exp (s/2) := by
    let q (u : ℝ) := ρ (u-s)-ρ u
    have hq : Integrable q ∧ (∫u : ℝ, q u) = s := MasulloRH.total_cutoff_translation r hr s
    obtain ⟨hqI,hqZ⟩ := MasulloRH.log_haar_integral q hq.1
    have he : d s = fun t : ℝ => Real.exp (s/2)*(q (Real.log t)/t) := by
      funext t; dsimp [d,q]; ring
    rw [he]
    exact ⟨hqI.const_mul _,by dsimp [m]; rw [integral_const_mul,hqZ,hq.2,mul_comm]⟩
  refine ⟨?_,hmass,?_⟩
  · intro h s hi
    obtain ⟨hI,hZ,hth⟩ := MasulloRH.theta_cocycle_core ρ h hi s
    refine ⟨hI,hZ,hth,?_⟩
    have he : (fun t => R (U s h) t - U s (R h) t) =ᵐ[volume.restrict (Ioi 0)] fun t => m h * d s t :=
      (ae_restrict_iff' measurableSet_Ioi).mpr <| Filter.Eventually.of_forall fun t ht => (hth t ht).2
    exact ⟨((hmass s).1.const_mul _).congr he.symm, by
      dsimp only [m]; rw [integral_congr_ae he, integral_const_mul]
      exact congrArg (fun z => m h*z) (hmass s).2⟩
  · intro p s hp
    simpa only [fun b => (hmass b).2] using MasulloRH.shifted_half_density_first_moment p s hp

open Set MeasureTheory Filter

namespace MasulloRH

/-- Endpoint energy on a single scale needs no information about the profile off that interval. -/
theorem total_cutoff_interval_energy {p A : ℝ} (hp : 1 < p) (hA : 0 < A)
    (M : ℝ) (j : ℕ) (K : ℝ → ℝ) (hj : 2*Real.log (2*A) ≤ (j:ℝ)*Real.log p)
    (hK : ∀ t ∈ Icc (A/p^j) (2*A/p^j), K t = -Real.exp (-(j:ℝ)*Real.log p/2)*M/t) :
    ((Real.log p)^2/(32*A^2))*M^2*(j:ℝ)^2*p^j ≤
      ∫ t in Icc (A/p^j) (2*A/p^j), (max t (1/t)*(1+(Real.log t)^2))*|K t|^2 := by
  let v := p^j
  let B := A/v
  let H := (j:ℝ)*Real.log p/2
  let a := Real.exp (-(j:ℝ)*Real.log p/2)
  let P := v⁻¹ * M^2 * (((2*B)⁻¹)^2) * (2*B)⁻¹ * H^2
  have hp0 := zero_lt_one.trans hp
  have hv : 0 < v := pow_pos hp0 _
  have hB : 0 < B := div_pos hA hv
  have hH : 0 ≤ H := by dsimp only [H]; positivity [Real.log_pos hp]
  have h2 : 2*B = 2*A/p^j := by dsimp only [B,v]; ring
  have he : a^2 = v⁻¹ := by
    dsimp only [a,v]
    rw [sq,←Real.exp_add, show -(j:ℝ)*Real.log p/2 + -(j:ℝ)*Real.log p/2 = -((j:ℝ)*Real.log p) by ring,
      Real.exp_neg,Real.exp_nat_mul,Real.exp_log hp0]
  let F (t : ℝ) := v⁻¹ * M^2 * (t⁻¹)^2 * max t t⁻¹ * (1 + (Real.log t)^2)
  have htpos (t : ℝ) (ht : t ∈ Icc B (2*B)) : 0 < t := hB.trans_le ht.1
  have hmono (t : ℝ) (ht : t ∈ Icc B (2*B)) : P ≤ F t := by
    have ht0 := htpos t ht
    have hi : (2*B)⁻¹ ≤ t⁻¹ := inv_anti₀ ht0 ht.2
    have hl : Real.log t ≤ -H := by
      have hlog := Real.log_le_log ht0 ht.2
      rw [h2, Real.log_div (by positivity) hv.ne',Real.log_pow] at hlog
      dsimp only [H]; linarith
    have hs : H^2 ≤ 1+(Real.log t)^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ -Real.log t-H) (by linarith : 0 ≤ -Real.log t+H)]
    dsimp only [P,F]
    gcongr
    exact hi.trans (le_max_right _ _)
  have hc : ContinuousOn F (Icc B (2*B)) := by
    have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Icc B (2*B)) :=
      continuousOn_id.inv₀ (fun t ht => (htpos t ht).ne')
    have hlog : ContinuousOn Real.log (Icc B (2*B)) :=
      Real.continuousOn_log.mono (fun t ht => (htpos t ht).ne')
    exact (((continuousOn_const.mul (hinv.pow 2)).mul (continuousOn_id.sup hinv)).mul (continuousOn_const.add (hlog.pow 2)))
  have hcomp : (∫ _t in Icc B (2*B), P) ≤ ∫ t in Icc B (2*B), F t :=
    setIntegral_mono_on (continuousOn_const.integrableOn_compact isCompact_Icc)
      (hc.integrableOn_compact isCompact_Icc) measurableSet_Icc hmono
  have hval : (∫ _t in Icc B (2*B), P) = ((Real.log p)^2/(32*A^2))*M^2*(j:ℝ)^2*p^j := by
    rw [setIntegral_const,Real.volume_real_Icc, max_eq_left (by linarith : 0 ≤ 2*B-B), smul_eq_mul]
    dsimp only [P,B,H]
    change _ = ((Real.log p)^2/(32*A^2))*M^2*(j:ℝ)^2*v
    field_simp [hA.ne',hv.ne']
    ring
  rw [←hval]
  apply hcomp.trans_eq
  rw [←h2]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  have hk := hK t (by simpa only [←h2] using ht)
  change F t = (max t (1/t)*(1+(Real.log t)^2))*|K t|^2
  rw [hk,sq_abs]
  change F t = (max t (1/t)*(1+(Real.log t)^2))*(-a*M/t)^2
  rw [div_pow,mul_pow,neg_sq,he]
  dsimp only [F]
  ring

/-- If the plateau holds eventually, the lower bound holds eventually with an explicit constant. -/
theorem total_cutoff_interval_energy_eventually {p A : ℝ} (hp : 1 < p) (hA : 0 < A)
    (M : ℝ) (K : ℕ → ℝ → ℝ)
    (hK : ∀ᶠ j : ℕ in atTop, ∀ t ∈ Icc (A/p^j) (2*A/p^j),
      K j t = -Real.exp (-(j:ℝ)*Real.log p/2)*M/t) :
    ∀ᶠ j : ℕ in atTop, ((Real.log p)^2/(32*A^2))*M^2*(j:ℝ)^2*p^j ≤
      ∫ t in Icc (A/p^j) (2*A/p^j), (max t (1/t)*(1+(Real.log t)^2))*|K j t|^2 := by
  obtain ⟨J,hJ⟩ := exists_nat_ge (2*Real.log (2*A)/Real.log p)
  filter_upwards [hK, eventually_ge_atTop J] with j hj hjJ
  apply total_cutoff_interval_energy hp hA M j (K j) _ hj
  apply (div_le_iff₀ (Real.log_pos hp)).mp
  exact hJ.trans (Nat.cast_le.mpr hjJ)

/-- Endpoint version for a range plateau given directly by the geometric half-density. -/
theorem total_cutoff_interval_energy_of_sqrt_plateau {p A : ℝ} (hp : 1 < p) (hA : 0 < A)
    (M : ℝ) (K : ℕ → ℝ → ℝ)
    (hK : ∀ᶠ j : ℕ in atTop, ∀ t ∈ Icc (A/p^j) (2*A/p^j),
      K j t = -((Real.sqrt p)⁻¹ ^ j)*M/t) :
    ∀ᶠ j : ℕ in atTop, ((Real.log p)^2/(32*A^2))*M^2*(j:ℝ)^2*p^j ≤
      ∫ t in Icc (A/p^j) (2*A/p^j), (max t (1/t)*(1+(Real.log t)^2))*|K j t|^2 := by
  apply total_cutoff_interval_energy_eventually hp hA M K
  filter_upwards [hK] with j hj
  have he : Real.exp (-(j:ℝ)*Real.log p/2) = (Real.sqrt p)⁻¹ ^ j := by
    rw [show -(j:ℝ)*Real.log p/2 = (j:ℝ)*(-(Real.log p/2)) by ring,
      Real.exp_nat_mul,Real.exp_neg,Real.exp_half,Real.exp_log (zero_lt_one.trans hp)]
  simpa only [he] using hj

end MasulloRH

open Set MeasureTheory

/-- On the indicated interval the left and right constant tails of the cutoff determine
its complete contribution, independent of its behavior across the transition. -/
theorem MasulloRH.half_density_prime_plateau_of_cutoff_tails (ρ φ : ℝ → ℝ) (p A L H : ℝ)
    (hp : 1 < p) (hA : 0 < A) (hlo : ∀ u : ℝ, u ≤ L → ρ u = 1)
    (hhi : ∀ u : ℝ, H < u → ρ u = 0)
    (hφ : ∀ x : ℝ, φ x ≠ 0 → x < Real.log A - H)
    (j : ℕ) (hband : 2*A/p^j ≤ Real.exp L) (t : ℝ) (ht : t ∈ Icc (A/p^j) (2*A/p^j)) :
    let d (b t : ℝ) : ℝ := Real.exp (b/2) * (ρ (Real.log t-b) - ρ (Real.log t)) / t
    (∫ x : ℝ, φ x * d (x-(j:ℝ)*Real.log p) t) =
      -((Real.sqrt p)⁻¹ ^ j) * (∫ x : ℝ, φ x * Real.exp (x/2)) /t := by
  intro d
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpj : 0 < p^j := pow_pos hp0 j
  have ht0 : 0 < t := (div_pos hA hpj).trans_le ht.1
  have htL : Real.log t ≤ L := by
    simpa only [Real.log_exp] using Real.log_le_log ht0 (ht.2.trans hband)
  have hlt : Real.log A - (j:ℝ)*Real.log p ≤ Real.log t := by
    simpa only [Real.log_div hA.ne' hpj.ne', Real.log_pow] using
      Real.log_le_log (div_pos hA hpj) ht.1
  have hbase : Real.exp (-(Real.log p/2)) = (Real.sqrt p)⁻¹ := by
    rw [Real.exp_neg, Real.exp_half, Real.exp_log hp0]
  have hphi (x : ℝ) : φ x * d (x - (j:ℝ)*Real.log p) t =
      (-((Real.sqrt p)⁻¹ ^ j)/t) * (φ x * Real.exp (x/2)) := by
    by_cases hx : φ x = 0
    · simp [hx]
    · have ha : H < Real.log t - (x - (j:ℝ)*Real.log p) := by linarith [hφ x hx]
      simp only [d, hhi _ ha, hlo _ htL]
      rw [show (x-(j:ℝ)*Real.log p)/2 = x/2+(j:ℝ)*(-(Real.log p/2)) by ring,
        Real.exp_add, Real.exp_nat_mul, hbase]
      ring
  simp_rw [hphi]
  rw [integral_const_mul]
  ring
open MeasureTheory Set Filter

theorem solution (r : ℝ → ℝ) (hr : Integrable r) :
    let ρ (u : ℝ) := (if u≤0 then (1:ℝ) else 0) + r u
    let m (g : ℝ → ℝ) := ∫ t in Ioi (0:ℝ), g t
    let θ (g : ℝ → ℝ) (t : ℝ) := ∑' n : ℕ, g (((n:ℝ)+1)*t)
    let U (s : ℝ) (g : ℝ → ℝ) (t : ℝ) := Real.exp (-s/2) * g (Real.exp (-s)*t)
    let R (g : ℝ → ℝ) (t : ℝ) := θ g t - m g * ρ (Real.log t) / t
    let d (b t : ℝ) := Real.exp (b/2)*(ρ (Real.log t-b)-ρ (Real.log t))/t
    (∀ (h : ℝ → ℝ) (s : ℝ), IntegrableOn h (Ioi 0) →
      IntegrableOn (U s h) (Ioi 0) ∧ m (U s h) = Real.exp (s/2)*m h ∧
      (∀ t : ℝ, 0<t →
        (Summable (fun n : ℕ => U s h (((n:ℝ)+1)*t)) ↔
          Summable (fun n : ℕ => h (((n:ℝ)+1)*(Real.exp (-s)*t)))) ∧
        R (U s h) t - U s (R h) t = m h * d s t) ∧
      IntegrableOn (fun t => R (U s h) t - U s (R h) t) (Ioi 0) ∧
      m (fun t => R (U s h) t - U s (R h) t) = m h * (s*Real.exp (s/2))) ∧
    (∀ s : ℝ, IntegrableOn (d s) (Ioi 0) ∧ m (d s) = s*Real.exp (s/2)) ∧
    (∀ p s : ℝ, 1<p →
      HasSum (fun j : ℕ => m (d (s-((j:ℝ)+1)*Real.log p)))
        (Real.exp (s/2)*(s/(Real.sqrt p-1) - Real.log p*Real.sqrt p/(Real.sqrt p-1)^2))) ∧
    (∀ (φ : ℝ → ℝ) (p A L H : ℝ), 1<p → 0<A →
      (∀ u : ℝ, u≤L → ρ u=1) → (∀ u : ℝ, H<u → ρ u=0) →
      (∀ x : ℝ, φ x≠0 → x<Real.log A-H) →
      let M := ∫ x : ℝ, φ x*Real.exp (x/2)
      let K (j : ℕ) (t : ℝ) := ∫ x : ℝ, φ x*d (x-(j:ℝ)*Real.log p) t
      ∀ᶠ j : ℕ in atTop, ((Real.log p)^2/(32*A^2))*M^2*(j:ℝ)^2*p^j ≤
        ∫ t in Icc (A/p^j) (2*A/p^j), (max t (1/t)*(1+(Real.log t)^2))*|K j t|^2) := by
  intro ρ m θ U R d
  obtain ⟨h0,h1,h2⟩ := theta_global_cocycle r hr
  refine ⟨h0,h1,h2,?_⟩
  intro φ p A L H hp hA hlo hhi hφ M K
  apply MasulloRH.total_cutoff_interval_energy_of_sqrt_plateau hp hA M K
  have hpow := (tendsto_pow_atTop_atTop_of_one_lt hp).eventually_ge_atTop (2*A/Real.exp L)
  filter_upwards [hpow] with j hj
  have hpj : 0 < p^j := pow_pos (zero_lt_one.trans hp) j
  have hband : 2*A/p^j ≤ Real.exp L := by
    rw [div_le_iff₀ hpj]
    simpa only [mul_comm] using (div_le_iff₀ (Real.exp_pos L)).mp hj
  intro t ht
  exact MasulloRH.half_density_prime_plateau_of_cutoff_tails ρ φ p A L H hp hA hlo hhi hφ j hband t ht
