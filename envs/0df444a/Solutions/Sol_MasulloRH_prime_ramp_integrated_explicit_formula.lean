-- Prove2me | solution 1 for MasulloRH.prime_ramp_integrated_explicit_formula
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:58:56.544722+00:00
-- url     : https://prove2.me/submissions/91ee233e-1605-44e7-9bf3-eee41f8a4bb3

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_GuthMaynard_davenport_truncated_explicit_formula
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Mathlib

open Filter Finset Set Topology MeasureTheory ArithmeticFunction
open scoped Interval
noncomputable section
open MasulloRH
namespace RampIncrementProof
private abbrev Zero := ZetaZerosInTraceStrip (1/2)
private theorem multiplicity_pos (ρ : ZetaZerosInTraceStrip (1/2)) :
    0 < analyticOrderNatAt riemannZeta ρ.val := by
  have h1 : ρ.val ≠ 1 := fun h => by
    have hr := congrArg Complex.re h
    simp only [Complex.one_re] at hr
    linarith [ρ.prop.2.2.1]
  have hA := analyticOn_riemannZeta
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hfin := hA.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
    (show (2:ℂ) ∈ ({1}:Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)
  apply Nat.pos_of_ne_zero
  unfold analyticOrderNatAt
  exact fun h => (ENat.toNat_eq_zero.mp h).elim
    ((hA _ h1).analyticOrderAt_ne_zero.mpr ρ.prop.1) hfin

private theorem finite_zeros_to_height (H : ℝ) (hH : 0 ≤ H) :
    {z : ZetaZerosInTraceStrip (1/2) | |z.val.im| ≤ H}.Finite := by
  let w := zeroDecayWeight (1/2)
  have hlim : Tendsto w cofinite (𝓝 0) := (weighted_zero_summability (1/2) (by norm_num)).tendsto_cofinite_zero
  have he := hlim.eventually (gt_mem_nhds (show (0:ℝ) < 1/(1+H^2) by positivity))
  have hbad : {z | ¬ w z < 1/(1+H^2)}.Finite := by
    simpa only [eventually_cofinite] using he
  apply hbad.subset
  intro z hz
  change |z.val.im| ≤ H at hz
  change ¬w z < 1/(1+H^2)
  apply not_lt.mpr
  have hysq : z.val.im^2 ≤ H^2 := by nlinarith [sq_abs z.val.im,mul_self_le_mul_self (abs_nonneg _) hz]
  have hm : (1:ℝ) ≤ analyticOrderNatAt riemannZeta z.val := by exact_mod_cast multiplicity_pos z
  exact (one_div_le_one_div_of_le (by positivity) (by linarith only [hysq])).trans
    (div_le_div_of_nonneg_right hm (by positivity))

private noncomputable def heights (T : ℝ) : Finset Zero :=
  ((finite_zeros_to_height |T| (abs_nonneg T)).subset (show {z : Zero | |z.val.im|<T} ⊆ {z | |z.val.im|≤|T|} from
    fun _ hz => (le_of_lt hz).trans (le_abs_self T))).toFinset
private theorem mem_heights (T : ℝ) (z : Zero) : z ∈ heights T ↔ |z.val.im|<T := Set.Finite.mem_toFinset _
private abbrev mass (z : Zero) : ℂ := analyticOrderNatAt riemannZeta z.val
private noncomputable def zterm (x : ℝ) (z : Zero) : ℂ := mass z * (x:ℂ)^z.val/z.val
private noncomputable def archTerm (x : ℝ) : ℝ := Real.log (2*Real.pi) + (1/2)*Real.log (1-x^(-2:ℝ))
private noncomputable def residual (T x : ℝ) : ℂ := ((Chebyshev.psi x - x : ℝ):ℂ) + (∑ z ∈ heights T,zterm x z) + (archTerm x:ℂ)
private noncomputable def gap (x : ℝ) : ℝ := sInf {d : ℝ | ∃ n : ℕ, IsPrimePow n ∧ (n:ℝ) ≠ x ∧ d=|x-n|}

private theorem reindex_zeros (x T : ℝ) :
    (∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ=0 ∧ 0<ρ.re ∧ ρ.re<1 ∧ |ρ.im|<T},
      (analyticOrderNatAt riemannZeta ρ:ℂ)*(x:ℂ)^ρ/ρ) = ∑ z ∈ heights T,zterm x z := by
  classical
  let S := (heights T).image Subtype.val
  have hS : {ρ : ℂ | riemannZeta ρ=0 ∧ 0<ρ.re ∧ ρ.re<1 ∧ |ρ.im|<T} = (S : Set ℂ) := by
    ext ρ;constructor
    · rintro ⟨h0,hr,h1,hT⟩
      let z : Zero := ⟨ρ,h0,hr,h1,abs_lt.mpr ⟨by linarith,by linarith⟩⟩
      exact Finset.mem_image.mpr ⟨z,(mem_heights T z).2 hT,rfl⟩
    · intro h;obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
      exact ⟨z.prop.1,z.prop.2.1,z.prop.2.2.1,(mem_heights T z).1 hz⟩
  rw [hS,finsum_mem_coe_finset]
  exact Finset.sum_image (fun _ _ _ _ he => Subtype.ext he)

private theorem gap_pos {x : ℝ} (hx : 0 ≤ x) (hn : ∀ n : ℕ, (n:ℝ) ≠ x) : 0 < gap x := by
  let N := ⌊x⌋₊
  have hN : (N:ℝ) < x := lt_of_le_of_ne (Nat.floor_le hx) (hn N)
  have hN' : x < (N:ℝ)+1 := Nat.lt_floor_add_one x
  let d := min (x-N) ((N:ℝ)+1-x)
  have hd : 0 < d := lt_min (by linarith) (by linarith)
  apply hd.trans_le
  apply le_csInf
  · exact ⟨|x-(2:ℕ)|,2,Nat.prime_two.isPrimePow,hn 2,rfl⟩
  · rintro v ⟨n,_,_,rfl⟩
    by_cases hk : n ≤ N
    · have hnr : (n:ℝ) ≤ N := by exact_mod_cast hk
      rw [abs_of_nonneg (by linarith : 0 ≤ x-(n:ℝ))]
      exact (min_le_left ..).trans (by linarith)
    · have hnr : (N:ℝ)+1 ≤ n := by exact_mod_cast (show N+1≤n by omega)
      rw [abs_of_neg (by linarith : x-(n:ℝ) < 0)]
      exact (min_le_right ..).trans (by linarith)

private theorem approx_constant : ∃ C : ℝ, 0 ≤ C ∧ ∀ x T : ℝ, 2 ≤ x → 2 ≤ T → (∀ n : ℕ, (n:ℝ) ≠ x) →
    ‖residual T x‖ ≤ C*(x*(Real.log (x*T))^2/T+Real.log x*min 1 (x/(T*gap x))) := by
  obtain ⟨C,hC⟩ := GuthMaynard.davenport_truncated_explicit_formula
  refine ⟨|C|,abs_nonneg _,fun x T hx hT hn => ?_⟩
  have h := hC x T hx hT
  rw [if_neg (hn ⌊x⌋₊),sub_zero,reindex_zeros] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right (le_abs_self _)
  have hx0 : 0 ≤ x := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hgap := gap_pos hx0 hn
  change 0 ≤ x*(Real.log (x*T))^2/T+Real.log x*min 1 (x/(T*gap x))
  have hlog := Real.log_nonneg (by linarith : 1≤x)
  positivity

private theorem log_limit {b : ℝ} (hb : 0 < b) :
    Tendsto (fun T : ℝ => Real.log (b*T)^2/T) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => Real.log t ^ 2 / t) atTop (𝓝 0) := by
    simpa using (isLittleO_log_rpow_rpow_atTop 2 (show 0<(1:ℝ) by norm_num)).tendsto_div_nhds_zero
  have hh := (h.comp (tendsto_id.const_mul_atTop hb)).mul_const b
  simp only [zero_mul] at hh
  convert hh using 1
  ext T
  dsimp
  field_simp

private theorem residual_limit {x : ℝ} (hx : 2 ≤ x) (hn : ∀ n : ℕ, (n:ℝ) ≠ x) :
    Tendsto (fun T => residual T x) atTop (𝓝 0) := by
  obtain ⟨C,hC,h⟩ := approx_constant
  have hx0 : 0<x := by linarith
  have hg := gap_pos hx0.le hn
  have hL := (log_limit hx0).const_mul x
  have hR : Tendsto (fun T : ℝ => x/(T*gap x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.atTop_mul_const hg)
  have htot := (hL.add (hR.const_mul (Real.log x))).const_mul C
  simp only [mul_zero,add_zero] at htot
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ htot
  filter_upwards [eventually_ge_atTop (2:ℝ)] with T hT
  refine (h x T hx hT hn).trans (mul_le_mul_of_nonneg_left ?_ hC)
  rw [mul_div_assoc]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (min_le_right ..) (Real.log_nonneg (by linarith : 1≤x)))

private theorem residual_integral_limit {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    Tendsto (fun T => ∫ t in a..b, residual T t / (t:ℂ)^2) atTop (𝓝 0) := by
  obtain ⟨C,hC,h⟩ := approx_constant
  have hb : 0 < b := by linarith
  have hn : ∀ᵐ t ∂(volume : Measure ℝ), ∀ n : ℕ, (n:ℝ) ≠ t := by
    apply ae_all_iff.mpr
    intro n
    exact (Measure.ae_ne volume (n:ℝ)).mono fun _ hne => Ne.symm hne
  have hm (T : ℝ) : Measurable (fun t : ℝ => residual T t/(t:ℂ)^2) := by
    unfold residual archTerm zterm
    have hp := Chebyshev.psi_mono.measurable
    have hpz (z : Zero) := (Complex.continuous_ofReal_cpow_const z.prop.2.1).measurable
    fun_prop
  have hD := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := (atTop : Filter ℝ)) (a:=a) (b:=b)
    (F := fun T t => residual T t / (t:ℂ)^2) (f:=fun _ => (0:ℂ))
    (fun _ => C*(b+Real.log b)) (Eventually.of_forall fun T => (hm T).aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop (2:ℝ), (log_limit hb).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with T hT hlog
      filter_upwards [hn] with t ht htI
      rw [uIoc_of_le hab] at htI
      have ht2 : 2 ≤ t := ha.trans htI.1.le
      have ht0 : 0 < t := by linarith
      have hT0 : 0 < T := by linarith
      rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht0]
      apply (div_le_self (norm_nonneg _) (by nlinarith : 1≤t^2)).trans
      apply (h t T ht2 hT ht).trans (mul_le_mul_of_nonneg_left ?_ hC)
      have hll : 0 ≤ Real.log (t*T) := Real.log_nonneg (by nlinarith)
      have hlb := Real.log_le_log (mul_pos ht0 hT0) (mul_le_mul_of_nonneg_right htI.2 hT0.le)
      have hs : Real.log (t*T)^2/T ≤ 1 := (div_le_div_of_nonneg_right (by nlinarith : Real.log (t*T)^2 ≤ Real.log (b*T)^2) hT0.le).trans hlog.le
      rw [mul_div_assoc]
      exact add_le_add ((mul_le_of_le_one_right ht0.le hs).trans htI.2)
        ((mul_le_of_le_one_right (Real.log_nonneg (by linarith)) (min_le_left ..)).trans (Real.log_le_log ht0 htI.2)))
    intervalIntegrable_const
    (by
      filter_upwards [hn] with t ht htI
      rw [uIoc_of_le hab] at htI
      simpa using (residual_limit (ha.trans htI.1.le) ht).div_const ((t:ℂ)^2))
  simpa using hD

private theorem heights_exhaust : Tendsto heights atTop atTop := by
  apply tendsto_atTop_finset_of_monotone
  · intro a b hab z hz
    exact (mem_heights _ _).2 (((mem_heights _ _).1 hz).trans_le hab)
  · intro z
    exact ⟨|z.val.im|+1,(mem_heights _ _).2 (by linarith)⟩

private def kernel (x : ℝ) (z : Zero) : ℂ := mass z * (x:ℂ)^(z.val-1)/(z.val*(z.val-1))

private theorem zero_den (z : Zero) : z.val ≠ 0 ∧ z.val-1 ≠ 0 := by
  constructor
  · intro h; have := z.prop.2.1; simpa [h] using this
  · intro h; have he := sub_eq_zero.mp h; have := z.prop.2.2.1; simpa [he] using this

private theorem zero_integral {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (z : Zero) :
    (∫ t in a..b, zterm t z / (t:ℂ)^2) = kernel b z-kernel a z := by
  have h0 : (0:ℝ) ∉ [[a,b]] := by rw [uIcc_of_le hab]; rintro ⟨h,_⟩; linarith
  have hn := zero_den z
  have hpow : z.val-2 ≠ -1 := fun h => hn.2 (by linear_combination h)
  calc
    _ = ∫ t in a..b, (mass z / z.val) * (t:ℂ)^(z.val-2) := by
      apply intervalIntegral.integral_congr; intro t ht
      have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (fun h => h0 (h ▸ ht) : t ≠ 0)
      dsimp only
      rw [Complex.cpow_sub _ _ ht0,show (t:ℂ)^(2:ℂ) = (t:ℂ)^2 by norm_cast]
      unfold zterm
      ring
    _ = kernel b z-kernel a z := by
      rw [intervalIntegral.integral_const_mul,integral_cpow (Or.inr ⟨hpow,h0⟩),show z.val-2+1=z.val-1 by ring]
      unfold kernel
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

private theorem invsq_cont {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    ContinuousOn (fun t : ℝ => (t^2)⁻¹) [[a,b]] := by
  apply (continuous_id.pow 2).continuousOn.inv₀
  intro t ht; rw [uIcc_of_le hab] at ht; exact pow_ne_zero _ (ha.trans_le ht.1).ne'

private theorem psi_integrable {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    IntervalIntegrable (fun t => Chebyshev.psi t/t^2) volume a b := by
  simpa only [div_eq_mul_inv] using Chebyshev.psi_mono.intervalIntegrable.mul_continuousOn (invsq_cont ha hab)

private theorem phys_integrable {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    IntervalIntegrable (fun t => ((Chebyshev.psi t - t:ℝ):ℂ)/(t:ℂ)^2) volume a b := by
  have h := (Chebyshev.psi_mono.intervalIntegrable.sub (continuous_id.intervalIntegrable (μ:=volume) a b)).mul_continuousOn (invsq_cont ha hab)
  rw [intervalIntegrable_iff] at *
  have hcast : Integrable (fun t : ℝ => (((Chebyshev.psi t-t)*(t^2)⁻¹:ℝ):ℂ)) (volume.restrict (Ι a b)) := h.ofReal
  simpa only [IntegrableOn,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,div_eq_mul_inv] using hcast

private theorem arch_cont {a b : ℝ} (ha : 2≤a) (hab : a≤b) :
    ContinuousOn (fun t : ℝ => (archTerm t:ℂ)/(t:ℂ)^2) [[a,b]] := by
  intro t ht
  rw [uIcc_of_le hab] at ht
  have ht2 : 2≤t := ha.trans ht.1
  have ht0 : 0<t := by linarith
  have ht' : 0 < 1-t^(-2:ℝ) := by
    rw [Real.rpow_neg ht0.le,Real.rpow_two]
    have : 1 < t^2 := by nlinarith
    simpa using (sub_pos.mpr (inv_lt_one_of_one_lt₀ this))
  unfold archTerm
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := first | positivity | exact ht'.ne' | exact Or.inl ht0.ne' | exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr ht0.ne') | exact ht0.ne')

private theorem zcont {a b : ℝ} (ha : 0<a) (hab : a≤b) (z : Zero) :
    ContinuousOn (fun t : ℝ => zterm t z/(t:ℂ)^2) [[a,b]] := by
  intro t ht
  rw [uIcc_of_le hab] at ht
  have ht0 := (ha.trans_le ht.1).ne'
  have hc := (Complex.continuous_ofReal_cpow_const z.prop.2.1).continuousAt (x:=t)
  unfold zterm
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := first | exact (zero_den z).1 | exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr ht0))

private theorem integrated_residual {a b : ℝ} (ha : 2≤a) (hab : a≤b) (T : ℝ) :
    (∫ t in a..b, residual T t/(t:ℂ)^2) =
      (∫ t in a..b, ((Chebyshev.psi t-t:ℝ):ℂ)/(t:ℂ)^2) +
      (∑ z ∈ heights T,(kernel b z-kernel a z)) +
      (∫ t in a..b, (archTerm t:ℂ)/(t:ℂ)^2) := by
  have ha0 : 0<a := by linarith
  have hZ (z : Zero) (_ : z ∈ heights T) := (zcont ha0 hab z).intervalIntegrable (μ:=volume)
  have hS : IntervalIntegrable (fun t => ∑ z ∈ heights T,zterm t z/(t:ℂ)^2) volume a b := by
    have he : (fun t : ℝ => ∑ z ∈ heights T,zterm t z/(t:ℂ)^2) = ∑ z ∈ heights T,fun t : ℝ => zterm t z/(t:ℂ)^2 := by
      funext t; rw [Finset.sum_apply]
    rw [he]; exact IntervalIntegrable.sum (heights T) hZ
  simp only [residual,add_div,Finset.sum_div]
  rw [intervalIntegral.integral_add ((phys_integrable ha0 hab).add hS) (arch_cont ha hab).intervalIntegrable,
    intervalIntegral.integral_add (phys_integrable ha0 hab) hS,intervalIntegral.integral_finsetSum hZ]
  simp only [zero_integral ha hab]

private theorem kernel_bound {x : ℝ} (hx : 1≤x) (z : Zero) :
    ‖kernel x z‖ ≤ 2*zeroDecayWeight (1/2) z := by
  let m := analyticOrderNatAt riemannZeta z.val
  have hy : 6 < |z.val.im| := by
    by_contra! h
    exact ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six z.prop.2.1 z.prop.2.2.1 h z.prop.1
  have hy2 : 1 ≤ z.val.im^2 := by nlinarith [sq_abs z.val.im,sq_nonneg (|z.val.im|-6)]
  have hz := Complex.abs_im_le_norm z.val
  have hz' : |z.val.im| ≤ ‖z.val - 1‖ := by simpa using Complex.abs_im_le_norm (z.val-1)
  have hden : 1+z.val.im^2 ≤ 2*(‖z.val‖*‖z.val-1‖) := by
    nlinarith [mul_le_mul hz hz' (abs_nonneg _) (norm_nonneg _),sq_abs z.val.im]
  have hx0 : 0<x := by linarith
  have hp : x^(z.val-1).re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by simp; linarith [z.prop.2.2.1])
  unfold kernel zeroDecayWeight
  rw [norm_div,norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx0,Complex.norm_natCast]
  change (m:ℝ)*x^(z.val-1).re/(‖z.val‖*‖z.val-1‖) ≤ 2*((m:ℝ)/(1+z.val.im^2))
  have hd := mul_pos (norm_pos_iff.mpr (zero_den z).1) (norm_pos_iff.mpr (zero_den z).2)
  calc
    _ ≤ (m:ℝ)/(‖z.val‖*‖z.val-1‖) := div_le_div_of_nonneg_right (mul_le_of_le_one_right (Nat.cast_nonneg _) hp) hd.le
    _ ≤ _ := by
      rw [← mul_div_assoc,div_le_div_iff₀ hd (by positivity)]
      calc (m:ℝ)*(1+z.val.im^2) ≤ (m:ℝ)*(2*(‖z.val‖*‖z.val-1‖)) := mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg _)
           _ = _ := by ring

private theorem kernel_summable {x : ℝ} (hx : 1≤x) : Summable (kernel x) :=
  ((weighted_zero_summability (1/2) (by norm_num)).mul_left 2).of_norm_bounded (kernel_bound hx)

private theorem explicit_difference {a b : ℝ} (ha : 2≤a) (hab : a≤b) :
    (∫ t in a..b, ((Chebyshev.psi t-t:ℝ):ℂ)/(t:ℂ)^2) +
      (∑' z : Zero,(kernel b z-kernel a z)) +
      (∫ t in a..b, (archTerm t:ℂ)/(t:ℂ)^2) = 0 := by
  have h := ((kernel_summable (by linarith : 1≤b)).sub (kernel_summable (by linarith : 1≤a))).hasSum.comp heights_exhaust
  have h' := (h.const_add (∫ t in a..b, ((Chebyshev.psi t-t:ℝ):ℂ)/(t:ℂ)^2)).add_const
    (∫ t in a..b, (archTerm t:ℂ)/(t:ℂ)^2)
  apply tendsto_nhds_unique h'
  apply (residual_integral_limit ha hab).congr
  intro T
  exact integrated_residual ha hab T

private def raw (x : ℝ) : ℝ := ∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0
private def G (x : ℝ) : ℝ := raw x-x*(Real.log x-1-Real.eulerMascheroniConstant)

private theorem raw_ratio {x : ℝ} (hx : 1≤x) :
    raw x /x = (∑ n ∈ Finset.Icc 0 ⌊x⌋₊,(n:ℝ)⁻¹*vonMangoldt n) - Chebyshev.psi x / x := by
  have hx0 : 0<x := by linarith
  rw [raw,Nat.range_succ_eq_Icc_zero,Finset.sum_div,Chebyshev.psi_eq_sum_Icc,Finset.sum_div,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rcases eq_or_ne n 0 with rfl | hnon
  · simp
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hnon
  have hnle : (n:ℝ) ≤ x := (Nat.le_floor_iff hx0.le).mp (Finset.mem_Icc.mp hn).2
  rw [max_eq_left (sub_nonneg.mpr ((one_le_div hnpos).mpr hnle))]
  field_simp
  <;> ring

private theorem raw_primitive {x : ℝ} (hx : 1≤x) : raw x/x = ∫ t in 1..x, Chebyshev.psi t/t^2 := by
  have hder : ContinuousOn (fun t : ℝ => -(t^2)⁻¹) (Set.Icc 1 x) := by
    rw [← uIcc_of_le hx]
    exact (invsq_cont one_pos hx).neg
  have h := sum_mul_eq_sub_integral_mul₀ (f:=fun t : ℝ => t⁻¹) (fun n => vonMangoldt n) (by simp) x
    (fun t ht => (hasDerivAt_inv (show t ≠ 0 by linarith [ht.1])).differentiableAt)
    (by rw [deriv_inv']; exact hder.integrableOn_Icc)
  simp only [deriv_inv,←Chebyshev.psi_eq_sum_Icc] at h
  have he : (fun t : ℝ => -(t^2)⁻¹*Chebyshev.psi t) = (fun t => -(Chebyshev.psi t/t^2)) := by funext; ring
  rw [he,integral_neg,←intervalIntegral.integral_of_le hx] at h
  rw [raw_ratio hx,h]
  ring

private theorem G_difference {a b : ℝ} (ha : 2≤a) (hab : a≤b) :
    ((G b/b-G a/a:ℝ):ℂ) = ∫ t in a..b, ((Chebyshev.psi t-t:ℝ):ℂ)/(t:ℂ)^2 := by
  have ha1 : 1≤a := by linarith
  have hb1 := ha1.trans hab
  have ha0 : 0<a := by linarith
  have hb0 := ha0.trans_le hab
  have hraw : raw b/b - raw a/a = ∫ t in a..b, Chebyshev.psi t/t^2 := by
    rw [raw_primitive ha1,raw_primitive hb1]
    have h := intervalIntegral.integral_add_adjacent_intervals (psi_integrable one_pos ha1) (psi_integrable ha0 hab)
    linarith
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹) [[a,b]] :=
    continuous_id.continuousOn.inv₀ (fun t ht => (ha0.trans_le ((uIcc_of_le hab) ▸ ht).1).ne')
  have he (t : ℝ) (ht : t ∈ [[a,b]]) : (Chebyshev.psi t-t)/t^2=Chebyshev.psi t/t^2 - t⁻¹ := by
    have ht0 : 0<t := ha0.trans_le ((uIcc_of_le hab) ▸ ht).1
    field_simp
  have hreal : G b/b-G a/a = ∫ t in a..b, (Chebyshev.psi t-t)/t^2 := by
    rw [intervalIntegral.integral_congr he,intervalIntegral.integral_sub (psi_integrable ha0 hab) hinv.intervalIntegrable,
      ←hraw,integral_inv_of_pos ha0 hb0,Real.log_div hb0.ne' ha0.ne']
    unfold G
    simp only [sub_div]
    field_simp
    <;> ring
  rw [hreal,←intervalIntegral.integral_ofReal]
  simp only [Complex.ofReal_div,Complex.ofReal_pow]

end RampIncrementProof
open RampIncrementProof
/-- Integrating the sharp explicit formula produces an absolutely convergent zero sum. -/
theorem solution :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let K (x : ℝ) (ρ : ZetaZerosInTraceStrip (1/2)) :=
      (analyticOrderNatAt riemannZeta ρ.val : ℂ) * (x:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1))
    (∀ x : ℝ, 1≤x → Summable (fun ρ => ‖K x ρ‖)) ∧
    (∀ a b : ℝ, 2≤a → a≤b →
      ((G b/b - G a/a:ℝ):ℂ) + (∑' ρ : ZetaZerosInTraceStrip (1/2),(K b ρ-K a ρ)) +
        (∫ t in a..b, ((Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)):ℝ):ℂ)/(t:ℂ)^2) = 0) := by
  constructor
  · exact fun x hx => (kernel_summable hx).norm
  · intro a b ha hab
    change ((G b/b-G a/a:ℝ):ℂ) + _ + _ = 0
    rw [G_difference ha hab]
    exact explicit_difference ha hab


end
