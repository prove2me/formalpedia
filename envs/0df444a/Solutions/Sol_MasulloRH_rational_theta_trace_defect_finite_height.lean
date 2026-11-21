-- Prove2me | solution 1 for MasulloRH.rational_theta_trace_defect_finite_height
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:19:17.97268+00:00
-- url     : https://prove2.me/submissions/f7a4fc48-b1ec-449f-91b6-89e7a1414b84

import Theorems.Thm_MasulloRH_regularized_mellin_limit
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_regularized_spectral_domination_any_window
import Theorems.Thm_MasulloRH_regularized_test_admissible
import Theorems.Thm_MasulloRH_trace_formula_rational_full_strip
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_MasulloRH_rational_theta_annihilator_jet_trace
import Theorems.Thm_MasulloRH_rational_theta_cutoff_trace_defect
import Theorems.Thm_MasulloRH_zero_decay_tail_at_real_lattice
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count
import Mathlib

section StandaloneGeometricCutoff

open MasulloRH Set Filter MeasureTheory
open scoped Topology

namespace ThetaGeometricLimit

/-- The pointwise regularization argument follows the full-strip and omitted-zero
limit proofs in MasulloRH. -/
private theorem cyclic_GeometricCutoff_traceTerm_limit (α : ℝ) (s : ℂ) (hs : (3/2:ℝ)<s.re)
    (ρ : ZetaZerosInTraceStrip α) :
    Tendsto (fun n : ℕ => zetaTraceTerm (regularizedTraceTest n s) α ρ) atTop
      (𝓝 (zeroResolventTerm α s ρ)) := by
  have hr : (ρ : ℂ).re < 1 := ρ.property.2.2.1
  have hwr : ((ρ : ℂ)-1/2).re = (ρ : ℂ).re - 1/2 := by simp
  have hm := regularized_mellin_limit s ((ρ : ℂ) - 1/2)
    (by rw [hwr]; linarith) (by rw [hwr]; linarith)
  have ha : s-1/2-((ρ:ℂ)-1/2) = s-ρ := by ring
  have hb : (2:ℂ)-((ρ:ℂ)-1/2) = 5/2-ρ := by ring
  simpa only [zetaTraceTerm, zeroResolventTerm, ha, hb] using
    hm.const_mul (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ)

private theorem cyclic_GeometricCutoff_full_cutoff_limit :
    Tendsto (fun n : ℕ => cutoffSpectral (1/2) n 3) atTop (𝓝 (regularizedSpectral (1/2) 3)) := by
  obtain ⟨C,_,hb⟩ := regularized_spectral_domination_any_window (1/2) 3 (by norm_num)
  apply tendsto_tsum_of_dominated_convergence ((weighted_zero_summability (1/2) (by norm_num)).mul_left C)
  · exact cyclic_GeometricCutoff_traceTerm_limit (1/2) 3 (by norm_num)
  · exact .of_forall hb

theorem geometric_cutoff_limit :
    Tendsto (fun n : ℕ => let φ := regularizedTraceTest n 3
      (mellin φ (1/2) + mellin φ (-1/2) -
        ((∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
          ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i)).re)
      atTop (𝓝 (regularizedSpectral (1/2) 3).re) := by
  apply (Complex.continuous_re.continuousAt.tendsto.comp cyclic_GeometricCutoff_full_cutoff_limit).congr
  intro n
  let φ := regularizedTraceTest n 3
  have he := (trace_formula_rational_full_strip φ (regularized_test_admissible n 3)).2.2.2
  dsimp only
  apply congrArg Complex.re
  change cutoffSpectral (1/2) n 3 = _ - (_ + _)
  rw [he]
  change _ = _ - (_ - cutoffSpectral (1/2) n 3)
  abel

/-- Strict positivity of the real kernel is the calculation used in the accepted
single-resolvent test of Yi (submission eaa70854). The injection comparison uses nonnegativity. -/
private theorem cyclic_GeometricCutoff_kernel_pos {b y : ℝ} (hb : 0 < b) (hb' : b < 1) (hy : 6 < |y|) :
    0 < (3-b)/((3-b)^2+y^2) - (5/2-b)/((5/2-b)^2+y^2) := by
  have hy' : 36 < y^2 := by nlinarith [sq_abs y, sq_nonneg (|y|-6)]
  have ha : 0 < (3-b)^2+y^2 := by positivity
  have hc : 0 < (5/2-b)^2+y^2 := by positivity
  rw [sub_pos, div_lt_div_iff₀ hc ha]
  nlinarith [mul_pos hb (sub_pos.mpr hb')]

private theorem cyclic_GeometricCutoff_term_nonnegative (β : ℝ) (z : ZetaZerosInTraceStrip β) :
    0 ≤ (zeroResolventTerm β 3 z).re := by
  have ht : 6 < |z.val.im| := lt_of_not_ge fun h =>
    ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six z.prop.2.1 z.prop.2.2.1 h z.prop.1
  rw [zeroResolventTerm, Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  apply mul_nonneg (Nat.cast_nonneg _)
  simp only [one_div,Complex.sub_re,Complex.inv_re,Complex.normSq_apply,Complex.sub_im]
  convert (cyclic_GeometricCutoff_kernel_pos z.prop.2.1 z.prop.2.2.1 ht).le using 1
  norm_num [pow_two,Complex.div_ofNat_re,Complex.div_ofNat_im]

private theorem cyclic_GeometricCutoff_resolvent_summable (β : ℝ) (hβ : 0 < β) :
    Summable (zeroResolventTerm β 3) := by
  obtain ⟨C,_,hb⟩ := regularized_spectral_domination_any_window β 3 (by norm_num)
  exact
    ((weighted_zero_summability β hβ).mul_left C).of_norm_bounded fun z =>
      le_of_tendsto' (cyclic_GeometricCutoff_traceTerm_limit β 3 (by norm_num) z).norm (fun n => hb n z)

theorem central_resolvent_le_window (β : ℝ) (hβ : 0 < β) :
    (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
      (analyticOrderNatAt riemannZeta z.val : ℂ) *
        (1/((3:ℂ)-z.val)-1/((5/2:ℂ)-z.val))).re ≤ (regularizedSpectral β 3).re := by
  let Z := {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}
  let i (z : Z) : ZetaZerosInTraceStrip β :=
    ⟨z.val,z.prop.1, by rw [z.prop.2]; norm_num, by rw [z.prop.2]; norm_num,
      by simpa [z.prop.2] using hβ⟩
  have hi : Function.Injective i := fun a b h => Subtype.ext <|
    congrArg (fun s : ZetaZerosInTraceStrip β => s.val) h
  have hs := cyclic_GeometricCutoff_resolvent_summable β hβ
  have hs' : Summable (fun z : Z => zeroResolventTerm β 3 (i z)) := hs.comp_injective hi
  change (∑' z : Z, (zeroResolventTerm β 3) (i z)).re ≤ (∑' z, zeroResolventTerm β 3 z).re
  rw [Complex.re_tsum hs', Complex.re_tsum hs]
  exact tsum_comp_le_tsum_of_inj (Complex.hasSum_re hs.hasSum).summable (cyclic_GeometricCutoff_term_nonnegative β) hi

theorem cutoff_polar_sub_geometric_limit :
    Tendsto (fun n : ℕ => (cutoffPolar n 3 - (cutoffArch n 3 + cutoffPrime n 3)).re)
      atTop (𝓝 (regularizedSpectral (1/2) 3).re) :=
  geometric_cutoff_limit

theorem central_resolvent_eq_window_of_RH (hRH : RiemannHypothesis) (β : ℝ) (hβ : 0 < β) :
    (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
      (analyticOrderNatAt riemannZeta z.val : ℂ) *
        (1/((3:ℂ)-z.val)-1/((5/2:ℂ)-z.val))) = regularizedSpectral β 3 := by
  let Z := {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}
  have hline (w : ZetaZerosInTraceStrip β) : w.val.re=1/2 := by
    apply hRH _ w.prop.1
    · rintro ⟨n,e⟩
      have hr := w.prop.2.1
      rw [e] at hr
      norm_num at hr
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · intro e
      have hr := w.prop.2.2.1
      simp [e] at hr
  let e : Z ≃ ZetaZerosInTraceStrip β :=
    { toFun := fun z => ⟨z.val,z.prop.1, by rw [z.prop.2]; norm_num, by rw [z.prop.2]; norm_num,
          by simpa [z.prop.2] using hβ⟩
      invFun := fun w => ⟨w.val,w.prop.1,hline w⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.tsum_eq (zeroResolventTerm β 3)

theorem central_resolvent_re_eq_full_of_RH (hRH : RiemannHypothesis) :
    (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
      (analyticOrderNatAt riemannZeta z.val : ℂ) *
        (1/((3:ℂ)-z.val)-1/((5/2:ℂ)-z.val))).re = (regularizedSpectral (1/2) 3).re :=
  congrArg Complex.re (central_resolvent_eq_window_of_RH hRH (1/2) (by norm_num))

/-- The spectral mass of a positive-width strip splits into its critical-line and
off-line parts. Both are absolutely convergent. -/
theorem window_sub_central_eq_offline (β : ℝ) (hβ : 0 < β) :
    (regularizedSpectral β 3).re -
      (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
        (analyticOrderNatAt riemannZeta z.val : ℂ) *
          (1/((3:ℂ)-z.val)-1/((5/2:ℂ)-z.val))).re =
      ∑' z : {z : ZetaZerosInTraceStrip β // z.val.re ≠ 1/2},
        (zeroResolventTerm β 3 z.val).re := by
  let Z := {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}
  let S : Set (ZetaZerosInTraceStrip β) := {z | z.val.re=1/2}
  let e : Z ≃ S :=
    { toFun := fun z => ⟨⟨z.val,z.prop.1,by rw [z.prop.2]; norm_num,by rw [z.prop.2]; norm_num,
          by simpa [z.prop.2] using hβ⟩, z.prop.2⟩
      invFun := fun w => ⟨w.val.val,w.val.prop.1,w.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let f := zeroResolventTerm β 3
  have h := (cyclic_GeometricCutoff_resolvent_summable β hβ).tsum_subtype_add_tsum_subtype_compl S
  have he := e.tsum_eq (fun w : S => f w.val)
  change (∑' w : S, f w.val) + (∑' w : (Sᶜ : Set _), f w.val) = ∑' w, f w at h
  rw [← he] at h
  have ht := congrArg Complex.re h
  have hcomp : Summable (fun w : (Sᶜ : Set _ ) => f w.val) :=
    (cyclic_GeometricCutoff_resolvent_summable β hβ).subtype (· ∈ Sᶜ)
  rw [Complex.add_re, Complex.re_tsum hcomp] at ht
  exact sub_eq_of_eq_add' ht.symm

theorem full_sub_central_eq_offline :
    (regularizedSpectral (1/2) 3).re -
      (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
        (analyticOrderNatAt riemannZeta z.val : ℂ) *
          (1/((3:ℂ)-z.val)-1/((5/2:ℂ)-z.val))).re =
      ∑' z : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2},
        (zeroResolventTerm (1/2) 3 z.val).re :=
  window_sub_central_eq_offline (1/2) (by norm_num)

end ThetaGeometricLimit

end StandaloneGeometricCutoff

section StandaloneTraceRateDetection

open MasulloRH Set Filter MeasureTheory
open scoped Topology
namespace MasulloRH.TraceRate
noncomputable section

private theorem cyclic_TraceRateDetection_rational_lower {b y : ℝ} (hb : 0<b) (hb' : b<1) (hy : 6 < |y|) :
    1/(8*(1+y^2)) ≤ (3-b)/((3-b)^2+y^2) - (5/2-b)/((5/2-b)^2+y^2) := by
  let t := y^2
  let a := 3-b
  let d := 5/2-b
  have ht : 36<t := by dsimp [t]; nlinarith [sq_abs y,sq_nonneg (|y|-6)]
  have ha : 0<a := by dsimp [a]; linarith
  have hd : 0<d := by dsimp [d]; linarith
  have hda : a-d=1/2 := by dsimp [a,d]; ring
  have ha3 : a≤3 := by dsimp [a]; linarith
  have hd3 : d≤3 := by dsimp [d]; linarith
  have h9 : a*d≤9 := by nlinarith only [mul_le_mul ha3 hd3 hd.le (by norm_num : (0:ℝ)≤3)]
  have hs1 : a^2+t ≤ 3/2*t := by nlinarith [sq_le_sq' (by linarith : -3≤a) ha3]
  have hs2 : d^2+t ≤ 3/2*t := by nlinarith [sq_le_sq' (by linarith : -3≤d) hd3]
  have h1 : 0 < a^2+t := by linarith [sq_nonneg a]
  have h2 : 0 < d^2+t := by linarith [sq_nonneg d]
  have hden := mul_le_mul hs1 hs2 h2.le (by linarith : 0≤3/2*t)
  change 1/(8*(1+t)) ≤ a/(a^2+t)-d/(d^2+t)
  rw [div_sub_div _ _ h1.ne' h2.ne',div_le_div_iff₀ (by linarith) (mul_pos h1 h2)]
  rw [show a*(d^2+t)-(a^2+t)*d=(a-d)*(t-a*d) by ring]
  have hnum2 : (t/3) ≤ (a-d)*(t-a*d) := by rw [hda]; linarith
  have hn := mul_le_mul_of_nonneg_left hnum2 (show 0≤8*(1+t) by linarith)
  nlinarith [sq_nonneg t]

theorem weight_le_resolvent (z : ZetaZerosInTraceStrip (1/2)) :
    zeroDecayWeight (1/2) z / 8 ≤ (zeroResolventTerm (1/2) 3 z).re := by
  have ht : 6 < |z.val.im| := lt_of_not_ge fun h =>
    ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six z.prop.2.1 z.prop.2.2.1 h z.prop.1
  rw [zeroResolventTerm,Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  rw [zeroDecayWeight,div_div, mul_comm (1+_)]
  rw [div_eq_mul_one_div]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  simp only [one_div,Complex.sub_re,Complex.inv_re,Complex.normSq_apply,Complex.sub_im]
  convert cyclic_TraceRateDetection_rational_lower z.prop.2.1 z.prop.2.2.1 ht using 1 <;>
    norm_num [pow_two,Complex.div_ofNat_re,Complex.div_ofNat_im] <;> rfl

private abbrev cyclic_TraceRateDetection_Off := {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2}

private theorem cyclic_TraceRateDetection_order_pos (z : ZetaZerosInTraceStrip (1/2)) : 0 < analyticOrderNatAt riemannZeta z.val := by
  have h1 : z.val ≠ 1 := fun h => (not_lt_of_ge (le_of_eq (congrArg Complex.re h).symm)) z.prop.2.2.1
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hf := analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
    (show (2:ℂ) ∈ ({1}:Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)
  have hne := (analyticOn_riemannZeta _ h1).analyticOrderAt_ne_zero.mpr z.prop.1
  exact Nat.pos_of_ne_zero (fun h => (ENat.toNat_eq_zero.mp h).elim hne hf)

private theorem cyclic_TraceRateDetection_res_summable_off : Summable (fun z : cyclic_TraceRateDetection_Off => (zeroResolventTerm (1/2) 3 z.val).re) := by
  obtain ⟨C,_,hc⟩ := regularized_spectral_domination_any_window (1/2) 3 (by norm_num)
  have hm : Summable (zeroResolventTerm (1/2) 3) := by
    apply ((weighted_zero_summability (1/2) (by norm_num)).mul_left C).of_norm_bounded
    intro z
    have h := regularized_mellin_limit 3 (z.val-1/2)
      (by simp only [Complex.sub_re]; norm_num; linarith [z.prop.2.2.1])
      (by simp only [Complex.sub_re]; norm_num; linarith [z.prop.2.2.1])
    have he := h.const_mul (analyticOrderNatAt riemannZeta z.val:ℂ)
    apply le_of_tendsto' (x := (atTop : Filter ℕ)) (f := fun n => ‖zetaTraceTerm (regularizedTraceTest n 3) (1/2) z‖)
    · convert he.norm using 1 <;> dsimp [zeroResolventTerm,zetaTraceTerm] <;> congr 2 <;> ring
    · exact fun n => hc n z
  exact (Complex.hasSum_re (hm.subtype _).hasSum).summable

theorem finite_offline_mass (H : ℝ) (_hH : 0≤H) (s : Finset cyclic_TraceRateDetection_Off) (hs : ∀ z∈s, |z.val.val.im|≤H) :
    (∑ z ∈ s, (analyticOrderNatAt riemannZeta z.val.val:ℝ)) ≤
      8*(1+H^2)*(∑' z : cyclic_TraceRateDetection_Off,(zeroResolventTerm (1/2) 3 z.val).re) := by
  have hDpos (z : cyclic_TraceRateDetection_Off) : 0 ≤ (zeroResolventTerm (1/2) 3 z.val).re :=
    le_trans (by dsimp [zeroDecayWeight]; positivity) (weight_le_resolvent z.val)
  have hE := cyclic_TraceRateDetection_res_summable_off.sum_le_tsum s (fun z _ => hDpos z)
  calc
    _ ≤ ∑ z ∈ s, 8*(1+H^2)*(zeroResolventTerm (1/2) 3 z.val).re := by
      apply Finset.sum_le_sum
      intro z hz
      have h := weight_le_resolvent z.val
      rw [zeroDecayWeight,div_div,div_le_iff₀ (by positivity)] at h
      have hi := pow_le_pow_left₀ (abs_nonneg _) (hs z hz) 2
      rw [sq_abs] at hi
      exact h.trans (by nlinarith only [mul_nonneg (sub_nonneg.mpr hi) (hDpos z)])
    _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hE (by positivity)

theorem offline_single_detected (H : ℝ) (hH : 0≤H) (z : cyclic_TraceRateDetection_Off) (hz : |z.val.val.im|≤H) :
    1 ≤ 8*(1+H^2)*(∑' w : cyclic_TraceRateDetection_Off,(zeroResolventTerm (1/2) 3 w.val).re) := by
  classical
  have hh := finite_offline_mass H hH {z} (by simpa using hz)
  simp only [Finset.sum_singleton] at hh
  exact (show (1:ℝ) ≤ analyticOrderNatAt riemannZeta z.val.val by exact_mod_cast cyclic_TraceRateDetection_order_pos z.val).trans hh
end
end MasulloRH.TraceRate

end StandaloneTraceRateDetection

section StandaloneTraceRateMellin

open MeasureTheory Set Filter MasulloRH
open scoped Topology
namespace MasulloRH.TraceRate
noncomputable section

private def cyclic_TraceRateMellin_cut (N x : ℝ) := Real.smoothTransition (N*x-1) * (1-Real.smoothTransition (x/N-1))
private def cyclic_TraceRateMellin_kern (w : ℂ) (x : ℝ) :=
  Complex.exp ((w-5/2)*x) - Complex.exp ((w-2)*x)

private lemma cyclic_TraceRateMellin_cut_cont (N : ℝ) : Continuous (cyclic_TraceRateMellin_cut N) := by
  unfold cyclic_TraceRateMellin_cut; fun_prop (disch := first | exact Real.smoothTransition.continuous)
private lemma cyclic_TraceRateMellin_cut_bounds (N x : ℝ) : 0≤cyclic_TraceRateMellin_cut N x ∧ cyclic_TraceRateMellin_cut N x≤1 := by
  unfold cyclic_TraceRateMellin_cut
  have hA := Real.smoothTransition.nonneg (N*x-1)
  have hB := Real.smoothTransition.le_one (N*x-1)
  have hC := Real.smoothTransition.nonneg (x/N-1)
  have hD := Real.smoothTransition.le_one (x/N-1)
  exact ⟨mul_nonneg hA (sub_nonneg.mpr hD),(mul_le_of_le_one_right hA (by linarith)).trans hB⟩

private lemma cyclic_TraceRateMellin_cut_one {N x : ℝ} (hN : 0<N) (h : 2/N≤x) (h' : x≤N) : cyclic_TraceRateMellin_cut N x=1 := by
  have hx := (div_le_iff₀ hN).mp h
  have hd := (div_le_one hN).mpr h'
  simp [cyclic_TraceRateMellin_cut,Real.smoothTransition.one_of_one_le (by nlinarith : 1≤N*x-1),
    Real.smoothTransition.zero_of_nonpos (by linarith : x/N-1≤0)]

private lemma cyclic_TraceRateMellin_kern_int {w : ℂ} (hw : w.re ≤ 1/2) :
    IntegrableOn (cyclic_TraceRateMellin_kern w) (Ioi 0) := by
  have h1 : (w-5/2).re < 0 := by norm_num [Complex.sub_re] at *; linarith
  have h2 : (w-2).re < 0 := by norm_num [Complex.sub_re] at *; linarith
  exact (integrableOn_exp_mul_complex_Ioi h1 0).sub (integrableOn_exp_mul_complex_Ioi h2 0)

private lemma cyclic_TraceRateMellin_kern_integral {w : ℂ} (hw : w.re ≤ 1/2) :
    (∫ x in Ioi 0, cyclic_TraceRateMellin_kern w x) = 1/((3:ℂ)-1/2-w)-1/(2-w) := by
  have h1 : (w-5/2).re < 0 := by norm_num [Complex.sub_re] at *; linarith
  have h2 : (w-2).re < 0 := by norm_num [Complex.sub_re] at *; linarith
  unfold cyclic_TraceRateMellin_kern
  rw [integral_sub (integrableOn_exp_mul_complex_Ioi h1 0) (integrableOn_exp_mul_complex_Ioi h2 0),
    integral_exp_mul_complex_Ioi h1,integral_exp_mul_complex_Ioi h2]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  rw [show (3:ℂ)-1/2-w=-(w-5/2) by ring,show (2:ℂ)-w=-(w-2) by ring]
  simp only [div_neg,neg_div]

private lemma cyclic_TraceRateMellin_kern_norm {w : ℂ} (hw : w.re≤1/2) {x : ℝ} (hx : 0≤x) :
    ‖cyclic_TraceRateMellin_kern w x‖ ≤ x/2 ∧ ‖cyclic_TraceRateMellin_kern w x‖ ≤ Real.exp ((-3/2)*x) := by
  have he : cyclic_TraceRateMellin_kern w x = Complex.exp ((w-2)*x) * ((Real.exp (-x/2):ℝ)-1:ℂ) := by
    unfold cyclic_TraceRateMellin_kern
    rw [mul_sub, mul_one,Complex.ofReal_exp,← Complex.exp_add]
    congr 2; push_cast; ring
  have hh : (w-2).re*x ≤ (-3/2)*x := by norm_num [Complex.sub_re]; nlinarith [mul_nonneg (sub_nonneg.mpr hw) hx]
  have hr : ‖cyclic_TraceRateMellin_kern w x‖ = Real.exp ((w-2).re*x) * (1-Real.exp (-x/2)) := by
    rw [he,norm_mul,Complex.norm_exp]
    have hn : ((Real.exp (-x/2):ℝ):ℂ)-1 = ((Real.exp (-x/2)-1:ℝ):ℂ) := by push_cast; rfl
    rw [hn,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith [Real.exp_le_one_iff.mpr (show -x/2≤0 by linarith)] : Real.exp (-x/2)-1≤0)]
    simp [Complex.mul_re]
  rw [hr]
  have hA : 1-Real.exp (-x/2) ≤ x/2 := by linarith [Real.add_one_le_exp (-x/2)]
  have hB := Real.exp_le_one_iff.mpr (hh.trans (by nlinarith : (-3/2)*x≤0))
  have hC : 0≤1-Real.exp (-x/2) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  exact ⟨(mul_le_of_le_one_left hC hB).trans hA,
    (mul_le_of_le_one_right (Real.exp_nonneg _) (by linarith [Real.exp_pos (-x/2)])).trans (Real.exp_le_exp.mpr hh)⟩

private lemma cyclic_TraceRateMellin_mellin_log (f : ℝ → ℂ) (w : ℂ) :
    mellin f w = ∫ x : ℝ, Complex.exp (w*x)*f (Real.exp x) := by
  have hd : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have him : Real.exp '' univ = Ioi 0 := by rw [image_univ,Real.range_exp]
  unfold mellin
  rw [← him,integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd Real.exp_injective.injOn,setIntegral_univ]
  apply integral_congr_ae; filter_upwards with x
  rw [abs_of_pos (Real.exp_pos _),Complex.real_smul,smul_eq_mul,Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),← Complex.ofReal_log (Real.exp_nonneg _),Real.log_exp,
    Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
  congr 2; ring

private lemma cyclic_TraceRateMellin_reg_log (n : ℕ) (w : ℂ) :
    mellin (regularizedTraceTest n 3) w = ∫ x in Ioi 0, ((cyclic_TraceRateMellin_cut (n+1) x:ℝ):ℂ)*cyclic_TraceRateMellin_kern w x := by
  rw [cyclic_TraceRateMellin_mellin_log,← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae; filter_upwards with x
  by_cases hx : 0<x
  · rw [indicator_of_mem (show x ∈ Ioi 0 from hx)]
    have ht : 1<Real.exp x := Real.one_lt_exp_iff.mpr hx
    simp only [regularizedTraceTest,traceLogCutoff,if_pos ht,Real.log_exp]
    change Complex.exp (w*x)*((cyclic_TraceRateMellin_cut (n+1) x:ℂ)*(_-_))=_
    rw [show ∀ z : ℂ, ((Real.exp x:ℝ):ℂ)^z = Complex.exp (x*z) from fun z => by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
        ← Complex.ofReal_log (Real.exp_nonneg _),Real.log_exp]]
    rw [show ((Real.exp x:ℝ):ℂ)^(-2:ℂ)=Complex.exp (x*(-2:ℂ)) by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
        ← Complex.ofReal_log (Real.exp_nonneg _),Real.log_exp]]
    unfold cyclic_TraceRateMellin_kern; rw [mul_left_comm, mul_sub,← Complex.exp_add,← Complex.exp_add]
    congr 2 <;> congr 1 <;> ring
  · rw [indicator_of_notMem (show x ∉ Ioi 0 from hx)]
    simp [regularizedTraceTest,not_lt.mpr (Real.exp_le_one_iff.mpr (not_lt.mp hx))]

private lemma cyclic_TraceRateMellin_cut_int {w : ℂ} (hw : w.re≤1/2) (N : ℝ) :
    IntegrableOn (fun x => ((cyclic_TraceRateMellin_cut N x:ℝ):ℂ)*cyclic_TraceRateMellin_kern w x) (Ioi 0) := by
  apply (cyclic_TraceRateMellin_kern_int hw).norm.mono'
  · apply Continuous.aestronglyMeasurable
    have h : Continuous (cyclic_TraceRateMellin_kern w) := by unfold cyclic_TraceRateMellin_kern; fun_prop
    exact (Complex.continuous_ofReal.comp (cyclic_TraceRateMellin_cut_cont N)).mul h
  · filter_upwards with x
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (cyclic_TraceRateMellin_cut_bounds N x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (cyclic_TraceRateMellin_cut_bounds N x).2

private lemma cyclic_TraceRateMellin_error_dom {w : ℂ} (hw : w.re≤1/2) {N x : ℝ} (hN : 0<N) (hx : 0<x) :
    ‖((cyclic_TraceRateMellin_cut N x:ℝ):ℂ)*cyclic_TraceRateMellin_kern w x-cyclic_TraceRateMellin_kern w x‖ ≤
      (Ioc 0 (2/N)).indicator (fun y : ℝ => y/2) x + (Ioi N).indicator (fun y : ℝ => Real.exp ((-3/2)*y)) x := by
  have hc := cyclic_TraceRateMellin_cut_bounds N x
  have hh : ‖((cyclic_TraceRateMellin_cut N x:ℝ):ℂ)*cyclic_TraceRateMellin_kern w x-cyclic_TraceRateMellin_kern w x‖ ≤ ‖cyclic_TraceRateMellin_kern w x‖ := by
    rw [← sub_one_mul,show ((cyclic_TraceRateMellin_cut N x:ℝ):ℂ)-1=((cyclic_TraceRateMellin_cut N x-1:ℝ):ℂ) by push_cast; rfl,
      norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hc.2)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  have hd := cyclic_TraceRateMellin_kern_norm hw hx.le
  by_cases ha : x≤2/N
  · rw [indicator_of_mem (show x∈Ioc 0 (2/N) from ⟨hx,ha⟩)]
    exact (hh.trans hd.1).trans (le_add_of_nonneg_right <| indicator_nonneg (fun y _ => Real.exp_nonneg _) _)
  · rw [indicator_of_notMem (show x ∉ Ioc 0 (2/N) from fun z => ha z.2),zero_add]
    by_cases hb : N<x
    · rw [indicator_of_mem (show x ∈ Ioi N from hb)]; exact hh.trans hd.2
    · rw [indicator_of_notMem (show x ∉ Ioi N from hb),cyclic_TraceRateMellin_cut_one hN (not_le.mp ha).le (not_lt.mp hb)]; simp

private lemma cyclic_TraceRateMellin_err_integral {w : ℂ} (hw : w.re≤1/2) {N : ℝ} (hN : 0<N) :
    ‖(∫ x in Ioi 0, ((cyclic_TraceRateMellin_cut N x:ℝ):ℂ)*cyclic_TraceRateMellin_kern w x)-(∫ x in Ioi 0,cyclic_TraceRateMellin_kern w x)‖ ≤
      1/N^2+(2/3)*Real.exp ((-3/2)*N) := by
  let V (x : ℝ) := (Ioc 0 (2/N)).indicator (fun y : ℝ => y/2) x
  let T (x : ℝ) := (Ioi N).indicator (fun y : ℝ => Real.exp ((-3/2)*y)) x
  have hV : Integrable V := (integrable_indicator_iff measurableSet_Ioc).mpr
    ((continuous_id.div_const 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have hT : Integrable T := (integrable_indicator_iff measurableSet_Ioi).mpr
    (integrableOn_exp_mul_Ioi (by norm_num : (-3/2:ℝ)<0) N)
  rw [← integral_sub (cyclic_TraceRateMellin_cut_int hw _) (cyclic_TraceRateMellin_kern_int hw)]
  have hbound := integral_mono_ae (((cyclic_TraceRateMellin_cut_int hw N).sub (cyclic_TraceRateMellin_kern_int hw)).norm)
    ((hV.add hT).integrableOn (s:=Ioi 0))
    ((ae_restrict_mem measurableSet_Ioi).mono fun _ hx => cyclic_TraceRateMellin_error_dom hw hN hx)
  apply (norm_integral_le_integral_norm _).trans (hbound.trans ?_)
  have hp : 0≤2/N := by positivity
  have hIV : (∫ x in Ioi 0,V x) = 1/N^2 := by
    dsimp [V]; rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (fun x h => h.1), ← intervalIntegral.integral_of_le hp,intervalIntegral.integral_div,
      integral_id]; ring
  have hIT : (∫ x in Ioi 0,T x) = (2/3)*Real.exp ((-3/2)*N) := by
    dsimp [T]; rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi hN.le),integral_exp_mul_Ioi (by norm_num : (-3/2:ℝ)<0)]; ring
  change (∫ x in Ioi 0,V x+T x) ≤ _
  rw [integral_add hV.integrableOn hT.integrableOn,hIV,hIT]

theorem regularized_mellin_error (n : ℕ) (w : ℂ) (hw : w.re≤1/2) :
    ‖mellin (regularizedTraceTest n 3) w - (1/((3:ℂ)-1/2-w)-1/(2-w))‖ ≤
      1/((n:ℝ)+1)^2+(2/3)*Real.exp ((-3/2)*((n:ℝ)+1)) := by
  rw [cyclic_TraceRateMellin_reg_log, ← cyclic_TraceRateMellin_kern_integral hw]; exact cyclic_TraceRateMellin_err_integral hw (by positivity)

theorem regularized_mellin_error_sq (n : ℕ) (w : ℂ) (hw : w.re≤1/2) :
    ‖mellin (regularizedTraceTest n 3) w - (1/((3:ℂ)-1/2-w)-1/(2-w))‖ ≤ 2/((n:ℝ)+1)^2 := by
  apply (regularized_mellin_error n w hw).trans
  let N : ℝ := n+1
  have hN : 0<N := by dsimp [N]; positivity
  change 1/N^2+ (2/3)*Real.exp ((-3/2)*N) ≤ 2/N^2
  have h := Real.quadratic_le_exp_of_nonneg (by positivity : 0≤(3/2)*N)
  rw [show (-3/2)*N= -((3/2)*N) by ring,Real.exp_neg]
  field_simp [hN.ne',Real.exp_pos]
  rw [show N*3/2=(3/2)*N by ring]
  nlinarith only [h, hN.le, sq_nonneg N]

end
end MasulloRH.TraceRate

end StandaloneTraceRateMellin

section StandaloneTraceRateSpectral

open Set Filter MeasureTheory
open scoped Topology
namespace MasulloRH.TraceRate
noncomputable section

private abbrev cyclic_TraceRateSpectral_Z := ZetaZerosInTraceStrip (1/2)
private abbrev cyclic_TraceRateSpectral_m (z : cyclic_TraceRateSpectral_Z) := analyticOrderNatAt riemannZeta z.val
private abbrev cyclic_TraceRateSpectral_wt (z : cyclic_TraceRateSpectral_Z) := zeroDecayWeight (1/2) z
private abbrev cyclic_TraceRateSpectral_res (z : cyclic_TraceRateSpectral_Z) := zeroResolventTerm (1/2) 3 z
private abbrev cyclic_TraceRateSpectral_ml (n : ℕ) (z : cyclic_TraceRateSpectral_Z) := mellin (regularizedTraceTest n 3) (z.val-1/2)

private theorem cyclic_TraceRateSpectral_term_limit (z : cyclic_TraceRateSpectral_Z) :
    Tendsto (fun n : ℕ => (cyclic_TraceRateSpectral_m z : ℂ)*cyclic_TraceRateSpectral_ml n z) atTop (𝓝 (cyclic_TraceRateSpectral_res z)) := by
  have hr : (z.val-1/2).re=z.val.re-1/2 := by simp
  have hb := z.property.2.2.1
  have h := regularized_mellin_limit 3 (z.val-1/2) (by rw [hr]; norm_num; linarith)
    (by rw [hr]; linarith)
  rw [show (3:ℂ)-1/2-(z.val-1/2)=3-z.val by ring,show (2:ℂ)-(z.val-1/2)=5/2-z.val by ring] at h
  exact h.const_mul _

private theorem cyclic_TraceRateSpectral_pointwise_low (n : ℕ) (z : cyclic_TraceRateSpectral_Z) :
    ‖(cyclic_TraceRateSpectral_m z:ℂ)*cyclic_TraceRateSpectral_ml n z-cyclic_TraceRateSpectral_res z‖ ≤ 2/((n:ℝ)+1)^2 * (cyclic_TraceRateSpectral_m z:ℝ) := by
  have h := regularized_mellin_error_sq n (z.val-1/2) (by
    have h := z.prop.2.2.1; simp only [Complex.sub_re,Complex.div_ofNat_re,Complex.one_re]; linarith)
  rw [show (3:ℂ)-1/2-(z.val-1/2)=3-z.val by ring,show (2:ℂ)-(z.val-1/2)=5/2-z.val by ring] at h
  change ‖(cyclic_TraceRateSpectral_m z:ℂ)*cyclic_TraceRateSpectral_ml n z-(cyclic_TraceRateSpectral_m z:ℂ)*_‖≤_
  rw [← mul_sub,norm_mul,Complex.norm_natCast,mul_comm (2/_)]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

private theorem cyclic_TraceRateSpectral_pointwise_truncated {C : ℝ} (hc :
    ∀ n : ℕ, ∀ z : cyclic_TraceRateSpectral_Z, ‖(cyclic_TraceRateSpectral_m z:ℂ)*cyclic_TraceRateSpectral_ml n z‖≤ C*cyclic_TraceRateSpectral_wt z) (n : ℕ) (z : cyclic_TraceRateSpectral_Z) {d : ℕ} (hd : d≤cyclic_TraceRateSpectral_m z) :
    ‖(d:ℂ)*cyclic_TraceRateSpectral_ml n z‖≤C*cyclic_TraceRateSpectral_wt z := by
  refine le_trans ?_ (hc n z)
  simp only [norm_mul,Complex.norm_natCast]
  gcongr

/-- The same estimate applies to every injectively indexed family of zeros, with multiplicities
capped away from the low-height range. -/
theorem sum_error_by_low_high {J : Type*} (i : J → cyclic_TraceRateSpectral_Z) (hi : Function.Injective i)
    (C : ℝ) (hC : 0≤C) (hc : ∀ n : ℕ, ∀ z : cyclic_TraceRateSpectral_Z, ‖(cyclic_TraceRateSpectral_m z:ℂ)*cyclic_TraceRateSpectral_ml n z‖≤C*cyclic_TraceRateSpectral_wt z)
    (n : ℕ) (d : J → ℕ) (hd : ∀ j, d j≤cyclic_TraceRateSpectral_m (i j)) (S : Set cyclic_TraceRateSpectral_Z)
    (hfull : ∀ j, i j∈S → d j=cyclic_TraceRateSpectral_m (i j))
    (hL : Summable (S.indicator (fun z => (cyclic_TraceRateSpectral_m z:ℝ)))) :
    ‖(∑' j : J,(d j:ℂ)*cyclic_TraceRateSpectral_ml n (i j))-(∑' j : J,cyclic_TraceRateSpectral_res (i j))‖ ≤
      2/((n:ℝ)+1)^2*(∑' z : cyclic_TraceRateSpectral_Z,S.indicator (fun a => (cyclic_TraceRateSpectral_m a:ℝ)) z)+
        (2*C)*(∑' z : cyclic_TraceRateSpectral_Z,Sᶜ.indicator cyclic_TraceRateSpectral_wt z) := by
  classical
  have hw := weighted_zero_summability (1/2) (by norm_num)
  have hR (z : cyclic_TraceRateSpectral_Z) : ‖cyclic_TraceRateSpectral_res z‖≤C*cyclic_TraceRateSpectral_wt z := le_of_tendsto' (cyclic_TraceRateSpectral_term_limit z).norm (fun n => hc n z)
  have hiW : Summable (fun j => C*cyclic_TraceRateSpectral_wt (i j)) := (hw.comp_injective hi).mul_left C
  have ha := hiW.of_norm_bounded (fun j => cyclic_TraceRateSpectral_pointwise_truncated hc n (i j) (hd j))
  have hb := hiW.of_norm_bounded (fun j => hR (i j))
  let a := 2/((n:ℝ)+1)^2
  let B (z : cyclic_TraceRateSpectral_Z) := a*S.indicator (fun t => (cyclic_TraceRateSpectral_m t:ℝ)) z+(2*C)*Sᶜ.indicator cyclic_TraceRateSpectral_wt z
  have hnB (z : cyclic_TraceRateSpectral_Z) : 0≤B z := by
    dsimp [B]; apply add_nonneg
    · exact mul_nonneg (by dsimp [a]; positivity) (indicator_nonneg (fun _ _ => Nat.cast_nonneg _) _)
    · apply mul_nonneg (by positivity)
      exact indicator_nonneg (fun z _ => by dsimp [cyclic_TraceRateSpectral_wt,zeroDecayWeight]; positivity) _
  have hH : Summable (Sᶜ.indicator cyclic_TraceRateSpectral_wt) := hw.indicator _
  have hB : Summable B := (hL.mul_left a).add (hH.mul_left (2*C))
  have hpt (j : J) : ‖(d j:ℂ)*cyclic_TraceRateSpectral_ml n (i j)-cyclic_TraceRateSpectral_res (i j)‖ ≤ B (i j) := by
    by_cases h : i j∈S
    · simpa [B,a,h,hfull j h] using cyclic_TraceRateSpectral_pointwise_low n (i j)
    · simpa [B,h,two_mul,add_mul] using (norm_sub_le _ _).trans
        (add_le_add (cyclic_TraceRateSpectral_pointwise_truncated hc n (i j) (hd j)) (hR (i j)))
  rw [← ha.tsum_sub hb]
  apply (norm_tsum_le_tsum_norm (ha.sub hb).norm).trans
  apply ((ha.sub hb).norm.tsum_le_tsum hpt (hB.comp_injective hi)).trans
  apply (tsum_comp_le_tsum_of_inj hB hnB hi).trans_eq
  dsimp only [B]
  rw [(hL.mul_left a).tsum_add (hH.mul_left (2*C)),tsum_mul_left,tsum_mul_left]

private abbrev cyclic_TraceRateSpectral_ZC := {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}
private def cyclic_TraceRateSpectral_em (z : cyclic_TraceRateSpectral_ZC) : cyclic_TraceRateSpectral_Z :=
  ⟨z.val,z.property.1,by rw [z.property.2]; norm_num,by rw [z.property.2]; norm_num,
    by rw [z.property.2]; norm_num⟩
private theorem cyclic_TraceRateSpectral_em_inj : Function.Injective cyclic_TraceRateSpectral_em := fun _ _ hh =>
  Subtype.ext (congrArg (fun z : cyclic_TraceRateSpectral_Z => z.val) hh)

/-- Common full-strip and critical-line spectral error estimate in terms of the low-height count,
high-height weighted tail, and the cutoff for multiplicities. -/
theorem spectral_rates_of_height_estimates (S : ℕ → Set cyclic_TraceRateSpectral_Z)
    (L H : ℝ) (hL : 0≤L) (hH : 0≤H)
    (h : ∀ᶠ n : ℕ in atTop,
      Summable ((S n).indicator (fun z => (cyclic_TraceRateSpectral_m z:ℝ))) ∧
      (∑' z : cyclic_TraceRateSpectral_Z,(S n).indicator (fun a => (cyclic_TraceRateSpectral_m a:ℝ)) z)≤L*((n:ℝ)+1)*Real.log ((n:ℝ)+2) ∧
      (∑' z : cyclic_TraceRateSpectral_Z,(S n)ᶜ.indicator cyclic_TraceRateSpectral_wt z)≤H*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) ∧
      ∀ z∈S n, cyclic_TraceRateSpectral_m z≤n+1) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop,
      ‖cutoffSpectral (1/2) n 3-regularizedSpectral (1/2) 3‖≤C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) ∧
      ‖(∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
        ((min (analyticOrderNatAt riemannZeta z.val) ⌈((n:ℝ)+1)-1/2⌉₊:ℕ):ℂ) *
          mellin (regularizedTraceTest n 3) (z.val-1/2))-
        (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}, (analyticOrderNatAt riemannZeta z.val:ℂ) *
          (1/((3:ℂ)-z.val)-1/(5/2-z.val)))‖≤C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) := by
  obtain ⟨B,hB,hd⟩ := regularized_spectral_domination_any_window (1/2) 3 (by norm_num)
  refine ⟨2*L+2*B*H+1,by positivity,?_⟩
  filter_upwards [h] with n hn
  obtain ⟨hs,hl,hh,hm⟩ := hn
  have hp : 0<((n:ℝ)+1) := by positivity
  have hnlog : 0≤Real.log ((n:ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have each {J : Type} (i : J → cyclic_TraceRateSpectral_Z) (hi : Function.Injective i) (d : J → ℕ)
      (hle : ∀ j, d j≤cyclic_TraceRateSpectral_m (i j)) (he : ∀ j, i j∈S n → d j=cyclic_TraceRateSpectral_m (i j)) :
      ‖(∑' j : J,(d j:ℂ)*cyclic_TraceRateSpectral_ml n (i j))-(∑' j : J,cyclic_TraceRateSpectral_res (i j))‖ ≤
        (2*L+2*B*H+1)*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) := by
    apply (sum_error_by_low_high i hi B hB.le hd n d hle (S n) he hs).trans
    apply (add_le_add (mul_le_mul_of_nonneg_left hl (by positivity)) (mul_le_mul_of_nonneg_left hh (by positivity))).trans
    have hr : 2/((n:ℝ)+1)^2*(L*((n:ℝ)+1)*Real.log ((n:ℝ)+2))+
        (2*B)*(H*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)))=
        (2*L+2*B*H)*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) := by field_simp [hp.ne']
    rw [hr]; exact mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hnlog hp.le)
  refine ⟨each id Function.injective_id cyclic_TraceRateSpectral_m (fun _ => le_rfl) (fun _ _ => rfl),?_⟩
  let d (j : cyclic_TraceRateSpectral_ZC) := min (cyclic_TraceRateSpectral_m (cyclic_TraceRateSpectral_em j)) ⌈((n:ℝ)+1)-1/2⌉₊
  apply each cyclic_TraceRateSpectral_em cyclic_TraceRateSpectral_em_inj d (fun _ => min_le_left _ _)
  intro j hj
  apply min_eq_left
  have hnceil : n+1 ≤ ⌈((n:ℝ)+1)-1/2⌉₊ := by
    apply Nat.add_one_le_iff.mpr
    exact (Nat.lt_ceil).mpr (by linarith)
  exact (hm (cyclic_TraceRateSpectral_em j) hj).trans hnceil

private lemma cyclic_TraceRateSpectral_finite_initial_uniform_bound (u v : ℕ → ℝ) (hu : ∀ n,0≤u n)
    (hv : ∀ n,0<v n) {C : ℝ} (hC : 0<C) (h : ∀ᶠ n in atTop,u n≤C*v n) :
    ∃ B : ℝ, 0<B ∧ ∀ n, u n≤B*v n := by
  obtain ⟨k,hk⟩ := eventually_atTop.mp h
  let D := ∑ j ∈ Finset.range k,u j/v j
  have hD : 0≤D := Finset.sum_nonneg (fun j _ => div_nonneg (hu j) (hv j).le)
  refine ⟨C+D,by positivity,fun n => ?_⟩
  by_cases hn : k≤n
  · exact (hk n hn).trans (mul_le_mul_of_nonneg_right (by linarith) (hv n).le)
  · have hl : u n/v n≤D := Finset.single_le_sum (f:=fun j => u j/v j)
       (fun j _ => div_nonneg (hu j) (hv j).le) (Finset.mem_range.mpr (lt_of_not_ge hn))
    exact (div_le_iff₀ (hv n)).mp (hl.trans (by linarith))

theorem spectral_rate_all_of_eventually (u v : ℕ → ℂ) {C : ℝ} (hC : 0<C)
    (h : ∀ᶠ n : ℕ in atTop, ‖u n‖≤C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) ∧
      ‖v n‖≤C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1))) :
    ∃ B : ℝ, 0<B ∧ ∀ n : ℕ, ‖u n‖≤B*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) ∧
      ‖v n‖≤B*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) := by
  have hv (n : ℕ) : 0<Real.log ((n:ℝ)+2)/((n:ℝ)+1) :=
    div_pos (Real.log_pos (by linarith [Nat.cast_nonneg (α:=ℝ) n])) (by positivity)
  obtain ⟨B,hB,hb⟩ := cyclic_TraceRateSpectral_finite_initial_uniform_bound (fun n => max ‖u n‖ ‖v n‖) _
    (fun n => (norm_nonneg _).trans (le_max_left _ _)) hv hC (h.mono (fun n hn => max_le hn.1 hn.2))
  exact ⟨B,hB,fun n => ⟨(le_max_left _ _).trans (hb n),(le_max_right _ _).trans (hb n)⟩⟩

end
end MasulloRH.TraceRate

end StandaloneTraceRateSpectral

section StandaloneTraceRatePhysical

open MasulloRH MasulloGRH Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace MasulloRH.TraceRate
noncomputable section

private abbrev cyclic_TraceRatePhysical_Op (n : ℕ) := rationalThetaAnnihilator ((n:ℝ)+1) →L[ℂ] rationalThetaAnnihilator ((n:ℝ)+1)

private theorem cyclic_TraceRatePhysical_op_trace (n : ℕ) (T : cyclic_TraceRatePhysical_Op n) (hT : IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) T) :
    operatorTrace T =
      ∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
        ((min (analyticOrderNatAt riemannZeta z.val) ⌈((n:ℝ)+1)-1/2⌉₊:ℕ):ℂ) *
          mellin (regularizedTraceTest n 3) (z.val-1/2) := by
  obtain ⟨S,⟨hS,_,hs⟩,_⟩ := (rational_theta_annihilator_jet_trace ((n:ℝ)+1)
    (by linarith [Nat.cast_nonneg (α:=ℝ) n])).2 _ (regularized_test_admissible n 3)
  have he : T=S := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    apply ext_inner_left ℂ
    exact fun v => (hT u v).trans (hS u v).symm
  exact he ▸ hs.tsum_eq.symm

private theorem cyclic_TraceRatePhysical_geo_eq (n : ℕ) :
    cutoffPolar n 3 - (cutoffArch n 3 + cutoffPrime n 3) = cutoffSpectral (1/2) n 3 := by
  have he := (trace_formula_rational_full_strip _ (regularized_test_admissible n 3)).2.2.2
  change cutoffArch n 3 + cutoffPrime n 3 = cutoffPolar n 3 - cutoffSpectral (1/2) n 3 at he
  rw [he]
  abel

theorem physical_rate_of_spectral (K : ℝ) (hK : 0<K)
    (hs : ∀ n : ℕ,
      ‖cutoffSpectral (1/2) n 3-regularizedSpectral (1/2) 3‖≤K*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) ∧
      ‖(∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
        ((min (analyticOrderNatAt riemannZeta z.val) ⌈((n:ℝ)+1)-1/2⌉₊:ℕ):ℂ) *
          mellin (regularizedTraceTest n 3) (z.val-1/2))-
        (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}, (analyticOrderNatAt riemannZeta z.val:ℂ) *
          (1/((3:ℂ)-z.val)-1/(5/2-z.val)))‖≤K*(Real.log ((n:ℝ)+2)/((n:ℝ)+1))) :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, ∀ T : cyclic_TraceRatePhysical_Op n,
      IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) T →
      let D := ∑' z : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2}, (zeroResolventTerm (1/2) 3 z.val).re
      let d := (cutoffPolar n 3-(cutoffArch n 3+cutoffPrime n 3)).re-(operatorTrace T).re
      let err := C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1))
      |d-D| ≤ err ∧ ∀ H : ℝ, 0≤H →
        (∀ s : Finset {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2},
          (∀ z∈s, |z.val.val.im|≤H) →
          (∑ z ∈ s, (analyticOrderNatAt riemannZeta z.val.val:ℝ)) ≤ 8*(1+H^2)*(d+err)) ∧
        (8*(1+H^2)*(d+err)<1 → ∀ z : ℂ, riemannZeta z=0 → 0<z.re → z.re<1 →
          |z.im|≤H → z.re=1/2) := by
  refine ⟨2*K,by positivity,?_⟩
  intro n
  have h := hs n
  intro T hT D d err
  have hR := (Complex.abs_re_le_norm (_:ℂ)).trans h.1
  have hC := (Complex.abs_re_le_norm (_:ℂ)).trans h.2
  rw [Complex.sub_re] at hR hC
  have hsum := ThetaGeometricLimit.full_sub_central_eq_offline
  have ha : |d-D|≤err := by
    dsimp only [d,D,err]
    rw [cyclic_TraceRatePhysical_geo_eq n,cyclic_TraceRatePhysical_op_trace n T hT,←hsum,abs_le]
    obtain ⟨hr1,hr2⟩ := abs_le.mp hR
    obtain ⟨hc1,hc2⟩ := abs_le.mp hC
    constructor <;> linarith
  have hD : D ≤ d+err := by linarith [(abs_le.mp ha).1]
  refine ⟨ha,fun H hH => ⟨fun s h => (finite_offline_mass H hH s h).trans
    (mul_le_mul_of_nonneg_left hD (by positivity)),?_⟩⟩
  intro hlt z hz h0 h1 hht
  by_contra hline
  let w : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2} :=
    ⟨⟨z,hz,h0,h1,abs_lt.mpr ⟨by linarith,by linarith⟩⟩,hline⟩
  exact (not_lt_of_ge ((offline_single_detected H hH w hht).trans
    (mul_le_mul_of_nonneg_left hD (by positivity)))) hlt

end
end MasulloRH.TraceRate

end StandaloneTraceRatePhysical

section StandaloneTraceRateLattice

open Set Filter
open scoped Topology
namespace MasulloRH.TraceRate
noncomputable section

def lowHeight (n : ℕ) : Set (ZetaZerosInTraceStrip (1/2)) := {z | |z.val.im|≤(5/2:ℝ)+2*n}

theorem lattice_tail_bound :
    ∃ H : ℝ, 0≤H ∧ ∀ n : ℕ,
      (∑' z : ZetaZerosInTraceStrip (1/2), (lowHeight n)ᶜ.indicator (zeroDecayWeight (1/2)) z)≤
        H*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) := by
  let c : ℝ := 8*((zetaLogDeriv 3).re-(zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re)-(zetaLogDeriv (5/2)).re
  refine ⟨4*(|c|+1),by positivity,fun n => ?_⟩
  have h := zero_decay_tail_at_real_lattice n
  dsimp only at h
  have heq : (lowHeight n)ᶜ.indicator (zeroDecayWeight (1/2)) =
      fun z : ZetaZerosInTraceStrip (1/2) => if (5/2:ℝ)+2*n < |z.val.im| then zeroDecayWeight (1/2) z else 0 := by
    funext z; simp [indicator,lowHeight]
  rw [heq]; apply h.trans
  let L := Real.log ((n:ℝ)+2)
  have hn : 0≤(n:ℝ) := by positivity
  have hp : 0<(n:ℝ)+1 := by positivity
  have hD : 0<(5/2:ℝ)+2*n-1 := by linarith
  have hL : 1/2≤L := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : 0<(2:ℝ))
    have h3 := Real.log_le_log (by norm_num : 0<(2:ℝ)) (show 2≤(n:ℝ)+2 by linarith)
    dsimp [L]; norm_num at h2; linarith
  have hlog : Real.log (n:ℝ)≤L := by
    rcases eq_or_ne n 0 with rfl|hz
    · simpa [L] using (Real.log_nonneg (by norm_num : 1≤(2:ℝ)))
    · apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz); linarith
  change 2/(5/2+2*(n:ℝ)-1)*(c+(1+Real.log n)/2) ≤ (4*(|c|+1))*(L/((n:ℝ)+1))
  have hk : c+(1+Real.log (n:ℝ))/2 ≤ 2*(|c|+1)*L := by
    nlinarith [le_abs_self c,mul_nonneg (abs_nonneg c) (sub_nonneg.mpr hL)]
  apply (mul_le_mul_of_nonneg_left hk (by positivity : 0≤2/(5/2+2*(n:ℝ)-1))).trans
  have hden : 2/(5/2+2*(n:ℝ)-1) ≤ 2/((n:ℝ)+1) :=
    div_le_div_of_nonneg_left (by norm_num) hp (by linarith)
  apply (mul_le_mul_of_nonneg_right hden (by positivity : 0≤2*(|c|+1)*L)).trans_eq
  ring

theorem spectral_rates_all_of_lattice_low
    (hlow : ∃ L : ℝ, 0≤L ∧ ∀ᶠ n : ℕ in atTop,
      Summable ((lowHeight n).indicator (fun z => (analyticOrderNatAt riemannZeta z.val:ℝ))) ∧
      ((∑' z, (lowHeight n).indicator (fun z => (analyticOrderNatAt riemannZeta z.val:ℝ)) z)≤
        L*((n:ℝ)+1)*Real.log ((n:ℝ)+2)) ∧
      ∀ z∈lowHeight n, analyticOrderNatAt riemannZeta z.val≤n+1) :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ,
      ‖cutoffSpectral (1/2) n 3-regularizedSpectral (1/2) 3‖≤C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) ∧
      ‖(∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
        ((min (analyticOrderNatAt riemannZeta z.val) ⌈((n:ℝ)+1)-1/2⌉₊:ℕ):ℂ) *
          mellin (regularizedTraceTest n 3) (z.val-1/2))-
        (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}, (analyticOrderNatAt riemannZeta z.val:ℂ) *
          (1/((3:ℂ)-z.val)-1/(5/2-z.val)))‖≤C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) := by
  obtain ⟨H,hH,ht⟩ := lattice_tail_bound
  obtain ⟨L,hL,hl⟩ := hlow
  obtain ⟨C,hC,h⟩ := spectral_rates_of_height_estimates lowHeight L H hL hH
    (hl.mono (fun n hn => ⟨hn.1,hn.2.1,ht n,hn.2.2⟩))
  exact spectral_rate_all_of_eventually _ _ hC h

end
end MasulloRH.TraceRate

end StandaloneTraceRateLattice

section StandaloneTraceRateLog

open Filter Asymptotics
open scoped Topology
namespace MasulloRH.TraceRate
theorem eventually_log_bound_le_n (C : ℝ) (hC : 0<C) :
    ∀ᶠ n : ℕ in atTop, C * Real.log ((n:ℝ)+2) ≤ (n:ℝ)+1 := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+2) atTop atTop := tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h := (Real.isLittleO_log_id_atTop.comp_tendsto ht).bound (show 0<(2*C)⁻¹ by positivity)
  filter_upwards [h] with n hn
  have hz : 0≤Real.log ((n:ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have hn' : 0≤(n:ℝ)+2 := by positivity
  change ‖Real.log ((n:ℝ)+2)‖ ≤ (2*C)⁻¹ * ‖(n:ℝ)+2‖ at hn
  rw [Real.norm_eq_abs,abs_of_nonneg hz,Real.norm_eq_abs,abs_of_nonneg hn'] at hn
  have h' : Real.log ((n:ℝ)+2)*(2*C) ≤ (n:ℝ)+2 := by
    rwa [← div_eq_inv_mul,le_div_iff₀ (by positivity : 0<2*C)] at hn
  nlinarith [Nat.cast_nonneg (α:=ℝ) n]
end MasulloRH.TraceRate

end StandaloneTraceRateLog

section StandaloneTraceRateLatticeCountSlab

open Set Filter Zeta23
namespace MasulloRH.TraceRate
noncomputable section

/-- Multiplicity of a strip zero in the half-open unit slab. -/
def slabWeight (j : ℤ) (z : ZetaZerosInTraceStrip (1/2)) : ℝ :=
  (Set.Ioc (j:ℝ) ((j:ℝ)+1)).indicator (fun _ => (analyticOrderNatAt riemannZeta z.val:ℝ)) z.val.im

theorem slabWeight_nonneg (j : ℤ) (z : ZetaZerosInTraceStrip (1/2)) :
    0 ≤ slabWeight j z := Set.indicator_nonneg (fun _ _ => Nat.cast_nonneg _) _

theorem slabWeight_count (j : ℤ) :
    Summable (slabWeight j) ∧
      ∑' z, slabWeight j z = (Ncount (j:ℝ) ((j:ℝ)+1) : ℝ) := by
  classical
  let S : Set (ZetaZerosInTraceStrip (1/2)) := {z | z.val.im ∈ Ioc (j:ℝ) ((j:ℝ)+1)}
  have hZ : (zerosIn (j:ℝ) ((j:ℝ)+1)).Finite := ZetaSeam.finite_window_holds _ _
  have hS : S.Finite := by
    refine (hZ.preimage (Subtype.val_injective.injOn)).subset ?_
    intro z hz
    exact ⟨⟨z.property.1,z.property.2.1,z.property.2.2.1⟩,hz⟩
  have hsup : Function.support (slabWeight j) ⊆ S := by
    intro z h
    by_contra hn
    change z.val.im ∉ Ioc (j:ℝ) ((j:ℝ)+1) at hn
    exact h (Set.indicator_of_notMem hn _)
  let e : S ≃ zerosIn (j:ℝ) ((j:ℝ)+1) := {
    toFun := fun z => ⟨z.val.val,⟨z.val.property.1,z.val.property.2.1,z.val.property.2.2.1⟩,z.property⟩
    invFun := fun z => ⟨⟨z.val,z.property.1.1,z.property.1.2.1,z.property.1.2.2,
        abs_lt.mpr ⟨by linarith [z.property.1.2.1],by linarith [z.property.1.2.2]⟩⟩,z.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  refine ⟨summable_of_hasFiniteSupport (hS.subset hsup),?_⟩
  calc
    _ = ∑' a : S, slabWeight j a.val := (tsum_subtype_eq_of_support_subset hsup).symm
    _ = ∑' a : S, (zeroMult (e a).val : ℝ) := by
      apply tsum_congr
      intro a
      have ha : a.val.val.im ∈ Ioc (j:ℝ) ((j:ℝ)+1) := a.property
      exact Set.indicator_of_mem ha _
    _ = ∑' z : zerosIn (j:ℝ) ((j:ℝ)+1), (zeroMult z.val:ℝ) := e.tsum_eq (fun z => (zeroMult z.val : ℝ))
    _ = _ := by
      rw [tsum_subtype (zerosIn (j:ℝ) ((j:ℝ)+1)) (fun z => (zeroMult z:ℝ)),
        tsum_eq_finsum (hZ.subset support_indicator_subset),← finsum_mem_def,Ncount,Nat.cast_finsum_mem hZ]

theorem le_slab_count_of_mem (j : ℤ) (z : ZetaZerosInTraceStrip (1/2))
    (hz : z.val.im ∈ Ioc (j:ℝ) ((j:ℝ)+1)) :
    (analyticOrderNatAt riemannZeta z.val:ℝ) ≤ (Ncount (j:ℝ) ((j:ℝ)+1):ℝ) := by
  obtain ⟨hs,he⟩ := slabWeight_count j
  rw [← he]
  have h := hs.le_tsum z (fun i _ => slabWeight_nonneg j i)
  simpa only [slabWeight,Set.indicator_of_mem hz] using h

end
end MasulloRH.TraceRate

end StandaloneTraceRateLatticeCountSlab

section StandaloneTraceRateLatticeArithmetic

open Finset
namespace MasulloRH.TraceRate
noncomputable section

def slabs (n : ℕ) : Finset ℤ := Finset.Icc (-(2*(n:ℤ)+4)) (2*(n:ℤ)+4)

theorem hit_slab (n : ℕ) (t : ℝ) (ht : |t|≤5/2+2*n) :
    ∃ j ∈ slabs n, (j:ℝ)<t ∧ t≤(j:ℝ)+1 := by
  have h₁ := Int.le_ceil t
  have h₂ := Int.ceil_lt_add_one t
  obtain ⟨h₃,h₄⟩ := abs_le.mp ht
  refine ⟨⌈t⌉-1,Finset.mem_Icc.mpr ⟨?_,?_⟩,?_,?_⟩
  · exact_mod_cast (show -(2*(n:ℝ)+4)≤(⌈t⌉:ℝ)-1 by linarith)
  · exact_mod_cast (show (⌈t⌉:ℝ)-1≤2*(n:ℝ)+4 by linarith)
  · push_cast; linarith
  · push_cast; linarith

theorem slab_log_le (n : ℕ) {j : ℤ} (hj : j∈slabs n) :
    Real.log (|(j:ℝ)|+3) ≤ 4*Real.log ((n:ℝ)+2) := by
  obtain ⟨ha,hb⟩ := Finset.mem_Icc.mp hj
  have ha' : -(2*(n:ℝ)+4)≤(j:ℝ) := by exact_mod_cast ha
  have hb' : (j:ℝ)≤2*(n:ℝ)+4 := by exact_mod_cast hb
  have hj' := abs_le.mpr ⟨ha',hb'⟩
  have hn : 0≤(n:ℝ) := by positivity
  have hs : |(j:ℝ)|+3≤((n:ℝ)+2)^4 := by nlinarith [sq_nonneg (n:ℝ),pow_nonneg hn 3,pow_nonneg hn 4]
  exact (Real.log_le_log (by positivity) hs).trans_eq (Real.log_pow _ _)

theorem slabs_card_le (n : ℕ) : ((slabs n).card:ℝ)≤9*((n:ℝ)+1) := by
  rw [slabs,Int.card_Icc]
  have hz : 0≤(2*(n:ℤ)+4)+1-(-(2*(n:ℤ)+4)) := by omega
  have hx := Int.toNat_of_nonneg hz
  norm_cast
  omega

end
end MasulloRH.TraceRate

end StandaloneTraceRateLatticeArithmetic

section StandaloneTraceRateLatticeAggregation

open Filter Set
open scoped Topology BigOperators
namespace MasulloRH.TraceRate
noncomputable section

theorem low_count_unconditional :
    ∃ L : ℝ, 0≤L ∧ ∀ᶠ n : ℕ in atTop,
      Summable ((lowHeight n).indicator (fun z => (analyticOrderNatAt riemannZeta z.val:ℝ))) ∧
      ((∑' z, (lowHeight n).indicator (fun z => (analyticOrderNatAt riemannZeta z.val:ℝ)) z) ≤
        L*((n:ℝ)+1)*Real.log ((n:ℝ)+2)) ∧
      ∀ z∈lowHeight n, analyticOrderNatAt riemannZeta z.val≤n+1 := by
  classical
  obtain ⟨A,hA,hab⟩ := Zeta23.RvM.zeta_local_zero_count
  have hpos : 0 < A*4 := by linarith
  refine ⟨36*A,by linarith,?_⟩
  filter_upwards [eventually_log_bound_le_n (A*4) hpos] with n hn
  let f := (lowHeight n).indicator (fun z => (analyticOrderNatAt riemannZeta z.val:ℝ))
  let g (z : ZetaZerosInTraceStrip (1/2)) := ∑ j∈slabs n, slabWeight j z
  have hg : Summable g := (hasSum_sum (s:=slabs n) (fun j _ => (slabWeight_count j).1.hasSum)).summable
  have hfg (z) : f z≤g z := by
    by_cases h : z∈lowHeight n
    · obtain ⟨j,hj,h₁,h₂⟩ := hit_slab n z.val.im h
      have he : f z=slabWeight j z := by
        rw [show f z=(analyticOrderNatAt riemannZeta z.val:ℝ) from Set.indicator_of_mem h _]
        simp only [slabWeight,Set.indicator_of_mem (show z.val.im∈Set.Ioc (j:ℝ) ((j:ℝ)+1) from ⟨h₁,h₂⟩)]
      rw [he]
      exact Finset.single_le_sum (fun j _ => slabWeight_nonneg j z) hj
    · rw [show f z=0 from Set.indicator_of_notMem h _]
      exact Finset.sum_nonneg (fun j _ => slabWeight_nonneg j z)
  have hf : Summable f := Summable.of_nonneg_of_le (fun z => indicator_nonneg (fun _ _ => Nat.cast_nonneg _) z) hfg hg
  have hbound (j : ℤ) (hj : j∈slabs n) : (Zeta23.Ncount (j:ℝ) ((j:ℝ)+1):ℝ) ≤ A*4*Real.log ((n:ℝ)+2) :=
    (hab (j:ℝ)).trans ((mul_le_mul_of_nonneg_left (slab_log_le n hj) (by linarith : 0≤A)).trans_eq (by ring))
  refine ⟨hf,(hf.tsum_le_tsum hfg hg).trans ?_,?_⟩
  · have hlog := Real.log_nonneg (show 1≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])
    calc
      ∑' z, g z = ∑ j∈slabs n, ∑' z, slabWeight j z := Summable.tsum_finsetSum (fun j _ => (slabWeight_count j).1)
      _ ≤ ∑ _j∈slabs n, A*4*Real.log ((n:ℝ)+2) :=
        Finset.sum_le_sum (fun j hj => (slabWeight_count j).2.le.trans (hbound j hj))
      _ = ((slabs n).card:ℝ)*(A*4*Real.log ((n:ℝ)+2)) := by simp
      _ ≤ (9*((n:ℝ)+1))*(A*4*Real.log ((n:ℝ)+2)) :=
        mul_le_mul_of_nonneg_right (slabs_card_le n) (mul_nonneg hpos.le hlog)
      _ = _ := by ring
  · intro z hz
    obtain ⟨j,hj,h₁,h₂⟩ := hit_slab n z.val.im hz
    have h := (le_slab_count_of_mem j z ⟨h₁,h₂⟩).trans ((hbound j hj).trans hn)
    exact_mod_cast h

end
end MasulloRH.TraceRate

end StandaloneTraceRateLatticeAggregation

section StandaloneTraceRateSpectralAll

namespace MasulloRH.TraceRate
noncomputable section

theorem spectral_rates_all :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ,
      ‖cutoffSpectral (1/2) n 3-regularizedSpectral (1/2) 3‖≤C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) ∧
      ‖(∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
        ((min (analyticOrderNatAt riemannZeta z.val) ⌈((n:ℝ)+1)-1/2⌉₊:ℕ):ℂ) *
          mellin (regularizedTraceTest n 3) (z.val-1/2))-
        (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}, (analyticOrderNatAt riemannZeta z.val:ℂ) *
          (1/((3:ℂ)-z.val)-1/(5/2-z.val)))‖≤C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) :=
  spectral_rates_all_of_lattice_low low_count_unconditional

end
end MasulloRH.TraceRate

end StandaloneTraceRateSpectralAll

section StandaloneTraceRateFinal

open MasulloRH MasulloGRH MeasureTheory Set Filter
open scoped Topology

theorem solution :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, ∀ T : (rationalThetaAnnihilator ((n:ℝ)+1) →L[ℂ] rationalThetaAnnihilator ((n:ℝ)+1)),
      IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) T →
      let D := ∑' z : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2}, (zeroResolventTerm (1/2) 3 z.val).re
      let d := (cutoffPolar n 3-(cutoffArch n 3+cutoffPrime n 3)).re-(operatorTrace T).re
      let err := C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1))
      |d-D| ≤ err ∧ ∀ H : ℝ, 0≤H →
        (∀ s : Finset {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2},
          (∀ z∈s, |z.val.val.im|≤H) →
          (∑ z ∈ s, (analyticOrderNatAt riemannZeta z.val.val:ℝ)) ≤ 8*(1+H^2)*(d+err)) ∧
        (8*(1+H^2)*(d+err)<1 → ∀ z : ℂ, riemannZeta z=0 → 0<z.re → z.re<1 →
          |z.im|≤H → z.re=1/2) := by
  obtain ⟨C,hC,h⟩ := MasulloRH.TraceRate.spectral_rates_all
  exact MasulloRH.TraceRate.physical_rate_of_spectral C hC h

end StandaloneTraceRateFinal
