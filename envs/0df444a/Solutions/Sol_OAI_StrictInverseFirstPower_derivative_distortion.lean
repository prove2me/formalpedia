-- Prove2me | solution 1 for OAI.StrictInverseFirstPower.derivative_distortion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:28:03.729687+00:00
-- url     : https://prove2.me/submissions/ddce8750-40c2-4dea-8d5c-a1c78c8decea

import Mathlib
import Definitions.Def_OAIQWSIFPK000
import Theorems.Thm_OAI_StrictInverseFirstPower_second_coefficient_le_two

section
-- module Solutions.OAIQW_StrictInverseFirstPower.DiskAutomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower

noncomputable section

lemma not_eventually_constant_of_injOn {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hs : s ∈ 𝓝 z) (hi : InjOn f s) :
    ¬ ∀ᶠ w in 𝓝 z, f w = f z := by
  intro h
  have hz := mem_of_mem_nhds hs
  have hh : ∀ᶠ w in 𝓝[≠] z, False := by
    filter_upwards [h.filter_mono nhdsWithin_le_nhds,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hs,
      eventually_mem_nhdsWithin] with w hw hws hwz
    exact hwz (hi hws hz hw)
  exact Filter.Eventually.exists hh |>.elim (fun _ h => h)

lemma analytic_injOn_map_nhds {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hs : s ∈ 𝓝 z) (hi : InjOn f s) (hf : AnalyticAt ℂ f z) :
    map f (𝓝 z) = 𝓝 (f z) := by
  exact le_antisymm hf.continuousAt
    (hf.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (not_eventually_constant_of_injOn hs hi))

lemma invFunOn_continuousAt {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hs : s ∈ 𝓝 z) (hi : InjOn f s) (hf : AnalyticAt ℂ f z) :
    ContinuousAt (invFunOn f s) (f z) := by
  have hz := mem_of_mem_nhds hs
  rw [ContinuousAt, hi.leftInvOn_invFunOn hz, ← analytic_injOn_map_nhds hs hi hf]
  change map (invFunOn f s) (map f (𝓝 z)) ≤ 𝓝 z
  rw [Filter.map_map]
  have hh : (invFunOn f s ∘ f) =ᶠ[𝓝 z] id := by
    filter_upwards [hs] with w hw
    exact hi.leftInvOn_invFunOn hw
  exact (tendsto_congr' hh).mpr tendsto_id

lemma deriv_eventually_ne_zero_of_injOn {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hs : IsOpen s) (hz : z ∈ s) (hi : InjOn f s) (hf : DifferentiableOn ℂ f s) :
    ∀ᶠ w in 𝓝[≠] z, deriv f w ≠ 0 := by
  have hfa : AnalyticAt ℂ (deriv f) z := (hf.deriv hs).analyticAt (hs.mem_nhds hz)
  refine hfa.eventually_eq_zero_or_eventually_ne_zero.resolve_left ?_
  intro hzero
  have he : ∀ᶠ w in 𝓝 z, w ∈ s ∧ deriv f w = 0 :=
    Filter.Eventually.and (hs.mem_nhds hz) hzero
  obtain ⟨r, hr, hrsub⟩ := Metric.eventually_nhds_iff.mp he
  have hdiff : DifferentiableOn ℂ f (ball z r) := hf.mono (fun w hw => (hrsub hw).1)
  have hc : ∀ᶠ w in 𝓝 z, f w = f z := by
    filter_upwards [ball_mem_nhds z hr] with w hw
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z r).isPreconnected hdiff
      (fun w hw => (hrsub hw).2) hw (mem_ball_self hr)
  exact not_eventually_constant_of_injOn (hs.mem_nhds hz) hi hc

theorem deriv_ne_zero_of_injOn {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hs : IsOpen s) (hz : z ∈ s) (hi : InjOn f s) (hf : DifferentiableOn ℂ f s) :
    deriv f z ≠ 0 := by
  let g := invFunOn f s
  have hfa : AnalyticAt ℂ f z := hf.analyticAt (hs.mem_nhds hz)
  have hg : ContinuousAt g (f z) := invFunOn_continuousAt (hs.mem_nhds hz) hi hfa
  have hgz : g (f z) = z := hi.leftInvOn_invFunOn hz
  have himage : f '' s ∈ 𝓝 (f z) := by
    rw [← analytic_injOn_map_nhds (hs.mem_nhds hz) hi hfa]
    exact image_mem_map (hs.mem_nhds hz)
  have hder := deriv_eventually_ne_zero_of_injOn hs hz hi hf
  have hder' : ∀ᶠ w in 𝓝 (f z), g w ≠ z → deriv f (g w) ≠ 0 := by
    have hh := hg.tendsto
    rw [hgz] at hh
    exact hh.eventually (eventually_nhdsWithin_iff.mp hder)
  have hgd : ∀ᶠ w in 𝓝[≠] (f z), DifferentiableAt ℂ g w := by
    filter_upwards [hder'.filter_mono nhdsWithin_le_nhds,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds himage, eventually_mem_nhdsWithin]
      with w hd hw hwz
    have hgw : g w ∈ s := invFunOn_mem hw
    have hfg : f (g w) = w := invFunOn_eq hw
    have hgne : g w ≠ z := by
      intro he
      apply hwz
      change w = f z
      rw [← hfg, he]
    have hleft : ∀ᶠ x in 𝓝 (g w), g (f x) = x := by
      filter_upwards [hs.mem_nhds hgw] with x hx
      exact hi.leftInvOn_invFunOn hx
    have hh := (hf.analyticAt (hs.mem_nhds hgw)).hasStrictDerivAt.to_local_left_inverse
      (hd hgne) hleft
    simpa only [hfg] using hh.hasDerivAt.differentiableAt
  have hga := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgd hg
  have hcomp := hga.differentiableAt.hasDerivAt.comp z (hf.differentiableAt (hs.mem_nhds hz)).hasDerivAt
  have hleft : (g ∘ f) =ᶠ[𝓝 z] id := by
    filter_upwards [hs.mem_nhds hz] with x hx
    exact hi.leftInvOn_invFunOn hx
  have hid : HasDerivAt (g ∘ f) 1 z := (hasDerivAt_id z).congr_of_eventuallyEq hleft
  have he := hcomp.unique hid
  intro hzero
  simp only [hzero, mul_zero] at he
  exact zero_ne_one he

end
end StrictInverseFirstPower

namespace StrictInverseFirstPower
noncomputable section

lemma second_deriv_eq_twice_dslope {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) :
    deriv (deriv f) 0 = 2 * deriv (dslope f 0) 0 := by
  let u := dslope f 0
  have hu : DifferentiableOn ℂ u (ball 0 1) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (by simp))).mpr hd
  have he (z : ℂ) : f z = z * u z + f 0 := by
    have hh := sub_smul_dslope f (0 : ℂ) z
    simp only [sub_zero, smul_eq_mul] at hh
    exact (eq_sub_iff_add_eq.mp hh).symm
  have hder : deriv f =ᶠ[𝓝 (0 : ℂ)] (fun z => u z + z * deriv u z) := by
    filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1)] with z hz
    have hzU := hu.differentiableAt (isOpen_ball.mem_nhds hz)
    have hp := ((hasDerivAt_id z).mul hzU.hasDerivAt).add_const (f 0)
    have hpf : HasDerivAt f (u z + z * deriv u z) z := by
      convert hp using 1
      all_goals first | rfl | exact funext he | simp
    exact hpf.deriv
  have hu0 := hu.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hu'0 := (hu.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hp := hu0.hasDerivAt.add ((hasDerivAt_id (0 : ℂ)).mul hu'0.hasDerivAt)
  have hpf : HasDerivAt (deriv f) (2 * deriv u 0) 0 := by
    convert hp.congr_of_eventuallyEq hder using 1
    all_goals first | rfl | simp [two_mul]
  exact hpf.deriv

lemma second_deriv_norm_le_four {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) : ‖deriv (deriv f) 0‖ ≤ 4 := by
  rw [second_deriv_eq_twice_dslope hd, norm_mul]
  have hh := second_coefficient_le_two hd hi h0 h1
  norm_num
  linarith

lemma diskAutomorphism_den_ne {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 + conj a * z ≠ 0 := by
  have hl : ‖conj a * z‖ < 1 := by
    rw [norm_mul, norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg z]
  intro he
  have he' : conj a * z = -1 := by linear_combination he
  rw [he'] at hl
  norm_num at hl

lemma diskAutomorphism_norm_identity (a z : ℂ) :
    ‖1 + conj a * z‖ ^ 2 - ‖a + z‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [← normSq_eq_norm_sq, normSq_apply, add_re, add_im, mul_re, mul_im,
    conj_re, conj_im, one_re, one_im]
  ring

lemma diskAutomorphism_mapsTo {a : ℂ} (ha : ‖a‖ < 1) :
    MapsTo (diskAutomorphism a) (ball 0 1) (ball 0 1) := by
  intro z hz
  simp only [mem_ball, dist_zero_right] at *
  have hn := diskAutomorphism_norm_identity a z
  have hp : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) :=
    mul_pos (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg z])
  have hl : ‖a + z‖ < ‖1 + conj a * z‖ := by
    nlinarith [norm_nonneg (a + z), norm_nonneg (1 + conj a * z)]
  dsimp only [diskAutomorphism]
  rw [norm_div, div_lt_one (norm_pos_iff.mpr (diskAutomorphism_den_ne ha hz))]
  exact hl

lemma diskAutomorphism_injOn {a : ℂ} (ha : ‖a‖ < 1) :
    InjOn (diskAutomorphism a) (ball 0 1) := by
  intro z hz w hw he
  have hz' : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
  have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
  have haN : 1 - conj a * a ≠ 0 := by
    rw [← normSq_eq_conj_mul_self, ← ofReal_one, ← ofReal_sub, ne_eq, ofReal_eq_zero]
    rw [normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have he' := (div_eq_div_iff (diskAutomorphism_den_ne ha hz') (diskAutomorphism_den_ne ha hw')).mp he
  have he'' : (1 - conj a * a) * (z - w) = 0 := by linear_combination he'
  exact sub_eq_zero.mp ((mul_eq_zero.mp he'').resolve_left haN)

lemma diskAutomorphism_hasDerivAt {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (diskAutomorphism a)
      ((1 - conj a * a) / (1 + conj a * z) ^ 2) z := by
  have hh := ((hasDerivAt_id z).const_add a).div
    (((hasDerivAt_id z).const_mul (conj a)).const_add 1) (diskAutomorphism_den_ne ha hz)
  convert hh using 1
  all_goals first | rfl | (dsimp only [id_eq, Function.comp_apply]; ring)

lemma diskAutomorphism_differentiableOn {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (diskAutomorphism a) (ball 0 1) := by
  intro z hz
  exact (diskAutomorphism_hasDerivAt ha (by simpa [mem_ball, dist_zero_right] using hz)).differentiableAt.differentiableWithinAt

lemma diskAutomorphism_deriv_zero {a : ℂ} (ha : ‖a‖ < 1) :
    deriv (diskAutomorphism a) 0 = 1 - conj a * a := by
  simpa using (diskAutomorphism_hasDerivAt (z := 0) ha (by simp)).deriv

lemma diskAutomorphism_second_deriv_zero {a : ℂ} (ha : ‖a‖ < 1) :
    deriv (deriv (diskAutomorphism a)) 0 = -2 * conj a * (1 - conj a * a) := by
  have he : deriv (diskAutomorphism a) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => (1 - conj a * a) / (1 + conj a * z) ^ 2) := by
    filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1)] with z hz
    exact (diskAutomorphism_hasDerivAt ha (by simpa [mem_ball, dist_zero_right] using hz)).deriv
  have hn : (1 + conj a * (0 : ℂ)) ^ 2 ≠ 0 := by simp
  have hp := (hasDerivAt_const (0 : ℂ) (1 - conj a * a)).div
    ((((hasDerivAt_id (0 : ℂ)).const_mul (conj a)).const_add 1).pow 2) hn
  have hpf : HasDerivAt (deriv (diskAutomorphism a)) (-2 * conj a * (1 - conj a * a)) 0 := by
    convert hp.congr_of_eventuallyEq he using 1
    all_goals first | rfl | (simp; ring)
  exact hpf.deriv

lemma second_deriv_comp {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f (g z)) (hg : AnalyticAt ℂ g z) :
    deriv (deriv (f ∘ g)) z = deriv (deriv f) (g z) * deriv g z ^ 2 +
      deriv f (g z) * deriv (deriv g) z := by
  have he : deriv (f ∘ g) =ᶠ[𝓝 z] (fun w => deriv f (g w) * deriv g w) := by
    filter_upwards [hg.eventually_analyticAt,
      hg.continuousAt.preimage_mem_nhds hf.eventually_analyticAt] with w hgw hfw
    exact deriv_comp w hfw.differentiableAt hgw.differentiableAt
  have hp := (hf.deriv.differentiableAt.hasDerivAt.comp z hg.differentiableAt.hasDerivAt).mul
    hg.deriv.differentiableAt.hasDerivAt
  have hpf : HasDerivAt (deriv (f ∘ g))
      (deriv (deriv f) (g z) * deriv g z ^ 2 + deriv f (g z) * deriv (deriv g) z) z := by
    convert hp.congr_of_eventuallyEq he using 1
    all_goals first | rfl | (dsimp only [id_eq, Function.comp_apply]; ring)
  exact hpf.deriv

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.DerivativeDistortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma second_deriv_normalize {f : ℂ → ℂ} {z b c : ℂ} (hf : AnalyticAt ℂ f z) :
    deriv (deriv (fun w => (f w - b) / c)) z = deriv (deriv f) z / c := by
  have he : deriv (fun w => (f w - b) / c) =ᶠ[𝓝 z] (fun w => deriv f w / c) := by
    filter_upwards [hf.eventually_analyticAt] with w hw
    exact ((hw.differentiableAt.hasDerivAt.sub_const b).div_const c).deriv
  have hp := hf.deriv.differentiableAt.hasDerivAt.div_const c
  exact (hp.congr_of_eventuallyEq he).deriv

theorem preSchwarzian_bound {f : ℂ → ℂ} {a : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (ha : ‖a‖ < 1) :
    ‖(1 - (‖a‖ ^ 2 : ℝ) : ℂ) * (deriv (deriv f) a / deriv f a) - 2 * conj a‖ ≤ 4 := by
  have ha' : a ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball, dist_zero_right] using ha
  have hfn := deriv_ne_zero_of_injOn isOpen_ball ha' hi hd
  let δ : ℂ := 1 - conj a * a
  have hδ : δ ≠ 0 := by
    dsimp only [δ]
    rw [← normSq_eq_conj_mul_self, ← ofReal_one, ← ofReal_sub, ne_eq, ofReal_eq_zero,
      normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  let g : ℂ → ℂ := fun w => (f (diskAutomorphism a w) - f a) / (δ * deriv f a)
  have hφd := diskAutomorphism_differentiableOn ha
  have hφm := diskAutomorphism_mapsTo ha
  have hgd : DifferentiableOn ℂ g (ball 0 1) :=
    ((hd.comp hφd hφm).sub_const _).div_const _
  have hgi : InjOn g (ball 0 1) := by
    intro z hz w hw he
    apply diskAutomorphism_injOn ha hz hw
    apply hi (hφm hz) (hφm hw)
    exact sub_left_inj.mp ((div_left_inj' (mul_ne_zero hδ hfn)).mp he)
  have hg0 : g 0 = 0 := by simp [g]
  have hφ0 : HasDerivAt (diskAutomorphism a) δ 0 := by
    convert diskAutomorphism_hasDerivAt (z := 0) ha (by simp) using 1; simp [δ]
  have hfa := hd.analyticAt (isOpen_ball.mem_nhds ha')
  have hfac : HasDerivAt f (deriv f a) (diskAutomorphism a 0) := by
    simpa using hfa.differentiableAt.hasDerivAt
  have hg1 : deriv g 0 = 1 := by
    have hp := ((hfac.comp 0 hφ0).sub_const (f a)).div_const (δ * deriv f a)
    convert hp.deriv using 1
    all_goals first | rfl | field_simp
  have hφa := hφd.analyticAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hF : AnalyticAt ℂ (f ∘ diskAutomorphism a) 0 :=
    (show AnalyticAt ℂ f (diskAutomorphism a 0) by simpa using hfa).comp hφa
  have hg2 : deriv (deriv g) 0 = δ * (deriv (deriv f) a / deriv f a) - 2 * conj a := by
    change deriv (deriv (fun w => ((f ∘ diskAutomorphism a) w - f a) /
      (δ * deriv f a))) 0 = _
    rw [second_deriv_normalize hF]
    rw [second_deriv_comp (by simpa using hfa) hφa]
    simp only [diskAutomorphism_zero, diskAutomorphism_deriv_zero ha,
      diskAutomorphism_second_deriv_zero ha]
    dsimp only [δ]
    dsimp only [δ] at hδ
    field_simp
    ring
  have hb := second_deriv_norm_le_four hgd hgi hg0 hg1
  rw [hg2] at hb
  simpa only [δ, ← normSq_eq_conj_mul_self, normSq_eq_norm_sq, ofReal_sub, ofReal_pow,
    ofReal_one] using hb

lemma hasDerivAt_log_norm {g : ℝ → ℂ} {g' : ℂ} {t : ℝ}
    (hg : HasDerivAt g g' t) (hn : g t ≠ 0) :
    HasDerivAt (fun s => Real.log ‖g s‖) (g' / g t).re t := by
  have hp := (hg.norm_sq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))).div_const 2
  have he : (fun s => Real.log (‖g s‖ ^ 2) / 2) = (fun s => Real.log ‖g s‖) := by
    funext s
    rw [Real.log_pow]
    ring
  have hv : (2 * inner ℝ (g t) g' / ‖g t‖ ^ 2) / 2 = (g' / g t).re := by
    rw [Complex.inner, Complex.div_re, ← normSq_eq_norm_sq]
    simp only [mul_re, conj_re, conj_im]
    ring
  convert hp using 1
  all_goals first | rfl | exact he.symm | exact hv.symm

end
end StrictInverseFirstPower

namespace StrictInverseFirstPower
noncomputable section

lemma radial_preSchwarzian_bounds {f : ℂ → ℂ} {u : ℂ} {t : ℝ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hu : ‖u‖ = 1) (ht : 0 ≤ t) (ht1 : t < 1) :
    (2 * t - 4) / (1 - t ^ 2) ≤
        (deriv (deriv f) ((t : ℂ) * u) * u / deriv f ((t : ℂ) * u)).re ∧
      (deriv (deriv f) ((t : ℂ) * u) * u / deriv f ((t : ℂ) * u)).re ≤
        (2 * t + 4) / (1 - t ^ 2) := by
  have hnorm : ‖(t : ℂ) * u‖ = t := by simp [hu, abs_of_nonneg ht]
  have hsu : conj u * u = 1 := by
    rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq, hu]
    norm_num
  have hb := preSchwarzian_bound hd hi (a := (t : ℂ) * u) (by rwa [hnorm])
  rw [hnorm] at hb
  let p : ℂ := deriv (deriv f) ((t : ℂ) * u) / deriv f ((t : ℂ) * u)
  have he : ((1 - (t ^ 2 : ℝ) : ℂ) * p - 2 * conj ((t : ℂ) * u)) * u =
      (1 - (t ^ 2 : ℝ) : ℂ) * (p * u) - 2 * (t : ℂ) := by
    simp only [map_mul, conj_ofReal, sub_mul]
    calc
      _ = (1 - (t ^ 2 : ℝ) : ℂ) * (p * u) - 2 * (t : ℂ) * (conj u * u) := by ring
      _ = _ := by rw [hsu, mul_one]; ring
  have hb' : ‖(1 - (t ^ 2 : ℝ) : ℂ) * (p * u) - 2 * (t : ℂ)‖ ≤ 4 := by
    rw [← he, norm_mul, hu, mul_one]
    exact hb
  have hh := (Complex.abs_re_le_norm _).trans hb'
  have hh' : |(1 - t ^ 2) * (p * u).re - 2 * t| ≤ 4 := by
    simpa [← ofReal_pow, Complex.mul_re] using hh
  have hp : 0 < 1 - t ^ 2 := by nlinarith
  have hlo := (abs_le.mp hh').1
  have hhi := (abs_le.mp hh').2
  have hval : (p * u).re =
      (deriv (deriv f) ((t : ℂ) * u) * u / deriv f ((t : ℂ) * u)).re := by
    congr 1
    dsimp only [p]
    ring
  rw [← hval]
  constructor
  · exact (div_le_iff₀ hp).mpr (by nlinarith)
  · exact (le_div_iff₀ hp).mpr (by nlinarith)

lemma hasDerivAt_radial_log_deriv {f : ℂ → ℂ} {u : ℂ} {t : ℝ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hmem : (t : ℂ) * u ∈ ball (0 : ℂ) 1) :
    HasDerivAt (fun s : ℝ => Real.log ‖deriv f ((s : ℂ) * u)‖)
      (deriv (deriv f) ((t : ℂ) * u) * u / deriv f ((t : ℂ) * u)).re t := by
  have hdf := (hd.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hmem)
  have hp := (hdf.hasDerivAt.comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).mul_const u)).comp_ofReal
  apply hasDerivAt_log_norm _ (deriv_ne_zero_of_injOn isOpen_ball hmem hi hd)
  simpa only [Function.comp_apply, id_eq, one_mul] using hp

lemma log_derivative_distortion_radial {f : ℂ → ℂ} {u : ℂ} {r : ℝ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h1 : deriv f 0 = 1) (hu : ‖u‖ = 1) (hr : 0 ≤ r) (hr1 : r < 1) :
    Real.log (1 - r) - 3 * Real.log (1 + r) ≤ Real.log ‖deriv f ((r : ℂ) * u)‖ ∧
      Real.log ‖deriv f ((r : ℂ) * u)‖ ≤ Real.log (1 + r) - 3 * Real.log (1 - r) := by
  let A : ℝ → ℝ := fun t => Real.log ‖deriv f ((t : ℂ) * u)‖
  let D : ℝ → ℝ := fun t =>
    (deriv (deriv f) ((t : ℂ) * u) * u / deriv f ((t : ℂ) * u)).re
  have hrad (t : ℝ) (ht : t ∈ Icc 0 r) : (t : ℂ) * u ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball, dist_zero_right, hu, abs_of_nonneg ht.1] using ht.2.trans_lt hr1
  have hA (t : ℝ) (ht : t ∈ Icc 0 r) : HasDerivAt A (D t) t :=
    hasDerivAt_radial_log_deriv hd hi (hrad t ht)
  have hL (t : ℝ) (ht : t ∈ Icc 0 r) :
      HasDerivAt (fun s : ℝ => Real.log (1 - s) - 3 * Real.log (1 + s))
        ((2 * t - 4) / (1 - t ^ 2)) t := by
    have hm : 1 - t ≠ 0 := by linarith [ht.2]
    have hp : 1 + t ≠ 0 := by linarith [ht.1]
    have hsq : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
    have hdminus : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    have hdplus : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add (1 : ℝ)
    have h := (hdminus.log hm).sub ((hdplus.log hp).const_mul 3)
    convert! h using 1
    field_simp
    ring
  have hU (t : ℝ) (ht : t ∈ Icc 0 r) :
      HasDerivAt (fun s : ℝ => Real.log (1 + s) - 3 * Real.log (1 - s))
        ((2 * t + 4) / (1 - t ^ 2)) t := by
    have hm : 1 - t ≠ 0 := by linarith [ht.2]
    have hp : 1 + t ≠ 0 := by linarith [ht.1]
    have hsq : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
    have hdminus : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    have hdplus : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add (1 : ℝ)
    have h := (hdplus.log hp).sub ((hdminus.log hm).const_mul 3)
    convert! h using 1
    field_simp
    ring
  have hbounds (t : ℝ) (ht : t ∈ Icc 0 r) :=
    radial_preSchwarzian_bounds hd hi hu ht.1 (ht.2.trans_lt hr1)
  have hmonoL : MonotoneOn (fun t => A t -
      (Real.log (1 - t) - 3 * Real.log (1 + t))) (Icc 0 r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
    · exact fun t ht => ((hA t ht).sub (hL t ht)).continuousAt.continuousWithinAt
    · exact fun t ht => ((hA t (interior_subset ht)).sub
        (hL t (interior_subset ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      change 0 ≤ deriv (A - (fun s => Real.log (1 - s) - 3 * Real.log (1 + s))) t
      rw [((hA t (interior_subset ht)).sub (hL t (interior_subset ht))).deriv]
      exact sub_nonneg.mpr (hbounds t (interior_subset ht)).1
  have hmonoU : MonotoneOn (fun t =>
      (Real.log (1 + t) - 3 * Real.log (1 - t)) - A t) (Icc 0 r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
    · exact fun t ht => ((hU t ht).sub (hA t ht)).continuousAt.continuousWithinAt
    · exact fun t ht => ((hU t (interior_subset ht)).sub
        (hA t (interior_subset ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      change 0 ≤ deriv ((fun s => Real.log (1 + s) - 3 * Real.log (1 - s)) - A) t
      rw [((hU t (interior_subset ht)).sub (hA t (interior_subset ht))).deriv]
      exact sub_nonneg.mpr (hbounds t (interior_subset ht)).2
  have hlo := hmonoL (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  have hhi := hmonoU (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  simp only [A, ofReal_zero, zero_mul, h1, norm_one, Real.log_one, sub_zero, add_zero,
    mul_zero, sub_self] at hlo hhi
  exact ⟨sub_nonneg.mp hlo, sub_nonneg.mp hhi⟩

theorem derivative_distortion_oai {f : ℂ → ℂ} {z : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h1 : deriv f 0 = 1) (hz : ‖z‖ < 1) :
    (1 - ‖z‖) / (1 + ‖z‖) ^ 3 ≤ ‖deriv f z‖ ∧
      ‖deriv f z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) ^ 3 := by
  by_cases hz0 : z = 0
  · subst z
    simp [h1]
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  let u : ℂ := z / (‖z‖ : ℂ)
  have hu : ‖u‖ = 1 := by simp [u, hr.ne']
  have he : (‖z‖ : ℂ) * u = z := by
    dsimp only [u]
    field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
  have hb := log_derivative_distortion_radial hd hi h1 hu hr.le hz
  rw [he] at hb
  have hm : 0 < 1 - ‖z‖ := sub_pos.mpr hz
  have hp : 0 < 1 + ‖z‖ := by positivity
  have hdf : 0 < ‖deriv f z‖ := norm_pos_iff.mpr
    (deriv_ne_zero_of_injOn isOpen_ball (by simpa using hz) hi hd)
  have expL : Real.exp (Real.log (1 - ‖z‖) - 3 * Real.log (1 + ‖z‖)) =
      (1 - ‖z‖) / (1 + ‖z‖) ^ 3 := by
    rw [show 3 * Real.log (1 + ‖z‖) = Real.log ((1 + ‖z‖) ^ 3) by
      rw [Real.log_pow]; norm_num]
    rw [Real.exp_sub, Real.exp_log hm, Real.exp_log (pow_pos hp 3)]
  have expU : Real.exp (Real.log (1 + ‖z‖) - 3 * Real.log (1 - ‖z‖)) =
      (1 + ‖z‖) / (1 - ‖z‖) ^ 3 := by
    rw [show 3 * Real.log (1 - ‖z‖) = Real.log ((1 - ‖z‖) ^ 3) by
      rw [Real.log_pow]; norm_num]
    rw [Real.exp_sub, Real.exp_log hp, Real.exp_log (pow_pos hm 3)]
  constructor
  · simpa only [expL, Real.exp_log hdf] using Real.exp_le_exp.mpr hb.1
  · simpa only [expU, Real.exp_log hdf] using Real.exp_le_exp.mpr hb.2

end
end StrictInverseFirstPower

end

end OAI
end

theorem solution : type_of% @OAI.StrictInverseFirstPower.derivative_distortion_oai := @OAI.StrictInverseFirstPower.derivative_distortion_oai
