-- Prove2me | solution 1 for OAI.Brennan.isCompact_univalent_restrictions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T20:22:17.146409+00:00
-- url     : https://prove2.me/submissions/4a785c1b-d1e5-4ab6-bb0a-f793d2c509ee

import Mathlib
import Definitions.Def_Brennan
import Definitions.Def_OAIQWBRNK000
import Theorems.Thm_OAI_StrictInverseFirstPower_derivative_distortion
import Theorems.Thm_OAI_StrictInverseFirstPower_koebe_quarter

section
-- module Solutions.OAIQW_BrennanCore.Distortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma nonconstant_germ_of_injOn {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : Set.InjOn f U) {a : ℂ} (ha : a ∈ U) :
    ¬ ∀ᶠ z in 𝓝 a, f z = f a := by
  intro hc
  have heq : ∀ᶠ z in 𝓝 a, z = a := by
    filter_upwards [hc, hU.mem_nhds ha] with z hz hzU
    exact hf hzU ha hz
  have heq' : ∀ᶠ z in 𝓝[≠] a, z = a := heq.filter_mono nhdsWithin_le_nhds
  have hne' : ∀ᶠ z in 𝓝[≠] a, z ≠ a := self_mem_nhdsWithin
  obtain ⟨z, hz, hne⟩ := (heq'.and hne').exists
  exact hne hz

lemma univalent_inverse_continuousAt {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : UnivalentOn f U) {a : ℂ} (ha : a ∈ U) :
    ContinuousAt (Function.invFunOn f U) (f a) := by
  have haan : AnalyticAt ℂ f a := (hf.1.analyticOnNhd hU) a ha
  have hopen : 𝓝 (f a) ≤ Filter.map f (𝓝 a) :=
    haan.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (nonconstant_germ_of_injOn hU hf.2 ha)
  have hl : ∀ᶠ z in 𝓝 a, Function.invFunOn f U (f z) = z := by
    filter_upwards [hU.mem_nhds ha] with z hz
    exact hf.2.leftInvOn_invFunOn hz
  have ht : Tendsto (Function.invFunOn f U ∘ f) (𝓝 a) (𝓝 a) :=
    tendsto_id.congr' (Filter.EventuallyEq.symm hl)
  rw [ContinuousAt, hf.2.leftInvOn_invFunOn ha]
  exact (tendsto_map'_iff.mpr ht).mono_left hopen

lemma univalent_deriv_ne_zero {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : UnivalentOn f U) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 := by
  have han : AnalyticAt ℂ f a := hf.1.analyticOnNhd hU a ha
  have hd_nonconst : ¬ ∀ᶠ z in 𝓝 a, deriv f z = 0 := by
    intro hc
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hc.and (hU.mem_nhds ha))
    have hfball : DifferentiableOn ℂ f (Metric.ball a r) :=
      hf.1.mono (fun z hz => (hball hz).2)
    have hcball : ∀ z ∈ Metric.ball a r, f z = f a := by
      intro z hz
      exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball a r).isPreconnected
        hfball (fun w hw => (hball hw).1) hz (Metric.mem_ball_self hr)
    apply nonconstant_germ_of_injOn hU hf.2 ha
    filter_upwards [Metric.ball_mem_nhds a hr] with z hz
    exact hcball z hz
  have hd : ∀ᶠ z in 𝓝[≠] a, deriv f z ≠ 0 :=
    han.deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left hd_nonconst
  let g := Function.invFunOn f U
  have hgc : ContinuousAt g (f a) := univalent_inverse_continuousAt hU hf ha
  have hga : g (f a) = a := hf.2.leftInvOn_invFunOn ha
  have hopen : 𝓝 (f a) ≤ Filter.map f (𝓝 a) :=
    han.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (nonconstant_germ_of_injOn hU hf.2 ha)
  have hright : ∀ᶠ w in 𝓝 (f a), g w ∈ U ∧ f (g w) = w := by
    apply (hopen (Filter.mem_map.mpr ?_))
    filter_upwards [hU.mem_nhds ha] with z hz
    exact ⟨Function.invFunOn_apply_mem hz, Function.invFunOn_apply_eq hz⟩
  have hgne : ∀ᶠ w in 𝓝[≠] (f a), g w ≠ a := by
    filter_upwards [hright.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with w hw hwne
    intro heq
    exact hwne (hw.2.symm.trans (congrArg f heq))
  have hgt : Tendsto g (𝓝[≠] (f a)) (𝓝[≠] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, hgne⟩
    simpa only [hga] using (hgc.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto g (𝓝[≠] (f a)) (𝓝 (g (f a))))
  have hgd : ∀ᶠ w in 𝓝[≠] (f a), DifferentiableAt ℂ g w := by
    filter_upwards [hgt.eventually hd, hright.filter_mono nhdsWithin_le_nhds]
      with w hwder hw
    have hwan : AnalyticAt ℂ f (g w) := hf.1.analyticOnNhd hU (g w) hw.1
    have hws : HasStrictDerivAt f (deriv f (g w)) (g w) :=
      (hwan.contDiffAt (n := 1)).hasStrictDerivAt (by norm_num)
    have hl : ∀ᶠ z in 𝓝 (g w), g (f z) = z := by
      filter_upwards [hU.mem_nhds hw.1] with z hz
      exact hf.2.leftInvOn_invFunOn hz
    simpa [hw.2] using (hws.to_local_left_inverse hwder hl).hasDerivAt.differentiableAt
  have hgan := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    hgd hgc
  have hcomp := hgan.differentiableAt.hasDerivAt.comp a han.differentiableAt.hasDerivAt
  have hid : (fun z => g (f z)) =ᶠ[𝓝 a] id := by
    filter_upwards [hU.mem_nhds ha] with z hz
    exact hf.2.leftInvOn_invFunOn hz
  have hprod : deriv g (f a) * deriv f a = 1 := by
    simpa using (hcomp.congr_of_eventuallyEq hid.symm).unique (hasDerivAt_id a)
  intro hzero
  simp [hzero] at hprod

lemma schlicht_quarter {f : ℂ → ℂ} (hf : Schlicht f) :
    Metric.ball (0 : ℂ) (1/4) ⊆ f '' disk :=
  OAI.StrictInverseFirstPower.koebe_quarter hf.1.1 hf.1.2 hf.2.1 hf.2.2

lemma schlicht_deriv_bounds {f : ℂ → ℂ} (hf : Schlicht f) {z : ℂ} (hz : z ∈ disk) :
    (1-‖z‖)/(1+‖z‖)^3 ≤ ‖deriv f z‖ ∧
      ‖deriv f z‖ ≤ (1+‖z‖)/(1-‖z‖)^3 :=
  OAI.StrictInverseFirstPower.derivative_distortion hf.1.1 hf.1.2 hf.2.2
    (by simpa [disk, Metric.mem_ball, dist_zero_right] using hz)

lemma schlicht_deriv_compact_bound {f : ℂ → ℂ} (hf : Schlicht f)
    {R : ℝ} (hR : R < 1) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖deriv f z‖ ≤ 2/(1-R)^3 := by
  have hzm : z ∈ disk := by simpa [disk] using hz.trans_lt hR
  apply (schlicht_deriv_bounds hf hzm).2.trans
  have hd : 0 < 1-R := sub_pos.mpr hR
  apply div_le_div₀ (by positivity) (by linarith [norm_nonneg z]) (by positivity)
  exact pow_le_pow_left₀ hd.le (by linarith) 3

lemma schlicht_lipschitz_bound {f : ℂ → ℂ} (hf : Schlicht f)
    {R : ℝ} (hR : R < 1) {z w : ℂ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖f z-f w‖ ≤ (2/(1-R)^3)*‖z-w‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s := Metric.closedBall 0 R)
    (𝕜 := ℂ) _ _ (convex_closedBall 0 R)
    (by simpa using hw) (by simpa using hz)
  · intro x hx
    apply (hf.1.1 x _).differentiableAt
      (Metric.isOpen_ball.mem_nhds (show x ∈ disk from ?_))
    all_goals simpa [disk] using (show ‖x‖ ≤ R by simpa using hx).trans_lt hR
  · intro x hx
    exact schlicht_deriv_compact_bound hf hR (by simpa using hx)

lemma schlicht_local_bound {f : ℂ → ℂ} (hf : Schlicht f)
    {R : ℝ} (hR : R < 1) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖f z‖ ≤ (2/(1-R)^3)*R := by
  have h := schlicht_lipschitz_bound hf hR hz
    (show ‖(0 : ℂ)‖ ≤ R by simpa using (norm_nonneg z).trans hz)
  simp only [hf.2.1,sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left hz (by positivity))

lemma affine_disk_maps_ball (a : ℂ) {R : ℝ} (hR : 0 < R) :
    MapsTo (fun z : ℂ => a+(R : ℂ)*z) disk (Metric.ball a R) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by simpa [disk] using hz
  simp only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
  nlinarith

lemma ballNormalize_deriv {f : ℂ → ℂ} {a z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball a R)) (hz : z ∈ disk) :
    HasDerivAt (ballNormalize f a R)
      (deriv f (a+(R : ℂ)*z)/deriv f a) z := by
  have hmap := affine_disk_maps_ball a hR hz
  have hd := ((hf _ hmap).differentiableAt (Metric.isOpen_ball.mem_nhds hmap)).hasDerivAt
  have hdz := (((hd.comp z (((hasDerivAt_id z).const_mul (R : ℂ)).const_add a)).sub_const (f a)).div_const
    ((R : ℂ)*deriv f a))
  convert hdz using 1 <;> try rfl
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  simp only [mul_one]
  field_simp

lemma ballNormalize_schlicht {f : ℂ → ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : UnivalentOn f (Metric.ball a R)) (hn : deriv f a ≠ 0) :
    Schlicht (ballNormalize f a R) := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hmap := affine_disk_maps_ball a hR
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro z hz
    exact (ballNormalize_deriv hR hf.1 hz).differentiableAt.differentiableWithinAt
  · intro z hz w hw he
    apply mul_left_cancel₀ hRc
    apply add_left_cancel (a := a)
    apply hf.2 (hmap hz) (hmap hw)
    have he' := (div_left_inj' (mul_ne_zero hRc hn)).mp he
    exact sub_left_inj.mp he'
  · simp [ballNormalize]
  · rw [(ballNormalize_deriv hR hf.1 (show (0 : ℂ) ∈ disk by simp [disk])).deriv]
    simp [hn]

lemma univalent_ball_quarter {f : ℂ → ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : UnivalentOn f (Metric.ball a R)) :
    Metric.ball (f a) (R*‖deriv f a‖/4) ⊆ f '' Metric.ball a R := by
  have ha : a ∈ Metric.ball a R := Metric.mem_ball_self hR
  have hn := univalent_deriv_ne_zero Metric.isOpen_ball hf ha
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hden := mul_ne_zero hRc hn
  intro w hw
  have hu : (w-f a)/((R : ℂ)*deriv f a) ∈ Metric.ball (0 : ℂ) (1/4) := by
    simp only [Metric.mem_ball,dist_zero_right,norm_div,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
    rw [div_lt_iff₀ (mul_pos hR (norm_pos_iff.mpr hn))]
    have hw' : ‖w-f a‖ < R*‖deriv f a‖/4 := by simpa [dist_eq_norm] using hw
    linarith
  obtain ⟨z,hz,he⟩ := schlicht_quarter (ballNormalize_schlicht hR hf hn) hu
  refine ⟨a+(R : ℂ)*z,affine_disk_maps_ball a hR hz,?_⟩
  have hes := (div_left_inj' hden).mp he
  exact sub_left_inj.mp hes

lemma schlicht_separation {f : ℂ → ℂ} (hf : Schlicht f)
    {z w : ℂ} (_hz : z ∈ disk) (hw : w ∈ disk) {R : ℝ} (hR : 0 < R)
    (hsub : Metric.ball z R ⊆ disk) (hdist : R ≤ ‖w-z‖) :
    R*‖deriv f z‖/4 ≤ ‖f w-f z‖ := by
  by_contra! hlt
  have hm : f w ∈ Metric.ball (f z) (R*‖deriv f z‖/4) := by
    simpa [dist_eq_norm] using hlt
  obtain ⟨v,hv,he⟩ := univalent_ball_quarter hR ⟨hf.1.1.mono hsub,hf.1.2.mono hsub⟩ hm
  have hvw := hf.1.2 (hsub hv) hw he
  subst v
  have : ‖w-z‖ < R := by simpa [dist_eq_norm] using hv
  exact (not_lt_of_ge hdist) this

lemma schlicht_uniform_separation {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk)
    (hne : z ≠ w) : ∃ c : ℝ, 0 < c ∧ ∀ f : ℂ → ℂ, Schlicht f → c ≤ ‖f w-f z‖ := by
  have hz1 : ‖z‖ < 1 := by simpa [disk] using hz
  let R := min ((1-‖z‖)/2) (‖w-z‖/2)
  have hR : 0 < R := lt_min (by linarith)
    (div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)) (by norm_num))
  have hR1 : R ≤ (1-‖z‖)/2 := min_le_left _ _
  have hR2 : R ≤ ‖w-z‖/2 := min_le_right _ _
  have hsub : Metric.ball z R ⊆ disk := by
    intro v hv
    have hvR : ‖v-z‖ < R := by simpa [dist_eq_norm] using hv
    have ht := norm_add_le (v-z) z
    rw [sub_add_cancel] at ht
    simp only [disk,Metric.mem_ball,dist_zero_right]
    linarith
  refine ⟨R*((1-‖z‖)/(1+‖z‖)^3)/4,by positivity,?_⟩
  intro f hf
  have h := schlicht_separation hf hz hw hR hsub (by linarith [norm_nonneg (w-z)])
  apply le_trans _ h
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (schlicht_deriv_bounds hf hz).1 hR.le)
    (by norm_num)

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_BrennanCore.CompactClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma compact_closure_of_disk_bounds (S : Set C(disk,ℂ))
    (hLip : ∀ R : ℝ, R < 1 → ∃ C : ℝ, ∀ g ∈ S, ∀ z w : disk,
      ‖(z : ℂ)‖ ≤ R → ‖(w : ℂ)‖ ≤ R → ‖g z-g w‖ ≤ C*‖(z : ℂ)-(w : ℂ)‖)
    (hBd : ∀ z : disk, ∃ C : ℝ, ∀ g ∈ S, ‖g z‖ ≤ C) :
    IsCompact (closure S) := by
  let : T2Space (UniformOnFun disk ℂ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (eq_univ_iff_forall.mpr
      (fun x => mem_sUnion_of_mem (mem_singleton x) isCompact_singleton))
  have heq : Equicontinuous (fun g : S => fun z : disk => g.1 z) := by
    intro z
    obtain ⟨R,hzR,hR⟩ := exists_between (show ‖(z : ℂ)‖ < 1 by simpa [disk] using z.2)
    obtain ⟨C,hC⟩ := hLip R hR
    apply Metric.equicontinuousAt_of_continuity_modulus
      (fun w : disk => C*dist (z : ℂ) (w : ℂ))
    · simpa using (tendsto_const_nhds (x := C)).mul
        ((tendsto_const_nhds (x := (z : ℂ))).dist (continuous_subtype_val.tendsto z))
    · have hn : ∀ᶠ w : disk in 𝓝 z, ‖(w : ℂ)‖ < R :=
        (continuous_norm.comp continuous_subtype_val).continuousAt (Iio_mem_nhds hzR)
      filter_upwards [hn] with w hw g
      simpa [dist_eq_norm] using hC g.1 g.2 z w hzR.le hw.le
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := fun g : C(disk,ℂ) => fun z : disk => g z)
    (𝔖 := {K | IsCompact K}) (fun _ h => h)
    (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding)
  · intro K _
    exact heq.equicontinuousOn K
  · intro K _ z _
    obtain ⟨C,hC⟩ := hBd z
    exact ⟨Metric.closedBall 0 C,isCompact_closedBall _ _,by simpa using hC⟩

lemma diskExtend_convergence.{u_1} {ι : Type u_1} {l : Filter ι}
    {g : ι → C(disk,ℂ)} {f : C(disk,ℂ)} (h : Tendsto g l (𝓝 f)) :
    TendstoLocallyUniformlyOn (fun i => diskExtend (g i)) (diskExtend f) l disk := by
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simpa only [Function.comp_def,diskExtend_apply] using
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp h

lemma isClosed_diskSchlichtSet : IsClosed diskSchlichtSet := by
  rw [isClosed_iff_forall_filter]
  intro g l hl hs hg
  let := hl
  have hS : ∀ᶠ f : C(disk,ℂ) in l, Schlicht (diskExtend f) :=
    le_principal_iff.mp hs
  have hc := diskExtend_convergence (g := id) hg
  have hhol : ∀ᶠ f : C(disk,ℂ) in l, DifferentiableOn ℂ (diskExtend f) disk :=
    hS.mono (fun _ h => h.1.1)
  have hgH := hc.differentiableOn hhol (show IsOpen disk from Metric.isOpen_ball)
  refine ⟨⟨hgH,?_⟩,?_,?_⟩
  · intro z hz w hw he
    by_contra hne
    obtain ⟨c,hc0,hs⟩ := schlicht_uniform_separation hz hw hne
    have hevent : ∀ᶠ f : C(disk,ℂ) in l, c ≤ ‖diskExtend f w-diskExtend f z‖ :=
      hS.mono (fun f hf => hs (diskExtend f) hf)
    have ht := ((hc.tendsto_at hw).sub (hc.tendsto_at hz)).norm
    have hc' := ge_of_tendsto ht hevent
    rw [he,sub_self,norm_zero] at hc'
    exact not_le_of_gt hc0 hc'
  · apply tendsto_nhds_unique (hc.tendsto_at (show (0 : ℂ) ∈ disk by simp [disk]))
    exact tendsto_const_nhds.congr' (hS.mono (fun _ hf => hf.2.1.symm))
  · apply tendsto_nhds_unique ((hc.deriv hhol (show IsOpen disk from Metric.isOpen_ball)).tendsto_at
      (show (0 : ℂ) ∈ disk by simp [disk]))
    exact tendsto_const_nhds.congr' (hS.mono (fun _ hf => hf.2.2.symm))

lemma isCompact_diskSchlichtSet : IsCompact diskSchlichtSet := by
  rw [← isClosed_diskSchlichtSet.closure_eq]
  apply compact_closure_of_disk_bounds
  · intro R hR
    refine ⟨2/(1-R)^3,?_⟩
    intro g hg z w hz hw
    simpa only [diskExtend_apply] using schlicht_lipschitz_bound hg hR hz hw
  · intro z
    refine ⟨(2/(1-‖(z : ℂ)‖)^3)*‖(z : ℂ)‖,?_⟩
    intro g hg
    simpa only [diskExtend_apply] using schlicht_local_bound hg
      (show ‖(z : ℂ)‖ < 1 by simpa [disk] using z.2) le_rfl

theorem isCompact_univalent_restrictions_oai :
    IsCompact {g : C(Metric.ball (0 : ℂ) 1, ℂ) | ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f (Metric.ball 0 1) ∧ Set.InjOn f (Metric.ball 0 1) ∧
      f 0 = 0 ∧ deriv f 0 = 1 ∧ ∀ z : Metric.ball (0 : ℂ) 1, g z = f z} := by
  have he : {g : C(Metric.ball (0 : ℂ) 1, ℂ) | ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f (Metric.ball 0 1) ∧ Set.InjOn f (Metric.ball 0 1) ∧
      f 0 = 0 ∧ deriv f 0 = 1 ∧ ∀ z : Metric.ball (0 : ℂ) 1, g z = f z} = diskSchlichtSet := by
    ext g
    constructor
    · rintro ⟨f, hd, hi, h0, h1, hg⟩
      have hon : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskExtend g z = f z := fun z hz =>
        (diskExtend_apply g ⟨z, hz⟩).trans (hg ⟨z, hz⟩)
      have h0m : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
      refine ⟨⟨hd.congr hon, ?_⟩, (hon 0 h0m).trans h0, ?_⟩
      · exact (Set.InjOn.congr hi (fun z hz => (hon z hz).symm))
      · have hev : diskExtend g =ᶠ[𝓝 (0 : ℂ)] f :=
          Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds h0m) hon
        rw [hev.deriv_eq]
        exact h1
    · intro hg
      exact ⟨diskExtend g, hg.1.1, hg.1.2, hg.2.1, hg.2.2, fun z => (diskExtend_apply g z).symm⟩
  rw [he]
  exact isCompact_diskSchlichtSet

end Brennan

end

end OAI
end

theorem solution : type_of% @OAI.Brennan.isCompact_univalent_restrictions_oai := @OAI.Brennan.isCompact_univalent_restrictions_oai
