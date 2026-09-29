-- Prove2me | solution 1 for ModularCurve.exists_meromorphic_logDeriv_eq_of_int_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/f7353b36-acfd-57e1-86f0-f05c6fdd7053

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue

open scoped Topology
open Filter Set Metric

namespace ModularCurve
namespace WeierstrassIntegration

theorem int_eq_zero_of_div_eventuallyEq_analytic {n : ℤ} {a : ℂ} {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h a) (heq : ∀ᶠ z in 𝓝[≠] a, (n : ℂ) / (z - a) = h z) : n = 0 := by

  have h1 : Tendsto (fun z : ℂ => h z * (z - a)) (𝓝[≠] a) (𝓝 (h a * (a - a))) :=
    ((hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      ((continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  rw [sub_self, mul_zero] at h1
  have h2 : Tendsto (fun _ : ℂ => (n : ℂ)) (𝓝[≠] a) (𝓝 0) := by
    refine h1.congr' ?_
    filter_upwards [heq, self_mem_nhdsWithin] with z hz hza
    have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
    rw [← hz, div_mul_cancel₀ _ hza']
  have h3 : (n : ℂ) = 0 := tendsto_nhds_unique tendsto_const_nhds h2
  exact_mod_cast h3

variable {m : ℂ → ℤ} {ω : ℂ → ℂ}

def ResidueHyp (m : ℂ → ℤ) (ω : ℂ → ℂ) : Prop :=
  ∀ a : ℂ, 0 < a.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
    (∀ᶠ z in 𝓝[≠] a, ω z = (m a : ℂ) / (z - a) + g z) ∧ (m a = 0 → ω a = g a)

theorem ResidueHyp.analyticAt (H : ResidueHyp m ω) {a : ℂ} (ha : 0 < a.im) (hm : m a = 0) :
    AnalyticAt ℂ ω a := by
  obtain ⟨g, hg, heq, hval⟩ := H a ha
  refine hg.congr ?_
  have heq' : ∀ᶠ z in 𝓝 a, z ≠ a → ω z = g z := by
    have := eventually_nhdsWithin_iff.mp heq
    filter_upwards [this] with z hz hza
    rw [hz hza, hm, Int.cast_zero, zero_div, zero_add]
  filter_upwards [heq'] with z hz
  by_cases hza : z = a
  · rw [hza, hval hm]
  · exact (hz hza).symm

theorem ResidueHyp.eventually_eq_zero (H : ResidueHyp m ω) {a : ℂ} (ha : 0 < a.im) :
    ∀ᶠ z in 𝓝[≠] a, m z = 0 := by
  obtain ⟨g, hg, heq, -⟩ := H a ha

  have h1 : ∀ᶠ z in 𝓝 a, z ≠ a → ω z = (m a : ℂ) / (z - a) + g z :=
    eventually_nhdsWithin_iff.mp heq
  have h2 : ∀ᶠ z in 𝓝 a, AnalyticAt ℂ g z := hg.eventually_analyticAt
  have h3 : ∀ᶠ z in 𝓝 a, 0 < z.im := (Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds ha
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and (h2.and h3))
  have hmem : ∀ᶠ z in 𝓝[≠] a, z ∈ ball a ε ∧ z ≠ a := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [ball_mem_nhds a hε] with z hz hza using ⟨hz, hza⟩
  filter_upwards [hmem] with z ⟨hz, hza⟩
  obtain ⟨-, hgz, hzim⟩ := hball z hz

  have hωz : AnalyticAt ℂ ω z := by
    have hP : ∀ᶠ w in 𝓝 z, w ∈ ball a ε ∧ w ≠ a :=
      (isOpen_ball.inter isOpen_ne).mem_nhds ⟨hz, hza⟩
    have : AnalyticAt ℂ (fun w => (m a : ℂ) / (w - a) + g w) z := by
      refine AnalyticAt.add ?_ hgz
      exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const) (sub_ne_zero.mpr hza)
    refine this.congr ?_
    filter_upwards [hP] with w ⟨hw, hwa⟩
    exact ((hball w hw).1 hwa).symm

  obtain ⟨g₁, hg₁, heq₁, -⟩ := H z hzim
  refine int_eq_zero_of_div_eventuallyEq_analytic (hωz.sub hg₁) ?_
  filter_upwards [heq₁] with w hw
  simp only [Pi.sub_apply, hw, add_sub_cancel_right]

theorem ResidueHyp.eventually_imp_eq_zero (H : ResidueHyp m ω) {a : ℂ} (ha : 0 < a.im) :
    ∀ᶠ z in 𝓝 a, z ≠ a → m z = 0 :=
  eventually_nhdsWithin_iff.mp (H.eventually_eq_zero ha)

theorem ResidueHyp.finite_support_inter (H : ResidueHyp m ω) {K : Set ℂ} (hK : IsCompact K)
    (hKU : ∀ z ∈ K, 0 < z.im) : {z ∈ K | m z ≠ 0}.Finite := by
  let V : ℂ → Set ℂ := fun a => {z | z ≠ a → m z = 0}
  have hV : ∀ a ∈ K, V a ∈ 𝓝 a := fun a ha => H.eventually_imp_eq_zero (hKU a ha)
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover V hV
  refine (t.finite_toSet).subset ?_
  intro z ⟨hzK, hmz⟩
  obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp (hcover hzK)
  by_contra hzt
  have : z ≠ a := fun h => hzt (h ▸ ha)
  exact hmz (hza this)

section Products

variable (T : Finset ℂ) (n : ℂ → ℤ)

noncomputable def zprod (z : ℂ) : ℂ := ∏ s ∈ T, (z - s) ^ (n s)

noncomputable def polarPart (z : ℂ) : ℂ := ∑ s ∈ T, (n s : ℂ) / (z - s)

theorem zprod_ne_zero {z : ℂ} (hz : z ∉ T) : zprod T n z ≠ 0 := by
  unfold zprod
  refine Finset.prod_ne_zero_iff.mpr fun s hs => zpow_ne_zero _ (sub_ne_zero.mpr ?_)
  rintro rfl; exact hz hs

theorem zprod_eq_zero {z : ℂ} (hz : z ∈ T) (hn : n z ≠ 0) : zprod T n z = 0 := by
  unfold zprod
  exact Finset.prod_eq_zero hz (by rw [sub_self, zero_zpow _ hn])

theorem analyticAt_zprod {z : ℂ} (hz : z ∉ T) : AnalyticAt ℂ (zprod T n) z := by
  have : zprod T n = fun w => ∏ s ∈ T, (w - s) ^ (n s) := rfl
  rw [this]
  refine Finset.analyticAt_fun_prod T fun s hs => ?_
  refine ((analyticAt_id).sub analyticAt_const).zpow ?_
  exact sub_ne_zero.mpr (by rintro rfl; exact hz hs)

theorem analyticAt_polarPart {z : ℂ} (hz : z ∉ T) : AnalyticAt ℂ (polarPart T n) z := by
  have : polarPart T n = fun w => ∑ s ∈ T, (n s : ℂ) / (w - s) := rfl
  rw [this]
  refine Finset.analyticAt_fun_sum T fun s hs => ?_
  refine analyticAt_const.div ((analyticAt_id).sub analyticAt_const) ?_
  exact sub_ne_zero.mpr (by rintro rfl; exact hz hs)

theorem hasDerivAt_zprod {z : ℂ} (hz : z ∉ T) :
    HasDerivAt (zprod T n) (zprod T n z * polarPart T n z) z := by
  classical
  unfold zprod polarPart
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, mul_zero]
    exact hasDerivAt_const z (1 : ℂ)
  | @insert a T haT ih =>
    have hza : z ≠ a := by rintro rfl; exact hz (Finset.mem_insert_self _ _)
    have hzT : z ∉ T := fun h => hz (Finset.mem_insert_of_mem h)
    have hza' : (z - a) ≠ 0 := sub_ne_zero.mpr hza
    have ih' := ih hzT
    have hfa : HasDerivAt (fun w : ℂ => (w - a) ^ (n a))
        ((n a : ℂ) * (z - a) ^ (n a - 1)) z := by
      have := (hasDerivAt_zpow (n a) (z - a) (Or.inl hza')).comp z
        ((hasDerivAt_id z).sub_const a)
      simp at this
      exact this
    have hprod := hfa.mul ih'
    have heq : (fun w : ℂ => ∏ s ∈ insert a T, (w - s) ^ n s) =
        fun w : ℂ => (w - a) ^ n a * ∏ s ∈ T, (w - s) ^ n s := by
      funext w; rw [Finset.prod_insert haT]
    rw [heq]
    refine hprod.congr_deriv (Eq.symm ?_)
    rw [Finset.prod_insert haT, Finset.sum_insert haT, zpow_sub_one₀ hza']
    field_simp

variable {T n}

theorem meromorphicOrderAt_zprod [DecidableEq ℂ] (z : ℂ) :
    meromorphicOrderAt (zprod T n) z = ((if z ∈ T then n z else 0 : ℤ) : WithTop ℤ) := by
  have hzp : zprod T n = ∏ s ∈ T, fun w : ℂ => (w - s) ^ (n s) := by
    funext w; simp [zprod, Finset.prod_apply]
  rw [hzp, meromorphicOrderAt_prod (fun s _ => by fun_prop)]
  have hterm : ∀ s ∈ T, meromorphicOrderAt (fun w : ℂ => (w - s) ^ (n s)) z =
      ((if z = s then n s else 0 : ℤ) : WithTop ℤ) := by
    intro s _
    by_cases hzs : z = s
    · subst hzs
      rw [if_pos rfl]
      exact fun_meromorphicOrderAt_zpow_id_sub_const
    · rw [if_neg hzs]
      have han : AnalyticAt ℂ (fun w : ℂ => (w - s) ^ (n s)) z :=
        ((analyticAt_id).sub analyticAt_const).zpow (sub_ne_zero.mpr hzs)
      rw [han.meromorphicOrderAt_eq, (han.analyticOrderAt_eq_zero.mpr
        (zpow_ne_zero _ (sub_ne_zero.mpr hzs)))]
      rfl
  rw [Finset.sum_congr rfl hterm, ← WithTop.coe_sum]
  congr 1
  rw [Finset.sum_ite_eq]

end Products

theorem isPreconnected_range_diff_of_countable {e : ℂ → ℂ} (he : Continuous e)
    (hinj : Function.Injective e) {S : Set ℂ} (hS : S.Countable) :
    IsPreconnected (range e \ S) := by
  have h1 : (e ⁻¹' S).Countable := hS.preimage_of_injOn (hinj.injOn)
  have h2 : IsPathConnected (e ⁻¹' S)ᶜ :=
    h1.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
  have h3 : IsPathConnected (e '' (e ⁻¹' S)ᶜ) := h2.image' he.continuousOn
  have h4 : e '' (e ⁻¹' S)ᶜ = range e \ S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨mem_range_self w, hw⟩
    · rintro ⟨⟨w, rfl⟩, hz⟩
      exact ⟨w, hz, rfl⟩
  rw [← h4]
  exact h3.isConnected.isPreconnected

theorem isPreconnected_ball_diff_of_countable (c : ℂ) {r : ℝ} (hr : 0 < r) {S : Set ℂ}
    (hS : S.Countable) : IsPreconnected (ball c r \ S) := by
  let e := OpenPartialHomeomorph.univBall c r
  have hrange : range (e : ℂ → ℂ) = ball c r := by
    rw [← image_univ, ← OpenPartialHomeomorph.univBall_source c r, e.image_source_eq_target,
      OpenPartialHomeomorph.univBall_target c hr]
  have hinj : Function.Injective (e : ℂ → ℂ) := by
    intro x y hxy
    exact e.injOn (by rw [OpenPartialHomeomorph.univBall_source]; trivial)
      (by rw [OpenPartialHomeomorph.univBall_source]; trivial) hxy
  rw [← hrange]
  exact isPreconnected_range_diff_of_countable (OpenPartialHomeomorph.continuous_univBall c r)
    hinj hS

noncomputable def cht (n : ℕ) : ℝ := ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1)

noncomputable def ctr (n : ℕ) : ℂ := (cht n : ℂ) * Complex.I

noncomputable def rad (n : ℕ) : ℝ := (n : ℝ) + 1

theorem rad_pos (n : ℕ) : 0 < rad n := by unfold rad; positivity

theorem ctr_im (n : ℕ) : (ctr n).im = cht n := by simp [ctr]

theorem ctr_re (n : ℕ) : (ctr n).re = 0 := by simp [ctr]

theorem cht_sub_rad (n : ℕ) : cht n - rad n = 1 / ((n : ℝ) + 1) := by unfold cht rad; ring

theorem im_pos_of_mem_closedBall {n : ℕ} {z : ℂ} (hz : z ∈ closedBall (ctr n) (rad n)) :
    0 < z.im := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h1 : |(z - ctr n).im| ≤ rad n := (Complex.abs_im_le_norm _).trans hz
  rw [Complex.sub_im, ctr_im] at h1
  have h2 : cht n - rad n ≤ z.im := by
    have := (abs_le.mp h1).1
    linarith
  rw [cht_sub_rad] at h2
  have h3 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem im_pos_of_mem_ball {n : ℕ} {z : ℂ} (hz : z ∈ ball (ctr n) (rad n)) : 0 < z.im :=
  im_pos_of_mem_closedBall (ball_subset_closedBall hz)

theorem dist_ctr_succ (n : ℕ) : dist (ctr n) (ctr (n + 1)) ≤ 1 := by
  rw [dist_eq_norm]
  have : ctr n - ctr (n + 1) = ((cht n - cht (n + 1) : ℝ) : ℂ) * Complex.I := by
    simp [ctr]; ring
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h1 : cht (n + 1) - cht n = 1 + (1 / ((n : ℝ) + 2) - 1 / ((n : ℝ) + 1)) := by
    unfold cht; push_cast; ring
  have h2 : 0 ≤ cht (n + 1) - cht n := by
    rw [h1]
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have h3 : cht (n + 1) - cht n ≤ 1 := by
    rw [h1]
    have : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  rw [abs_sub_comm, abs_of_nonneg h2]
  exact h3

theorem ball_mono_succ (n : ℕ) : ball (ctr n) (rad n) ⊆ ball (ctr (n + 1)) (rad (n + 1)) := by
  intro z hz
  rw [mem_ball] at hz ⊢
  calc dist z (ctr (n + 1)) ≤ dist z (ctr n) + dist (ctr n) (ctr (n + 1)) := dist_triangle _ _ _
    _ < rad n + 1 := add_lt_add_of_lt_of_le hz (dist_ctr_succ n)
    _ = rad (n + 1) := by unfold rad; push_cast; ring

theorem ball_mono {n k : ℕ} (h : n ≤ k) : ball (ctr n) (rad n) ⊆ ball (ctr k) (rad k) := by
  induction h with
  | refl => exact Subset.rfl
  | step _ ih => exact ih.trans (ball_mono_succ _)

theorem exists_mem_ball {z : ℂ} (hz : 0 < z.im) : ∃ n : ℕ, z ∈ ball (ctr n) (rad n) := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((‖z‖ ^ 2 + 3) / (2 * z.im))
  refine ⟨n, ?_⟩
  have hn' : ‖z‖ ^ 2 + 3 < 2 * z.im * ((n : ℝ) + 1) := by
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith
  rw [mem_ball, dist_eq_norm]
  have hr : 0 ≤ rad n := (rad_pos n).le
  rw [← sq_lt_sq₀ (norm_nonneg _) hr, Complex.sq_norm, Complex.normSq_apply]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn'
  simp only [Complex.sub_re, Complex.sub_im, ctr_re, ctr_im, sub_zero]
  have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hε1 : 1 / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hcht : cht n = rad n + 1 / ((n : ℝ) + 1) := by unfold cht rad; ring
  set ε := 1 / ((n : ℝ) + 1) with hε_def
  have hεn : ((n : ℝ) + 1) * ε = 1 := by
    rw [hε_def]; field_simp
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le hε1
  rw [hcht]
  unfold rad
  nlinarith [sq_nonneg ε, hz, mul_pos hz hε, hεn, hε2, hn']

section OneDisc

variable (H : ResidueHyp m ω) (n : ℕ)
include H

noncomputable def poles : Finset ℂ :=
  (H.finite_support_inter (isCompact_closedBall (x := ctr n) (r := rad n))
    (fun _ hz => im_pos_of_mem_closedBall hz)).toFinset

variable {n} in
theorem mem_poles {z : ℂ} : z ∈ poles H n ↔ z ∈ closedBall (ctr n) (rad n) ∧ m z ≠ 0 := by
  unfold poles
  rw [Set.Finite.mem_toFinset]
  rfl

noncomputable def rho (z : ℂ) : ℂ := ω z - polarPart (poles H n) m z

noncomputable def rho' (z : ℂ) : ℂ :=
  if m z = 0 then rho H n z else limUnder (𝓝[≠] z) (rho H n)

variable {n} in
theorem rho'_of_eq_zero {z : ℂ} (hz : m z = 0) :
    rho' H n z = ω z - polarPart (poles H n) m z := by
  simp [rho', hz, rho]

variable {n} in

theorem analyticAt_rho' {z : ℂ} (hzB : z ∈ ball (ctr n) (rad n)) : AnalyticAt ℂ (rho' H n) z := by
  classical
  have hzU : 0 < z.im := im_pos_of_mem_ball hzB
  by_cases hm : m z = 0
  · have hzp : z ∉ poles H n := by
      rw [mem_poles]; exact fun h => h.2 hm
    have hρ : AnalyticAt ℂ (rho H n) z :=
      (H.analyticAt hzU hm).fun_sub (analyticAt_polarPart (poles H n) m hzp)
    refine hρ.congr ?_
    filter_upwards [H.eventually_imp_eq_zero hzU] with w hw
    by_cases hwz : w = z
    · subst hwz; simp [rho', hm]
    · simp [rho', hw hwz]
  · obtain ⟨g, hg, heq, -⟩ := H z hzU
    have hzp : z ∈ poles H n := (mem_poles H).mpr ⟨ball_subset_closedBall hzB, hm⟩
    let h : ℂ → ℂ := fun w => g w - polarPart ((poles H n).erase z) m w
    have hh : AnalyticAt ℂ h z :=
      hg.fun_sub (analyticAt_polarPart ((poles H n).erase z) m (Finset.notMem_erase z _))
    have hρh : rho H n =ᶠ[𝓝[≠] z] h := by
      filter_upwards [heq] with w hw
      simp only [rho, polarPart, hw, h]
      rw [← Finset.add_sum_erase _ _ hzp]
      ring
    have hlim : limUnder (𝓝[≠] z) (rho H n) = h z :=
      ((hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hρh.symm).limUnder_eq
    refine hh.congr ?_
    have h1 := eventually_nhdsWithin_iff.mp hρh
    filter_upwards [h1, H.eventually_imp_eq_zero hzU] with w hw1 hw2
    by_cases hwz : w = z
    · subst hwz
      simp only [rho', if_neg hm, hlim]
    · rw [rho', if_pos (hw2 hwz), hw1 hwz]

theorem differentiableOn_rho' : DifferentiableOn ℂ (rho' H n) (ball (ctr n) (rad n)) :=
  fun _ hz => (analyticAt_rho' H hz).differentiableAt.differentiableWithinAt

theorem exists_primitive_rho' :
    ∃ Φ : ℂ → ℂ, ∀ z ∈ ball (ctr n) (rad n), HasDerivAt Φ (rho' H n z) z :=
  (differentiableOn_rho' H n).isExactOn_ball

noncomputable def Phi : ℂ → ℂ := Classical.choose (exists_primitive_rho' H n)

variable {n} in
theorem hasDerivAt_Phi {z : ℂ} (hz : z ∈ ball (ctr n) (rad n)) :
    HasDerivAt (Phi H n) (rho' H n z) z :=
  Classical.choose_spec (exists_primitive_rho' H n) z hz

variable {n} in
theorem analyticAt_exp_Phi {z : ℂ} (hz : z ∈ ball (ctr n) (rad n)) :
    AnalyticAt ℂ (fun w => Complex.exp (Phi H n w)) z := by
  have hd : DifferentiableOn ℂ (Phi H n) (ball (ctr n) (rad n)) :=
    fun w hw => (hasDerivAt_Phi H hw).differentiableAt.differentiableWithinAt
  exact (hd.analyticAt (isOpen_ball.mem_nhds hz)).cexp

noncomputable def Fpre : ℂ → ℂ := (fun w => Complex.exp (Phi H n w)) * zprod (poles H n) m

theorem Fpre_apply (z : ℂ) : Fpre H n z = Complex.exp (Phi H n z) * zprod (poles H n) m z := rfl

variable {n} in
theorem meromorphicAt_Fpre {z : ℂ} (hz : z ∈ ball (ctr n) (rad n)) : MeromorphicAt (Fpre H n) z := by
  unfold Fpre
  exact (analyticAt_exp_Phi H hz).meromorphicAt.mul (by unfold zprod; fun_prop)

variable {n} in
theorem meromorphicOrderAt_Fpre {z : ℂ} (hz : z ∈ ball (ctr n) (rad n)) :
    meromorphicOrderAt (Fpre H n) z = (m z : WithTop ℤ) := by
  classical
  unfold Fpre
  rw [meromorphicOrderAt_mul_of_ne_zero (analyticAt_exp_Phi H hz) (Complex.exp_ne_zero _),
    meromorphicOrderAt_zprod]
  congr 1
  by_cases hzp : z ∈ poles H n
  · rw [if_pos hzp]
  · rw [if_neg hzp]
    rw [mem_poles, not_and, not_not] at hzp
    exact (hzp (ball_subset_closedBall hz)).symm

variable {n} in
theorem Fpre_eq_zero {z : ℂ} (hz : z ∈ ball (ctr n) (rad n)) (hm : m z ≠ 0) : Fpre H n z = 0 := by
  rw [Fpre_apply, zprod_eq_zero (poles H n) m ((mem_poles H).mpr ⟨ball_subset_closedBall hz, hm⟩) hm,
    mul_zero]

variable {n} in
theorem analyticAt_Fpre {z : ℂ} (hz : z ∈ ball (ctr n) (rad n)) (hm : m z = 0) :
    AnalyticAt ℂ (Fpre H n) z := by
  have hzp : z ∉ poles H n := by rw [mem_poles]; exact fun h => h.2 hm
  unfold Fpre
  exact (analyticAt_exp_Phi H hz).mul (analyticAt_zprod (poles H n) m hzp)

variable {n} in
theorem Fpre_ne_zero {z : ℂ} (hm : m z = 0) : Fpre H n z ≠ 0 := by
  have hzp : z ∉ poles H n := by rw [mem_poles]; exact fun h => h.2 hm
  rw [Fpre_apply]
  exact mul_ne_zero (Complex.exp_ne_zero _) (zprod_ne_zero (poles H n) m hzp)

variable {n} in
theorem hasDerivAt_Fpre {z : ℂ} (hz : z ∈ ball (ctr n) (rad n)) (hm : m z = 0) :
    HasDerivAt (Fpre H n) (ω z * Fpre H n z) z := by
  have hzp : z ∉ poles H n := by rw [mem_poles]; exact fun h => h.2 hm
  have h1 : HasDerivAt (fun w => Complex.exp (Phi H n w))
      (Complex.exp (Phi H n z) * rho' H n z) z := (hasDerivAt_Phi H hz).cexp
  have h2 := hasDerivAt_zprod (poles H n) m hzp
  have h3 := h1.mul h2
  unfold Fpre
  refine h3.congr_deriv (Eq.symm ?_)
  rw [rho'_of_eq_zero H hm]
  try rw [Pi.mul_apply]
  ring

end OneDisc

section Glue

variable (H : ResidueHyp m ω)
include H

theorem exists_base : ∃ z : ℂ, z ∈ ball (ctr 0) (rad 0) ∧ m z = 0 := by
  have h0 : 0 < (ctr 0).im := by
    rw [ctr_im]; unfold cht; norm_num
  have h1 : ∀ᶠ z in 𝓝[≠] ctr 0, z ∈ ball (ctr 0) (rad 0) :=
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (rad_pos 0))
  exact (h1.and (H.eventually_eq_zero h0)).exists

noncomputable def base : ℂ := Classical.choose (exists_base H)

theorem base_mem (n : ℕ) : base H ∈ ball (ctr n) (rad n) :=
  ball_mono (Nat.zero_le n) (Classical.choose_spec (exists_base H)).1

theorem m_base : m (base H) = 0 := (Classical.choose_spec (exists_base H)).2

noncomputable def Fn (n : ℕ) (z : ℂ) : ℂ := Fpre H n z / Fpre H n (base H)

theorem Fn_eq (n : ℕ) : Fn H n = (fun _ => (Fpre H n (base H))⁻¹) * Fpre H n := by
  funext z; simp [Fn, div_eq_inv_mul]

theorem Fn_agree {n k : ℕ} (hnk : n ≤ k) {z : ℂ} (hz : z ∈ ball (ctr n) (rad n)) :
    Fn H n z = Fn H k z := by
  classical
  by_cases hm : m z = 0
  swap
  · simp only [Fn, Fpre_eq_zero H hz hm, Fpre_eq_zero H (ball_mono hnk hz) hm, zero_div]

  let V : Set ℂ := ball (ctr n) (rad n) \ (poles H n : Set ℂ)
  have hVo : IsOpen V := isOpen_ball.sdiff (poles H n).finite_toSet.isClosed
  have hVc : IsPreconnected V :=
    isPreconnected_ball_diff_of_countable _ (rad_pos n) (poles H n).finite_toSet.countable
  have hVm : ∀ w ∈ V, m w = 0 := by
    rintro w ⟨hw1, hw2⟩
    by_contra hmw
    exact hw2 ((mem_poles H).mpr ⟨ball_subset_closedBall hw1, hmw⟩)
  let q : ℂ → ℂ := fun w => Fpre H k w / Fpre H n w
  have hq : ∀ w ∈ V, HasDerivAt q 0 w := by
    intro w hw
    have hmw := hVm w hw
    have h1 := hasDerivAt_Fpre H (ball_mono hnk hw.1) hmw
    have h2 := hasDerivAt_Fpre H hw.1 hmw
    have h3 := h1.div h2 (Fpre_ne_zero H hmw)
    convert h3 using 1
    · rfl
    · rfl
    · rfl
    ring
  have hqd : DifferentiableOn ℂ q V := fun w hw => (hq w hw).differentiableAt.differentiableWithinAt
  have hq0 : V.EqOn (deriv q) 0 := fun w hw => (hq w hw).deriv
  have hzV : z ∈ V := ⟨hz, fun h => ((mem_poles H).mp h).2 hm⟩
  have hbV : base H ∈ V := ⟨base_mem H n, fun h => ((mem_poles H).mp h).2 (m_base H)⟩
  have hconst := hVo.is_const_of_deriv_eq_zero hVc hqd hq0 hzV hbV

  simp only [q] at hconst
  simp only [Fn]
  have ha := Fpre_ne_zero H (n := n) hm
  have hb := Fpre_ne_zero H (n := n) (m_base H)
  have hc := Fpre_ne_zero H (n := k) (m_base H)
  rw [div_eq_div_iff ha hb] at hconst
  rw [div_eq_div_iff hb hc]
  linear_combination -hconst

noncomputable def G (z : ℂ) : ℂ :=
  if h : 0 < z.im then Fn H (Classical.choose (exists_mem_ball h)) z else 0

theorem G_eq {n : ℕ} {z : ℂ} (hz : z ∈ ball (ctr n) (rad n)) : G H z = Fn H n z := by
  have h : 0 < z.im := im_pos_of_mem_ball hz
  rw [G, dif_pos h]
  have hspec := Classical.choose_spec (exists_mem_ball h)
  rcases le_total (Classical.choose (exists_mem_ball h)) n with hle | hle
  · exact Fn_agree H hle hspec
  · exact (Fn_agree H hle hz).symm

theorem G_eventuallyEq {n : ℕ} {z : ℂ} (hz : z ∈ ball (ctr n) (rad n)) :
    G H =ᶠ[𝓝 z] Fn H n :=
  Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) fun _ hw => G_eq H hw

theorem G_spec {a : ℂ} (ha : 0 < a.im) :
    MeromorphicAt (G H) a ∧ meromorphicOrderAt (G H) a = (m a : WithTop ℤ) ∧
      (m a ≠ 0 → G H a = 0) ∧
      (m a = 0 → AnalyticAt ℂ (G H) a ∧ G H a ≠ 0 ∧ HasDerivAt (G H) (ω a * G H a) a) := by
  obtain ⟨n, hn⟩ := exists_mem_ball ha
  have hev := G_eventuallyEq H hn
  have hev' : G H =ᶠ[𝓝[≠] a] Fn H n := hev.filter_mono nhdsWithin_le_nhds
  have hcst : AnalyticAt ℂ (fun _ : ℂ => (Fpre H n (base H))⁻¹) a := analyticAt_const
  have hcst0 : (Fpre H n (base H))⁻¹ ≠ 0 := inv_ne_zero (Fpre_ne_zero H (m_base H))
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine MeromorphicAt.congr ?_ hev'.symm
    rw [Fn_eq]
    exact hcst.meromorphicAt.mul (meromorphicAt_Fpre H hn)
  · rw [meromorphicOrderAt_congr hev', Fn_eq, meromorphicOrderAt_mul_of_ne_zero hcst hcst0,
      meromorphicOrderAt_Fpre H hn]
  · intro hm
    rw [G_eq H hn, Fn, Fpre_eq_zero H hn hm, zero_div]
  · intro hm
    have han : AnalyticAt ℂ (Fn H n) a := by
      rw [Fn_eq]; exact hcst.mul (analyticAt_Fpre H hn hm)
    have hne : Fn H n a ≠ 0 := by
      rw [Fn]; exact div_ne_zero (Fpre_ne_zero H hm) (Fpre_ne_zero H (m_base H))
    have hder : HasDerivAt (Fn H n) (ω a * Fn H n a) a := by
      have := (hasDerivAt_Fpre H hn hm).div_const (Fpre H n (base H))
      simp only [Fn]
      convert this using 1
      · rfl
      · rfl
      · rfl
      ring
    refine ⟨han.congr hev.symm, by rwa [G_eq H hn], ?_⟩
    rw [G_eq H hn]
    exact hder.congr_of_eventuallyEq hev

end Glue

end ModularCurve.WeierstrassIntegration

open ModularCurve.WeierstrassIntegration in
theorem solution
    (m : ℂ → ℤ) (ω : ℂ → ℂ)
    (hres : ∀ a : ℂ, 0 < a.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      (∀ᶠ z in 𝓝[≠] a, ω z = (m a : ℂ) / (z - a) + g z) ∧ (m a = 0 → ω a = g a)) :
    ∃ G : ℂ → ℂ, ∀ a : ℂ, 0 < a.im →
      MeromorphicAt G a ∧ meromorphicOrderAt G a = (m a : WithTop ℤ) ∧
      (m a ≠ 0 → G a = 0) ∧
      (m a = 0 → AnalyticAt ℂ G a ∧ G a ≠ 0 ∧ HasDerivAt G (ω a * G a) a) :=
  ⟨G hres, fun _ ha => G_spec hres ha⟩

end S_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue
end P2MW
export P2MW.S_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue (solution)
