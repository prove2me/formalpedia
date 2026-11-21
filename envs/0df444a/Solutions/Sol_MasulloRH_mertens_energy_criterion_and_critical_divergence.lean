-- Prove2me | solution 1 for MasulloRH.mertens_energy_criterion_and_critical_divergence
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T04:01:16.161372+00:00
-- url     : https://prove2.me/submissions/19a64445-d5fd-4ac7-992d-93ed6f87cd04

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Theorems.Thm_XiQuantitativePublished_zeta_zero_between_1413_1414
import Mathlib
open Filter Finset Set Topology MeasureTheory ArithmeticFunction Asymptotics
open scoped Interval
noncomputable section
open MasulloRH
namespace MertensEnergyProof
private abbrev Z := ZetaZerosInTraceStrip (1/2)
private def M (n : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 n,(moebius i:ℝ)
private def G (x : ℝ) : ℝ := M ⌊x⌋₊
private theorem measG : Measurable G := (measurable_of_countable M).comp Nat.measurable_floor
private abbrev μ : Measure ℝ := volume.restrict (Ioi (0:ℝ))
private def profile (θ u : ℝ) : ℝ := G (Real.exp u)*Real.exp (-(θ*u))/(1+u)
private def raw (θ u : ℝ) : ℝ := G (Real.exp u)*Real.exp (-(θ*u))
private theorem raw_meas (θ : ℝ) : Measurable (raw θ) := by unfold raw; have := measG; fun_prop
private theorem prof_meas (θ : ℝ) : Measurable (profile θ) := by unfold profile; have := measG; fun_prop
noncomputable def gammaMoment (a : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  u^n * Real.exp (-(a*u)) / (n.factorial : ℝ)

theorem gammaMoment_nonneg (a : ℝ) (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ gammaMoment a n u := by
  unfold gammaMoment
  positivity

theorem gammaMoment_integrable {a : ℝ} (ha : 0 < a) (n : ℕ) :
    IntegrableOn (gammaMoment a n) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n:ℝ))
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) zero_lt_one ha
  unfold gammaMoment
  simpa only [IntegrableOn, Real.rpow_one, Real.rpow_natCast, neg_mul] using
    h.div_const (n.factorial : ℝ)
private def J (s : ℂ) (u : ℝ) : ℂ := (G (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ))
private def L (s : ℂ) : ℂ := ∫ u in Ioi (0:ℝ), J s u
private def bump (ε u : ℝ) : ℝ := (1+u)^2*Real.exp (-(ε*u))

private theorem bump_mem {ε : ℝ} (hε : 0 < ε) : MemLp (bump ε) 2 μ := by
  have hpoly (n : ℕ) : MemLp (fun u : ℝ => u^n*Real.exp (-(ε*u))) 2 μ := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    have hi := (gammaMoment_integrable (by linarith : 0 < 2*ε) (2*n)).mul_const (((2*n).factorial):ℝ)
    apply hi.congr
    apply Eventually.of_forall
    intro u
    change gammaMoment (2*ε) (2*n) u * _ = _
    rw [gammaMoment,div_mul_cancel₀ _ (by exact_mod_cast (2*n).factorial_ne_zero)]
    dsimp only
    rw [mul_pow,←Real.exp_nat_mul,←pow_mul]
    norm_num
    ring_nf
  have h := ((hpoly 0).add ((hpoly 1).const_mul 2)).add (hpoly 2)
  apply (memLp_congr_ae _).mp h
  apply Eventually.of_forall
  intro u; dsimp [bump]; ring

private theorem J_meas (s : ℂ) : Measurable (J s) := by
  have h := measG; unfold J; fun_prop
private theorem J_norm {θ ε : ℝ} {s : ℂ} (hs : θ+ε ≤ s.re) {u : ℝ} (hu : 0 ≤ u) :
    ‖J s u‖  ≤  ‖profile θ u‖*((1+u)*Real.exp (-(ε*u))) := by
  have hden : 0 < 1+u := by linarith
  have he (z : ℂ) : (-z*(u:ℂ)).re = -(z.re*u) := by simp [Complex.mul_re]
  simp only [J,profile,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,he,abs_mul,abs_div,
    abs_of_pos (Real.exp_pos _),abs_of_pos hden]
  have hmul := Real.exp_le_exp.mpr (show -(s.re*u)  ≤  -(θ*u)+ -(ε*u) by nlinarith [mul_le_mul_of_nonneg_right hs hu])
  rw [Real.exp_add] at hmul
  apply (mul_le_mul_of_nonneg_left hmul (abs_nonneg _)).trans_eq
  field_simp

private theorem L_diff {θ : ℝ} (hp : MemLp (profile θ) 2 μ) {s : ℂ} (hs : θ < s.re) : DifferentiableAt ℂ L s := by
  let ε := (s.re-θ)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let U := {z : ℂ | θ+ε < z.re}
  have hU : U ∈ 𝓝 s := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp [ε]; linarith)
  let Bd (u : ℝ) := ‖profile θ u‖*bump ε u
  have hBd : Integrable Bd μ := hp.norm.integrable_mul (bump_mem hε)
  have hder (u : ℝ) (z : ℂ) : HasDerivAt (fun w => J w u) (-(u:ℂ)*J z u) z := by
    have h : HasDerivAt (fun w : ℂ => -w*(u:ℂ)) (-(u:ℂ)) z := by simpa using (hasDerivAt_id z).neg.mul_const (u:ℂ)
    exact (h.cexp.const_mul (G (Real.exp u):ℂ)).congr_deriv (by unfold J; ring)
  have hint : Integrable (J s) μ := by
    apply hBd.mono' (J_meas s).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : 0 ≤ u := le_of_lt hu
    have hj := J_norm (by dsimp [ε]; linarith : θ+ε ≤ s.re) hu'
    exact hj.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by nlinarith : 1+u ≤ (1+u)^2) (Real.exp_nonneg _)) (norm_nonneg _))
  have hdom : ∀ᵐ u : ℝ ∂μ, ∀ z ∈ U, ‖-(u:ℂ)*J z u‖  ≤  Bd u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro z hz
    have hu' := le_of_lt (show 0 < u from hu)
    rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg hu']
    apply (mul_le_mul_of_nonneg_left (J_norm (le_of_lt (show θ+ε < z.re from hz)) hu') hu').trans
    change _  ≤  ‖profile θ u‖*((1+u)^2*Real.exp (-(ε*u)))
    calc _ = ‖profile θ u‖*((u*(1+u))*Real.exp (-(ε*u))) := by ring
         _  ≤  _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_nonneg _)) (norm_nonneg _)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=μ) (F:=J) (F':=fun z u => -(u:ℂ)*J z u) (bound:=Bd) hU
    (Eventually.of_forall fun z => (J_meas z).aestronglyMeasurable) hint
    (show Measurable (fun u : ℝ => -(u:ℂ)*J s u) by have h:=J_meas s; fun_prop).aestronglyMeasurable
    hdom hBd (Eventually.of_forall fun u z _ => hder u z)).2
  exact hd.differentiableAt

private theorem zeta₁_eq_product {s : ℂ} (h : s ≠ 1) :
    riemannZeta₁ s = (s-1)*riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul h, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr h), one_mul]

private theorem usual_RH : RiemannHypothesis ↔ ∀ z : Z,z.val.re ≤ 1/2 := by
  rw [riemannHypothesis_iff_zeros_in_strip_on_line]
  constructor
  · exact fun h z => (h z.val z.prop.1 z.prop.2.1 z.prop.2.2.1).le
  · intro h s hzero h0 h1
    let z : Z := ⟨s,hzero,h0,h1,abs_lt.mpr ⟨by linarith,by linarith⟩⟩
    have hu : s.re ≤ 1/2 := h z
    have hnot (n : ℕ) : s ≠ -n := by
      intro he; have hr := congrArg Complex.re he; simp only [Complex.neg_re,Complex.natCast_re] at hr
      linarith [n.cast_nonneg (α:=ℝ)]
    have hne : s ≠ 1 := fun he => by simp [he] at h1
    have hz' : riemannZeta (1-s)=0 := by rw [riemannZeta_one_sub hnot hne,hzero,mul_zero]
    have h0' : 0 < (1-s).re := by simp; linarith
    have h1' : (1-s).re < 1 := by simp; linarith
    let z' : Z := ⟨1-s,hz',h0',h1',abs_lt.mpr ⟨by linarith,by linarith⟩⟩
    have hl : (1-s).re ≤ 1/2 := h z'
    rw [Complex.sub_re,Complex.one_re] at hl
    linarith

private def mf (n : ℕ) : ℂ := (moebius n : ℂ)
private theorem cm (n : ℕ) : (M n:ℂ) = ∑ k ∈ Finset.Icc 1 n,mf k := by
  unfold M mf; push_cast; rfl
private theorem Mbound (n : ℕ) : |M n| ≤ n := by
  calc _ ≤ ∑ k ∈ Finset.Icc 1 n,|(moebius k:ℝ)| := Finset.abs_sum_le_sum_abs ..
       _ ≤ ∑ _k ∈ Finset.Icc 1 n,(1:ℝ) := sum_le_sum fun k _ => by exact_mod_cast (abs_moebius_le_one (n:=k))
       _ = _ := by simp
private theorem Mbig : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,mf k) =O[atTop] (fun n : ℕ => (n:ℝ)^(1:ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards with n
  rw [←cm,Complex.norm_real,Real.norm_eq_abs,Real.rpow_one,Real.norm_of_nonneg (Nat.cast_nonneg _),one_mul]
  exact Mbound n

private theorem initial_mellin {s : ℂ} (hs : 1<s.re) : riemannZeta s*(s*L s)=1 := by
  have hi := LSeries_eq_mul_integral mf (r:=1) (by norm_num) hs (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs) Mbig
  have hj : L s = ∫ t in Ioi (1:ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,mf k) * (t:ℂ)^(-(s+1)) := by
    let H (t : ℝ) := (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,mf k) * (t:ℂ)^(-(s+1))
    have h := integral_comp_exp_Ioi H 0
    rw [Real.exp_zero] at h
    apply Eq.trans _ h
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change (G (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ)) = Real.exp u • H (Real.exp u)
    unfold H G
    rw [←cm,Algebra.smul_def,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),←Complex.ofReal_log (Real.exp_nonneg _),Real.log_exp]
    change _ = ((Real.exp u:ℝ):ℂ) * _
    rw [Complex.ofReal_exp,mul_left_comm,←Complex.exp_add]
    congr 2
    ring
  have h₀ := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at h₀
  change riemannZeta s*LSeries mf s=1 at h₀
  rwa [hi,←hj] at h₀

private theorem product_id {θ : ℝ} (hθ : θ<1) (hp : MemLp (profile θ) 2 μ) {s : ℂ} (hs : θ<s.re) :
    riemannZeta₁ s * (s*L s)=s-1 := by
  let U := {z : ℂ | θ<z.re}
  have ho : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hc : IsPreconnected U := (convex_halfSpace_re_gt θ).isPreconnected
  have ha : AnalyticOnNhd ℂ (fun z => riemannZeta₁ z*(z*L z)) U := by
    intro z hz
    apply (differentiable_riemannZeta₁.analyticAt _).mul
    exact analyticAt_id.mul (DifferentiableOn.analyticOnNhd (fun w hw => (L_diff hp hw).differentiableWithinAt) ho z hz)
  have hb : AnalyticOnNhd ℂ (fun z : ℂ => z-1) U := fun _ _ => analyticAt_id.sub analyticAt_const
  have hbase : (2:ℂ)∈U := by change θ<(2:ℂ).re; norm_num; linarith
  have he : (fun z => riemannZeta₁ z*(z*L z)) =ᶠ[𝓝 (2:ℂ)] (fun z => z-1) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show (1:ℝ)<(2:ℂ).re by norm_num)] with z hz
    have hn : z≠1 := by intro h; simp [h] at hz
    rw [zeta₁_eq_product hn]
    linear_combination (z-1)*initial_mellin hz
  exact ha.eqOn_of_preconnected_of_eventuallyEq hb hc hbase he hs

private theorem ordinary_strip {θ : ℝ} (hθ : θ<1) (hp : MemLp (profile θ) 2 μ) :
    ∀ z : Z, z.val.re≤θ := by
  intro z
  by_contra! h
  have hn : z.val≠1 := fun he => by have hz:=z.prop.2.2.1; simpa [he] using hz
  have hi := product_id hθ hp h
  rw [zeta₁_eq_product hn,z.prop.1,mul_zero,zero_mul] at hi
  exact hn (sub_eq_zero.mp hi.symm)

private theorem profile_of_raw {θ : ℝ} (h : MemLp (raw θ) 2 μ) : MemLp (profile θ) 2 μ := by
  apply h.norm.mono' (prof_meas θ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change ‖raw θ u/(1+u)‖ ≤ _
  rw [norm_div,Real.norm_of_nonneg (by linarith [show 0<u from hu] : 0≤1+u)]
  exact div_le_self (norm_nonneg (raw θ u)) (show 1≤1+u by linarith [show 0<u from hu])

private def a (θ : ℝ) (n : ℕ) := (M (n+1))^2 * ((n:ℝ)+1)^(-(1+2*θ))
private def dens (θ x : ℝ) := (G x)^2*x^(-(1+2*θ))
private def cell (n : ℕ) : Set ℝ := Ico ((n:ℝ)+1) ((n:ℝ)+1+1)
private theorem a_pos (θ : ℝ) (n : ℕ) : 0≤a θ n := by unfold a; positivity
private theorem dens_meas (θ : ℝ) : Measurable (dens θ) := by unfold dens; have := measG; fun_prop
private theorem dens_nonneg {θ x : ℝ} (hx : 0≤x) : 0≤dens θ x := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx _)
private theorem cell_dom {θ : ℝ} (hθ : 0≤θ) {n : ℕ} {x : ℝ} (hx : x∈cell n) :
    ‖dens θ x‖≤a θ n := by
  have hh : (n:ℝ)+1≤x ∧ x<(n:ℝ)+1+1 := hx
  have hxr : 0≤x := by linarith [n.cast_nonneg (α:=ℝ)]
  have hf : ⌊x⌋₊=n+1 := (Nat.floor_eq_iff hxr).2 (by push_cast; exact hh)
  rw [Real.norm_of_nonneg (dens_nonneg hxr)]
  unfold dens G a
  rw [hf]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) hh.1 (by linarith)) (sq_nonneg _)

private theorem raw_of_samples {θ : ℝ} (hθ : 0≤θ) (h : Summable (a θ)) : MemLp (raw θ) 2 μ := by
  have hd (n : ℕ) : IntegrableOn (dens θ) (cell n) := by
    apply (integrableOn_const (C:=a θ n) (s:=cell n) (μ:=volume) measure_Ico_lt_top.ne).mono' (dens_meas θ).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    exact cell_dom hθ hx
  have hi (n : ℕ) : (∫ x in cell n,‖dens θ x‖) ≤ a θ n := by
    calc _ ≤ ∫ _ in cell n,a θ n := setIntegral_mono_on (hd n).norm (integrableOn_const measure_Ico_lt_top.ne) measurableSet_Ico (fun _ hx => cell_dom hθ hx)
         _ = _ := by rw [setIntegral_const,cell,Real.volume_real_Ico_of_le (by linarith),smul_eq_mul]; ring
  have hm := integrableOn_iUnion_of_summable_integral_norm hd (Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hi h)
  have hh : Ioi (1:ℝ) ⊆ ⋃ n : ℕ,cell n := by
    intro x hx
    have hxr : 1<x := hx
    have hfloor : 1≤⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hxr.le
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ⌊x⌋₊ ≠0)
    apply mem_iUnion.mpr ⟨n,?_⟩
    have hf := (Nat.floor_eq_iff (by linarith : 0≤x)).mp hn
    simpa only [cell,Set.mem_Ico,Nat.cast_succ] using hf
  have hh' := (integrableOn_comp_exp_Ioi (dens θ) 0).2 (by simpa using hm.mono_set hh)
  apply (memLp_two_iff_integrable_sq (raw_meas θ).aestronglyMeasurable).2
  apply hh'.congr (Eventually.of_forall fun u => ?_)
  change Real.exp u*dens θ (Real.exp u)=(raw θ u)^2
  rw [dens,raw,mul_pow,←Real.exp_mul,←Real.exp_nat_mul]
  push_cast
  rw [mul_left_comm,←Real.exp_add]
  congr 2
  ring

private theorem sum_of_RH (hRH : RiemannHypothesis) {θ : ℝ} (hθ : 1/2<θ) : Summable (a θ) := by
  let d := (θ-1/2)/2
  have hd : 0<d := by dsimp [d]; linarith
  obtain ⟨C,hC⟩ := (moebius_summatory_rpow_bound_of_riemannHypothesis hRH d hd).exists_nonneg
  obtain ⟨hc,hb⟩ := hC
  have hpow : Summable (fun n : ℕ => ((n:ℝ)+1)^(-1-2*d)) := by
    have hs := (Real.summable_nat_rpow.mpr (show -1-2*d < -1 by linarith))
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  apply Summable.of_norm_bounded_eventually_nat (g:=fun n : ℕ => C^2*(((n:ℝ)+1)^(-1-2*d))) (hpow.mul_left _)
  have ht : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
  filter_upwards [ht.eventually hb.bound] with n hn
  let r := (n:ℝ)+1
  have hr : 0<r := by dsimp [r]; positivity
  have hcm : ‖(∑ i ∈ Finset.Icc 1 (n+1),(moebius i:ℂ))‖=|M (n+1)| := by change ‖∑ i ∈ Finset.Icc 1 (n+1),mf i‖=_; rw [←cm]; simp
  rw [hcm,Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),Nat.cast_succ] at hn
  have hs : (M (n+1))^2≤(C*r^(1/2+d))^2 := by
    have hmul := mul_self_le_mul_self (abs_nonneg _) hn; nlinarith [sq_abs (M (n+1))]
  rw [Real.norm_of_nonneg (a_pos _ _)]
  change (M (n+1))^2*r^(-(1+2*θ)) ≤ C^2*r^(-1-2*d)
  apply (mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hr.le _)).trans_eq
  rw [mul_pow,←Real.rpow_mul_natCast hr.le,mul_assoc,←Real.rpow_add hr]
  congr 2
  dsimp [d]; push_cast; ring

private def mass (θ : ℝ) := ∫ u in Ioi (0:ℝ),(raw θ u)^2
private theorem mass_nonneg (θ : ℝ) : 0≤ mass θ := integral_nonneg fun _ => sq_nonneg _
private theorem radial_bound {θ t : ℝ} (hr : MemLp (raw θ) 2 μ) (ht : 0<t) {s : ℂ} (hs : s.re=θ+t) :
    2*t*‖L s‖^2 ≤ mass θ := by
  let g (u : ℝ) := Real.exp (-t*u)
  have hsquare (u : ℝ) : (g u)^2 = Real.exp ((-(2*t))*u) := by
    dsimp [g]; rw [←Real.exp_nat_mul]; congr 1; push_cast; ring
  have hg : MemLp g 2 μ := by
    apply (memLp_two_iff_integrable_sq (by dsimp [g]; fun_prop)).2
    simp_rw [hsquare]
    exact integrableOn_exp_mul_Ioi (by linarith) 0
  have hgpos (u : ℝ) : 0≤g u := (Real.exp_pos _).le
  have hm : (∫ u, ‖g u‖^(2:ℝ) ∂μ) = 1/(2*t) := by
    simp_rw [Real.rpow_two,Real.norm_of_nonneg (hgpos _),hsquare]
    rw [μ,integral_exp_mul_Ioi (by linarith) 0]
    simp
  have hm' : (∫ u, ‖raw θ u‖^(2:ℝ) ∂μ)=mass θ := by
    simp [mass,μ,Real.norm_eq_abs,sq_abs]
  have hc := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ:=μ) Real.HolderConjugate.two_two
    (f:=raw θ) (g:=g) (by simpa using hr) (by simpa using hg)
  rw [hm,hm',←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow] at hc
  have hnorm : ‖L s‖ ≤ Real.sqrt (mass θ)*Real.sqrt (1/(2*t)) := by
    apply (norm_integral_le_integral_norm (J s)).trans (le_trans (le_of_eq ?_) hc)
    apply integral_congr_ae (Eventually.of_forall fun u => ?_)
    change ‖(G (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ))‖ = ‖G (Real.exp u)*Real.exp (-(θ*u))‖*‖g u‖
    rw [norm_mul,Complex.norm_real,Complex.norm_exp,norm_mul,Real.norm_of_nonneg (Real.exp_nonneg _),
      Real.norm_of_nonneg (show 0≤g u from (Real.exp_pos _).le),mul_assoc,←Real.exp_add]
    congr 2
    simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,hs]
    ring
  have hf := mul_self_le_mul_self (norm_nonneg _) hnorm
  have hrhs : (Real.sqrt (mass θ)*Real.sqrt (1/(2*t)))^2 = mass θ/(2*t) := by
    rw [mul_pow,Real.sq_sqrt (mass_nonneg θ),Real.sq_sqrt (by positivity)]; ring
  have hlast : ‖L s‖^2≤ mass θ/(2*t) := by rw [←hrhs]; nlinarith only [hf]
  have := (le_div_iff₀ (by positivity : 0<2*t)).mp hlast
  linarith

private theorem boundary_zero {θ : ℝ} (hθ : θ<1) (hr : MemLp (raw θ) 2 μ) (z : Z) (hz : z.val.re=θ) :
    False := by
  let ρ := z.val
  have hne : ρ≠1 := fun he => by have h := z.prop.2.2.1; change ρ.re<1 at h; simp [he] at h
  have hz₁ : riemannZeta₁ ρ=0 := by rw [zeta₁_eq_product hne,z.prop.1,mul_zero]
  obtain ⟨C,hC,hb⟩ := (differentiable_riemannZeta₁ ρ).hasDerivAt.isBigO_sub.exists_nonneg
  have hv : Tendsto (fun t : ℝ => ρ+(t:ℂ)) (𝓝[>] 0) (𝓝 ρ) := by
    have h : Tendsto (fun t : ℝ => ρ+(t:ℂ)) (𝓝 0) (𝓝 (ρ+(0:ℂ))) := tendsto_const_nhds.add Complex.continuous_ofReal.continuousAt
    simpa using h.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from inf_le_left)
  let K := C^2*(‖ρ‖+1)^2*mass θ
  have hp := profile_of_raw hr
  have hfinal : ∀ᶠ (t : ℝ) in 𝓝[>] (0:ℝ), ‖(ρ+(t:ℂ))-1‖^2 ≤ K*t := by
    filter_upwards [hv.eventually hb.bound,self_mem_nhdsWithin,
      (show ∀ᶠ t : ℝ in 𝓝[>] 0, t<1 from (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono inf_le_left)] with t ht ht0 ht1
    have htpos : 0<t := ht0
    let s := ρ+(t:ℂ)
    have hs : s.re=θ+t := by dsimp [s,ρ]; simp [hz]
    have hs' : ‖s‖≤‖ρ‖+1 := by
      apply (norm_add_le _ _).trans
      rw [Complex.norm_real,Real.norm_of_nonneg htpos.le]; linarith
    have hzc : ‖riemannZeta₁ s‖≤C*t := by simpa [s,hz₁,Complex.norm_real,Real.norm_of_nonneg htpos.le] using ht
    have hi := product_id hθ hp (s:=s) (by rw [hs]; linarith)
    have hrad := radial_bound hr htpos hs
    have hcap : t*‖L s‖^2 ≤ mass θ := by nlinarith only [hrad,mul_nonneg htpos.le (sq_nonneg ‖L s‖)]
    have hnorm : ‖s-1‖ ≤ (C*t)*(‖ρ‖+1)*‖L s‖ := by
      rw [←hi,norm_mul,norm_mul,←mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul hzc hs' (norm_nonneg _) (mul_nonneg hC htpos.le)) (norm_nonneg _)
    change ‖s-1‖^2≤K*t
    calc _ ≤ ((C*t)*(‖ρ‖+1)*‖L s‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm _
         _ = (C^2*(‖ρ‖+1)^2*t)*(t*‖L s‖^2) := by ring
         _ ≤ (C^2*(‖ρ‖+1)^2*t)*mass θ := mul_le_mul_of_nonneg_left hcap (by positivity)
         _ = _ := by dsimp [K]; ring
  have hleft : Tendsto (fun t : ℝ => ‖(ρ+(t:ℂ))-1‖^2) (𝓝[>] 0) (𝓝 (‖ρ-1‖^2)) := ((hv.sub_const _).norm).pow _
  have hright : Tendsto (fun t : ℝ => K*t) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=K)).mul (tendsto_id.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from inf_le_left))
  have h := le_of_tendsto_of_tendsto hleft hright hfinal
  have hn := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  nlinarith [sq_pos_of_pos hn]
private def A (N : ℕ) : ℝ := ∑ n ∈ range N,(M (n+1))^2
private def quad : Prop := ∀ d : ℝ,0<d → ∃ C : ℝ,0≤C ∧ ∀ N : ℕ, A N≤C*((N:ℝ)+1)^(2+d)

private theorem quad_of_RH (h : RiemannHypothesis) : quad := by
  intro d hd
  let θ := 1/2+d/2
  have hs := sum_of_RH h (θ:=θ) (by dsimp [θ]; linarith)
  refine ⟨∑' j,a θ j,tsum_nonneg (a_pos θ),fun N => ?_⟩
  have ht (n : ℕ) (hn : n ∈ range N) : (M (n+1))^2 ≤ a θ n*((N:ℝ)+1)^(2+d) := by
    let r := (n:ℝ)+1
    have hr : 0<r := by dsimp [r]; positivity
    have hnr : (n:ℝ)<N := by exact_mod_cast mem_range.mp hn
    have hrN : r≤(N:ℝ)+1 := by dsimp [r]; linarith
    have he : a θ n*r^(2+d) = (M (n+1))^2 := by
      change ((M (n+1))^2*r^(-(1+2*θ)))*r^(2+d) = _
      rw [mul_assoc,←Real.rpow_add hr,show -(1+2*θ)+(2+d)=0 by dsimp [θ]; ring,Real.rpow_zero,mul_one]
    exact (le_of_eq he.symm).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hrN (by linarith)) (a_pos _ _))
  calc A N ≤ ∑ n ∈ range N,a θ n*((N:ℝ)+1)^(2+d) := sum_le_sum ht
       _ = (∑ n ∈ range N,a θ n)*((N:ℝ)+1)^(2+d) := (Finset.sum_mul ..).symm
       _ ≤ _ := mul_le_mul_of_nonneg_right (hs.sum_le_tsum _ (fun i _ => a_pos _ i)) (by positivity)

private theorem summable_of_quad (h : quad) {θ : ℝ} (hθ : 1/2<θ) : Summable (a θ) := by
  let d := θ-1/2
  let p := 2+d
  let q := 1+2*θ
  have hd : 0<d := by dsimp [d]; linarith
  have hp : 0≤p := by dsimp [p]; linarith
  have hq : p<q := by dsimp [p,q,d]; linarith
  obtain ⟨C,hC,hb⟩ := h d hd
  let b (n : ℕ) := (M (n+1))^2
  have hO : (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n,b i) =O[atTop] (fun n : ℕ => (n:ℝ)^p) := by
    apply Asymptotics.IsBigO.of_bound (C*3^p)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : 1≤(n:ℝ) := by exact_mod_cast hn
    have hs : (∑ i ∈ Finset.Icc 1 n,b i) ≤ A (n+1) :=
      sum_le_sum_of_subset_of_nonneg (fun i hi => mem_range.mpr (by have := (mem_Icc.mp hi).2; omega)) (fun i _ _ => sq_nonneg _)
    have hpos : 0≤∑ i ∈ Finset.Icc 1 n,b i := sum_nonneg (fun _ _ => sq_nonneg _)
    rw [Real.norm_of_nonneg hpos,Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) p)]
    apply hs.trans ((hb (n+1)).trans ?_)
    push_cast
    calc C*((n:ℝ)+1+1)^p ≤ C*(3*n)^p := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hp) hC
         _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
  have hS : LSeriesSummable (fun n => (b n:ℂ)) (q:ℂ) :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun _ => sq_nonneg _) hp (by simpa)
  apply Summable.of_norm_bounded_eventually_nat (g:=fun n => ‖LSeries.term (fun n => (b n:ℂ)) (q:ℂ) n‖) hS.norm
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : 0<(n:ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  rw [LSeries.term_of_ne_zero (by omega),norm_div,Complex.norm_real,Real.norm_of_nonneg (show 0≤b n from sq_nonneg _)]
  change ‖b n*((n:ℝ)+1)^(-q)‖ ≤ b n/‖((n:ℕ):ℂ)^(q:ℂ)‖
  rw [show (n:ℂ)=((n:ℝ):ℂ) by simp,Complex.norm_cpow_eq_rpow_re_of_pos hnR,Complex.ofReal_re,
    Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)),
    Real.rpow_neg (by positivity),←div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (Real.rpow_pos_of_pos hnR q)
    (Real.rpow_le_rpow hnR.le (by linarith) (hp.trans hq.le))

private theorem rh_of_summable (h : ∀ θ : ℝ,1/2<θ → Summable (a θ)) : RiemannHypothesis := by
  apply usual_RH.2
  intro z
  by_contra! hr
  let θ := (1/2+z.val.re)/2
  have hlo : 1/2<θ := by dsimp [θ]; linarith
  have hhi : θ<z.val.re := by dsimp [θ]; linarith
  have hh := ordinary_strip (hhi.trans z.prop.2.2.1) (profile_of_raw (raw_of_samples (by linarith) (h θ hlo))) z
  linarith

private theorem no_critical_energy : ¬Summable (a (1/2)) := by
  intro h
  obtain ⟨t,ht,hz⟩ := XiQuantitativePublished.zeta_zero_between_1413_1414
  let s : ℂ := 1/2+t*Complex.I
  have hr : s.re=1/2 := by simp [s,Complex.mul_re]
  let z : Z := ⟨s,hz,by rw [hr]; norm_num,by rw [hr]; norm_num,by rw [hr]; norm_num⟩
  exact boundary_zero (by norm_num : (1/2:ℝ)<1) (raw_of_samples (by norm_num) h) z hr

end MertensEnergyProof
open MertensEnergyProof

theorem solution :
    let M (n : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 n,(moebius i:ℝ)
    let a (θ : ℝ) (n : ℕ) := (M (n+1))^2*((n:ℝ)+1)^(-(1+2*θ))
    (RiemannHypothesis ↔ ∀ θ : ℝ,1/2<θ → Summable (a θ)) ∧
    (RiemannHypothesis ↔ ∀ d : ℝ,0<d → ∃ C : ℝ,0≤C ∧ ∀ N : ℕ,
      (∑ n ∈ range N,(M (n+1))^2) ≤ C*((N:ℝ)+1)^(2+d)) ∧
    (∀ θ : ℝ,0≤θ → θ<1 → Summable (a θ) →
      ∀ z : ZetaZerosInTraceStrip (1/2), z.val.re<θ) ∧
    ¬Summable (a (1/2)) := by
  dsimp only
  refine ⟨⟨fun h _ hθ => sum_of_RH h hθ,rh_of_summable⟩,
    ⟨quad_of_RH,fun h => rh_of_summable (fun _ hθ => summable_of_quad h hθ)⟩,?_,no_critical_energy⟩
  intro θ hθ h1 hs z
  have hr := raw_of_samples hθ hs
  exact lt_of_le_of_ne (ordinary_strip h1 (profile_of_raw hr) z) (fun he => boundary_zero h1 hr z he)

