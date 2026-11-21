-- Prove2me | solution 1 for MasulloAudit.one_prime_difference_range_not_closed
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:11:32.338289+00:00
-- url     : https://prove2.me/submissions/1c2e34cb-f7fd-4fec-a40e-2030d80e3336

import Mathlib

open Filter Set Topology MeasureTheory
open scoped ENNReal NNReal
noncomputable section
private def wt (t : ℝ) := ENNReal.ofReal (1+t^2)
private def μ : Measure ℝ := volume.withDensity wt
private abbrev H := Lp ℂ 2 μ
private theorem vol_le : (volume:Measure ℝ)≤μ := by
  rw [←withDensity_one (μ:=(volume:Measure ℝ))]
  apply withDensity_mono;apply ae_of_all;intro x
  change 1≤ENNReal.ofReal (1+x^2)
  exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1:ℝ) ≤ 1+x^2 by nlinarith [sq_nonneg x]))
private theorem ae_eq_vol : ae μ=ae (volume:Measure ℝ) :=
  le_antisymm (withDensity_absolutelyContinuous _ _).ae_le (Measure.absolutelyContinuous_of_le vol_le).ae_le
private theorem ae_shift {P : ℝ→Prop} (h : ∀ᵐ x ∂μ,P x) (t : ℝ) : ∀ᵐ x ∂μ,P (x+t) := by
  rw [ae_eq_vol] at h ⊢
  exact (measurePreserving_add_right volume t).quasiMeasurePreserving.ae h

private theorem periodic_zero {t : ℝ} (ht : 0<t) (f : H) (hf : ∀ᵐ x ∂μ,f x=f (x+t)) : f=0 := by
  let F (x : ℝ) := ‖f x‖^2
  have hint : Integrable F volume := (MemLp.mono_measure vol_le (Lp.memLp f)).integrable_norm_pow (p:=2) (by norm_num)
  have B (s : ℝ) : Integrable (fun x => Real.arctan (x+s)*F x) volume := by
    apply hint.bdd_mul (c:=Real.pi/2) (by fun_prop)
    apply ae_of_all;intro x
    rw [Real.norm_eq_abs,abs_le]
    exact ⟨(Real.neg_pi_div_two_lt_arctan _).le,(Real.arctan_lt_pi_div_two _).le⟩
  have h0 : Integrable (fun x => Real.arctan x * F x) volume := by simpa only [add_zero] using B 0
  have hd := (B t).sub h0
  let G := fun x : ℝ => Real.arctan (x+t)*F x - Real.arctan x*F x
  have hG : ∀ x,0≤G x := fun x => sub_nonneg.mpr (mul_le_mul_of_nonneg_right (Real.arctan_mono (by linarith)) (sq_nonneg _))
  have he : (∫ x,G x)=0 := by
    rw [show (∫ x,G x)=(∫ x, Real.arctan (x+t)*F x) - (∫ x,Real.arctan x*F x) by exact integral_sub (B t) h0]
    apply sub_eq_zero.mpr
    rw [←integral_add_right_eq_self (μ:=volume) (fun x => Real.arctan x*F x) t]
    apply integral_congr_ae
    rw [ae_eq_vol] at hf
    filter_upwards [hf] with x hx
    simp only [F,hx.symm]
  have hZ := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hG) hd).mp he
  apply Lp.ext
  rw [ae_eq_vol]
  filter_upwards [hZ,(ae_eq_vol ▸ Lp.coeFn_zero ℂ 2 μ)] with x hx hz
  change Real.arctan (x+t)*F x - Real.arctan x*F x=0 at hx
  rw [←sub_mul] at hx
  have hn : Real.arctan (x+t)-Real.arctan x≠0 := (sub_pos.mpr (Real.arctan_strictMono (by linarith))).ne'
  have hfz := (mul_eq_zero.mp hx).resolve_left hn
  have hfx : f x=0 := norm_eq_zero.mp (by change ‖f x‖^2=0 at hfz; nlinarith [norm_nonneg (f x)])
  exact hfx.trans hz.symm

private theorem inj_diff (t : ℝ) (ht : 0<t) (D : H→L[ℂ]H)
    (hD : ∀ f : H, (fun x => D f x)=ᵐ[μ] fun x => f x-f (x+t)) : Function.Injective D := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  apply periodic_zero ht f
  have he := hD f
  change D f=0 at hf
  rw [hf] at he
  filter_upwards [he,Lp.coeFn_zero ℂ 2 μ] with x hx hz
  exact sub_eq_zero.mp (hx.symm.trans hz)

private def mval (a b : ℝ) := (b-a)+(b^3-a^3)/3
private theorem μcell {a b : ℝ} (hab : a≤b) : μ (Ioc a b)=ENNReal.ofReal (mval a b) := by
  rw [μ,withDensity_apply _ measurableSet_Ioc]
  have hcont : Continuous (fun x : ℝ => 1+x^2) := by fun_prop
  have hnon : ∀ᵐ x ∂(volume.restrict (Ioc a b)),0≤1+x^2 := ae_of_all _ fun x => by positivity
  change (∫⁻ x in Ioc a b,ENNReal.ofReal (1+x^2))=_
  rw [←ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self) hnon]
  congr 1
  rw [←intervalIntegral.integral_of_le hab, intervalIntegral.integral_add (f:=fun _ : ℝ => (1:ℝ)) (g:=fun x : ℝ => x^2) (continuous_const.intervalIntegrable _ _) ((continuous_id.pow 2).intervalIntegrable _ _)]
  simp [mval,integral_pow]
  ring

private theorem cellFinite (a b : ℝ) : μ (Ioc a b)≠∞ := by
  by_cases h : a≤b
  · rw [μcell h];exact ENNReal.ofReal_ne_top
  · simp [Ioc_eq_empty (by linarith : ¬a<b)]
private def cell (a b : ℝ) : H := indicatorConstLp 2 measurableSet_Ioc (cellFinite a b) (1:ℂ)
private theorem cell_ae (a b : ℝ) : ⇑(cell a b)=ᵐ[μ] (Ioc a b).indicator (fun _ => (1:ℂ)) := indicatorConstLp_coeFn
private theorem cell_norm {a b : ℝ} (hab : a≤b) : ‖cell a b‖^2=mval a b := by
  have hn : 0 ≤ mval a b := by
    dsimp [mval];have h := sub_nonneg.mpr hab
    nlinarith [mul_nonneg h (sq_nonneg (a+b)),mul_nonneg h (sq_nonneg a),mul_nonneg h (sq_nonneg b)]
  rw [cell,norm_indicatorConstLp (by norm_num) (by norm_num),norm_one,one_mul,measureReal_def,μcell hab,ENNReal.toReal_ofReal hn]
  norm_num [←Real.sqrt_eq_rpow,Real.sq_sqrt hn]

private theorem mval_bounds {a b : ℝ} (ha : 0≤a) (hab : a≤b) :
    (b-a)*(1+a^2) ≤ mval a b ∧ mval a b≤(b-a)*(1+b^2) := by
  obtain ⟨d,hd,rfl⟩ := exists_nonneg_add_of_le hab
  constructor <;> dsimp [mval] <;> nlinarith [mul_nonneg ha (sq_nonneg d),pow_nonneg hd 3]

private theorem diff_cell (t R : ℝ) (ht : 0<t) (hR : t≤R) (D : H→L[ℂ]H)
    (hD : ∀ f : H, (fun x => D f x)=ᵐ[μ] fun x => f x-f (x+t)) :
    D (cell R (2*R))=cell (2*R-t) (2*R)-cell (R-t) R := by
  apply Lp.ext
  filter_upwards [hD (cell R (2*R)),cell_ae R (2*R),ae_shift (cell_ae R (2*R)) t,
    Lp.coeFn_sub (cell (2*R-t) (2*R)) (cell (R-t) R),cell_ae (2*R-t) (2*R),cell_ae (R-t) R] with x h h₁ h₂ h₃ h₄ h₅
  rw [h,h₁,h₂,h₃,Pi.sub_apply,h₄,h₅]
  simp only [indicator_apply,mem_Ioc]
  split_ifs <;> simp_all only [not_and_or,not_lt,not_le] <;> (try norm_num) <;> grind

private theorem diff_nonclosed (t : ℝ) (ht : 0<t) (D : H→L[ℂ]H)
    (hD : ∀ f : H, (fun x => D f x)=ᵐ[μ] fun x => f x-f (x+t)) : ¬IsClosed (Set.range D) := by
  intro hcl
  obtain ⟨C,hC⟩ := D.antilipschitz_of_injective_of_isClosed_range (inj_diff t ht D hD) hcl
  let R : ℝ := 20*(C:ℝ)^2*t+t+1
  have hc : 0≤(C:ℝ) := C.coe_nonneg
  have hR : t≤R := by dsimp [R];nlinarith [mul_nonneg (sq_nonneg (C:ℝ)) ht.le]
  have hR1 : 1≤R := by dsimp [R];nlinarith [mul_nonneg (sq_nonneg (C:ℝ)) ht.le]
  have hr : 0<R := by linarith
  let A := cell R (2*R)
  let B := cell (2*R-t) (2*R)
  let E := cell (R-t) R
  have hc' := hC.le_mul_dist A 0
  simp only [map_zero,dist_zero_right] at hc'
  rw [show D A=B-E by exact diff_cell t R ht hR D hD] at hc'
  have hp := hc'.trans (mul_le_mul_of_nonneg_left (norm_sub_le B E) hc)
  have hl : (R*(1+R^2))≤‖A‖^2 := by rw [cell_norm (by linarith : R≤2*R)];simpa only [show 2*R-R=R by ring] using (mval_bounds hr.le (by linarith : R≤2*R)).1
  have hb : ‖B‖^2≤t*(1+4*R^2) := by
    rw [cell_norm (by linarith : 2*R-t≤2*R)]
    convert (mval_bounds (by linarith : 0≤2*R-t) (by linarith : 2*R-t≤2*R)).2 using 1;ring
  have he : ‖E‖^2≤t*(1+4*R^2) := by
    rw [cell_norm (by linarith : R-t≤R)]
    have h := (mval_bounds (by linarith : 0≤R-t) (by linarith : R-t≤R)).2
    nlinarith [mul_nonneg ht.le (sq_nonneg R)]
  have hub : (‖B‖+‖E‖)^2≤4*t*(1+4*R^2) := by nlinarith [sq_nonneg (‖B‖-‖E‖)]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hp 2
  rw [mul_pow] at hsq
  have hA := hl.trans (hsq.trans (mul_le_mul_of_nonneg_left hub (sq_nonneg _)))
  have hr2 : 1 ≤ R^2 := by nlinarith [sq_nonneg (R-1)]
  have bound : R*R^2≤20*(C:ℝ)^2*t*R^2 := by
    nlinarith only [hA,hr.le,mul_nonneg (mul_nonneg (sq_nonneg (C:ℝ)) ht.le) (sub_nonneg.mpr hr2)]
  have bad := (le_of_mul_le_mul_right bound (sq_pos_of_pos hr))
  dsimp only [R] at bad
  linarith

private def shiftC (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (2+2*t^2)
private theorem shiftC_ne (t : ℝ) : shiftC t≠∞ := ENNReal.ofReal_ne_top
private theorem map_le (t : ℝ) : Measure.map (fun x : ℝ => x+t) μ ≤ shiftC t • μ := by
  have hmap : Measure.map (fun x : ℝ => x+t) μ = volume.withDensity (fun x => wt (x-t)) := by
    ext s hs
    rw [Measure.map_apply (by fun_prop) hs,μ,withDensity_apply _ (MeasurableSet.preimage hs (by fun_prop)),withDensity_apply _ hs]
    have h := (measurePreserving_add_right volume t).setLIntegral_comp_preimage (s:=s) hs (f:=fun x => wt (x-t)) (by unfold wt;fun_prop)
    simpa only [add_sub_cancel_right] using h
  rw [hmap,μ,←withDensity_smul' _ _ (shiftC_ne _)]
  apply withDensity_mono;apply ae_of_all;intro x
  change ENNReal.ofReal (1+(x-t)^2) ≤ ENNReal.ofReal (2+2*t^2)*ENNReal.ofReal (1+x^2)
  rw [←ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [sq_nonneg (x+t),sq_nonneg (x*t)]

private theorem shift_mem (t : ℝ) (f : H) : MemLp (fun x => f (x+t)) 2 μ := by
  have h := MemLp.mono_measure (map_le t) ((Lp.memLp f).smul_measure (shiftC_ne t))
  exact h.comp_of_map (by fun_prop)
private def shift (t : ℝ) (f : H) : H := (shift_mem t f).toLp _
private theorem shift_ae (t : ℝ) (f : H) : ⇑(shift t f)=ᵐ[μ] fun x => f (x+t) := (shift_mem t f).coeFn_toLp
private def shiftLin (t : ℝ) : H→ₗ[ℂ]H where
  toFun := shift t
  map_add' f g := by
    apply Lp.ext
    filter_upwards [shift_ae t (f+g),ae_shift (Lp.coeFn_add f g) t,Lp.coeFn_add (shift t f) (shift t g),shift_ae t f,shift_ae t g] with x h₁ h₂ h₃ h₄ h₅
    simp only [h₁,h₂,h₃,Pi.add_apply,h₄,h₅]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [shift_ae t (c • f),ae_shift (Lp.coeFn_smul c f) t,Lp.coeFn_smul c (shift t f),shift_ae t f] with x h₁ h₂ h₃ h₄
    change shift t (c • f) x=(c • shift t f) x
    simp only [h₁,h₂,h₃,Pi.smul_apply,h₄]
private theorem shift_bdd (t : ℝ) (f : H) :
    ‖shiftLin t f‖≤((shiftC t)^((1/(2:ℝ≥0∞)).toReal)).toReal*‖f‖ := by
  let C := (shiftC t)^((1/(2:ℝ≥0∞)).toReal)
  have hC : C≠∞ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (shiftC_ne _)
  have hm := MemLp.mono_measure (map_le t) ((Lp.memLp f).smul_measure (shiftC_ne _))
  have hn : eLpNorm (fun x => f (x+t)) 2 μ≤C*eLpNorm f 2 μ := by
    rw [show eLpNorm (fun x => f (x+t)) 2 μ = eLpNorm f 2 (Measure.map (fun x : ℝ => x+t) μ) by exact (eLpNorm_map_measure hm.1 (by fun_prop)).symm]
    exact (eLpNorm_mono_measure _ (map_le t)).trans (eLpNorm_smul_measure_le _ _ _ _)
  change ‖(shift_mem t f).toLp _‖≤C.toReal*‖f‖
  rw [Lp.norm_toLp,Lp.norm_def,←ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC (Lp.memLp f).2.ne) hn
private def shiftL (t : ℝ) : H→L[ℂ]H := (shiftLin t).mkContinuous _ (shift_bdd t)
private def difference (t : ℝ) : H→L[ℂ]H := ContinuousLinearMap.id ℂ H-shiftL t
private theorem difference_ae (t : ℝ) (f : H) : ⇑(difference t f)=ᵐ[μ] fun x => f x-f (x+t) := by
  change ⇑(f-shift t f)=ᵐ[μ] _
  filter_upwards [Lp.coeFn_sub f (shift t f),shift_ae t f] with x hx hy
  simp only [hx,Pi.sub_apply,hy]

theorem solution (h : ℝ) (hh : 0<h) :
    let ν : Measure ℝ := volume.withDensity (fun t : ℝ => ENNReal.ofReal (1+t^2))
    ∃ D : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν,
      (∀ f : Lp ℂ 2 ν, (fun x => D f x)=ᵐ[ν] fun x => f x-f (x+h)) ∧
      Function.Injective D ∧ ¬IsClosed (Set.range D) := by
  exact ⟨difference h,difference_ae h,inj_diff h hh _ (difference_ae h),diff_nonclosed h hh _ (difference_ae h)⟩
