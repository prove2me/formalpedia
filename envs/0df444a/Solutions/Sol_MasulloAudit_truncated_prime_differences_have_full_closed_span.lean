-- Prove2me | solution 1 for MasulloAudit.truncated_prime_differences_have_full_closed_span
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:15:53.108007+00:00
-- url     : https://prove2.me/submissions/531c1a68-4db8-40d7-9633-78a62cf01619

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


private def cutoff (s : Set ℝ) (hs : MeasurableSet s) (f : H) : H :=
  ((Lp.memLp f).indicator hs).toLp (s.indicator f)
private theorem cutoff_ae {s : Set ℝ} (hs : MeasurableSet s) (f : H) :
    ⇑(cutoff s hs f)=ᵐ[μ] s.indicator f := MemLp.coeFn_toLp _
private def cutLin (s : Set ℝ) (hs : MeasurableSet s) : H→ₗ[ℂ]H where
  toFun := cutoff s hs
  map_add' f g := by
    apply Lp.ext
    filter_upwards [cutoff_ae hs (f+g),Lp.coeFn_add f g,Lp.coeFn_add (cutoff s hs f) (cutoff s hs g),cutoff_ae hs f,cutoff_ae hs g] with x h1 h2 h3 h4 h5
    by_cases hx : x∈s <;> simp_all [Set.indicator_apply,hx]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [cutoff_ae hs (c • f),Lp.coeFn_smul c f,Lp.coeFn_smul c (cutoff s hs f),cutoff_ae hs f] with x h1 h2 h3 h4
    change cutoff s hs (c • f) x=(c • cutoff s hs f) x
    by_cases hx : x∈s <;> simp_all [Set.indicator_apply,hx]
private def mask (s : Set ℝ) (hs : MeasurableSet s) : H→L[ℂ]H :=
  (cutLin s hs).mkContinuous 1 (fun f => by
    change ‖((Lp.memLp f).indicator hs).toLp (s.indicator f)‖≤1*‖f‖
    rw [one_mul,Lp.norm_toLp,Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.memLp f).2.ne (eLpNorm_indicator_le f))

private def zeroAbove (b : ℝ) (f : H) := ∀ᵐ x ∂μ,b<x → f x=0
private def agree (a : ℝ) (f g : H) := ∀ᵐ x ∂μ,a≤x → f x=g x
private theorem agree_trans {a : ℝ} {f g u : H} (hf : agree a f g) (hg : agree a g u) : agree a f u := by
  filter_upwards [hf,hg] with x h h' using fun hx => (h hx).trans (h' hx)
private theorem diff_agree {a t : ℝ} (ht : 0≤t) {f g : H} (h : agree a f g) :
    agree a (difference t f) (difference t g) := by
  filter_upwards [h,ae_shift h t,difference_ae t f,difference_ae t g] with x h1 h2 h3 h4
  intro hx;rw [h3,h4,h1 hx,h2 (by linarith)]
private theorem shifts_add (u v : ℝ) (f : H) : shiftL u (shiftL v f)=shiftL (u+v) f := by
  apply Lp.ext
  filter_upwards [shift_ae u (shiftL v f),ae_shift (shift_ae v f) u,shift_ae (u+v) f] with x h1 h2 h3
  change shift _ (shiftL v f) x=shift (u+v) f x
  rw [h1];change shift v f (x+u)=shift (u+v) f x;rw [h2,h3,add_assoc]
private theorem shift_zero (f : H) : shiftL 0 f=f := by
  apply Lp.ext;change ⇑(shift 0 f)=ᵐ[μ] ⇑f;simpa only [add_zero] using shift_ae 0 f
private def primitive (t : ℝ) (N : ℕ) (f : H) := ∑ j∈Finset.range N,shiftL ((j:ℝ)*t) f
private theorem primitive_diff (t : ℝ) (N : ℕ) (f : H) : difference t (primitive t N f)=f-shiftL ((N:ℝ)*t) f := by
  induction N with
  | zero => simp [primitive,shift_zero]
  | succ n ih =>
    rw [show primitive t (n+1) f=primitive t n f+shiftL ((n:ℝ)*t) f by exact Finset.sum_range_succ ..,map_add,ih]
    have hd (g : H) : difference t g=g-shiftL t g := rfl
    rw [hd,shifts_add,show t+n*t=((n+1:ℕ):ℝ)*t by push_cast;ring];abel
private theorem primitive_zeroAbove {t b : ℝ} (ht : 0≤t) (N : ℕ) (f : H) (h : zeroAbove b f) : zeroAbove b (primitive t N f) := by
  induction N with
  | zero => simp only [primitive,Finset.range_zero,Finset.sum_empty];exact (Lp.coeFn_zero ℂ 2 μ).mono (fun x hx _ => hx)
  | succ n ih =>
    rw [show primitive t (n+1) f=primitive t n f+shiftL ((n:ℝ)*t) f by exact Finset.sum_range_succ ..]
    filter_upwards [ih,ae_shift h ((n:ℝ)*t),shift_ae ((n:ℝ)*t) f,Lp.coeFn_add (primitive t n f) (shiftL ((n:ℝ)*t) f)] with x h1 h2 h3 h4
    intro hx;rw [h4,Pi.add_apply,h1 hx];change 0+shift ((n:ℝ)*t) f x=0
    simpa only [zero_add] using h3.trans (h2 (by linarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) ht]))
private theorem inverse_above {t a b : ℝ} (ht : 0<t) {f : H} (hf : zeroAbove b f) :
    ∃ g : H, zeroAbove b g ∧ agree a (difference t g) f := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((b-a)/t)
  refine ⟨primitive t n f,primitive_zeroAbove ht.le n f hf,?_⟩
  rw [primitive_diff]
  filter_upwards [Lp.coeFn_sub f (shiftL ((n:ℝ)*t) f),shift_ae ((n:ℝ)*t) f,ae_shift hf ((n:ℝ)*t)] with x h1 h2 h3
  intro hx;rw [h1,Pi.sub_apply];change f x-shift ((n:ℝ)*t) f x=f x
  rw [h2,h3 (by linarith [(div_lt_iff₀ ht).mp hn]),sub_zero]
private def diffs (L : List ℝ) : H→L[ℂ]H := L.foldr (fun t D => (difference t).comp D) (ContinuousLinearMap.id ℂ H)
private theorem list_inverse (L : List ℝ) (hL : ∀ t∈L,0<t) {a b : ℝ} {f : H} (hf : zeroAbove b f) :
    ∃ u : H, agree a (diffs L u) f := by
  induction L generalizing f with
  | nil => exact ⟨f,ae_of_all _ (fun x _ => rfl)⟩
  | cons t ts ih =>
    have ht := hL t (by simp)
    obtain ⟨g,hg,he⟩ := inverse_above (a:=a) ht hf
    obtain ⟨u,hu⟩ := ih (fun r hr => hL r (by simp [hr])) hg
    exact ⟨u,agree_trans (diff_agree ht.le hu) he⟩

private theorem lower_trunc (f : H) : Tendsto (fun n : ℕ => mask (Iic (n:ℝ)) measurableSet_Iic f) atTop (𝓝 f) := by
  let V (n : ℕ) := mask (Iic (n:ℝ)) measurableSet_Iic f -f
  have he (n : ℕ) : ‖V n‖^2=∫ x in Ioi (n:ℝ),‖f x‖^2 ∂μ := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def,←integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (mask (Iic (n:ℝ)) measurableSet_Iic f) f,cutoff_ae (s:=Iic (n:ℝ)) measurableSet_Iic f] with x h1 h2
    simp only [real_inner_self_eq_norm_sq,V,h1,Pi.sub_apply]
    change ‖cutoff (Iic (n:ℝ)) measurableSet_Iic f x-f x‖^2=_
    rw [h2];by_cases hx : x≤(n:ℝ) <;> simp [hx,not_lt.mpr,show (n:ℝ)<x ↔ ¬x≤n from lt_iff_not_ge]
  have hl := tendsto_integral_Ioi_zero (μ:=μ) (f:=fun x => ‖f x‖^2) (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hl
  change Tendsto (fun n => ‖V n‖) atTop (𝓝 0)
  change Tendsto (fun n => Real.sqrt _) atTop (𝓝 (Real.sqrt 0)) at hh
  simpa only [←he,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

private theorem mask_agree {a : ℝ} {s : Set ℝ} (hs : MeasurableSet s) (hsa : s⊆Ici a) {f g : H}
    (h : agree a f g) : mask s hs f=mask s hs g := by
  apply Lp.ext;change ⇑(cutoff s hs f)=ᵐ[μ] ⇑(cutoff s hs g)
  filter_upwards [cutoff_ae hs f,cutoff_ae hs g,h] with x hf hg he
  by_cases hx : x∈s <;> simp [hf,hg,indicator_apply,hx,he]
  exact he (hsa hx)
private theorem mask_closed {s : Set ℝ} (hs : MeasurableSet s) : IsClosed (range (mask s hs)) := by
  have he : range (mask s hs)={f | mask s hs f=f} := by
    ext f;constructor
    · rintro ⟨g,rfl⟩;apply Lp.ext
      change ⇑(cutoff s hs (mask s hs g))=ᵐ[μ] ⇑(cutoff s hs g)
      filter_upwards [cutoff_ae hs (mask s hs g),cutoff_ae hs g] with x hx hy
      rw [hx];by_cases h : x∈s
      · rw [indicator_of_mem h];rfl
      · rw [indicator_of_notMem h,hy,indicator_of_notMem h]
    · intro h;exact ⟨f,h⟩
  rw [he];exact isClosed_eq (mask s hs).continuous continuous_id

private theorem full_image (L : List ℝ) (hL : ∀ t∈L,0<t) (a : ℝ) (s : Set ℝ)
    (hs : MeasurableSet s) (hsa : s⊆Ici a) (X : Set H) (hX : Dense X) :
    closure ((fun f => mask s hs (diffs L f)) '' X)=range (mask s hs) := by
  let F := (mask s hs).comp (diffs L)
  change closure (F '' X)=_
  apply le_antisymm
  · apply closure_minimal _ (mask_closed hs)
    rintro _ ⟨x,hx,rfl⟩;exact ⟨diffs L x,rfl⟩
  · rintro _ ⟨f,rfl⟩
    have hr (u : H) : F u∈closure (F '' X) := image_closure_subset_closure_image F.continuous ⟨u,hX u,rfl⟩
    have hmem (n : ℕ) : mask s hs (mask (Iic (n:ℝ)) measurableSet_Iic f) ∈ closure (F '' X) := by
      let v := mask (Iic (n:ℝ)) measurableSet_Iic f
      have hv : zeroAbove n v := by
        filter_upwards [cutoff_ae (s:=Iic (n:ℝ)) measurableSet_Iic f] with x h hx
        exact h.trans (indicator_of_notMem (show x∉Iic (n:ℝ) from not_le.mpr hx) _)
      obtain ⟨u,hu⟩ := list_inverse L hL (a:=a) hv
      have he := mask_agree hs hsa hu
      change mask s hs v∈_;rw [←he];exact hr u
    exact isClosed_closure.mem_of_tendsto (((mask s hs).continuous.tendsto f).comp (lower_trunc f)) (Eventually.of_forall hmem)

theorem solution (a : ℝ) (s : Set ℝ) (hs : MeasurableSet s) (hsa : s⊆Ici a) :
    let ν : Measure ℝ := volume.withDensity (fun t : ℝ => ENNReal.ofReal (1+t^2))
    let E := Lp ℂ 2 ν
    ∃ (M : E→L[ℂ]E) (D : ℝ→E→L[ℂ]E),
      (∀ f : E, (fun x => M f x)=ᵐ[ν] s.indicator f) ∧
      (∀ (t : ℝ) (f : E), (fun x => D t f x)=ᵐ[ν] fun x => f x-f (x+t)) ∧
      ∀ (L : List ℝ), (∀ t∈L,0<t) → ∀ (X : Set E), Dense X →
        let T := L.foldr (fun t (B : E→L[ℂ]E) => (D t).comp B) (ContinuousLinearMap.id ℂ E)
        closure ((fun f => M (T f)) '' X)=Set.range M := by
  refine ⟨mask s hs,difference,fun f => cutoff_ae hs f,difference_ae,?_⟩
  exact fun L hL X hX => full_image L hL a s hs hsa X hX
