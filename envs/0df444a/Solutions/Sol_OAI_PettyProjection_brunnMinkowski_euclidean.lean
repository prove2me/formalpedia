-- Prove2me | solution 1 for OAI.PettyProjection.brunnMinkowski_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:09:03.250605+00:00
-- url     : https://prove2.me/submissions/13160522-a381-48ee-aa40-607df50528cd

import Mathlib
import Definitions.Def_PettyProjectionVolume
import Definitions.Def_OAIQWPP000

section
-- module Solutions.OAIQW_PettyProjection.ShadowSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection

lemma compact_convex_real_interval {C : Set ℝ} (hC : IsCompact C) (hc : Convex ℝ C)
    (hn : C.Nonempty) : C = Icc (sInf C) (sSup C) := by
  apply Subset.antisymm
  · exact fun x hx => ⟨csInf_le hC.bddBelow hx,le_csSup hC.bddAbove hx⟩
  · exact (convex_iff_ordConnected.mp hc).out (hC.sInf_mem hn) (hC.sSup_mem hn)

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.SliceTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Filter Topology
namespace PettyProjection

/-- The strict scalar inequality in the slice transport proof of
Brunn--Minkowski. The variables `p,q` are the positive slice-volume roots. -/
lemma transport_scalar {m : ℕ} (hm : 0 < m) {a b p q : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a+b=1) (hp : 0 < p) (hq : 0 < q) :
    1 ≤ (a*p+b*q)^m*(a/(p^m)+b/(q^m)) ∧
      ((a*p+b*q)^m*(a/(p^m)+b/(q^m))=1 ↔ p=q) := by
  let D := p^a*q^b
  have hD : 0 < D := mul_pos (Real.rpow_pos_of_pos hp _) (Real.rpow_pos_of_pos hq _)
  have hX : D ≤ a*p+b*q := Real.geom_mean_le_arith_mean2_weighted ha.le hb.le hp.le hq.le hab
  have hXi : D < a*p+b*q ↔ p ≠ q :=
    Real.geom_mean_lt_arith_mean2_weighted_iff_of_pos ha hb hp.le hq.le hab
  have hY : (D^m)⁻¹ ≤ a/(p^m)+b/(q^m) := by
    have hh := Real.geom_mean_le_arith_mean2_weighted ha.le hb.le
      (inv_nonneg.mpr (pow_nonneg hp.le m)) (inv_nonneg.mpr (pow_nonneg hq.le m)) hab
    convert hh using 1
    · dsimp [D]
      rw [mul_pow,mul_inv,Real.inv_rpow (pow_nonneg hp.le m),
        Real.inv_rpow (pow_nonneg hq.le m)]
      rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_mul hp.le,
        ← Real.rpow_mul hq.le]
      rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_mul hp.le,
        ← Real.rpow_mul hq.le]
      simp only [mul_comm]
    · simp only [div_eq_mul_inv]
  have hYP : 0 < a/(p^m)+b/(q^m) := by positivity
  have hX0 : 0 < a*p+b*q := by positivity
  have hle : 1 ≤ (a*p+b*q)^m*(a/(p^m)+b/(q^m)) := by
    calc
      1 = D^m*(D^m)⁻¹ := (mul_inv_cancel₀ (pow_ne_zero _ hD.ne')).symm
      _ ≤ (a*p+b*q)^m*(a/(p^m)+b/(q^m)) :=
        mul_le_mul (pow_le_pow_left₀ hD.le hX m) hY (inv_nonneg.mpr (pow_nonneg hD.le _))
          (pow_nonneg hX0.le _)
  refine ⟨hle,⟨fun he => ?_,fun he => ?_⟩⟩
  · by_contra hn
    have hlt : D^m < (a*p+b*q)^m := pow_lt_pow_left₀ (hXi.mpr hn) hD.le hm.ne'
    have hh : 1 < (a*p+b*q)^m*(a/(p^m)+b/(q^m)) := calc
      1 = D^m*(D^m)⁻¹ := (mul_inv_cancel₀ (pow_ne_zero _ hD.ne')).symm
      _ ≤ D^m*(a/(p^m)+b/(q^m)) := mul_le_mul_of_nonneg_left hY (pow_nonneg hD.le _)
      _ < _ := mul_lt_mul_of_pos_right hlt hYP
    linarith
  · subst q
    rw [← add_mul,hab,one_mul,← add_div,hab]
    exact mul_one_div_cancel (pow_ne_zero _ hp.ne')

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
namespace PettyProjection

/-- The inverse cumulative mass coordinate on a compact interval. Zero density
at the two endpoints is allowed; the derivative is needed only in the interior. -/
theorem exists_interval_quantile {l r : ℝ} (hlr : l < r) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo l r)) (hI : IntervalIntegrable f volume l r)
    (hpos : ∀ x ∈ Ioo l r, 0 < f x)
    (hmass : (∫ x in l..r, f x)=1) :
    ∃ Q : ℝ → ℝ, Continuous Q ∧ Q 0=l ∧ Q 1=r ∧
      (∀ s ∈ Icc (0:ℝ) 1, Q s ∈ Icc l r) ∧
      (∀ s ∈ Ioo (0:ℝ) 1, Q s ∈ Ioo l r ∧
        HasDerivAt Q (f (Q s))⁻¹ s) := by
  let F : ℝ → ℝ := fun x => ∫ y in l..x, f y
  have hFc : ContinuousOn F (Icc l r) := by
    simpa only [uIcc_of_le hlr.le] using
      (intervalIntegral.continuousOn_primitive_interval' hI left_mem_uIcc)
  have hd : ∀ x ∈ Ioo l r, HasDerivAt F (f x) x := by
    intro x hx
    have hc : ContinuousAt f x := hf.continuousAt (Ioo_mem_nhds hx.1 hx.2)
    exact intervalIntegral.integral_hasDerivAt_right (hI.mono_set (by
      simp only [uIcc_of_le hlr.le,uIcc_of_le hx.1.le]
      exact Icc_subset_Icc_right hx.2.le))
      (hf.stronglyMeasurableAtFilter isOpen_Ioo x hx) hc
  have hmono : StrictMonoOn F (Icc l r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc l r) hFc
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd x hx).deriv]
    exact hpos x hx
  have hFl : F l=0 := intervalIntegral.integral_same
  have hFr : F r=1 := hmass
  have hIm : F '' Icc l r = Icc (0:ℝ) 1 := by
    simpa only [hFl,hFr] using hFc.image_Icc_of_monotoneOn hlr.le hmono.monotoneOn
  let e : Icc l r ≃o Icc (0:ℝ) 1 :=
    (hmono.orderIso F (Icc l r)).trans (OrderIso.setCongr _ _ hIm)
  let Q : ℝ → ℝ := fun s => (e.symm (projIcc 0 1 (by norm_num) s)).val
  have hQc : Continuous Q := continuous_subtype_val.comp
    (e.symm.continuous.comp continuous_projIcc)
  have hQmem : ∀ s, Q s ∈ Icc l r := fun s => (e.symm (projIcc 0 1 (by norm_num) s)).property
  have hFQ : ∀ s ∈ Icc (0:ℝ) 1, F (Q s)=s := by
    intro s hs
    have he := congrArg Subtype.val (e.apply_symm_apply (projIcc 0 1 (by norm_num) s))
    change F (Q s) = (projIcc 0 1 (by norm_num) s).val at he
    simpa only [projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) hs] using he
  have hQ0 : Q 0=l := hmono.injOn (hQmem 0) (left_mem_Icc.mpr hlr.le)
    ((hFQ 0 (by norm_num)).trans hFl.symm)
  have hQ1 : Q 1=r := hmono.injOn (hQmem 1) (right_mem_Icc.mpr hlr.le)
    ((hFQ 1 (by norm_num)).trans hFr.symm)
  refine ⟨Q,hQc,hQ0,hQ1,fun s _ => hQmem s,?_⟩
  intro s hs
  have hQi : Q s ∈ Ioo l r := by
    refine ⟨lt_of_le_of_ne (hQmem s).1 ?_,lt_of_le_of_ne (hQmem s).2 ?_⟩
    · intro he
      have hy := hFQ s ⟨hs.1.le,hs.2.le⟩
      rw [← he,hFl] at hy
      linarith [hs.1]
    · intro he
      have hy := hFQ s ⟨hs.1.le,hs.2.le⟩
      rw [he,hFr] at hy
      linarith [hs.2]
  refine ⟨hQi,HasDerivAt.of_local_left_inverse hQc.continuousAt (hd _ hQi)
    (hpos _ hQi).ne' ?_⟩
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
  exact hFQ t ⟨ht.1.le,ht.2.le⟩

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
namespace PettyProjection

/-- The analytic step of the slice proof. All three functions here are actual
slice densities when this result is applied to convex bodies. -/
theorem slice_transport {m : ℕ} (hm : 0 < m) {a b l r L R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a+b=1) (hlr : l<r) (hLR : L<R)
    {f g h : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo l r)) (hg : ContinuousOn g (Ioo L R))
    (hfi : IntervalIntegrable f volume l r) (hgi : IntervalIntegrable g volume L R)
    (hfp : ∀ x ∈ Ioo l r, 0<f x) (hgp : ∀ x ∈ Ioo L R, 0<g x)
    (hfI : (∫ x in l..r, f x)=1) (hgI : (∫ x in L..R, g x)=1)
    (hhi : IntervalIntegrable h volume (a*l+b*L) (a*r+b*R))
    (hbound : ∀ x ∈ Ioo l r, ∀ y ∈ Ioo L R,
      (a*(f x)^((m:ℝ)⁻¹)+b*(g y)^((m:ℝ)⁻¹))^m ≤ h (a*x+b*y)) :
    1 ≤ ∫ z in (a*l+b*L)..(a*r+b*R), h z := by
  obtain ⟨Q,hQc,hQ0,hQ1,hQmem,hQd⟩ := exists_interval_quantile hlr hf hfi hfp hfI
  obtain ⟨P,hPc,hP0,hP1,hPmem,hPd⟩ := exists_interval_quantile hLR hg hgi hgp hgI
  let z : ℝ → ℝ := fun s => a*Q s+b*P s
  let z' : ℝ → ℝ := fun s => a/(f (Q s))+b/(g (P s))
  have hzc : Continuous z := by dsimp [z]; fun_prop
  have hzd : ∀ s ∈ Ioo (0:ℝ) 1, HasDerivAt z (z' s) s := by
    intro s hs
    convert ((hQd s hs).2.const_mul a).add ((hPd s hs).2.const_mul b) using 1
    all_goals rfl
  have hzp : ∀ s ∈ Ioo (0:ℝ) 1, 0<z' s := by
    intro s hs
    exact add_pos (div_pos ha (hfp _ (hQd s hs).1)) (div_pos hb (hgp _ (hPd s hs).1))
  have hz0 : z 0=a*l+b*L := by dsimp [z]; rw [hQ0,hP0]
  have hz1 : z 1=a*r+b*R := by dsimp [z]; rw [hQ1,hP1]
  have hzz : z 0 ≤ z 1 := by rw [hz0,hz1]; nlinarith
  have hhi : IntervalIntegrable h volume (z 0) (z 1) := by
    rwa [hz0,hz1]
  have hzdu : ∀ s ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1), HasDerivAt z (z' s) s := by
    simpa only [min_eq_left zero_le_one,max_eq_right zero_le_one] using hzd
  have hzpu : ∀ s ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1), 0≤z' s := by
    simpa only [min_eq_left zero_le_one,max_eq_right zero_le_one] using fun s hs => (hzp s hs).le
  have hint : IntervalIntegrable (fun s => h (z s)*z' s) volume 0 1 :=
    (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg hzc.continuousOn hzdu hzpu).mpr hhi
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := h) hzc.continuousOn hzdu hzpu
  change (∫ s in (0:ℝ)..1, h (z s)*z' s) = _ at hsub
  have hpt : ∀ s ∈ Ioo (0:ℝ) 1, 1 ≤ h (z s)*z' s := by
    intro s hs
    let p := (f (Q s))^((m:ℝ)⁻¹)
    let q := (g (P s))^((m:ℝ)⁻¹)
    have hp : 0<p := Real.rpow_pos_of_pos (hfp _ (hQd s hs).1) _
    have hq : 0<q := Real.rpow_pos_of_pos (hgp _ (hPd s hs).1) _
    have hpm : p^m=f (Q s) := Real.rpow_inv_natCast_pow (hfp _ (hQd s hs).1).le hm.ne'
    have hqm : q^m=g (P s) := Real.rpow_inv_natCast_pow (hgp _ (hPd s hs).1).le hm.ne'
    have ht := (transport_scalar hm ha hb hab hp hq).1
    rw [hpm,hqm] at ht
    exact ht.trans (mul_le_mul_of_nonneg_right
      (hbound _ (hQd s hs).1 _ (hPd s hs).1) (hzp s hs).le)
  have hae : (fun _ : ℝ => (1:ℝ)) ≤ᵐ[volume.restrict (Icc (0:ℝ) 1)] (fun s => h (z s)*z' s) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ hpt)
  have hi := intervalIntegral.integral_mono_ae_restrict (by norm_num : (0:ℝ)≤1)
    intervalIntegrable_const hint hae
  rw [intervalIntegral.integral_const] at hi
  norm_num at hi
  rw [hsub,hz0,hz1] at hi
  exact hi

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma horizontalSlice_compact {K : Set (E × ℝ)} (hK : IsCompact K) (s : ℝ) :
    IsCompact (horizontalSlice K s) :=
  (IsClosedEmbedding.of_isEmbedding_isClosedMap (isEmbedding_prodMkLeft s)
    (isClosedMap_prodMk_right s)).isCompact_preimage hK

lemma horizontalSlice_convex {K : Set (E × ℝ)} (hK : Convex ℝ K) (s : ℝ) :
    Convex ℝ (horizontalSlice K s) := by
  intro x hx y hy a b ha hb hab
  have h := hK hx hy ha hb hab
  change (a • x+b • y,s) ∈ K
  simpa only [Prod.smul_mk,Prod.mk_add_mk,← add_smul,hab,one_smul] using h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma horizontalSlice_nonempty_iff {K : Set (E × ℝ)} {s : ℝ} :
    (horizontalSlice K s).Nonempty ↔ s ∈ Prod.snd '' K := by
  constructor
  · rintro ⟨x,hx⟩; exact ⟨(x,s),hx,rfl⟩
  · rintro ⟨⟨x,t⟩,hx,rfl⟩; exact ⟨x,hx⟩

lemma horizontalSlice_minkowski_subset (K M : Set (E × ℝ)) (a b s t : ℝ) :
    a • horizontalSlice K s+b • horizontalSlice M t ⊆
      horizontalSlice (a • K+b • M) (a*s+b*t) := by
  rintro _ ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩
  exact ⟨a • (x,s),smul_mem_smul_set hx,b • (y,t),smul_mem_smul_set hy,rfl⟩

lemma horizontalSlice_combo_subset {K : Set (E × ℝ)} (hK : Convex ℝ K)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) (s t : ℝ) :
    a • horizontalSlice K s+b • horizontalSlice K t ⊆
      horizontalSlice K (a*s+b*t) := by
  rintro _ ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩
  exact hK hx hy ha hb hab

omit [NormedSpace ℝ E] in
lemma interior_slice_of_interior {K : Set (E × ℝ)} {x : E} {s : ℝ}
    (hx : (x,s) ∈ interior K) : x ∈ interior (horizontalSlice K s) :=
  preimage_interior_subset_interior_preimage (by fun_prop) hx

/-- A projection point strictly between two attained heights is a height of an
interior point. No smoothness of the convex body is imposed. -/
lemma interior_point_at_height {K : Set (E × ℝ)} (hK : Convex ℝ K)
    (hi : (interior K).Nonempty) {l r s : ℝ}
    (hl : l ∈ Prod.snd '' K) (hr : r ∈ Prod.snd '' K) (hs : s ∈ Ioo l r) :
    ∃ x : E, (x,s) ∈ interior K := by
  obtain ⟨⟨x0,s0⟩,h0⟩ := hi
  obtain ⟨⟨xl,sl⟩,hxl,hl⟩ := hl
  obtain ⟨⟨xr,sr⟩,hxr,hr⟩ := hr
  change sl=l at hl
  change sr=r at hr
  subst sl; subst sr
  obtain h | h | h := lt_trichotomy s s0
  · let t := (s0-s)/(s0-l)
    have hd : 0<s0-l := by linarith [hs.1]
    have ht0 : 0≤t := (div_pos (by linarith) hd).le
    have ht1 : t<1 := (div_lt_one hd).mpr (by linarith [hs.1])
    have hc := hK.combo_interior_self_mem_interior h0 hxl (by linarith : 0<1-t) ht0 (by ring : (1-t)+t=1)
    refine ⟨(1-t) • x0+t • xl,?_⟩
    convert hc using 1
    ext
    · rfl
    · dsimp [t]
      field_simp
      ring
  · subst s
    exact ⟨x0,h0⟩
  · let t := (s-s0)/(r-s0)
    have hd : 0<r-s0 := by linarith [hs.2]
    have ht0 : 0≤t := (div_pos (by linarith) hd).le
    have ht1 : t<1 := (div_lt_one hd).mpr (by linarith [hs.2])
    have hc := hK.combo_interior_self_mem_interior h0 hxr (by linarith : 0<1-t) ht0 (by ring : (1-t)+t=1)
    refine ⟨(1-t) • x0+t • xr,?_⟩
    convert hc using 1
    ext
    · rfl
    · dsimp [t]
      field_simp
      ring

lemma horizontalSlice_interior_nonempty {K : Set (E × ℝ)} (hK : Convex ℝ K)
    (hi : (interior K).Nonempty) {l r s : ℝ}
    (hl : l ∈ Prod.snd '' K) (hr : r ∈ Prod.snd '' K) (hs : s ∈ Ioo l r) :
    (interior (horizontalSlice K s)).Nonempty := by
  obtain ⟨x,hx⟩ := interior_point_at_height hK hi hl hr hs
  exact ⟨x,interior_slice_of_interior hx⟩

lemma vertical_projection_interval {K : Set (E × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    ∃ l r : ℝ, l<r ∧ Prod.snd '' K=Icc l r := by
  have hn : K.Nonempty := hi.mono interior_subset
  refine ⟨sInf (Prod.snd '' K),sSup (Prod.snd '' K),?_,
    compact_convex_real_interval (hK.image continuous_snd)
      (hc.linear_image (LinearMap.snd ℝ E ℝ)) (hn.image _)⟩
  have hInt : (interior (Prod.snd '' K)).Nonempty :=
    (hi.image Prod.snd).mono (isOpenMap_snd.image_interior_subset K)
  rw [compact_convex_real_interval (hK.image continuous_snd)
    (hc.linear_image (LinearMap.snd ℝ E ℝ)) (hn.image _),interior_Icc] at hInt
  exact nonempty_Ioo.mp hInt

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology Function
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
lemma sliceDensity_nonneg (K : Set (E × ℝ)) (s : ℝ) : 0 ≤ sliceDensity K s := measureReal_nonneg

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma sliceDensity_pos {K : Set (E × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hi : (interior K).Nonempty) {l r s : ℝ}
    (hl : l ∈ Prod.snd '' K) (hr : r ∈ Prod.snd '' K) (hs : s ∈ Ioo l r) :
    0 < sliceDensity K s := by
  apply ENNReal.toReal_pos (ne_of_gt ?_) (horizontalSlice_compact hK s).measure_ne_top
  exact lt_of_lt_of_le (isOpen_interior.measure_pos volume
    (horizontalSlice_interior_nonempty hc hi hl hr hs)) (measure_mono interior_subset)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
lemma sliceDensity_zero_of_notMem {K : Set (E × ℝ)} {s : ℝ}
    (hs : s ∉ Prod.snd '' K) : sliceDensity K s=0 := by
  have he : horizontalSlice K s=∅ := not_nonempty_iff_eq_empty.mp
    (fun h => hs (horizontalSlice_nonempty_iff.mp h))
  simp [sliceDensity,he]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
lemma sliceDensity_indicator_integral {K : Set (E × ℝ)} (hK : IsCompact K) (s : ℝ) :
    (∫ x : E, K.indicator (fun _ => (1:ℝ)) (x,s))=sliceDensity K s := by
  have he : (fun x : E => K.indicator (fun _ => (1:ℝ)) (x,s)) =
      (horizontalSlice K s).indicator (fun _ => (1:ℝ)) := by
    funext x
    by_cases hx : (x,s) ∈ K
    · rw [Set.indicator_of_mem hx,Set.indicator_of_mem (show x ∈ horizontalSlice K s from hx)]
    · rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem (show x ∉ horizontalSlice K s from hx)]
  rw [he,integral_indicator (horizontalSlice_compact hK s).measurableSet,setIntegral_const]
  simp only [smul_eq_mul,mul_one,sliceDensity]

lemma sliceDensity_integrable {K : Set (E × ℝ)} (hK : IsCompact K) :
    Integrable (sliceDensity K) := by
  have hi : Integrable (K.indicator (fun _ => (1:ℝ))) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
  exact hi.integral_prod_right.congr (Eventually.of_forall fun s => sliceDensity_indicator_integral hK s)

lemma sliceDensity_integral {K : Set (E × ℝ)} (hK : IsCompact K) :
    (∫ s, sliceDensity K s)=volume.real K := by
  have hi : Integrable (K.indicator (fun _ => (1:ℝ))) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
  have he := integral_prod_symm (K.indicator (fun _ => (1:ℝ))) hi
  simp_rw [sliceDensity_indicator_integral hK] at he
  rw [← he,← Measure.volume_eq_prod,integral_indicator hK.measurableSet,setIntegral_const]
  simp only [smul_eq_mul,mul_one]

lemma sliceDensity_interval_integral {K : Set (E × ℝ)} (hK : IsCompact K) {l r : ℝ}
    (hlr : l≤r) (hp : Prod.snd '' K ⊆ Icc l r) :
    (∫ s in l..r, sliceDensity K s)=volume.real K := by
  rw [intervalIntegral.integral_of_le hlr,← integral_Icc_eq_integral_Ioc]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact sliceDensity_integral hK
  · intro s hs
    exact sliceDensity_zero_of_notMem (fun h => hs (hp h))

end
end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.BrunnMinkowski
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma sliceDensity_root_concave {m : ℕ} (hm : BrunnMinkowskiRoot E m)
    {K : Set (E × ℝ)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hi : (interior K).Nonempty) {l r : ℝ}
    (hl : l ∈ Prod.snd '' K) (hr : r ∈ Prod.snd '' K) :
    ConcaveOn ℝ (Ioo l r) (fun s => (sliceDensity K s)^((m:ℝ)⁻¹)) := by
  refine ⟨convex_Ioo l r,?_⟩
  intro s hs t ht a b ha hb hab
  have hlower := hm (horizontalSlice K s) (horizontalSlice K t)
    (horizontalSlice_compact hK s) (horizontalSlice_convex hc s)
    (horizontalSlice_interior_nonempty hc hi hl hr hs)
    (horizontalSlice_compact hK t) (horizontalSlice_convex hc t)
    (horizontalSlice_interior_nonempty hc hi hl hr ht) a b ha hb hab
  exact hlower.trans (Real.rpow_le_rpow measureReal_nonneg
    (measureReal_mono (horizontalSlice_combo_subset hc ha hb hab s t)
      (horizontalSlice_compact hK (a*s+b*t)).measure_ne_top) (by positivity))

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma sliceDensity_continuous {m : ℕ} (hm0 : 0 < m) (hm : BrunnMinkowskiRoot E m)
    {K : Set (E × ℝ)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hi : (interior K).Nonempty) {l r : ℝ}
    (hl : l ∈ Prod.snd '' K) (hr : r ∈ Prod.snd '' K) :
    ContinuousOn (sliceDensity K) (Ioo l r) := by
  have h := (ConcaveOn.continuousOn isOpen_Ioo
    (sliceDensity_root_concave hm hK hc hi hl hr)).pow m
  convert h using 1
  funext s
  exact (Real.rpow_inv_natCast_pow (sliceDensity_nonneg K s) hm0.ne').symm

/-- The actual convex-body product step, not a replacement by abstract densities. -/
theorem brunnMinkowski_product_unit {m : ℕ} (hm0 : 0 < m) (hm : BrunnMinkowskiRoot E m)
    {K M : Set (E × ℝ)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty) (hvK : volume.real K=1) (hvM : volume.real M=1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1) :
    1 ≤ volume.real (a • K+b • M) := by
  obtain ⟨l,r,hlr,hpr⟩ := vertical_projection_interval hK hcK hiK
  obtain ⟨L,R,hLR,hPR⟩ := vertical_projection_interval hM hcM hiM
  have hl : l ∈ Prod.snd '' K := by rw [hpr]; exact left_mem_Icc.mpr hlr.le
  have hr : r ∈ Prod.snd '' K := by rw [hpr]; exact right_mem_Icc.mpr hlr.le
  have hL : L ∈ Prod.snd '' M := by rw [hPR]; exact left_mem_Icc.mpr hLR.le
  have hR : R ∈ Prod.snd '' M := by rw [hPR]; exact right_mem_Icc.mpr hLR.le
  have hC : IsCompact (a • K+b • M) := (hK.smul a).add (hM.smul b)
  have hbounds : Prod.snd '' (a • K+b • M) ⊆ Icc (a*l+b*L) (a*r+b*R) := by
    rintro s ⟨_,⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩,rfl⟩
    have hx' : x.2 ∈ Icc l r := by rw [← hpr]; exact mem_image_of_mem _ hx
    have hy' : y.2 ∈ Icc L R := by rw [← hPR]; exact mem_image_of_mem _ hy
    change a*l+b*L ≤ a*x.2+b*y.2 ∧ a*x.2+b*y.2 ≤ a*r+b*R
    exact ⟨add_le_add (mul_le_mul_of_nonneg_left hx'.1 ha.le) (mul_le_mul_of_nonneg_left hy'.1 hb.le),
      add_le_add (mul_le_mul_of_nonneg_left hx'.2 ha.le) (mul_le_mul_of_nonneg_left hy'.2 hb.le)⟩
  rw [← sliceDensity_interval_integral hC (by nlinarith) hbounds]
  apply slice_transport hm0 ha hb hab hlr hLR
    (sliceDensity_continuous hm0 hm hK hcK hiK hl hr)
    (sliceDensity_continuous hm0 hm hM hcM hiM hL hR)
    (sliceDensity_integrable hK).intervalIntegrable
    (sliceDensity_integrable hM).intervalIntegrable
    (fun s hs => sliceDensity_pos hK hcK hiK hl hr hs)
    (fun s hs => sliceDensity_pos hM hcM hiM hL hR hs)
  · rw [sliceDensity_interval_integral hK hlr.le (by rw [hpr]),hvK]
  · rw [sliceDensity_interval_integral hM hLR.le (by rw [hPR]),hvM]
  · exact (sliceDensity_integrable hC).intervalIntegrable
  · intro s hs t ht
    have hroot := hm (horizontalSlice K s) (horizontalSlice M t)
      (horizontalSlice_compact hK s) (horizontalSlice_convex hcK s)
      (horizontalSlice_interior_nonempty hcK hiK hl hr hs)
      (horizontalSlice_compact hM t) (horizontalSlice_convex hcM t)
      (horizontalSlice_interior_nonempty hcM hiM hL hR ht) a b ha.le hb.le hab
    have hf0 := sliceDensity_nonneg K s
    have hg0 := sliceDensity_nonneg M t
    have hroot' := pow_le_pow_left₀ (by positivity : 0 ≤ a*(sliceDensity K s)^((m:ℝ)⁻¹)+b*(sliceDensity M t)^((m:ℝ)⁻¹)) hroot m
    rw [Real.rpow_inv_natCast_pow measureReal_nonneg hm0.ne'] at hroot'
    exact hroot'.trans (measureReal_mono (horizontalSlice_minkowski_subset K M a b s t)
      (horizontalSlice_compact hC _).measure_ne_top)

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

lemma volumeReal_smul_nonneg {r : ℝ} (hr : 0 ≤ r) (K : Set E) :
    volume.real (r • K)=r^(Module.finrank ℝ E)*volume.real K := by
  rw [Measure.real,Measure.addHaar_smul_of_nonneg volume hr,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr _)]
  rfl

/-- Usual normalization from the unit-volume form. The exponent is the actual
finite dimension of the Haar space, and the bodies remain arbitrary. -/
theorem brunnMinkowski_of_unit {d : ℕ} (hd : 0 < d) (hDim : Module.finrank ℝ E=d)
    (hunit : ∀ K M : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
      IsCompact M → Convex ℝ M → (interior M).Nonempty →
      volume.real K=1 → volume.real M=1 → ∀ a b : ℝ, 0 < a → 0 < b → a+b=1 →
      1 ≤ volume.real (a • K+b • M)) : BrunnMinkowskiRoot E d := by
  intro K M hK hcK hiK hM hcM hiM a b ha hb hab
  obtain rfl | ha := ha.eq_or_lt
  · have hb1 : b=1 := by linarith
    simp [hb1,zero_smul_set (hiK.mono interior_subset)]
  obtain rfl | hb := hb.eq_or_lt
  · have ha1 : a=1 := by linarith
    simp [ha1,zero_smul_set (hiM.mono interior_subset)]
  let p := (volume.real K)^((d:ℝ)⁻¹)
  let q := (volume.real M)^((d:ℝ)⁻¹)
  let D := a*p+b*q
  have hp : 0 < p := Real.rpow_pos_of_pos (volumeReal_pos_of_body hK hiK) _
  have hq : 0 < q := Real.rpow_pos_of_pos (volumeReal_pos_of_body hM hiM) _
  have hD : 0 < D := by dsimp [D]; positivity
  have hpm : p^d=volume.real K := Real.rpow_inv_natCast_pow measureReal_nonneg hd.ne'
  have hqm : q^d=volume.real M := Real.rpow_inv_natCast_pow measureReal_nonneg hd.ne'
  have hUK : volume.real (p⁻¹ • K)=1 := by
    rw [volumeReal_smul_nonneg (inv_nonneg.mpr hp.le),hDim,inv_pow,hpm]
    exact inv_mul_cancel₀ (volumeReal_pos_of_body hK hiK).ne'
  have hUM : volume.real (q⁻¹ • M)=1 := by
    rw [volumeReal_smul_nonneg (inv_nonneg.mpr hq.le),hDim,inv_pow,hqm]
    exact inv_mul_cancel₀ (volumeReal_pos_of_body hM hiM).ne'
  have hiUK : (interior (p⁻¹ • K)).Nonempty := by
    rw [interior_smul₀ (inv_ne_zero hp.ne')]
    exact hiK.image _
  have hiUM : (interior (q⁻¹ • M)).Nonempty := by
    rw [interior_smul₀ (inv_ne_zero hq.ne')]
    exact hiM.image _
  have he := hunit (p⁻¹ • K) (q⁻¹ • M) (hK.smul _) (hcK.smul _) hiUK
    (hM.smul _) (hcM.smul _) hiUM hUK hUM (a*p/D) (b*q/D)
    (by positivity) (by positivity) (by rw [← add_div]; exact div_self hD.ne')
  have hsets : (a*p/D) • (p⁻¹ • K)+(b*q/D) • (q⁻¹ • M)=D⁻¹ • (a • K+b • M) := by
    rw [smul_add,smul_smul,smul_smul,smul_smul,smul_smul]
    congr 2 <;> field_simp
  rw [hsets,volumeReal_smul_nonneg (inv_nonneg.mpr hD.le),hDim,inv_pow] at he
  have hpow : D^d ≤ volume.real (a • K+b • M) := by
    have hx := mul_le_mul_of_nonneg_left he (pow_nonneg hD.le d)
    simpa only [mul_one,← mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hD.ne'),one_mul] using hx
  have hr := Real.rpow_le_rpow (pow_nonneg hD.le d) hpow (by positivity : 0 ≤ (d:ℝ)⁻¹)
  rw [← Real.rpow_natCast,← Real.rpow_mul hD.le,mul_inv_cancel₀ (by exact_mod_cast hd.ne'),Real.rpow_one] at hr
  exact hr

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasureSpace E] [BorelSpace E] [MeasureSpace F] [BorelSpace F]

omit [MeasureSpace E] [BorelSpace E] [MeasureSpace F] [BorelSpace F] in
lemma linearEquiv_preimage_combo (e : E ≃L[ℝ] F) (K M : Set F) (a b : ℝ) :
    e ⁻¹' (a • K+b • M)=a • (e ⁻¹' K)+b • (e ⁻¹' M) := by
  ext z
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,he⟩
    refine ⟨a • e.symm x,⟨e.symm x,by simpa using hx,rfl⟩,
      b • e.symm y,⟨e.symm y,by simpa using hy,rfl⟩,?_⟩
    apply e.injective
    simpa using he
  · rintro ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨a • e x,⟨e x,hx,rfl⟩,b • e y,⟨e y,hy,rfl⟩,by simp⟩

omit [BorelSpace E] in
lemma BrunnMinkowskiRoot.equiv {m : ℕ} (hm : BrunnMinkowskiRoot E m)
    (e : E ≃L[ℝ] F) (he : MeasurePreserving e) : BrunnMinkowskiRoot F m := by
  intro K M hK hcK hiK hM hcM hiM a b ha hb hab
  have hPK : IsCompact (e ⁻¹' K) := e.toHomeomorph.isCompact_preimage.mpr hK
  have hPM : IsCompact (e ⁻¹' M) := e.toHomeomorph.isCompact_preimage.mpr hM
  have hiPK : (interior (e ⁻¹' K)).Nonempty := by
    change (interior (e.toHomeomorph ⁻¹' K)).Nonempty
    rw [← e.toHomeomorph.preimage_interior]
    obtain ⟨x,hx⟩ := hiK
    exact ⟨e.symm x,by simpa using hx⟩
  have hiPM : (interior (e ⁻¹' M)).Nonempty := by
    change (interior (e.toHomeomorph ⁻¹' M)).Nonempty
    rw [← e.toHomeomorph.preimage_interior]
    obtain ⟨x,hx⟩ := hiM
    exact ⟨e.symm x,by simpa using hx⟩
  have h := hm (e ⁻¹' K) (e ⁻¹' M) hPK (hcK.linear_preimage e.toLinearMap) hiPK
    hPM (hcM.linear_preimage e.toLinearMap) hiPM a b ha hb hab
  have hm' (S : Set F) (hS : IsCompact S) : volume.real (e ⁻¹' S)=volume.real S :=
    congrArg ENNReal.toReal (he.measure_preimage hS.measurableSet.nullMeasurableSet)
  rw [hm' K hK,hm' M hM,← linearEquiv_preimage_combo,hm' _ ((hK.smul _).add (hM.smul _))] at h
  exact h
end

/-- The one-dimensional base case, with no symmetry or origin condition. -/
lemma brunnMinkowski_real : BrunnMinkowskiRoot ℝ 1 := by
  intro K M hK hcK hiK hM hcM hiM a b ha hb hab
  obtain rfl | ha := ha.eq_or_lt
  · have hb1 : b=1 := by linarith
    simp [hb1,zero_smul_set (hiK.mono interior_subset)]
  obtain rfl | hb := hb.eq_or_lt
  · have ha1 : a=1 := by linarith
    simp [ha1,zero_smul_set (hiM.mono interior_subset)]
  rw [compact_convex_real_interval hK hcK (hiK.mono interior_subset),
    compact_convex_real_interval hM hcM (hiM.mono interior_subset)]
  have hKlr : sInf K ≤ sSup K := (hK.isGLB_sInf (hiK.mono interior_subset)).1
    (hK.sSup_mem (hiK.mono interior_subset))
  have hMlr : sInf M ≤ sSup M := (hM.isGLB_sInf (hiM.mono interior_subset)).1
    (hM.sSup_mem (hiM.mono interior_subset))
  have hKa : a*sInf K ≤ a*sSup K := mul_le_mul_of_nonneg_left hKlr ha.le
  have hMb : b*sInf M ≤ b*sSup M := mul_le_mul_of_nonneg_left hMlr hb.le
  rw [LinearOrderedField.smul_Icc ha,LinearOrderedField.smul_Icc hb,Icc_add_Icc hKa hMb]
  simp only [Nat.cast_one,inv_one,Real.rpow_one,Real.volume_real_Icc]
  rw [max_eq_left (sub_nonneg.mpr hKlr),max_eq_left (sub_nonneg.mpr hMlr),
    max_eq_left (sub_nonneg.mpr (add_le_add hKa hMb))]
  nlinarith

lemma finSplit_measurePreserving (n : ℕ) : MeasurePreserving (finSplit n) := by
  have hs : MeasurePreserving (Prod.swap : ℝ × (Fin n → ℝ) → (Fin n → ℝ) × ℝ) := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ))))
  exact hs.comp (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0)

lemma finOne_measurePreserving : MeasurePreserving finOne :=
  volume_preserving_piUnique (fun _ : Fin 1 => ℝ)

/-- Brunn--Minkowski in all positive Cartesian dimensions, obtained by the
actual convex-body slice induction. -/
theorem brunnMinkowski_fin (n : ℕ) : BrunnMinkowskiRoot (Fin (n+1) → ℝ) (n+1) := by
  induction n with
  | zero =>
    exact brunnMinkowski_real.equiv finOne.symm
      (MeasurePreserving.symm finOne.toHomeomorph.toMeasurableEquiv finOne_measurePreserving)
  | succ n ih =>
    let : Measure.IsAddHaarMeasure (volume : Measure ((Fin (n+1) → ℝ) × ℝ)) := by
      rw [Measure.volume_eq_prod]
      infer_instance
    have hprod : BrunnMinkowskiRoot ((Fin (n+1) → ℝ) × ℝ) (n+1+1) := by
      apply brunnMinkowski_of_unit (by omega)
      · simp
      · intro K M hK hcK hiK hM hcM hiM hvK hvM a b ha hb hab
        exact brunnMinkowski_product_unit (by omega) ih hK hcK hiK hM hcM hiM hvK hvM ha hb hab
    exact hprod.equiv (finSplit (n+1)).symm
      (MeasurePreserving.symm (finSplit (n+1)).toHomeomorph.toMeasurableEquiv
        (finSplit_measurePreserving (n+1)))

/-- The Brunn–Minkowski inequality in `ℝⁿ` (`EuclideanSpace ℝ (Fin n)`, `n ≥ 1`, Lebesgue
measure), concavity form: for compact convex sets `K`, `M` with nonempty interior and
`a, b ≥ 0` with `a + b = 1`,
`a · vol(K)^(1/n) + b · vol(M)^(1/n) ≤ vol(a • K + b • M)^(1/n)`. -/
theorem brunnMinkowski_euclidean_oai {n : ℕ} (hn : 0 < n) (K M : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hcK : Convex ℝ K) (hiK : (interior K).Nonempty)
    (hM : IsCompact M) (hcM : Convex ℝ M) (hiM : (interior M).Nonempty)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * volume.real K ^ ((n:ℝ)⁻¹) + b * volume.real M ^ ((n:ℝ)⁻¹) ≤
      volume.real (a • K + b • M) ^ ((n:ℝ)⁻¹) := by
  have h : BrunnMinkowskiRoot (Space n) n := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact (brunnMinkowski_fin m).equiv
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m+1) => ℝ)).symm
      (PiLp.volume_preserving_toLp (Fin (m+1)))
  exact h K M hK hcK hiK hM hcM hiM a b ha hb hab

end PettyProjection
end

end OAI
end

theorem solution : type_of% @OAI.PettyProjection.brunnMinkowski_euclidean_oai := @OAI.PettyProjection.brunnMinkowski_euclidean_oai
