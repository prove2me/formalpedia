-- Prove2me | solution 1 for OAI.PettyProjection.brunnMinkowski_equality_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:09:02.238275+00:00
-- url     : https://prove2.me/submissions/840e86fe-bf36-4c96-8e6a-58c68acddd13

import Mathlib
import Definitions.Def_PettyProjectionVolume
import Definitions.Def_OAIQWPP000
import Theorems.Thm_OAI_PettyProjection_brunnMinkowski_euclidean

section
-- module Solutions.OAIQW_PettyProjection.Support
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

lemma support_eq_iff {n : ℕ} {K L : Set (Space n)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (hKn : K.Nonempty)
    (hL : IsCompact L) (hcL : Convex ℝ L) (hLn : L.Nonempty) :
    support K = support L ↔ K = L := by
  constructor
  · intro h
    ext x
    rw [mem_iff_inner_le_support hK hcK hKn,mem_iff_inner_le_support hL hcL hLn,h]
  · rintro rfl; rfl

end PettyProjection
end

end OAI
end

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

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

lemma shadowContinuousEquiv_apply {n : ℕ} (u : Sphere n) (z : perpendicular (u : Space n) × ℝ) :
    shadowContinuousEquiv u z = z.1+z.2 • (u : Space n) := rfl

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

/-- Standard Euclidean volume version used for the projection-body theorem. -/
theorem brunnMinkowski_space {n : ℕ} (hn : 0 < n) : BrunnMinkowskiRoot (Space n) n :=
  brunnMinkowski_euclidean hn

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
namespace PettyProjection

/-- Brunn--Minkowski for the canonical Euclidean volume on any finite-dimensional
real inner-product space. -/
theorem brunnMinkowski_innerProduct {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hE : 0 < Module.finrank ℝ E) : BrunnMinkowskiRoot E (Module.finrank ℝ E) := by
  exact (brunnMinkowski_space hE).equiv
    (stdOrthonormalBasis ℝ E).repr.symm.toContinuousLinearEquiv
    (stdOrthonormalBasis ℝ E).measurePreserving_repr_symm

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.Homothety
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Filter Topology
namespace PettyProjection

lemma quantile_first_moment {l r : ℝ} {f Q : ℝ → ℝ}
    (hQc : Continuous Q) (hQ0 : Q 0=l) (hQ1 : Q 1=r)
    (hQd : ∀ s ∈ Ioo (0:ℝ) 1, HasDerivAt Q (f (Q s))⁻¹ s)
    (hfp : ∀ s ∈ Ioo (0:ℝ) 1, 0 < f (Q s)) :
    (∫ s in (0:ℝ)..1, Q s)=(∫ x in l..r, x*f x) := by
  have hdu : ∀ s ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1), HasDerivAt Q (f (Q s))⁻¹ s := by
    simpa only [min_eq_left zero_le_one,max_eq_right zero_le_one] using hQd
  have hpu : ∀ s ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1), 0 ≤ (f (Q s))⁻¹ := by
    simpa only [min_eq_left zero_le_one,max_eq_right zero_le_one] using
      fun s hs => (inv_pos.mpr (hfp s hs)).le
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := fun x => x*f x) hQc.continuousOn hdu hpu
  rw [hQ0,hQ1] at he
  refine (intervalIntegral.integral_congr_ae_restrict ?_).trans he
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  simp [(hfp s hs).ne']

/-- Equality in slice transport forces the two full marginal distributions to
be translates. In particular both projection endpoints differ by the difference
of their first moments. -/
theorem slice_transport_equality {m : ℕ} (hm : 0 < m) {a b l r L R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a+b=1) (hlr : l<r) (hLR : L<R)
    {f g h : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo l r)) (hg : ContinuousOn g (Ioo L R))
    (hfi : IntervalIntegrable f volume l r) (hgi : IntervalIntegrable g volume L R)
    (hfp : ∀ x ∈ Ioo l r, 0 < f x) (hgp : ∀ x ∈ Ioo L R, 0 < g x)
    (hfI : (∫ x in l..r, f x)=1) (hgI : (∫ x in L..R, g x)=1)
    (hhi : IntervalIntegrable h volume (a*l+b*L) (a*r+b*R))
    (hbound : ∀ x ∈ Ioo l r, ∀ y ∈ Ioo L R,
      (a*(f x)^((m:ℝ)⁻¹)+b*(g y)^((m:ℝ)⁻¹))^m ≤ h (a*x+b*y))
    (hI : (∫ z in (a*l+b*L)..(a*r+b*R), h z)=1) :
    l-L=(∫ x in l..r, x*f x)-(∫ y in L..R, y*g y) ∧
    r-R=(∫ x in l..r, x*f x)-(∫ y in L..R, y*g y) := by
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
  have hInt : (∫ s in Icc (0:ℝ) 1, h (z s)*z' s)=1 := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      hsub,hz0,hz1,hI]
  have hOne : (∫ _ in Icc (0:ℝ) 1, (1:ℝ))=1 := by simp
  have hAe : (fun _ : ℝ => (1:ℝ)) =ᵐ[volume.restrict (Icc (0:ℝ) 1)]
      (fun s => h (z s)*z' s) :=
    (integral_eq_iff_of_ae_le (integrableOn_const isCompact_Icc.measure_ne_top)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp hint) hae).mp
        (hOne.trans hInt.symm)
  have hAe' : (fun s => f (Q s)) =ᵐ[volume.restrict (Ioo (0:ℝ) 1)] (fun s => g (P s)) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc] at hAe
    filter_upwards [hAe,ae_restrict_mem measurableSet_Ioo] with s hs hsmem
    let p := (f (Q s))^((m:ℝ)⁻¹)
    let q := (g (P s))^((m:ℝ)⁻¹)
    have hp : 0 < p := Real.rpow_pos_of_pos (hfp _ (hQd s hsmem).1) _
    have hq : 0 < q := Real.rpow_pos_of_pos (hgp _ (hPd s hsmem).1) _
    have hpm : p^m=f (Q s) := Real.rpow_inv_natCast_pow (hfp _ (hQd s hsmem).1).le hm.ne'
    have hqm : q^m=g (P s) := Real.rpow_inv_natCast_pow (hgp _ (hPd s hsmem).1).le hm.ne'
    have ht := transport_scalar hm ha hb hab hp hq
    have hle : (a*p+b*q)^m*(a/(p^m)+b/(q^m)) ≤ 1 := by
      rw [hpm,hqm,hs]
      exact mul_le_mul_of_nonneg_right (hbound _ (hQd s hsmem).1 _ (hPd s hsmem).1) (hzp s hsmem).le
    have hpq : p=q := ht.2.mp (le_antisymm hle ht.1)
    exact hpm.symm.trans ((congrArg (fun x : ℝ => x^m) hpq).trans hqm)
  have hfg : EqOn (fun s => f (Q s)) (fun s => g (P s)) (Ioo (0:ℝ) 1) :=
    Measure.eqOn_open_of_ae_eq hAe' isOpen_Ioo
      (hf.comp hQc.continuousOn (fun s hs => (hQd s hs).1))
      (hg.comp hPc.continuousOn (fun s hs => (hPd s hs).1))
  obtain ⟨c,hc⟩ := IsOpen.exists_eq_add_of_deriv_eq isOpen_Ioo (convex_Ioo (0:ℝ) 1).isPreconnected
    (fun s hs => (hQd s hs).2.differentiableAt.differentiableWithinAt)
    (fun s hs => (hPd s hs).2.differentiableAt.differentiableWithinAt)
    (fun s hs => by
      rw [(hQd s hs).2.deriv,(hPd s hs).2.deriv]
      exact congrArg Inv.inv (hfg hs))
  have hcc : EqOn Q (fun s => P s+c) (Icc (0:ℝ) 1) := by
    simpa only [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] using hc.closure hQc (hPc.add continuous_const)
  have hQInt := quantile_first_moment hQc hQ0 hQ1 (fun s hs => (hQd s hs).2)
    (fun s hs => hfp _ (hQd s hs).1)
  have hPInt := quantile_first_moment hPc hP0 hP1 (fun s hs => (hPd s hs).2)
    (fun s hs => hgp _ (hPd s hs).1)
  have hcInt : (∫ s in (0:ℝ)..1, Q s)=(∫ s in (0:ℝ)..1, P s)+c := by
    rw [intervalIntegral.integral_congr (fun s hs => hcc (by simpa only [uIcc_of_le zero_le_one] using hs)),
      intervalIntegral.integral_add (hPc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp
  have hc0 := hcc (show (0:ℝ) ∈ Icc 0 1 by norm_num)
  have hc1 := hcc (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  dsimp only at hc0 hc1
  rw [hQ0,hP0] at hc0
  rw [hQ1,hP1] at hc1
  rw [hQInt,hPInt] at hcInt
  constructor <;> linarith

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

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
lemma sliceDensity_moment_indicator {K : Set (E × ℝ)} (hK : IsCompact K) (s : ℝ) :
    (∫ x : E, K.indicator Prod.snd (x,s))=s*sliceDensity K s := by
  have he : (fun x : E => K.indicator Prod.snd (x,s)) =
      (horizontalSlice K s).indicator (fun _ => s) := by
    funext x
    by_cases hx : (x,s) ∈ K
    · rw [Set.indicator_of_mem hx,Set.indicator_of_mem (show x ∈ horizontalSlice K s from hx)]
    · rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem (show x ∉ horizontalSlice K s from hx)]
  rw [he,integral_indicator (horizontalSlice_compact hK s).measurableSet,setIntegral_const]
  simp only [smul_eq_mul,sliceDensity,mul_comm]

lemma sliceDensity_moment {K : Set (E × ℝ)} (hK : IsCompact K) :
    (∫ s, s*sliceDensity K s)=(∫ x in K, x.2) := by
  have hi : Integrable (K.indicator Prod.snd) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (continuous_snd.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  have he := integral_prod_symm (K.indicator Prod.snd) hi
  simp_rw [sliceDensity_moment_indicator hK] at he
  rw [← he,← Measure.volume_eq_prod,integral_indicator hK.measurableSet]

lemma sliceDensity_interval_moment {K : Set (E × ℝ)} (hK : IsCompact K) {l r : ℝ}
    (hlr : l≤r) (hp : Prod.snd '' K ⊆ Icc l r) :
    (∫ s in l..r, s*sliceDensity K s)=(∫ x in K, x.2) := by
  rw [intervalIntegral.integral_of_le hlr,← integral_Icc_eq_integral_Ioc]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact sliceDensity_moment hK
  · intro s hs
    rw [sliceDensity_zero_of_notMem (fun h => hs (hp h)),mul_zero]

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

/-- Equality in the actual product-body step identifies both extreme heights
with the difference of the (unit-volume) vertical first moments. -/
theorem brunnMinkowski_product_unit_equality {m : ℕ} (hm0 : 0 < m) (hm : BrunnMinkowskiRoot E m)
    {K M : Set (E × ℝ)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty) (hvK : volume.real K=1) (hvM : volume.real M=1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hvC : volume.real (a • K+b • M)=1)
    {l r L R : ℝ} (hlr : l<r) (hLR : L<R)
    (hpr : Prod.snd '' K=Icc l r) (hPR : Prod.snd '' M=Icc L R) :
    l-L=(∫ x in K, x.2)-(∫ x in M, x.2) ∧
    r-R=(∫ x in K, x.2)-(∫ x in M, x.2) := by
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
  have hmain : l-L=(∫ s in l..r, s*sliceDensity K s)-(∫ t in L..R, t*sliceDensity M t) ∧
      r-R=(∫ s in l..r, s*sliceDensity K s)-(∫ t in L..R, t*sliceDensity M t) := by
    apply slice_transport_equality hm0 ha hb hab hlr hLR
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
    · rw [sliceDensity_interval_integral hC (by nlinarith) hbounds,hvC]
  rwa [sliceDensity_interval_moment hK hlr.le (by rw [hpr]),
    sliceDensity_interval_moment hM hLR.le (by rw [hPR])] at hmain

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology Function
open scoped Pointwise RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma shadowContinuousEquiv_inner {n : ℕ} (u : Sphere n)
    (z : perpendicular (u : Space n) × ℝ) :
    ⟪(u : Space n),shadowContinuousEquiv u z⟫=z.2 := by
  rw [shadowContinuousEquiv_apply,inner_add_right,perpendicular_inner,
    real_inner_smul_right,real_inner_self_eq_norm_sq,norm_coe]
  ring

lemma shadow_vertical_image {n : ℕ} (u : Sphere n) (K : Set (Space n)) :
    Prod.snd '' (shadowContinuousEquiv u ⁻¹' K)=(fun x => ⟪(u : Space n),x⟫) '' K := by
  ext s
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨shadowContinuousEquiv u z,hz,shadowContinuousEquiv_inner u z⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨(shadowContinuousEquiv u).symm x,by simpa using hx,?_⟩
    rw [← shadowContinuousEquiv_inner u,ContinuousLinearEquiv.apply_symm_apply]

lemma shadow_firstMoment {n : ℕ} (u : Sphere n) {K : Set (Space n)} (hK : IsCompact K) :
    (∫ z in shadowContinuousEquiv u ⁻¹' K, z.2)=⟪(u : Space n),firstMoment K⟫ := by
  have he : MeasurePreserving (shadowContinuousEquiv u) := shadowMeasurableEquiv_measurePreserving u
  have hi := (he.restrict_preimage hK.measurableSet).integral_comp
    (shadowContinuousEquiv u).toHomeomorph.measurableEmbedding (fun x => ⟪(u : Space n),x⟫)
  simp_rw [shadowContinuousEquiv_inner] at hi
  rw [hi]
  exact integral_inner (continuous_id.continuousOn.integrableOn_compact hK) _

lemma perpendicular_finrank {n : ℕ} (u : Sphere n) :
    Module.finrank ℝ (perpendicular (u : Space n))=n-1 := by
  have hu : (u : Space n) ≠ 0 := by intro h; simpa [h] using norm_coe u
  have hr := (Submodule.span ℝ {(u : Space n)}).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hu] at hr
  have he : Module.finrank ℝ (Space n)=n := by simp [Space]
  rw [he] at hr
  change Module.finrank ℝ ((Submodule.span ℝ {(u : Space n)})ᗮ)=n-1
  omega

/-- Equality for an intermediate Minkowski combination of unit-volume bodies
identifies every directional support difference with the first-moment shift. -/
theorem brunnMinkowski_unit_support_equality {n : ℕ} (hn : 2 ≤ n)
    {K M : Set (Space n)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty) (hvK : volume.real K=1) (hvM : volume.real M=1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hvC : volume.real (a • K+b • M)=1) (u : Sphere n) :
    support K u-support M u=⟪(u : Space n),firstMoment K-firstMoment M⟫ := by
  let e := shadowContinuousEquiv u
  have he : MeasurePreserving e := shadowMeasurableEquiv_measurePreserving u
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
  have hcPK := hcK.linear_preimage e.toLinearMap
  have hcPM := hcM.linear_preimage e.toLinearMap
  obtain ⟨l,r,hlr,hpr⟩ := vertical_projection_interval hPK hcPK hiPK
  obtain ⟨L,R,hLR,hPR⟩ := vertical_projection_interval hPM hcPM hiPM
  have hv (S : Set (Space n)) (hS : IsCompact S) : volume.real (e ⁻¹' S)=volume.real S :=
    congrArg ENNReal.toReal (he.measure_preimage hS.measurableSet.nullMeasurableSet)
  have hm0 : 0 < Module.finrank ℝ (perpendicular (u : Space n)) := by
    rw [perpendicular_finrank]; omega
  have heq := brunnMinkowski_product_unit_equality hm0 (brunnMinkowski_innerProduct hm0)
    hPK hcPK hiPK hPM hcPM hiPM ((hv K hK).trans hvK) ((hv M hM).trans hvM) ha hb hab
    (by rw [← linearEquiv_preimage_combo,hv _ ((hK.smul _).add (hM.smul _)),hvC]) hlr hLR hpr hPR
  have hr : support K u=r := by
    unfold support
    rw [← shadow_vertical_image u K,hpr,csSup_Icc hlr.le]
  have hR : support M u=R := by
    unfold support
    rw [← shadow_vertical_image u M,hPR,csSup_Icc hLR.le]
  rw [hr,hR,heq.2,inner_sub_right]
  change (∫ z in shadowContinuousEquiv u ⁻¹' K, z.2)-
      (∫ z in shadowContinuousEquiv u ⁻¹' M, z.2)=_
  rw [shadow_firstMoment u hK,shadow_firstMoment u hM]

lemma support_translate {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (hKn : K.Nonempty) (c u : Space n) :
    support ((fun x => c+x) '' K) u=⟪u,c⟫+support K u := by
  apply le_antisymm
  · apply (support_le_iff (hK.image (by fun_prop)) (hKn.image _)).mpr
    rintro _ ⟨x,hx,rfl⟩
    rw [inner_add_right]
    exact add_le_add_right (inner_le_support hK hx u) _
  · obtain ⟨x,hx,he⟩ := support_attained hK hKn u
    rw [he,← inner_add_right]
    exact inner_le_support (hK.image (by fun_prop)) (mem_image_of_mem _ hx) u

/-- The unrestricted translated-body equality case of the unit-volume
Brunn--Minkowski inequality (no origin symmetry or boundary regularity). -/
theorem brunnMinkowski_unit_equality {n : ℕ} (hn : 2 ≤ n)
    {K M : Set (Space n)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty) (hvK : volume.real K=1) (hvM : volume.real M=1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hvC : volume.real (a • K+b • M)=1) :
    K=(fun x => firstMoment K-firstMoment M+x) '' M := by
  have hKn := hiK.mono interior_subset
  have hMn := hiM.mono interior_subset
  apply (support_eq_iff hK hcK hKn (hM.image (by fun_prop))
    (hcM.translate _) (hMn.image _)).mp
  funext x
  rw [support_translate hM hMn]
  by_cases hx : x=0
  · subst x
    simp [support,hKn,hMn]
  · let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hx]⟩
    have hxu : x=‖x‖ • (u : Space n) := by
      change x=‖x‖ • (‖x‖⁻¹ • x)
      rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]
    have he := brunnMinkowski_unit_support_equality hn hK hcK hiK hM hcM hiM hvK hvM ha hb hab hvC u
    rw [hxu,support_smul hK hKn (norm_nonneg x),support_smul hM hMn (norm_nonneg x),real_inner_smul_left]
    rw [← he]
    ring

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection

lemma volumeRoot_pow {n : ℕ} (hn : 0 < n) (K : Set (Space n)) :
    volumeRoot K^n=volume.real K :=
  Real.rpow_inv_natCast_pow measureReal_nonneg hn.ne'

/-- Equality in the homogeneous additive form, retaining arbitrary translation. -/
theorem brunnMinkowski_add_equality {n : ℕ} (hn : 2 ≤ n)
    {K M : Set (Space n)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty)
    (hv : volumeRoot (K+M)=volumeRoot K+volumeRoot M) :
    ∃ z : Space n, ∃ c : ℝ, 0 < c ∧ K=(fun x => z+c • x) '' M := by
  let p := volumeRoot K
  let q := volumeRoot M
  have hp : 0 < p := volumeRoot_pos hK hiK
  have hq : 0 < q := volumeRoot_pos hM hiM
  have hpq : 0 < p+q := add_pos hp hq
  have hd : Module.finrank ℝ (Space n)=n := by simp [Space]
  have hUK : volume.real (p⁻¹ • K)=1 := by
    rw [volumeReal_smul_nonneg (inv_nonneg.mpr hp.le),hd,inv_pow,volumeRoot_pow (by omega)]
    exact inv_mul_cancel₀ (volumeReal_pos_of_body hK hiK).ne'
  have hUM : volume.real (q⁻¹ • M)=1 := by
    rw [volumeReal_smul_nonneg (inv_nonneg.mpr hq.le),hd,inv_pow,volumeRoot_pow (by omega)]
    exact inv_mul_cancel₀ (volumeReal_pos_of_body hM hiM).ne'
  have hiUK : (interior (p⁻¹ • K)).Nonempty := by
    rw [interior_smul₀ (inv_ne_zero hp.ne')]
    exact hiK.image _
  have hiUM : (interior (q⁻¹ • M)).Nonempty := by
    rw [interior_smul₀ (inv_ne_zero hq.ne')]
    exact hiM.image _
  have hsets : (p/(p+q)) • (p⁻¹ • K)+(q/(p+q)) • (q⁻¹ • M)=(p+q)⁻¹ • (K+M) := by
    rw [smul_add,smul_smul,smul_smul]
    congr 2 <;> field_simp
  have hunit : volume.real ((p/(p+q)) • (p⁻¹ • K)+(q/(p+q)) • (q⁻¹ • M))=1 := by
    rw [hsets,volumeReal_smul_nonneg (inv_nonneg.mpr hpq.le),hd,inv_pow,
      ← volumeRoot_pow (by omega) (K+M),hv]
    exact inv_mul_cancel₀ (pow_ne_zero _ hpq.ne')
  have he := brunnMinkowski_unit_equality hn (hK.smul _) (hcK.smul _) hiUK
    (hM.smul _) (hcM.smul _) hiUM hUK hUM (div_pos hp hpq) (div_pos hq hpq)
    (by rw [← add_div,div_self hpq.ne']) hunit
  let d := firstMoment (p⁻¹ • K)-firstMoment (q⁻¹ • M)
  refine ⟨p • d,p/q,div_pos hp hq,?_⟩
  calc
    K = p • (p⁻¹ • K) := by rw [smul_smul,mul_inv_cancel₀ hp.ne',one_smul]
    _ = p • ((fun x => d+x) '' (q⁻¹ • M)) := by rw [he]
    _ = (fun x => p • d+(p/q) • x) '' M := by
      rw [← image_smul,image_image,← image_smul,image_image]
      congr 1
      funext x
      simp only [smul_add,smul_smul,div_eq_mul_inv]

/-- Equality in the Brunn–Minkowski inequality in `ℝⁿ` (`EuclideanSpace ℝ (Fin n)`, `n ≥ 2`,
Lebesgue measure): if compact convex sets `K`, `M` with nonempty interior satisfy
`vol(K + M)^(1/n) = vol(K)^(1/n) + vol(M)^(1/n)`, then `K = z + c • M` for some point `z` and
some `c > 0`. -/
theorem brunnMinkowski_equality_euclidean_oai {n : ℕ} (hn : 2 ≤ n)
    {K M : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty)
    (hv : volume.real (K + M) ^ ((n:ℝ)⁻¹)
      = volume.real K ^ ((n:ℝ)⁻¹) + volume.real M ^ ((n:ℝ)⁻¹)) :
    ∃ z : EuclideanSpace ℝ (Fin n), ∃ c : ℝ, 0 < c ∧ K = (fun x => z + c • x) '' M :=
  brunnMinkowski_add_equality hn hK hcK hiK hM hcM hiM hv

end PettyProjection
end

end OAI
end

theorem solution : type_of% @OAI.PettyProjection.brunnMinkowski_equality_euclidean_oai := @OAI.PettyProjection.brunnMinkowski_equality_euclidean_oai
