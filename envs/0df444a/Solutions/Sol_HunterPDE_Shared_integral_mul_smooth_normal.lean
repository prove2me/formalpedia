-- Prove2me | solution 1 for HunterPDE.Shared.integral_mul_smooth_normal
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-18T16:47:31.586228+00:00
-- url     : https://prove2.me/submissions/e466223c-d021-426a-b596-8aca7f3c693e

import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith

open MeasureTheory HunterPDE.Compactness HunterPDE.Shared Filter Set
open scoped ENNReal Topology ContDiff
set_option autoImplicit false

theorem solution {m : ℕ}
    (f ψ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : IsTestFunction Set.univ f) (hψ : IsTestFunction Set.univ ψ) :
    (∫ x in upperHalfSpace m, partialDeriv f (Fin.last m) x * ψ x) =
      -(∫ x in upperHalfSpace m, f x * multiDeriv ψ (Pi.single (Fin.last m) 1) x) -
        ∫ x', f (boundaryPoint x') * ψ (boundaryPoint x') := by
  classical
  let i := Fin.last m
  have hl (l : List (Fin (m + 1))) (hl : l.Nodup) :
      l.flatMap (fun j => List.replicate ((Pi.single i 1 : Fin (m + 1) → ℕ) j) j) =
        if i ∈ l then [i] else [] := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have ha := (List.nodup_cons.mp hl).1
      have hh := ih (List.nodup_cons.mp hl).2
      by_cases h : a = i
      · subst a; simp [List.flatMap_cons, hh, ha]
      · simp [List.flatMap_cons, hh, h, Ne.symm h]
  have hm : multiDeriv ψ (Pi.single i 1) = partialDeriv ψ i := by
    unfold multiDeriv multiIndexList
    rw [hl (List.finRange (m + 1)) (List.nodup_finRange (m + 1))]
    simp [iteratedPartial]
  change (∫ x in upperHalfSpace m, partialDeriv f i x * ψ x) =
    -(∫ x in upperHalfSpace m, f x * multiDeriv ψ (Pi.single i 1) x) - _
  rw [hm]
  have hdf : Continuous (partialDeriv f i) :=
    ((hf.1.contDiff_fderiv_apply (m := ∞) (by simp)).comp
      (contDiff_id.prodMk contDiff_const)).continuous
  have hdψ : Continuous (partialDeriv ψ i) :=
    ((hψ.1.contDiff_fderiv_apply (m := ∞) (by simp)).comp
      (contDiff_id.prodMk contDiff_const)).continuous
  have hA : Integrable (fun x => partialDeriv f i x * ψ x) :=
    (hdf.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left
  have hB : Integrable (fun x => f x * partialDeriv ψ i x) :=
    (hf.1.continuous.mul hdψ).integrable_of_hasCompactSupport hf.2.1.mul_right
  let F := fun x => partialDeriv f i x * ψ x + f x * partialDeriv ψ i x
  have hF : Integrable F := hA.add hB
  let e : EuclideanSpace ℝ (Fin (m + 1)) ≃ᵐ
      ℝ × EuclideanSpace ℝ (Fin m) :=
    ((MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm.trans
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i)).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
          (MeasurableEquiv.toLp 2 (Fin m → ℝ)))
  have he : MeasurePreserving e volume (volume.prod volume) :=
    ((PiLp.volume_preserving_ofLp (Fin (m + 1))).trans
      (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i)).trans
        ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin m)))
  have hval (t : ℝ) (x' : EuclideanSpace ℝ (Fin m)) :
      e.symm (t, x') = WithLp.toLp 2 (Fin.snoc (fun j => x' j) t) := by
    change WithLp.toLp 2 ((Fin.insertNthEquiv (fun _ : Fin (m + 1) => ℝ)
      (Fin.last m)) (t, WithLp.ofLp x')) = _
    simp [Fin.insertNthEquiv, Fin.insertNth_last']
  have hpre : e.symm ⁻¹' upperHalfSpace m = Ioi (0 : ℝ) ×ˢ univ := by
    ext p
    simp [hval, upperHalfSpace]
  have hFI : IntegrableOn (F ∘ e.symm) (Ioi (0 : ℝ) ×ˢ univ)
      (volume.prod volume) := by
    rw [← hpre]
    exact (he.symm.integrableOn_comp_preimage e.symm.measurableEmbedding).mpr hF.integrableOn
  have hchange : (∫ x in upperHalfSpace m, F x) =
      ∫ x' : EuclideanSpace ℝ (Fin m), ∫ t in Ioi (0 : ℝ), F (e.symm (t, x')) := by
    rw [← (he.symm.restrict_preimage_emb e.symm.measurableEmbedding
      (upperHalfSpace m)).integral_comp e.symm.measurableEmbedding, hpre]
    unfold IntegrableOn at hFI
    rw [← Measure.prod_restrict] at hFI ⊢
    simp only [Measure.restrict_univ] at hFI ⊢
    exact integral_prod_symm _ hFI
  have hsections : ∀ᵐ x' : EuclideanSpace ℝ (Fin m),
      IntegrableOn (fun t => F (e.symm (t, x'))) (Ioi (0 : ℝ)) := by
    unfold IntegrableOn at hFI
    rw [← Measure.prod_restrict] at hFI
    simp only [Measure.restrict_univ] at hFI
    exact hFI.prod_left_ae
  have hray : ∀ᵐ x' : EuclideanSpace ℝ (Fin m),
      (∫ t in Ioi (0 : ℝ), F (e.symm (t, x'))) =
        -(f (boundaryPoint x') * ψ (boundaryPoint x')) := by
    filter_upwards [hsections] with x' hx'
    let v : EuclideanSpace ℝ (Fin (m + 1)) := EuclideanSpace.single i 1
    let c : ℝ → EuclideanSpace ℝ (Fin (m + 1)) := fun t => boundaryPoint x' + t • v
    have hc (t : ℝ) : c t = e.symm (t, x') := by
      rw [hval]
      ext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [c, v, i, boundaryPoint]
    have hc0 : c 0 = boundaryPoint x' := by simp [c]
    have hdc (t : ℝ) : HasDerivAt c v t := by
      convert! (hasDerivAt_const t (boundaryPoint x')).add
        ((hasDerivAt_id t).smul_const v) using 1
      simp only [zero_add, one_smul]
    have hder (t : ℝ) : HasDerivAt (fun t => f (c t) * ψ (c t)) (F (e.symm (t, x'))) t := by
      convert! ((hf.1.differentiable (by simp) (c t)).hasFDerivAt.comp_hasDerivAt t (hdc t)).mul
        ((hψ.1.differentiable (by simp) (c t)).hasFDerivAt.comp_hasDerivAt t (hdc t)) using 1
      simp [F, partialDeriv, v, hc]
    have hlim : Tendsto (fun t => f (c t) * ψ (c t)) atTop (𝓝 0) := by
      obtain ⟨R, hR⟩ := hf.2.1.isCompact.isBounded.exists_norm_le
      have hz : (fun t => f (c t) * ψ (c t)) =ᶠ[atTop] (fun _ => 0) := by
        filter_upwards [eventually_gt_atTop (max R 0)] with t ht
        have hct : c t ∉ tsupport f := by
          intro h
          have hn := PiLp.norm_apply_le (c t) i
          have hi : c t i = t := by simp [c, v, i, boundaryPoint]
          rw [hi, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt (le_max_right R 0) ht)] at hn
          have := hR (c t) h
          linarith [le_max_left R 0]
        simp [image_eq_zero_of_notMem_tsupport hct]
      exact tendsto_const_nhds.congr' hz.symm
    simpa only [zero_sub, hc0] using
      integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hder t) hx' hlim
  have hid : (∫ x in upperHalfSpace m, F x) =
      -(∫ x', f (boundaryPoint x') * ψ (boundaryPoint x')) := by
    rw [hchange, integral_congr_ae hray, integral_neg]
  rw [show (∫ x in upperHalfSpace m, F x) =
    (∫ x in upperHalfSpace m, partialDeriv f i x * ψ x) +
      ∫ x in upperHalfSpace m, f x * partialDeriv ψ i x from
        integral_add hA.integrableOn hB.integrableOn] at hid
  linarith
