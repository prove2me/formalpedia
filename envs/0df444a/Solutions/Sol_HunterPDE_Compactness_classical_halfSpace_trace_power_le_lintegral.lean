-- Prove2me | solution 1 for HunterPDE.Compactness.classical_halfSpace_trace_power_le_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T16:56:46.584509+00:00
-- url     : https://prove2.me/submissions/cb0903c1-1a71-4478-a338-25d8239515f9

import Theorems.Thm_Real_enorm_rpow_le_lintegral_deriv_of_eq_zero
import Theorems.Thm_MeasureTheory_lintegral_halfSpace_snoc
import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory HunterPDE.Compactness HunterPDE.Shared Set
open scoped ENNReal NNReal ContDiff
set_option autoImplicit false

theorem solution {m : ℕ} (r : ℝ) (hr : 1 ≤ r)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : ContDiffOn ℝ 1 f (closedUpperHalfSpace m))
    (hK : ∃ K : Set (EuclideanSpace ℝ (Fin (m + 1))), IsCompact K ∧
      ∀ x ∈ closedUpperHalfSpace m, x ∉ K → f x = 0) :
    (∫⁻ x', ‖f (boundaryPoint x')‖ₑ ^ r) ≤ ENNReal.ofReal r *
      ∫⁻ x, ‖f x‖ₑ ^ (r - 1) * ‖partialDeriv f (Fin.last m) x‖ₑ
        ∂volume.restrict (upperHalfSpace m) := by
  have hsub : upperHalfSpace m ⊆ closedUpperHalfSpace m := by
    intro x hx
    exact (show 0 < x (Fin.last m) from hx).le
  have ho : IsOpen (upperHalfSpace m) :=
    isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last m)).continuous
  have hfH := hf.mono hsub
  have hdH : ContinuousOn (partialDeriv f (Fin.last m)) (upperHalfSpace m) :=
    (hfH.continuousOn_fderiv_of_isOpen ho le_rfl).clm_apply continuousOn_const
  have hFM : AEMeasurable
      (fun x => ‖f x‖ₑ ^ (r - 1) * ‖partialDeriv f (Fin.last m) x‖ₑ)
      (volume.restrict (upperHalfSpace m)) := by
    exact ((hfH.continuousOn.aemeasurable ho.measurableSet).enorm.pow_const _).mul
      (hdH.aemeasurable ho.measurableSet).enorm
  rw [MeasureTheory.lintegral_halfSpace_snoc _ hFM]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x'
  let v : EuclideanSpace ℝ (Fin (m + 1)) := EuclideanSpace.single (Fin.last m) 1
  let c : ℝ → EuclideanSpace ℝ (Fin (m + 1)) := fun t => boundaryPoint x' + t • v
  have hc (t : ℝ) : c t = WithLp.toLp 2 (Fin.snoc (fun i => x' i) t) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [c, v, boundaryPoint]
  have hc0 : c 0 = boundaryPoint x' := by simp [c]
  have hcl (t : ℝ) : c t (Fin.last m) = t := by simp [hc]
  have hcc : ContDiff ℝ 1 c := contDiff_const.add (contDiff_id.smul contDiff_const)
  obtain ⟨K, hcompact, hsupport⟩ := hK
  obtain ⟨R, hR⟩ := hcompact.isBounded.exists_norm_le
  let b : ℝ := max R 0 + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hcb : c b ∉ K := by
    intro h
    have hh := hR (c b) h
    have hn := PiLp.norm_apply_le (c b) (Fin.last m)
    rw [hcl, Real.norm_eq_abs, abs_of_pos hb] at hn
    have : R < b := by dsimp [b]; linarith [le_max_left R 0]
    linarith
  have hmaps : MapsTo c (Icc 0 b) (closedUpperHalfSpace m) := by
    intro t ht
    change 0 ≤ c t (Fin.last m)
    simpa [hcl] using ht.1
  have hg : ContDiffOn ℝ 1 (f ∘ c) (Icc 0 b) :=
    hf.comp hcc.contDiffOn hmaps
  have hzero : (f ∘ c) b = 0 :=
    hsupport (c b) (by change 0 ≤ c b (Fin.last m); simpa [hcl] using hb.le) hcb
  have hder (t : ℝ) (ht : 0 < t) : deriv (f ∘ c) t = partialDeriv f (Fin.last m) (c t) := by
    have hct : c t ∈ upperHalfSpace m := by change 0 < c t (Fin.last m); simpa [hcl]
    have hdf : DifferentiableAt ℝ f (c t) :=
      ((hfH (c t) hct).contDiffAt (ho.mem_nhds hct)).differentiableAt one_ne_zero
    have hdc : HasDerivAt c v t := by
      convert! (hasDerivAt_const t (boundaryPoint x')).add
        ((hasDerivAt_id t).smul_const v) using 1
      simp only [zero_add, one_smul]
    exact (hdf.hasFDerivAt.comp_hasDerivAt t hdc).deriv
  have hbound := Real.enorm_rpow_le_lintegral_deriv_of_eq_zero r hr (f ∘ c) 0 b hb.le hg hzero
  simp only [Function.comp_apply, hc0] at hbound
  refine hbound.trans (mul_le_mul le_rfl ?_ (by positivity) (by positivity))
  refine (lintegral_mono_set (show Ioo 0 b ⊆ Ioi 0 from fun _ ht => ht.1)).trans_eq ?_
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  rw [hder t ht]
  simp only [hc]

