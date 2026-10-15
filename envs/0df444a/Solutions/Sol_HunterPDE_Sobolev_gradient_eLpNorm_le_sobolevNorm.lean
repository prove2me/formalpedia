-- Prove2me | solution 1 for HunterPDE.Sobolev.gradient_eLpNorm_le_sobolevNorm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T21:17:08.432241+00:00
-- url     : https://prove2.me/submissions/1385fe53-be13-4a89-8447-de156bda0c0a

import Theorems.Thm_HunterPDE_Sobolev_hasWeakDeriv_of_contDiff
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_ae_eq
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open MeasureTheory HunterPDE.Sobolev
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsTestFunction Set.univ f) :
    eLpNorm (fun x => ‖gradient f x‖) (ENNReal.ofReal p) volume ≤
      (n : ENNReal) * sobolevNorm 1 (ENNReal.ofReal p) Set.univ f := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpE : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have word (i : Fin n) (l : List (Fin n)) (hl : l.Nodup)
      (u : EuclideanSpace ℝ (Fin n) → ℝ) :
      l.foldr (fun j (v : EuclideanSpace ℝ (Fin n) → ℝ) =>
        (partialDeriv j)^[((Pi.single i (1 : ℕ) : Fin n → ℕ) j)] v) u =
        if i ∈ l then partialDeriv i u else u := by
    induction l with
    | nil => simp
    | cons j l ih =>
      obtain ⟨hj, hln⟩ := List.nodup_cons.mp hl
      by_cases hij : i = j
      · subst j
        have hi : i ∉ l := hj
        simp [List.foldr_cons, ih hln, hi]
      · simp [List.foldr_cons, ih hln, hij]
  have hpartial (i : Fin n) : iteratedPartial (Pi.single i (1 : ℕ)) f = partialDeriv i f := by
    simpa [iteratedPartial] using word i (List.finRange n) (List.nodup_finRange n) f
  have coord (i : Fin n) : eLpNorm (partialDeriv i f) (ENNReal.ofReal p) volume ≤
      sobolevNorm 1 (ENNReal.ofReal p) Set.univ f := by
    have hweak := hasWeakDeriv_of_contDiff f hf.1 (Pi.single i (1 : ℕ))
    have chosen : HasWeakDeriv Set.univ (Pi.single i (1 : ℕ)) f
        (weakDeriv Set.univ (Pi.single i (1 : ℕ)) f) := by
      unfold weakDeriv
      rw [dif_pos (show ∃ v, HasWeakDeriv Set.univ (Pi.single i (1 : ℕ)) f v from ⟨_, hweak⟩)]
      exact Exists.choose_spec _
    have hae : weakDeriv Set.univ (Pi.single i (1 : ℕ)) f =ᵐ[volume] partialDeriv i f := by
      simpa only [Measure.restrict_univ, hpartial i] using chosen.ae_eq isOpen_univ hweak
    have hmem : Pi.single i (1 : ℕ) ∈ multiIndices n 1 := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨Pi.single i (1 : Fin 2), Finset.mem_univ _, ?_⟩, ?_⟩
      · ext j
        by_cases h : j = i <;> simp [h]
      · simp
    rw [sobolevNorm, if_neg ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le]
    have hs := Finset.single_le_sum (s := multiIndices n 1)
      (f := fun α => eLpNorm (weakDeriv Set.univ α f) (ENNReal.ofReal p)
        (volume.restrict Set.univ) ^ p) (fun _ _ => bot_le) hmem
    have hr := ENNReal.rpow_le_rpow hs (by positivity : 0 ≤ 1 / p)
    simpa only [Measure.restrict_univ, eLpNorm_congr_ae hae, ← ENNReal.rpow_mul,
      mul_one_div_cancel hp0.ne', ENNReal.rpow_one] using hr
  let v : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun i x => EuclideanSpace.single i (partialDeriv i f x)
  have decomp : gradient f = ∑ i, v i := by
    funext x
    apply PiLp.ext
    intro i
    have hi : (gradient f x) i = partialDeriv i f x := by
      have h := inner_gradient_left (𝕜 := ℝ) (f := f) (x := x)
        (y := EuclideanSpace.single i 1)
      rw [EuclideanSpace.inner_single_right] at h
      change (1 : ℝ) * (gradient f x) i = _ at h
      simpa only [one_mul, partialDeriv] using h
    simpa [v, Finset.sum_apply, PiLp.single_apply] using hi
  have vmeas (i : Fin n) : AEStronglyMeasurable (v i) volume := by
    have hc : Continuous (partialDeriv i f) := by
      exact ((hf.1.contDiff_fderiv_apply (m := ∞) (by simp)).comp
        (contDiff_id.prodMk contDiff_const)).continuous
    have hi : Isometry (fun t : ℝ => EuclideanSpace.single i t) := by
      intro a b
      simp [edist_dist, dist_eq_norm, ← PiLp.single_sub]
    exact (hi.continuous.comp hc).aestronglyMeasurable
  calc
    _ = eLpNorm (gradient f) (ENNReal.ofReal p) volume := eLpNorm_norm _
    _ ≤ ∑ i, eLpNorm (v i) (ENNReal.ofReal p) volume := by
      rw [decomp]
      exact eLpNorm_sum_le (fun i _ => vmeas i) hpE
    _ ≤ ∑ _i : Fin n, sobolevNorm 1 (ENNReal.ofReal p) Set.univ f := by
      apply Finset.sum_le_sum
      intro i _
      have heq : eLpNorm (v i) (ENNReal.ofReal p) volume =
          eLpNorm (partialDeriv i f) (ENNReal.ofReal p) volume :=
        eLpNorm_congr_norm_ae (Filter.Eventually.of_forall (fun x => by simp [v]))
      rw [heq]
      exact coord i
    _ = _ := by simp
