-- Prove2me | solution 1 for HunterPDE.Shared.normalJet_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T19:39:01.298296+00:00
-- url     : https://prove2.me/submissions/1b68c500-e6bd-4829-8d6c-f81b44e8e098

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
open HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

theorem solution {n : ℕ} (i : Fin n) (k : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f)
    (hb : ∀ r : ℕ, r < k → ∀ x : EuclideanSpace ℝ (Fin n), x i = 0 →
      iteratedPartial f (List.replicate r i) x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      ‖f x‖ ≤ C * ‖x i‖ ^ k := by
  induction k generalizing f with
  | zero =>
    obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf.continuous
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    simpa using (hC x).trans (le_max_left C 0)
  | succ k ih =>
    have hp : ContDiff ℝ ∞ (partialDeriv f i) :=
      (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hrep (r : ℕ) : iteratedPartial (partialDeriv f i) (List.replicate r i) =
        iteratedPartial f (List.replicate (r + 1) i) := by
      induction r with
      | zero => rfl
      | succ r hr => simpa only [List.replicate_succ, iteratedPartial] using congrArg (fun g => partialDeriv g i) hr
    obtain ⟨C, hC, hbound⟩ := ih (partialDeriv f i) hp (hc.fderiv_apply ℝ _) (by
      intro r hr x hx
      rw [hrep]
      exact hb (r + 1) (by omega) x hx)
    refine ⟨C, hC, fun x => ?_⟩
    let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
    let z := x - (x i) • e
    let g : ℝ → EuclideanSpace ℝ (Fin n) := fun t => z + (t * x i) • e
    have hz : z i = 0 := by simp [z, e]
    have hg (t : ℝ) : HasDerivAt g ((x i) • e) t := by
      simpa [g] using (((hasDerivAt_id t).mul_const (x i)).smul_const e).const_add z
    have hfg (t : ℝ) : HasDerivAt (fun s => f (g s))
        ((x i) * partialDeriv f i (g t)) t := by
      convert (hf.differentiable (by simp) (g t)).hasFDerivAt.comp_hasDerivAt t (hg t) using 1 <;>
        first | rfl | simp [partialDeriv, e]
    have hM := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t _ => (hfg t).hasDerivWithinAt) (C := C * ‖x i‖ ^ (k + 1)) (by
        intro t ht
        have ht' : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht.1]; exact ht.2.le
        have hgi : ‖g t i‖ ≤ ‖x i‖ := by
          simp only [g, PiLp.add_apply, PiLp.smul_apply, hz, e, PiLp.single_apply,
            ↓reduceIte, smul_eq_mul, mul_one, zero_add]
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) ht'
        calc
          ‖x i * partialDeriv f i (g t)‖ = ‖x i‖ * ‖partialDeriv f i (g t)‖ := norm_mul _ _
          _ ≤ ‖x i‖ * (C * ‖g t i‖ ^ k) := mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
          _ ≤ ‖x i‖ * (C * ‖x i‖ ^ k) := by gcongr
          _ = C * ‖x i‖ ^ (k + 1) := by ring)
    have hzero : f z = 0 := hb 0 (by omega) z hz
    simpa [g, hzero, z, sub_add_cancel] using hM

