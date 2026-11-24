-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.sum_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:23.902875+00:00
-- url     : https://prove2.me/submissions/51023964-0695-4274-b1f8-2cddafa3809f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnalyticWord
variable {V H : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type}
namespace GlobalTheory.CompanionTheory.AnalyticWord
theorem _root_.solution [Fintype ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V)
    (hskew : ∀ i v w, inner ℂ (j (Z i v)) (j w) = - inner ℂ (j v) (j (Z i w)))
    (S Ω : Module.End ℂ V) (hT : ∑ i, Z i * Z i = Ω + S + S) (v : V) (i : ι) :
    ‖j (Z i v)‖ ^ 2 ≤ ‖j v‖ * (‖j (Ω v)‖ + 2 * ‖j (S v)‖) := by
  have key : ∀ k, ‖j (Z k v)‖ ^ 2 = - RCLike.re (inner ℂ (j v) (j ((Z k * Z k) v))) := by
    intro k
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hskew, Module.End.mul_apply, map_neg]
  have hsum : ∑ k, ‖j (Z k v)‖ ^ 2 = - RCLike.re (inner ℂ (j v) (j ((Ω + S + S) v))) := by
    rw [← hT, LinearMap.sum_apply, map_sum, inner_sum, map_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => key k
  have hle : ‖j (Z i v)‖ ^ 2 ≤ ∑ k, ‖j (Z k v)‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖j (Z k v)‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
  rw [hsum] at hle
  have h2 : - RCLike.re (inner ℂ (j v) (j ((Ω + S + S) v))) ≤ ‖j v‖ * ‖j ((Ω + S + S) v)‖ :=
    (neg_le_abs _).trans ((RCLike.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
  have h3 : ‖j ((Ω + S + S) v)‖ ≤ ‖j (Ω v)‖ + 2 * ‖j (S v)‖ := by
    rw [LinearMap.add_apply, LinearMap.add_apply, map_add, map_add]
    calc _ ≤ ‖j (Ω v) + j (S v)‖ + ‖j (S v)‖ := norm_add_le _ _
      _ ≤ ‖j (Ω v)‖ + ‖j (S v)‖ + ‖j (S v)‖ := add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by ring
  exact (hle.trans h2).trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
end GlobalTheory.CompanionTheory.AnalyticWord
