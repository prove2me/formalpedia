-- Prove2me | solution 1 for GlobalTheory.pnorm_near_half_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:40:28.095058+00:00
-- url     : https://prove2.me/submissions/8360bfbd-4070-4dbe-99e6-550b5822399b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_ScaledBoundInequality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe
import Theorems.Thm_GlobalTheory_dmin_rmul_near_one
import Theorems.Thm_GlobalTheory_exists_pnorm_eq_mul_exp
import Theorems.Thm_GlobalTheory_rmul_one_frame
import Theorems.Thm_GlobalTheory_differentiable_rmul_add
import Theorems.Thm_schwarz_ball_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory
theorem _root_.solution {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : DifferentiableOn ℂ P X.dom) (S : ℝ)
    (hS : ∀ x ∈ X.dom, X.pnorm la P x ≤ S) (x : Frame X.Ψ r)
    (hx : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (hhalf : S / 2 ≤ X.pnorm la P x)
    (A : Frame X.Ψ r) (hA : ∀ τ a b, ‖A τ a b - (if a = b then 1 else 0)‖ ≤ 1 / (1000 * (r : ℝ) ^ 2 * (1 + ∑ τ, ∑ i, |(la τ i : ℝ)|))) :
    rmul x A ∈ X.dom ∧ S / 4 ≤ X.pnorm la P (rmul x A) := by
  set L : ℝ := ∑ τ, ∑ i, |(la τ i : ℝ)| with hL
  have hL0 : 0 ≤ L := by positivity
  set I : Frame X.Ψ r := fun _ a b => if a = b then 1 else 0 with hI
  have hxI : rmul x I = x := rmul_one_frame x
  obtain ⟨hxd, hx0⟩ := dmin_rmul_near_one X x hx I le_rfl (by norm_num) (by simp [hI])
  rw [hxI] at hxd hx0
  obtain ⟨s0, hs0, hs0'⟩ := exists_pnorm_eq_mul_exp X la x hx0
  have hPx : X.pnorm la P x = ‖P x‖ := by
    have : s0 = 0 := by simpa using hs0
    rw [hs0', this, Real.exp_zero, mul_one]
  have hSx := hS x hxd
  rw [hPx] at hSx hhalf
  have hS0 : 0 ≤ S := (norm_nonneg _).trans hSx
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have : rmul x A = x := Subsingleton.elim _ _
    rw [this, hPx]
    exact ⟨hxd, by linarith⟩
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (100 * (r : ℝ) ^ 2 * (1 + L)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : (r : ℝ) ^ 2 * δ * (1 + L) = 1 / 100 := by rw [hδ]; field_simp
  have hδ2 : 1 / (1000 * (r : ℝ) ^ 2 * (1 + L)) = δ / 10 := by rw [hδ]; field_simp; norm_num
  rw [hδ2] at hA
  have hrδ : 0 ≤ (r : ℝ) ^ 2 * δ := by positivity
  have key : ∀ z : Frame X.Ψ r, ‖z‖ ≤ δ → rmul x (I + z) ∈ X.dom ∧
      ∃ s : ℝ, |s| ≤ 0.09 ∧ X.pnorm la P (rmul x (I + z)) = ‖P (rmul x (I + z))‖ * Real.exp s := by
    intro z hz
    obtain ⟨h1, h2⟩ := dmin_rmul_near_one X x hx (I + z) hδ0.le (by nlinarith) (fun τ a b => by
      simp only [hI, Pi.add_apply, add_sub_cancel_left]
      exact (norm_le_pi_norm (z τ a) b).trans ((norm_le_pi_norm (z τ) a).trans
        ((norm_le_pi_norm z τ).trans hz)))
    obtain ⟨s, hs, hs'⟩ := exists_pnorm_eq_mul_exp X la _ h2
    exact ⟨h1, s, hs.trans (by rw [← hL]; nlinarith), hs' P⟩
  have hexp : ∀ s : ℝ, |s| ≤ 0.09 → 0.91 ≤ Real.exp s := fun s hs => by
    linarith [Real.add_one_le_exp s, (abs_le.1 hs).1]
  have hsch := schwarz_ball_bound (Frame X.Ψ r) (fun z => P (rmul x (I + z))) δ (2.1 * S) hδ0
    (hP.comp (differentiable_rmul_add x I).differentiableOn fun z hz =>
      (key z (mem_ball_zero_iff.1 hz).le).1)
    (fun z hz => by
      obtain ⟨h1, s, h2, h3⟩ := key z (mem_ball_zero_iff.1 hz).le
      have h4 := hS _ h1
      have h5 := hexp s h2
      simp only [add_zero, hxI]
      refine (norm_sub_le _ _).trans ?_
      nlinarith [norm_nonneg (P (rmul x (I + z)))])
  have hz : ‖A - I‖ ≤ δ / 10 := by
    have h0 : 0 ≤ δ / 10 := by positivity
    exact (pi_norm_le_iff_of_nonneg h0).2 fun τ => (pi_norm_le_iff_of_nonneg h0).2 fun a =>
      (pi_norm_le_iff_of_nonneg h0).2 fun b => hA τ a b
  obtain ⟨h1, s, h2, h3⟩ := key (A - I) (by linarith)
  have h4 := hsch (A - I) (mem_ball_zero_iff.2 (by linarith))
  simp only [add_zero, hxI] at h4
  rw [add_sub_cancel] at h1 h3 h4
  refine ⟨h1, ?_⟩
  have h5 : 2.1 * S * ‖A - I‖ / δ ≤ 0.21 * S := by
    rw [div_le_iff₀ hδ0]
    nlinarith
  have h6 := hexp s h2
  have h7 := norm_le_insert (P (rmul x A)) (P x)
  rw [h3]
  nlinarith [norm_nonneg (P (rmul x A))]
end GlobalTheory
