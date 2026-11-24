-- Prove2me | solution 1 for GlobalTheory.continuousOn_norm_diag_of_triangular_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:58.153919+00:00
-- url     : https://prove2.me/submissions/420f78fe-daa8-44a7-96c2-2f25ac1117a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ContinuousOnNormDiagOfTriangularSqrt
import Theorems.Thm_GlobalTheory_TriSqrt_det_eq_prod_diag
import Theorems.Thm_GlobalTheory_TriSqrt_det_minor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
namespace GlobalTheory
theorem _root_.solution : ∀ (g : ℕ) (α : Type) [Fintype α] (V : Type) [TopologicalSpace V] (t : Fin g → α) (w : Fin g → ℕ) (d : Fin g → ℝ) (B : Set V) (S Hm : V → Matrix (Fin g) (Fin g) ℂ), (∀ j j', t j = t j' → w j = w j' → j = j') → (∀ j, 0 < d j) → (∀ j j', ContinuousOn (fun b => Hm b j j') B) → (∀ b ∈ B, IsUnit (S b).det ∧ (∀ j j', S b j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') ∧ Hm b = (S b)ᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * (S b).map (starRingEnd ℂ))) → ∀ j, ContinuousOn (fun b => ‖S b j j‖) B := by
  intro g α _ V _ t w d B S Hm hinj hd hc hS j
  classical
  have hH : ContinuousOn Hm B := continuousOn_pi.2 fun k => continuousOn_pi.2 fun l => hc k l
  have hP : ∀ n : ℕ, ContinuousOn (fun b =>
      ∏ c ∈ Finset.univ.filter (fun c => t c = t j ∧ w c < n), ‖S b c c‖ ^ 2 * d c) B := by
    intro n
    have h1 : Continuous fun M : Matrix (Fin g) (Fin g) ℂ =>
        ((M.submatrix (Subtype.val : {c // t c = t j ∧ w c < n} → Fin g) Subtype.val).det).re :=
      Complex.continuous_re.comp (continuous_id.matrix_submatrix _ _).matrix_det
    refine (h1.comp_continuousOn hH).congr fun b hb => ?_
    obtain ⟨-, h2, h3⟩ := hS b hb
    simp only [Function.comp_apply]
    rw [h3, GlobalTheory.TriSqrt.det_minor t w hinj d (S b) h2 (fun c => t c = t j ∧ w c < n), Complex.ofReal_re]
    intro c a hne ha
    obtain ⟨h4, h5⟩ := h2 c a hne
    exact ⟨h4.trans ha.1, by omega⟩
  have hne : ∀ b ∈ B, ∀ c, S b c c ≠ 0 := by
    intro b hb c
    obtain ⟨h1, h2, -⟩ := hS b hb
    rw [GlobalTheory.TriSqrt.det_eq_prod_diag t w hinj _ h2, isUnit_iff_ne_zero] at h1
    exact Finset.prod_ne_zero_iff.1 h1 c (Finset.mem_univ _)
  have hne' : ∀ b ∈ B, (∏ c ∈ Finset.univ.filter (fun c => t c = t j ∧ w c < w j),
      ‖S b c c‖ ^ 2 * d c) * d j ≠ 0 := fun b hb =>
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun c _ =>
      mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 (hne b hb c))) (hd c).ne') (hd j).ne'
  have hins : Finset.univ.filter (fun c => t c = t j ∧ w c < w j + 1)
      = insert j (Finset.univ.filter (fun c => t c = t j ∧ w c < w j)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h3 : w c = w j
      · exact Or.inl (hinj _ _ h1 h3)
      · exact Or.inr ⟨h1, by omega⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨rfl, by omega⟩
      · exact ⟨h1, by omega⟩
  refine (((hP (w j + 1)).div ((hP (w j)).mul continuousOn_const) hne').sqrt).congr fun b hb => ?_
  have h0 := hne' b hb
  simp only [Pi.div_apply, Pi.mul_apply]
  rw [hins, Finset.prod_insert (by simp), mul_assoc, mul_comm (d j), mul_div_assoc, div_self h0, mul_one,
    Real.sqrt_sq (norm_nonneg _)]
end GlobalTheory
