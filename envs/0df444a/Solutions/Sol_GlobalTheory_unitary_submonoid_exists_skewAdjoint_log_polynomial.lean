-- Prove2me | solution 1 for GlobalTheory.unitary_submonoid_exists_skewAdjoint_log_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:39:44.732456+00:00
-- url     : https://prove2.me/submissions/c314a592-d8e4-45d8-bbb1-79ceff029cbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryExistsSkewLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open scoped Matrix.Norms.L2Operator
namespace GlobalTheory
theorem _root_.solution (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ)
    (hk : k ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
      star X = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by
  classical
  have hspec := spectrum.subset_circle_of_unitary (𝕜 := ℂ) hk
  have hfin := Matrix.finite_spectrum k
  have hcont : ∀ f : ℂ → ℂ, ContinuousOn f (spectrum ℂ k) := fun f => hfin.continuousOn f
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℂ, ∀ z ∈ spectrum ℂ k, p.eval z = Complex.log z := by
    refine ⟨Lagrange.interpolate hfin.toFinset id Complex.log, fun z hz => ?_⟩
    have := Lagrange.eval_interpolate_at_node (s := hfin.toFinset) (v := id) (i := z) Complex.log
      (Set.injOn_id _) (by simpa using hz)
    simpa using this
  refine ⟨cfc Complex.log k, p, ?_, ?_, ?_⟩
  · rw [← cfc_star, ← cfc_neg]
    refine cfc_congr fun z hz => ?_
    have h1 : ‖z‖ = 1 := by simpa using hspec hz
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]
  · rw [← CFC.complex_exp_eq_normedSpace_exp, ← cfc_comp Complex.exp Complex.log k
      (hg := (Set.Finite.image _ hfin).continuousOn _) (hf := hcont _)]
    have h0 : ∀ z ∈ spectrum ℂ k, (Complex.exp ∘ Complex.log) z = id z := by
      intro z hz
      have h1 : ‖z‖ = 1 := by simpa using hspec hz
      have : z ≠ 0 := by rintro rfl; simp at h1
      simp [Complex.exp_log this]
    rw [cfc_congr h0, cfc_id ℂ k]
  · rw [← cfc_polynomial p k]
    exact cfc_congr fun z hz => (hp z hz).symm
end GlobalTheory
