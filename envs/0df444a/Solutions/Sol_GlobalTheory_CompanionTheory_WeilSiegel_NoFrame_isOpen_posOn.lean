-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:48.865795+00:00
-- url     : https://prove2.me/submissions/141e6ac5-91e6-4eaa-a471-ac172cbfc565

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableOfMulUnimodular
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PositiveOnSubspaceOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
theorem _root_.solution (n : ℕ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)) :
    IsOpen {Z : Matrix (Fin n) (Fin n) ℂ | PosOn ε Z S} := by
  set K : Set (Fin n → ℂ) := (S : Set (Fin n → ℂ)) ∩ Metric.sphere 0 1 with hK
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_left S.closed_of_finiteDimensional
  let F : Matrix (Fin n) (Fin n) ℂ → (Fin n → ℂ) → ℝ := fun Z w => ε * (star w ⬝ᵥ Z.mulVec w).re
  have hF : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) => F p.1 p.2) :=
    continuous_const.mul (Complex.continuous_re.comp
      ((continuous_snd.star).dotProduct (continuous_fst.matrix_mulVec continuous_snd)))
  have hscale : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) (c : ℝ),
      F Z ((c : ℂ) • w) = c ^ 2 * F Z w := by
    intro Z w c
    simp only [F, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul,
      Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul]
    ring
  have heq : {Z : Matrix (Fin n) (Fin n) ℂ | PosOn ε Z S} = {Z | ∀ w ∈ K, 0 < F Z w} := by
    ext Z
    constructor
    · rintro hZ w ⟨hwS, hw1⟩
      refine hZ w hwS ?_
      rintro rfl
      simp at hw1
    · intro hZ w hwS hw0
      have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hmem : ((‖w‖⁻¹ : ℝ) : ℂ) • w ∈ K := by
        refine ⟨S.smul_mem _ hwS, ?_⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
      have h2 := hZ _ hmem
      rw [hscale] at h2
      exact pos_of_mul_pos_right h2 (by positivity)
  rw [heq, isOpen_iff_mem_nhds]
  intro Z₀ hZ₀
  exact hKc.eventually_forall_of_forall_eventually fun w hw =>
    (hF.tendsto (Z₀, w)).eventually (lt_mem_nhds (hZ₀ w hw))
end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
