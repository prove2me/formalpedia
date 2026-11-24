-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.exists_basis_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:28:32.937636+00:00
-- url     : https://prove2.me/submissions/d79b6b55-9730-4942-9763-a89554cf847a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Theorems.Thm_GlobalTheory_QuadraticZeta_exists_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors UpperHalfPlane ComplexConjugate
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ) :
    ∃ (b : Basis (Fin 2) ℤ (𝓞 K)) (t : ℤ), b 0 = 1 ∧ 2 * (σ (b 1)).re = t ∧
      4 * (σ (b 1)).im ^ 2 = d := by
  obtain ⟨b, t, n, h0, hw, hD'⟩ := exists_basis h2
  have hd : (0 : ℝ) < d := by
    have := discr_ne_zero K
    exact_mod_cast (by omega : 0 < d)
  have e : (t : ℝ) ^ 2 - 4 * n = -d := by exact_mod_cast hD'.symm.trans hD
  have h : σ (b 1) ^ 2 = t * σ (b 1) - n := by
    have := congrArg (fun x : 𝓞 K => σ x) hw
    simpa using this
  refine ⟨b, t, h0, ?_⟩
  generalize σ (b 1) = W at h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [sq] at h1 h2
  have h3 : W.im ≠ 0 := fun h => by
    rw [h] at h1
    nlinarith [sq_nonneg (2 * W.re - t)]
  have h4 : 2 * W.re = t := mul_right_cancel₀ h3 (by linarith)
  refine ⟨h4, ?_⟩
  rw [← h4] at h1 e
  nlinarith
end GlobalTheory.QuadraticZeta
