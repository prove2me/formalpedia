-- Prove2me | solution 1 for GlobalTheory.UnitaryChar.exists_conj_diagHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:15:34.565956+00:00
-- url     : https://prove2.me/submissions/c51ec5a1-0799-483b-a493-140154ca23ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CircleHomEqZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupContinuousCharEqDetZpow
import Theorems.Thm_GlobalTheory_UnitaryChar_exists_conj_diagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.UnitaryChar
variable {n : ℕ}
namespace GlobalTheory.UnitaryChar
theorem _root_.solution (u : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ (V : Matrix.unitaryGroup (Fin n) ℂ) (t : Fin n → Circle), V⁻¹ * u * V = diagHom n t := by
  obtain ⟨V, d, h⟩ := exists_conj_diagonal u
  have h1 := (V⁻¹ * u * V).2.2
  rw [h, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal] at h1
  have h2 : ∀ i, ‖d i‖ = 1 := fun i => by
    have := congrFun (congrFun h1 i) i
    simp only [diagonal_apply_eq, one_apply_eq, Pi.star_apply, RCLike.star_def,
      Complex.mul_conj, Complex.normSq_eq_norm_sq] at this
    have h3 : ‖d i‖ ^ 2 = 1 := by exact_mod_cast this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
  exact ⟨V, fun i => ⟨d i, by simpa [Submonoid.unitSphere] using h2 i⟩, Subtype.ext h⟩
end GlobalTheory.UnitaryChar
