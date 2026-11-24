-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GLFirstBasisOrbit.exists_gl_cov
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:39.754727+00:00
-- url     : https://prove2.me/submissions/adb84892-a0b2-457e-843f-886b27f31395

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_star_e0_dotProduct
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_exists_GL_first_basis_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical PositivityTheory.Rg.Rs
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GLFirstBasisOrbit
variable {k : Type} [Field k] {n : ℕ}
namespace GlobalTheory.CompanionTheory.GLFirstBasisOrbit
theorem _root_.solution (a : Fin (n + 1) → k) (ha : a ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k, ∀ x, a ⬝ᵥ (g.val *ᵥ x) = x 0 := by
  obtain ⟨h, hh⟩ := exists_GL_first_basis_eq a ha
  have hd : (h.val)ᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnits_det_units h).ne_zero
  let T : GL (Fin (n + 1)) k := Matrix.GeneralLinearGroup.mkOfDetNeZero (h.val)ᵀ hd
  refine ⟨T⁻¹, fun x => ?_⟩
  have hT : T.val = (h.val)ᵀ := rfl
  have h1 : a = e0 k n ᵥ* T.val := by rw [hT, Matrix.vecMul_transpose, hh]
  rw [Matrix.dotProduct_mulVec, h1, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.vecMul_one, star_e0_dotProduct]
end GlobalTheory.CompanionTheory.GLFirstBasisOrbit
