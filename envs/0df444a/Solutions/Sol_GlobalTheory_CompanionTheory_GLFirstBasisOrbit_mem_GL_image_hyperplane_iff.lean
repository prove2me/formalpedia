-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GLFirstBasisOrbit.mem_GL_image_hyperplane_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:32.410415+00:00
-- url     : https://prove2.me/submissions/3b67d827-26ce-4404-b6b5-250815a8bda7

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_mem_riemannRochSpace_iff_regularAt_everywhere

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
theorem _root_.solution (g : GL (Fin (n + 1)) k) (a : Fin (n + 1) → k)
    (h : ∀ x, a ⬝ᵥ (g.val *ᵥ x) = x 0) (z : Fin (n + 1) → k) :
    z ∈ gmap g (H0 k n) ↔ a ⬝ᵥ z = 0 := by
  rw [mem_gmap, mem_riemannRochSpace_iff_regularAt_everywhere, ← h ((g⁻¹).val *ᵥ z), Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mulVec]
end GlobalTheory.CompanionTheory.GLFirstBasisOrbit
