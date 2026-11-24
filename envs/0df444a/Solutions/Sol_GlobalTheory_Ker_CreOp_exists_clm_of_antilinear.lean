-- Prove2me | solution 1 for GlobalTheory.Ker.CreOp.exists_clm_of_antilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:29:49.515299+00:00
-- url     : https://prove2.me/submissions/9c950355-33c0-41af-b425-c6d15183e0e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FoldrHolDEqIteratedFDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.Ker GlobalTheory.Ker.CreOp
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace GlobalTheory.Ker.CreOp
theorem _root_.solution [FiniteDimensional ℂ W] {lam : W → ℂ}
    (h1 : ∀ a b, lam (a + b) = lam a + lam b) (h2 : ∀ (t : ℂ) a, lam (t • a) = conj t * lam a) :
    ∃ T : W →L[ℝ] ℂ, lam = T := by
  have hr : ∀ (r : ℝ) (a : W), lam (r • a) = r • lam a := by
    intro r a
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r a, h2]
    simp [Complex.real_smul]
  have : FiniteDimensional ℝ W := Module.Finite.trans ℂ W
  exact ⟨LinearMap.toContinuousLinearMap
    ({ toFun := lam, map_add' := h1, map_smul' := fun r a => by rw [RingHom.id_apply]; exact hr r a }
      : W →ₗ[ℝ] ℂ), rfl⟩
end GlobalTheory.Ker.CreOp
