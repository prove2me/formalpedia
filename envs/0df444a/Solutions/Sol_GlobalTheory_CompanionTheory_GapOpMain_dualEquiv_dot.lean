-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpMain.dualEquiv_dot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:12.115905+00:00
-- url     : https://prove2.me/submissions/50fdaef5-9b60-476e-a634-cf51db1b518e

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpMain
variable {k : Type} [Field k] [Fintype k] {n : ℕ} {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
  {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {red : Γ →* GL (Fin (n + 1)) k} {ρ : Γ →* Module.End ℂ V} {t : Module.End ℂ V}
  {v : Submodule k (Fin (n + 1) → k) → V}
namespace GlobalTheory.CompanionTheory.GapOpMain
theorem _root_.solution (g : GL (Fin (n + 1)) k) (a x : Fin (n + 1) → k) :
    dualEquiv g a ⬝ᵥ (g.val *ᵥ x) = a ⬝ᵥ x := by
  show (a ᵥ* (g⁻¹).val) ⬝ᵥ (g.val *ᵥ x) = a ⬝ᵥ x
  rw [← dotProduct_mulVec, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
end GlobalTheory.CompanionTheory.GapOpMain
