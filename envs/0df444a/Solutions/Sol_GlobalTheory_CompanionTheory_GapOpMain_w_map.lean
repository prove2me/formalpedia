-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpMain.w_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:49.150821+00:00
-- url     : https://prove2.me/submissions/9b562004-70ea-48e7-a2b1-2f82d572c53e

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_fix_of_gmap
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_dualEquiv_dot
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_dualEquiv_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_mem_GL_image_hyperplane_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
namespace GlobalTheory.CompanionTheory.GapOpMain
variable {k : Type} [Field k] [Fintype k] {n : ℕ} {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
  {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {red : Γ →* GL (Fin (n + 1)) k} {ρ : Γ →* Module.End ℂ V} {t : Module.End ℂ V}
  {v : Submodule k (Fin (n + 1) → k) → V}
private theorem monoidHom_mul_apply_eq_apply_apply (ρ : Γ →* Module.End ℂ V) (a b : Γ) (x : V) : ρ (a * b) x = ρ a (ρ b x) :=
  congrArg (fun f : Module.End ℂ V => f x) (map_mul ρ a b)
end GlobalTheory.CompanionTheory.GapOpMain
end
end

set_option autoImplicit false
noncomputable section
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpMain
variable {k : Type} [Field k] [Fintype k] {n : ℕ} {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
  {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {red : Γ →* GL (Fin (n + 1)) k} {ρ : Γ →* Module.End ℂ V} {t : Module.End ℂ V}
  {v : Submodule k (Fin (n + 1) → k) → V}
namespace GlobalTheory.CompanionTheory.GapOpMain
theorem _root_.solution (hD : LatData k n B red ρ t v) {gam : (Fin (n + 1) → k) → Γ} (hc : IsCov red gam)
    {y : V} (hy : y ∈ stabV red ρ) (γ : Γ) {a : Fin (n + 1) → k} (ha : a ≠ 0) :
    ρ γ (ρ (gam a) (t y)) = ρ (gam (dualEquiv (red γ) a)) (t y) := by
  have ha' : dualEquiv (red γ) a ≠ 0 := dualEquiv_ne _ ha
  rw [← monoidHom_mul_apply_eq_apply_apply]
  apply fix_of_gmap hD hy
  ext z
  rw [mem_GL_image_hyperplane_iff (red (gam (dualEquiv (red γ) a))) _ (hc _ ha') z]
  rw [map_mul, gmap_mul, mem_gmap (red γ), mem_GL_image_hyperplane_iff _ _ (hc a ha)]
  have key : dualEquiv (red γ) a ⬝ᵥ z = a ⬝ᵥ (((red γ)⁻¹).val *ᵥ z) := by
    have h2 := dualEquiv_dot (red γ) a (((red γ)⁻¹).val *ᵥ z)
    rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h2
  rw [key]
end GlobalTheory.CompanionTheory.GapOpMain
