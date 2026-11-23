-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpMain.fix_of_gmap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:33.495895+00:00
-- url     : https://prove2.me/submissions/50262747-6232-4db8-90e8-97bdeb6eb6eb

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_mem_stabV

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
theorem _root_.solution (hD : LatData k n B red ρ t v) {y : V} (hy : y ∈ stabV red ρ) {γ₁ γ₂ : Γ}
    (h : gmap (red γ₁) (H0 k n) = gmap (red γ₂) (H0 k n)) : ρ γ₁ (t y) = ρ γ₂ (t y) := by
  have hfix := (mem_stabV red ρ y).mp hy
  have hδ : gmap (red (γ₂⁻¹ * γ₁)) (H0 k n) = H0 k n := by
    rw [map_mul, gmap_mul, h, ← gmap_mul, ← map_mul, inv_mul_cancel, map_one, gmap_one]
  have key := hD.fix y hfix (γ₂⁻¹ * γ₁) hδ
  calc ρ γ₁ (t y) = ρ (γ₂ * (γ₂⁻¹ * γ₁)) (t y) := by rw [mul_inv_cancel_left]
    _ = ρ γ₂ (ρ (γ₂⁻¹ * γ₁) (t y)) := monoidHom_mul_apply_eq_apply_apply ρ _ _ _
    _ = ρ γ₂ (t y) := by rw [key]
end GlobalTheory.CompanionTheory.GapOpMain
