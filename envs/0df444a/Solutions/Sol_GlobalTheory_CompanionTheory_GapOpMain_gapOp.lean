-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpMain.gapOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:34:52.483935+00:00
-- url     : https://prove2.me/submissions/69fc2d61-8a2e-426a-bd87-c78192a2ad32

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_zx_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_uop_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_uop_bound
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_uop_zx
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_pairing
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_zx_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_zx_last
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_exists_gl_cov


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
theorem _root_.solution : PositivityTheory.Rg.Rs.GapOp := by
  unfold GapOp
  intro k _ _ n V Γ _ _ _ B red ρ t v lam hD hl
  have hgam : ∀ a : Fin (n + 1) → k, a ≠ 0 → ∃ γ : Γ, ∀ x, a ⬝ᵥ ((red γ).val *ᵥ x) = x 0 := by
    intro a ha
    obtain ⟨g, hg⟩ := exists_gl_cov a ha
    obtain ⟨γ, rfl⟩ := hD.surj g
    exact ⟨γ, hg⟩
  let gam : (Fin (n + 1) → k) → Γ := fun a => if ha : a = 0 then 1 else Classical.choose (hgam a ha)
  have hc : IsCov red gam := by
    intro a ha x
    have h1 : gam a = Classical.choose (hgam a ha) := dif_neg ha
    rw [h1]
    exact Classical.choose_spec (hgam a ha) x
  exact ⟨stabV red ρ, uop ρ t gam, zx v (e0 k n), fun y hy => uop_mem hD hc hy, fun j => zx_mem hD j,
    fun y hy => uop_bound hD hc hy, zx_zero hD, zx_last v, fun j hj => uop_zx hD hc lam hl hj,
    fun j hj => pairing hD lam hl hj⟩
end GlobalTheory.CompanionTheory.GapOpMain
