-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpMain.w_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:20.065326+00:00
-- url     : https://prove2.me/submissions/a9e5e9ed-34e2-4e8e-b9b2-9e14aa8a2e5a

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_fix_of_gmap
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_mem_GL_image_hyperplane_iff


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
theorem _root_.solution (hD : LatData k n B red ρ t v) {gam : (Fin (n + 1) → k) → Γ} (hc : IsCov red gam)
    {y : V} (hy : y ∈ stabV red ρ) {a : Fin (n + 1) → k} (ha : a ≠ 0) {s : k} (hs : s ≠ 0) :
    ρ (gam (s • a)) (t y) = ρ (gam a) (t y) := by
  have hsa : s • a ≠ 0 := smul_ne_zero hs ha
  apply fix_of_gmap hD hy
  ext z
  rw [mem_GL_image_hyperplane_iff _ _ (hc (s • a) hsa) z, mem_GL_image_hyperplane_iff _ _ (hc a ha) z, smul_dotProduct, smul_eq_mul,
    mul_eq_zero, or_iff_right hs]
end GlobalTheory.CompanionTheory.GapOpMain
