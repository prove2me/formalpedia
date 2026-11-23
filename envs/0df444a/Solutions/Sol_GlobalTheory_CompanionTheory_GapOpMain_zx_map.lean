-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpMain.zx_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:52.439939+00:00
-- url     : https://prove2.me/submissions/549b1361-37ab-44af-846c-528cd6cbbc48

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_finrank_gmap
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_smul_mem_gmap


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
theorem _root_.solution (hD : LatData k n B red ρ t v) (γ : Γ) (x : Fin (n + 1) → k) (j : ℕ) :
    ρ γ (zx v x j) = zx v ((red γ).val *ᵥ x) j := by
  unfold zx
  rw [map_sum]
  simp_rw [hD.equiv]
  refine Finset.sum_equiv (gmapEquiv (red γ)) ?_ (fun _ _ => rfl)
  intro M
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  show _ ↔ (red γ).val *ᵥ x ∈ gmap (red γ) M ∧ Module.finrank k ↥(gmap (red γ) M) + j = n + 1
  rw [smul_mem_gmap, finrank_gmap]
end GlobalTheory.CompanionTheory.GapOpMain
