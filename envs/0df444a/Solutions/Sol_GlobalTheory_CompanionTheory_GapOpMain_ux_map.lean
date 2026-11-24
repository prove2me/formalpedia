-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpMain.ux_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:06:41.381506+00:00
-- url     : https://prove2.me/submissions/fa339cca-6599-4fed-8d25-3a398b4d4900

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_dualEquiv_dot
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_w_map

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
    {y : V} (hy : y ∈ stabV red ρ) (γ : Γ) (x : Fin (n + 1) → k) :
    ρ γ (ux ρ t gam y x) = ux ρ t gam y ((red γ).val *ᵥ x) := by
  unfold ux
  rw [map_sum]
  refine Finset.sum_equiv (dualEquiv (red γ)) ?_ ?_
  · intro a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, dualEquiv_dot]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    exact w_map hD hc hy γ ha0
end GlobalTheory.CompanionTheory.GapOpMain
