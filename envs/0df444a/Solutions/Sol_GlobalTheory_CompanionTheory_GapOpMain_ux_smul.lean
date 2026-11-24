-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpMain.ux_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:33:28.973719+00:00
-- url     : https://prove2.me/submissions/ab1baf66-bd55-43d8-96ad-21d23ec43829

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_w_scale

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
    {y : V} (hy : y ∈ stabV red ρ) (x : Fin (n + 1) → k) {s : k} (hs : s ≠ 0) :
    ux ρ t gam y (s • x) = ux ρ t gam y x := by
  let e : (Fin (n + 1) → k) ≃ (Fin (n + 1) → k) :=
    { toFun := fun a => s • a
      invFun := fun b => s⁻¹ • b
      left_inv := fun a => by simp only [smul_smul, inv_mul_cancel₀ hs, one_smul]
      right_inv := fun b => by simp only [smul_smul, mul_inv_cancel₀ hs, one_smul] }
  unfold ux
  refine Finset.sum_equiv e ?_ ?_
  · intro a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show a ⬝ᵥ (s • x) = 1 ↔ (s • a) ⬝ᵥ x = 1
    rw [dotProduct_smul, smul_dotProduct]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    exact (w_scale hD hc hy ha0 hs).symm
end GlobalTheory.CompanionTheory.GapOpMain
