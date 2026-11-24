-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpMain.sum_hyperplanes_complement_flags
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:33:26.571045+00:00
-- url     : https://prove2.me/submissions/21d133b1-cd50-458b-9b95-70ef1e46fc19

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_finrank_gmap
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_mem_riemannRochSpace_iff_regularAt_everywhere
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
theorem _root_.solution (hD : LatData k n B red ρ t v) {gam : (Fin (n + 1) → k) → Γ} (hc : IsCov red gam)
    {a : Fin (n + 1) → k} (ha : a ≠ 0) (j : ℕ) :
    ρ (gam a) (∑ M ∈ Finset.univ.filter
      (fun M : Submodule k (Fin (n + 1) → k) => M ≤ H0 k n ∧ Module.finrank k M + (j + 1) = n + 1), v M) =
    ∑ M ∈ Finset.univ.filter
      (fun M : Submodule k (Fin (n + 1) → k) => (∀ x ∈ M, a ⬝ᵥ x = 0) ∧ Module.finrank k M + (j + 1) = n + 1), v M := by
  rw [map_sum]
  simp_rw [hD.equiv]
  refine Finset.sum_equiv (gmapEquiv (red (gam a))) ?_ (fun _ _ => rfl)
  intro M
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  show _ ↔ (∀ x ∈ gmap (red (gam a)) M, a ⬝ᵥ x = 0) ∧
    Module.finrank k ↥(gmap (red (gam a)) M) + (j + 1) = n + 1
  rw [finrank_gmap]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro hM x hx
    rw [mem_gmap] at hx
    have h2 := hc a ha (((red (gam a))⁻¹).val *ᵥ x)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h2
    rw [h2]
    exact (mem_riemannRochSpace_iff_regularAt_everywhere _).mp (hM hx)
  · intro h z hz
    rw [mem_riemannRochSpace_iff_regularAt_everywhere, ← hc a ha z]
    exact h _ ((smul_mem_gmap _ _ _).mpr hz)
end GlobalTheory.CompanionTheory.GapOpMain
