-- Prove2me | solution 1 for GlobalTheory.exists_awayFrac_common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:55:11.235347+00:00
-- url     : https://prove2.me/submissions/8f2837eb-dc68-471c-8804-d8be90fa6237

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsBaseChangeAwayOfIntertwine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
open GlobalTheory
variable {R₀ R A₀ A : Type} [CommRing R₀] [CommRing R] [CommRing A₀] [CommRing A] [Algebra R₀ R]
  [Algebra R₀ A₀] [Algebra R A] [Algebra R₀ A] [IsScalarTower R₀ R A]
  {N₀ N : Type} [AddCommGroup N₀] [Module R₀ N₀] [Module A₀ N₀] [IsScalarTower R₀ A₀ N₀]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] [Module R₀ N]
  [IsScalarTower R₀ R N] [IsScalarTower R₀ A N]
namespace GlobalTheory
theorem _root_.solution {f : A₀} (z w : LocalizedModule.Away f N₀) :
    ∃ k m m', awayFrac N₀ f k m = z ∧ awayFrac N₀ f k m' = w := by
  obtain ⟨k, m, rfl⟩ := exists_awayFrac z
  obtain ⟨j, m', rfl⟩ := exists_awayFrac w
  exact ⟨k + j, f ^ j • m, f ^ k • m', awayFrac_add_pow_smul _ _ _ _,
    by rw [add_comm, awayFrac_add_pow_smul]⟩
end GlobalTheory
