-- Prove2me | solution 1 for GlobalTheory.homLocLift_injective_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:18.375479+00:00
-- url     : https://prove2.me/submissions/5d2bef1f-01f5-4b36-964e-f7d2e4d469e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial CategoryTheory
universe u
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  [IsScalarTower R (MvPolynomial ι R) M] {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ]
  {T : Type*} [AddCommGroup T] [Module R T] {s : Finset ι} {n : ℤ}
  (φ : ∀ k : ℕ, ℳ (n + k * s.card) →ₗ[R] T)
  (hφ : ∀ (k : ℕ) (m : ℳ (n + k * s.card)) (m' : ℳ (n + (k + 1 : ℕ) * s.card)),
    (m' : M) = xProd R s • (m : M) → φ (k + 1) m' = φ k m)
include hφ
namespace GlobalTheory
theorem _root_.solution : Function.Injective (homLocLift φ hφ) ↔
    ∀ k m, φ k m = 0 → ∃ l : ℕ, xProd R s ^ l • (m : M) = 0 := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h k m hm
    exact awayFrac_eq_zero_iff.1
      (congrArg Subtype.val (h _ ((homLocLift_homLocMk φ hφ k m).trans hm)))
  · intro h z hz
    obtain ⟨k, m, rfl⟩ := exists_homLocMk z
    exact Subtype.ext (awayFrac_eq_zero_iff.2 (h k m ((homLocLift_homLocMk φ hφ k m).symm.trans hz)))
end GlobalTheory
