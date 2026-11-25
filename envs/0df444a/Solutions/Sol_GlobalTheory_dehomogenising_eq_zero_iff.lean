-- Prove2me | solution 1 for GlobalTheory.dehomogenising_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:58:45.695684+00:00
-- url     : https://prove2.me/submissions/856b2bae-e9bc-49c5-a8a0-1112a8a47f1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsXPowSmulEqZeroOfEqXSubOneSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_DehomogenisingEqZeroIff
import Theorems.Thm_GlobalTheory_exists_homogeneous_add_X_sub_one_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) (B : Type) [CommRing B] (π : MvPolynomial ι R →+* B) (P : Type) [AddCommGroup P] [Module B P] (ε : M →ₛₗ[π] P), π (X i) = 1 → (∀ n, ∀ y ∈ ℳ n, ε y = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0) → ∀ y, ε y = 0 ↔ ∃ w : M, y = (X i - 1 : MvPolynomial ι R) • w := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i B _ π P _ _ ε hπ hker y
  have hkill : ∀ w : M, ε ((X i - 1 : MvPolynomial ι R) • w) = 0 := by
    intro w
    rw [ε.map_smulₛₗ, map_sub, hπ, map_one, sub_self, zero_smul]
  constructor
  · intro hy
    obtain ⟨n₀, hn⟩ := exists_homogeneous_add_X_sub_one_smul ℳ i y
    obtain ⟨y', hy', w, rfl⟩ := hn n₀ le_rfl
    have hε : ε y' = 0 := by
      rwa [map_add, hkill, add_zero] at hy
    obtain ⟨k, hk⟩ := hker n₀ y' hy' hε
    refine ⟨w - (∑ j ∈ Finset.range k, (X i : MvPolynomial ι R) ^ j) • y', ?_⟩
    rw [smul_sub, smul_smul, mul_geom_sum, sub_smul ((X i : MvPolynomial ι R) ^ k), hk, one_smul]
    abel
  · rintro ⟨w, rfl⟩
    exact hkill w
end GlobalTheory
