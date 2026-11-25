-- Prove2me | solution 1 for GlobalTheory.nonempty_homLoc_singleton_equiv_quotSMulTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:10:48.898515+00:00
-- url     : https://prove2.me/submissions/d6045c79-68f0-423b-8a5f-3633319989ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsXPowSmulEqZeroOfEqXSubOneSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyHomLocSingletonEquivQuotSMulTop
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_X_sub_one_smul_graded
import Theorems.Thm_GlobalTheory_homLocLift_injective_iff
import Theorems.Thm_GlobalTheory_homLocLift_surjective_iff
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open scoped Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι), Nonempty (homLoc ℳ {i} 0 ≃ₗ[R] QuotSMulTop (X i - 1 : MvPolynomial ι R) M) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i
  obtain ⟨-, h2, h3⟩ := GlobalTheory.X_sub_one_smul_graded ι R M ℳ i
  let K : Submodule (MvPolynomial ι R) M := (X i - 1 : MvPolynomial ι R) • ⊤
  have hK : ∀ y : M, y ∈ K ↔ ∃ w : M, y = (X i - 1 : MvPolynomial ι R) • w := fun y => by
    rw [Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨w, _, h⟩ => ⟨w, h.symm⟩, fun ⟨w, h⟩ => ⟨w, trivial, h.symm⟩⟩
  let φ : ∀ k : ℕ, ℳ (0 + k * (({i} : Finset ι).card : ℤ)) →ₗ[R]
      QuotSMulTop (X i - 1 : MvPolynomial ι R) M :=
    fun k => (K.mkQ.restrictScalars R) ∘ₗ (ℳ _).subtype
  have hφv : ∀ k m, φ k m = Submodule.Quotient.mk (m : M) := fun _ _ => rfl
  have hφ : ∀ (k : ℕ) (m : ℳ (0 + k * (({i} : Finset ι).card : ℤ)))
      (m' : ℳ (0 + (k + 1 : ℕ) * (({i} : Finset ι).card : ℤ))),
      (m' : M) = xProd R {i} • (m : M) → φ (k + 1) m' = φ k m := by
    intro k m m' h
    rw [hφv, hφv, Submodule.Quotient.eq]
    refine (hK _).2 ⟨m, ?_⟩
    rw [h, sub_smul, one_smul, xProd, Finset.prod_singleton]
  refine ⟨LinearEquiv.ofBijective (homLocLift φ hφ) ⟨?_, ?_⟩⟩
  · rw [homLocLift_injective_iff]
    intro k m hm
    rw [hφv, Submodule.Quotient.mk_eq_zero] at hm
    obtain ⟨w, hw⟩ := (hK _).1 hm
    obtain ⟨l, hl⟩ := h2 _ _ w m.2 hw
    exact ⟨l, by rwa [xProd, Finset.prod_singleton]⟩
  · rw [homLocLift_surjective_iff]
    intro t
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    obtain ⟨n₀, hn⟩ := h3 y
    obtain ⟨y', hy', w, hw⟩ := hn (0 + (n₀.toNat : ℕ) * (({i} : Finset ι).card : ℤ))
      (by simp)
    refine ⟨n₀.toNat, ⟨y', hy'⟩, ?_⟩
    rw [hφv, eq_comm, Submodule.Quotient.eq]
    exact (hK _).2 ⟨w, by rw [hw, add_sub_cancel_left]⟩
end GlobalTheory
