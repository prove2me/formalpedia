-- Prove2me | solution 1 for NumberField.isPGroup_algEquiv_compositum_of_isPGroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3ea1d78c-00df-55e6-8789-48d8a04eb646

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_isPGroup_algEquiv_compositum_of_isPGroup

set_option autoImplicit false

theorem solution
    (E F L N : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra E F] [Algebra E L] [Algebra E N] [Algebra F N] [Algebra L N]
    [IsScalarTower E F N] [IsScalarTower E L N] [IsGalois E F] [IsGalois E L] [IsGalois E N]
    (p : ℕ) [Fact p.Prime] (hF : IsPGroup p (F ≃ₐ[E] F)) (hL : IsPGroup p (L ≃ₐ[E] L))
    (hgen : ∀ σ : N ≃ₐ[E] N, (∀ x : F, σ (algebraMap F N x) = algebraMap F N x) →
      (∀ y : L, σ (algebraMap L N y) = algebraMap L N y) → σ = 1) :
    IsPGroup p (N ≃ₐ[E] N) := by
  intro σ
  obtain ⟨i, hi⟩ := hF (AlgEquiv.restrictNormalHom F σ)
  obtain ⟨j, hj⟩ := hL (AlgEquiv.restrictNormalHom L σ)
  refine ⟨i + j, hgen _ (fun x => ?_) (fun y => ?_)⟩
  · have h1 : AlgEquiv.restrictNormalHom F (σ ^ p ^ (i + j)) = 1 := by
      rw [map_pow, pow_add, pow_mul, hi, one_pow]
    have h2 := AlgEquiv.restrictNormal_commutes (σ ^ p ^ (i + j)) F x
    rw [← h2]
    change algebraMap F N (AlgEquiv.restrictNormalHom F (σ ^ p ^ (i + j)) x) = _
    rw [h1, AlgEquiv.one_apply]
  · have h1 : AlgEquiv.restrictNormalHom L (σ ^ p ^ (i + j)) = 1 := by
      rw [map_pow, pow_add, mul_comm, pow_mul, hj, one_pow]
    have h2 := AlgEquiv.restrictNormal_commutes (σ ^ p ^ (i + j)) L y
    rw [← h2]
    change algebraMap L N (AlgEquiv.restrictNormalHom L (σ ^ p ^ (i + j)) y) = _
    rw [h1, AlgEquiv.one_apply]

end S_NumberField_isPGroup_algEquiv_compositum_of_isPGroup
end P2MW
export P2MW.S_NumberField_isPGroup_algEquiv_compositum_of_isPGroup (solution)
