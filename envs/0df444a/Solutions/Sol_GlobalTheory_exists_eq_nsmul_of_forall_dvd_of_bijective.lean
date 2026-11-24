-- Prove2me | solution 1 for GlobalTheory.exists_eq_nsmul_of_forall_dvd_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:40:19.567447+00:00
-- url     : https://prove2.me/submissions/4a7e8e8d-ddb5-49ea-b24b-3c9ce81218f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEqNsmulOfForallDvdOfBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {La : Type} [AddCommGroup La]
    (EF : LinearMap.BilinForm ℤ La) (hEF : Function.Bijective EF) (N : ℕ) (hN : 0 < N) (c : La)
    (hc : ∀ x, (N : ℤ) ∣ EF c x) : ∃ b, c = N • b := by
  let g : La →ₗ[ℤ] ℤ :=
    { toFun := fun x => EF c x / N
      map_add' := fun x y => by
        simp only [map_add]
        exact Int.add_ediv_of_dvd_left (hc x)
      map_smul' := fun r x => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc r (hc x) }
  obtain ⟨b, hb⟩ := hEF.2 g
  refine ⟨b, hEF.1 ?_⟩
  ext x
  have h1 : EF b x = EF c x / N := by rw [hb]; rfl
  rw [map_nsmul, LinearMap.smul_apply, h1, nsmul_eq_mul]
  exact (Int.mul_ediv_cancel' (hc x)).symm
end GlobalTheory
