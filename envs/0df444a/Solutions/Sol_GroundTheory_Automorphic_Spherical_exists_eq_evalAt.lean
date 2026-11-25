-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.exists_eq_evalAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:30.20273+00:00
-- url     : https://prove2.me/submissions/4bcec012-f0c2-40ec-97c2-b4a186d8476e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical
open AddMonoidAlgebra
variable {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution (ψ : LaurentRing n →ₐ[ℂ] ℂ) : ∃ w : Fin n → ℂˣ, ψ = evalAt w := by
  set M : Multiplicative (Fin n → ℤ) →* ℂ := (AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ)).symm ψ
  let U : Multiplicative (Fin n → ℤ) →* ℂˣ := M.toHomUnits
  set w : Fin n → ℂˣ := fun i => U (Multiplicative.ofAdd (Pi.single i 1))
  refine ⟨w, ?_⟩
  have hl : ∀ l : Multiplicative (Fin n → ℤ),
      l = ∏ i, (Multiplicative.ofAdd (Pi.single i 1 : Fin n → ℤ)) ^ (Multiplicative.toAdd l i) := by
    intro l
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hM : M = pointHom w := by
    refine MonoidHom.ext fun l => ?_
    have h1 : M l = (U l : ℂ) := rfl
    rw [h1]
    conv_lhs => rw [hl l]
    rw [map_prod, Units.coe_prod]
    simp only [map_zpow]
    rfl
  rw [evalAt, ← hM, Equiv.apply_symm_apply]
end GroundTheory.Automorphic.Spherical
