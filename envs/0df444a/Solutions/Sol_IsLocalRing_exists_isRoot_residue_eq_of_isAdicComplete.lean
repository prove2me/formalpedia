-- Prove2me | solution 1 for IsLocalRing.exists_isRoot_residue_eq_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8066531b-fd48-51d8-9e12-34a7b3ad29ac

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_isRoot_residue_eq_of_isAdicComplete

set_option autoImplicit false

open Polynomial IsLocalRing in
theorem solution
    {C : Type*} [CommRing C] [IsLocalRing C] [IsAdicComplete (maximalIdeal C) C]
    (p : C[X]) (hp : p.Monic) (α : ResidueField C)
    (hα : (p.map (residue C)).IsRoot α) (hα' : ¬ (derivative (p.map (residue C))).IsRoot α) :
    ∃ x : C, p.IsRoot x ∧ residue C x = α := by
  obtain ⟨a₀, rfl⟩ := residue_surjective α
  have hev : ∀ q : C[X], residue C (q.eval a₀) = (q.map (residue C)).eval (residue C a₀) := fun q => by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have h₁ : p.eval a₀ ∈ maximalIdeal C := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    show residue C (p.eval a₀) = 0
    rw [hev]
    exact hα
  have h₂ : IsUnit (Ideal.Quotient.mk (maximalIdeal C) (p.derivative.eval a₀)) := by
    show IsUnit (residue C (p.derivative.eval a₀))
    rw [hev, ← Polynomial.derivative_map, isUnit_iff_ne_zero]
    exact hα'
  obtain ⟨a, ha, hamem⟩ := HenselianRing.is_henselian p hp a₀ h₁ h₂
  refine ⟨a, ha, ?_⟩
  rw [← sub_eq_zero, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hamem

end S_IsLocalRing_exists_isRoot_residue_eq_of_isAdicComplete
end P2MW
export P2MW.S_IsLocalRing_exists_isRoot_residue_eq_of_isAdicComplete (solution)
