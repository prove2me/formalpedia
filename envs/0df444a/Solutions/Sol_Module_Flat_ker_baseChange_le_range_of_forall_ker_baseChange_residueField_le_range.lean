-- Prove2me | solution 1 for Module.Flat.ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/37cbc2af-5ae5-5453-b619-18c7fff79ad3

import Mathlib
import Theorems.Thm_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range
import Theorems.Thm_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Flat_ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range

set_option autoImplicit false

universe u

open TensorProduct

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (hfib : ∀ i : ℕ,
      LinearMap.ker ((d (i + 1)).baseChange (IsLocalRing.ResidueField R)) ≤
        LinearMap.range ((d i).baseChange (IsLocalRing.ResidueField R))) :
    (∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i)) ∧
      ∀ (K : Type u) [Field K] [Algebra R K] (i : ℕ),
        LinearMap.ker ((d (i + 1)).baseChange K) ≤ LinearMap.range ((d i).baseChange K) := by
  have hex : ∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i) := by
    refine Module.Flat.ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range C d hdd n hbd hfin ?_
    intro 𝔪 h𝔪 i
    obtain rfl : 𝔪 = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal h𝔪
    exact hfib i
  exact ⟨hex, fun K _ _ i => (Module.Flat.flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range C d hdd n hbd hex).2.2 K i⟩

end S_Module_Flat_ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range
end P2MW
export P2MW.S_Module_Flat_ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range (solution)
