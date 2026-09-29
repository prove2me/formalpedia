-- Prove2me | solution 1 for ModularCurve.characterLattice_free_and_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/2f842041-0184-5bf6-8d27-ace9baaac546

import Mathlib
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_characterLattice_free_and_finrank_eq

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "degreeOn degreeOn_apply characterLattice"
p2m_open "ModularCurve"

theorem dzl_degreeOn_single {S : Type*} [Fintype S] [DecidableEq S] (s : S) (n : ℤ) :
    degreeOn S (Pi.single s n) = n := by
  simp [degreeOn_apply]

theorem dzl_degreeOn_surjective {S : Type*} [Fintype S] (s₀ : S) :
    Function.Surjective (degreeOn S) := by
  classical
  intro n
  exact ⟨Pi.single s₀ n, dzl_degreeOn_single s₀ n⟩

theorem dzl_finrank_eq_of_nonempty {S : Type*} [Fintype S] (s₀ : S) :
    Module.finrank ℤ (characterLattice S) = Fintype.card S - 1 := by

  have hq : Module.finrank ℤ ((S → ℤ) ⧸ characterLattice S) + Module.finrank ℤ (characterLattice S) =
      Module.finrank ℤ (S → ℤ) :=
    Submodule.finrank_quotient_add_finrank (characterLattice S)
  have h1 : Module.finrank ℤ ((S → ℤ) ⧸ characterLattice S) = Module.finrank ℤ ℤ :=
    LinearEquiv.finrank_eq ((degreeOn S).quotKerEquivOfSurjective (dzl_degreeOn_surjective s₀))
  rw [h1, Module.finrank_self, Module.finrank_pi] at hq
  omega

end ModularCurve

theorem solution (S : Type*) [Fintype S] :
    Module.Free ℤ (ModularCurve.characterLattice S) ∧
      Module.finrank ℤ (ModularCurve.characterLattice S) = Fintype.card S - 1 := by
  refine ⟨inferInstance, ?_⟩
  cases isEmpty_or_nonempty S with
  | inl h =>
    haveI : Subsingleton (ModularCurve.characterLattice S) := inferInstance
    rw [Fintype.card_eq_zero, Module.finrank_zero_of_subsingleton]
  | inr h =>
    obtain ⟨s₀⟩ := h
    exact ModularCurve.dzl_finrank_eq_of_nonempty s₀

#print axioms solution

end S_ModularCurve_characterLattice_free_and_finrank_eq
end P2MW
export P2MW.S_ModularCurve_characterLattice_free_and_finrank_eq (solution)
