-- Prove2me | solution 1 for HeckeCharacter.IsFiniteOrderHeckeChar.exists_dirichletIdeleChar_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/78f6d283-4e98-552d-9bb1-57d1f4a54e02

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Theorems.Thm_HeckeCharacter_IsFiniteOrderHeckeChar_exists_admitsModulus
import Theorems.Thm_HeckeCharacter_IsFiniteOrderHeckeChar_exists_dirichletIdeleChar_eq_of_admitsModulus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_IsFiniteOrderHeckeChar_exists_dirichletIdeleChar_eq

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem solution
    {μ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} (hμ : HeckeCharacter.IsFiniteOrderHeckeChar ℚ μ) :
    ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N), χ.dirichletIdeleChar = μ := by
  obtain ⟨N, hN0, hmod⟩ := hμ.exists_admitsModulus
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨χ, hχ⟩ := hμ.exists_dirichletIdeleChar_eq_of_admitsModulus hmod
  exact ⟨N, inferInstance, χ, hχ⟩

end S_HeckeCharacter_IsFiniteOrderHeckeChar_exists_dirichletIdeleChar_eq
end P2MW
export P2MW.S_HeckeCharacter_IsFiniteOrderHeckeChar_exists_dirichletIdeleChar_eq (solution)
